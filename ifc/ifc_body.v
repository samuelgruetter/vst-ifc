Require Export lib.LibTactics.
Require Export compcert.cfrontend.Clight.
Require Export veric.Clight_new.
Require Export compcert.lib.Maps. (* for PMap and ZMap *)
Require Export compcert.common.Events.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export sepcomp.semantics.
Require Export sepcomp.semantics_lemmas.
Require Export veric.semax.
Require Export floyd.base.
Require Export floyd.canon.
Require Export ifc.clsf_expr.
Require Export ifc.ifc_def.
Require Import List. Import ListNotations.


Definition WITHclause_type(fspec: ident * funspec): Type := match fspec with
| (_, mk_funspec _ _ (rmaps.ConstType A) _ _ _ _) => A
(* error: we always expect an rmaps.ConstType, because that's what NDmk_funspec passes to mk_funspec *)
| _ => unit
end.

Record ifc_funspec: Type := mk_ifc_funspec {
  functional_spec : (ident * funspec)%type;
  ifc_stack_pre   : (WITHclause_type functional_spec) -> stack_clsf;
  ifc_heap_pre    : (WITHclause_type functional_spec) -> heap_clsf;
  ifc_stack_post  : (WITHclause_type functional_spec) -> ret_stack_clsf;
  ifc_heap_post   : (WITHclause_type functional_spec) -> ret_heap_clsf
}.

Local Open Scope logic.

Require Import veric.rmaps.

(* "T -> assertion" *)
Definition vst_fun_assert (T: Type): Type :=
  forall ts : list Type,
    msl.functors.MixVariantFunctor._functor 
     (dependent_type_functor_rec ts (AssertTT (rmaps.ConstType T))) mpred.

(* inspired by semax_body in VST/veric/semax_prog.v *)
Definition ifc_body00 (V: varspecs) (G: funspecs) (C: compspecs) (f: function)
  (T: Type)
  (P : vst_fun_assert T) (N : T -> stack_clsf) (A : T -> heap_clsf)
  (P': vst_fun_assert T) (N': T -> ret_stack_clsf) (A': T -> ret_heap_clsf)
: Prop :=
  forall Espec ts,
    @ifc_def T C Espec (func_tycontext f V G)
             (fun x rho => P ts x rho * stackframe_of f rho)
             N A
             (Ssequence f.(fn_body) (Sreturn None))
             (fun x => (frame_ret_assert (function_body_ret_assert (fn_return f) (P' ts x))
                                         (stackframe_of f)))
             N' A'.

Definition force_const_type(t: TypeTree): Type :=
      match t with
      | ConstType A0 => A0
      | Mpred => unit
      | DependentType _ => unit
      | ProdType _ _ => unit
      | ArrowType _ _ => unit
      end.

(* dependent types craziness... *)
Definition ifc_body0 (V : varspecs) (G : funspecs) (C : compspecs) (f : function) (i : ident)
  (fsig : base.funsig) (c : calling_convention) (T0 : TypeTree)
  (P P' : forall ts : list Type,
        functors.MixVariantFunctor._functor
          (dependent_type_functor_rec ts (AssertTT T0)) mpred)
  (P_ne : super_non_expansive P) (Q_ne : super_non_expansive P')
  (N  : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> stack_clsf)
  (A  : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> heap_clsf)
  (N' : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> ret_stack_clsf)
  (A' : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> ret_heap_clsf)
: Prop := 
  match T0 as t return
    (let T := force_const_type t in (forall
       P0 P'0 ,
     super_non_expansive P0 ->
     super_non_expansive P'0 ->
     (T -> stack_clsf) ->
     (T -> heap_clsf) ->
     (T -> ret_stack_clsf) ->
     (T -> ret_heap_clsf) -> Prop))
  with
  | ConstType T => fun P0 P'0 _ _ N0 A0 N'0 A'0 => ifc_body00 V G C f T P0 N0 A0 P'0 N'0 A'0
  | _ => fun _ _ _ _ _ _ _ _  => False
  end P P' P_ne Q_ne N A N' A'.

Definition ifc_body
       (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ifc_funspec) : Prop :=
  match spec with (mk_ifc_funspec (i, mk_funspec fsig cc T P P' Pne P'ne) N A N' A') =>
    ifc_body0 V G C f i fsig cc T P P' Pne P'ne N A N' A'
  end.
