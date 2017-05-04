(* In this file, P, N, A are separate, rather than a triple *)

Require Export compcert.cfrontend.Clight.
Require Export veric.Clight_new.
Require Export examples.if1.
Require Export compcert.lib.Maps. (* for PMap and ZMap *)
Require Export compcert.common.Events.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export floyd.base.
Require Import List. Import ListNotations.

Definition simplestate := (corestate * mem)%type.

Inductive label : Set := Lo | Hi.

Definition stack_clsf := ident -> label.

Definition heap_loc := (positive * Z)%type. (* block id and offset *)

Definition heap_clsf := heap_loc -> label.

(* TODO this should match VST, i.e. we should have "state_pred = environ->mpred" for preconditions,
   and for postconditions, it's ret_assert in VST *)
Definition state_pred := corestate -> mem -> Prop.

Definition pre_assert := environ -> mpred.
(* "ret_assert := exitkind -> option val -> environ -> mpred" is already defined by VST *)

Definition ifc_pre(A: Type) := ((A -> pre_assert) * (A -> stack_clsf) * (A -> heap_clsf))%type.
Definition ifc_post(A: Type) := ((A -> ret_assert) * (A -> stack_clsf) * (A -> heap_clsf))%type.

(* TODO get rid of these *)
Parameter VST_pre_to_state_pred : pre_assert -> state_pred.
Parameter VST_post_to_state_pred : ret_assert -> state_pred.

Inductive star (ge: genv): corestate -> mem -> corestate -> mem -> Prop :=
  | star_refl: forall s m,
      star ge s m s m
  | star_step: forall s1 m1 s2 m2 s3 m3,
      cl_step ge s1 m1 s2 m2 ->
      star ge s2 m2 s3 m3 ->
      star ge s1 m1 s3 m3.

(* general low-equivalence *)
Definition gen_lo_equiv{Loc V: Type}(f1 f2: Loc -> label)(s1 s2: Loc -> V) :=
  forall (l: Loc), f1 l = Lo -> f2 l = Lo -> s1 l = s2 l.

(* ExtCall not considered currently *)
Definition stack_lo_equiv(s1 s2: corestate)(N1 N2: stack_clsf): Prop :=
  match s1, s2 with
  | (State e1 te1 c1), (State e2 te2 c2) =>
     e1 = e2 /\ c1 = c2 /\ gen_lo_equiv N1 N2 (fun i => te1 ! i) (fun i => te2 ! i)
  | _, _ => False
  end.

Definition heap_access(m: mem)(l: heap_loc): memval :=
  let (b, i) := l in (ZMap.get i (PMap.get b (Mem.mem_contents m))).

Definition heap_lo_equiv(m1 m2: mem)(A1 A2: heap_clsf): Prop :=
  gen_lo_equiv A1 A2 (heap_access m1) (heap_access m2).

Definition simple_ifc {A : Type} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> state_pred) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= forall (x1 x2: A) (ge: genv) (e1 e2: env) (te1 te2: temp_env) (s1' s2': corestate)
          (m1 m1' m2 m2': mem),
   let s1 := (State e1 te1 [Kseq c]) in
   let s2 := (State e2 te2 [Kseq c]) in
   preP x1 s1 m1 ->
   preP x2 s2 m2 ->
   stack_lo_equiv s1 s2 (preN x1) (preN x2) ->
   heap_lo_equiv  m1 m2 (preA x1) (preA x2) ->
   star ge s1 m1 s1' m1' ->
   star ge s2 m2 s2' m2' ->
   stack_lo_equiv s1' s2' (postN x1) (postN x2) /\ heap_lo_equiv m1 m2 (postA x1) (postA x2).

Definition ifc_core {A: Type} (Delta: tycontext)
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= let preP'  := fun (x: A) => VST_pre_to_state_pred (preP x) in
   let postP' := fun (x: A) => VST_post_to_state_pred (postP x) in
   simple_ifc Delta preP' preN preA c postP' postN postA.

Definition ifc_def {A: Type} {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= (forall x: A, @semax cs Espec Delta (preP x) c (postP x)) /\
   (ifc_core Delta preP preN preA c postP postN postA).

Notation "'ifc' [ x : A ] Delta |-- preP preN preA c postP postN postA" :=
  (@ifc_def A _ _ Delta (fun x => preP)
                        (fun x => preN)
                        (fun x => preA)
                        c
                        (fun x => postP)
                        (fun x => postN)
                        (fun x => postA))
  (at level 200,
   x at level 0, Delta at level 0,
   preP at level 0, preN at level 0, preA at level 0,
   c at level 0,
   postP at level 0, postN at level 0, postA at level 0).

(*
Parameter D1: tycontext.
Parameter P1: pre_assert.
Parameter Q1: ret_assert.
Definition N1: stack_clsf := fun i => if Pos.testbit i 0 then Lo else Hi.
Definition A1: heap_clsf := fun l => let (b, ofs) := l in if Z.testbit ofs 0 then Lo else Hi.
Require Import floyd.proofauto.
Instance CompSpecs : compspecs. admit. Admitted.
Instance Espec: OracleKind. Admitted.
Definition t1 := ifc [ a : nat ] D1 |-- P1 N1 A1 Sskip (fun _ => fun _ => !! (a = a)) N1 A1.
Print t1.
*)

Definition WITHclause_type(fspec: ident * funspec): Type := match fspec with
| (_, mk_funspec _ _ (rmaps.ConstType A) _ _ _ _) => A
(* error: we always expect an rmaps.ConstType, because that's what NDmk_funspec passes to mk_funspec *)
| _ => unit
end.

Record ifc_funspec: Type := mk_ifc_funspec {
  functional_spec : (ident * funspec)%type;
  ifc_stack_pre   : (WITHclause_type functional_spec) -> stack_clsf;
  ifc_heap_pre    : (WITHclause_type functional_spec) -> heap_clsf;
  ifc_stack_post  : (WITHclause_type functional_spec) -> stack_clsf;
  ifc_heap_post   : (WITHclause_type functional_spec) -> heap_clsf
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
  (P': vst_fun_assert T) (N': T -> stack_clsf) (A': T -> heap_clsf)
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
  (N' : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> stack_clsf)
  (A' : WITHclause_type (i, mk_funspec fsig c T0 P P' P_ne Q_ne) -> heap_clsf)
: Prop := 
  match T0 as t return
    (let T := force_const_type t in (forall
       P0 P'0 ,
     super_non_expansive P0 ->
     super_non_expansive P'0 ->
     (T -> stack_clsf) ->
     (T -> heap_clsf) ->
     (T -> stack_clsf) ->
     (T -> heap_clsf) -> Prop))
  with
  | ConstType T => fun P0 P'0 _ _ N0 A0 N'0 A'0 => ifc_body00 V G C f T P0 N0 A0 P'0 N'0 A'0
  | _ => fun _ _ _ _ _ _ _ _  => False
  end P P' P_ne Q_ne N A N' A'.

Definition ifc_body
       (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ifc_funspec) : Prop :=
  match spec with (mk_ifc_funspec (i, mk_funspec fsig cc T P P' Pne P'ne) N A N' A') =>
    ifc_body0 V G C f i fsig cc T P P' Pne P'ne N A N' A'
  end.
