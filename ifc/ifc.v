(* In this file, P, N, A are separate, rather than a triple *)

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
Require Import List. Import ListNotations.

Local Open Scope logic.

Definition stack_clsf := ident -> label.

Definition ret_stack_clsf := exitkind -> option val -> stack_clsf.

Definition heap_loc := (positive * int)%type. (* block id and offset *)

Definition heap_clsf := heap_loc -> label.

Definition ret_heap_clsf := exitkind -> option val -> heap_clsf.

(* TODO this should match VST, i.e. we should have "state_pred = environ->mpred" for preconditions,
   and for postconditions, it's ret_assert in VST
   TODO or as a first step, maybe use environ instead of env and temp_env, and
   construct_rho: genviron -> env -> temp_env -> environ
 *)
Definition state_pred := env -> temp_env -> mem -> Prop.

Definition pre_assert := environ -> mpred.
(* "ret_assert := exitkind -> option val -> environ -> mpred" is already defined by VST *)

(* TODO get rid of these *)
Parameter VST_to_state_pred : pre_assert -> state_pred.
Definition VST_post_to_state_pred : ret_assert -> exitkind -> option val -> state_pred :=
  fun R ek vl => VST_to_state_pred (R ek vl).

Lemma VST_overridePost_to_state_pred00: forall Q R ek vl,
  VST_to_state_pred (overridePost Q R ek vl) =
  if eq_dec ek EK_normal
  then VST_to_state_pred (fun rho : environ => !! (vl = None) && Q rho)
  else VST_to_state_pred (R ek vl).
Proof.
  unfold overridePost. intros. destruct ek; reflexivity.
Qed.

Axiom VST_to_state_pred_commutes_imp: forall P P',
  (P |-- P') ->
  (forall e te m, VST_to_state_pred P e te m -> VST_to_state_pred P' e te m).

Axiom VST_to_state_pred_commutes_imp': forall Delta P P',
  (ENTAIL Delta, P |-- P') ->
  (forall e te m, VST_to_state_pred P e te m -> VST_to_state_pred P' e te m).

Axiom VST_indep_state_pred00: forall P e te m,
  VST_to_state_pred (!! P) e te m -> P.

Axiom VST_indep_state_pred: forall P,
  VST_to_state_pred (!! P) = fun e te m => P.

Axiom VST_to_state_pred_and: forall (P Q: environ -> mpred),
  VST_to_state_pred (P && Q) = 
  (fun e te m => VST_to_state_pred P e te m /\ VST_to_state_pred Q e te m).

Lemma VST_overridePost_to_state_pred: forall Q R ek vl,
  VST_to_state_pred (overridePost Q R ek vl) =
  if eq_dec ek EK_normal
  then fun e te m => vl = None /\ VST_to_state_pred Q e te m
  else VST_to_state_pred (R ek vl).
Proof.
  unfold overridePost. intros. destruct ek; simpl; try reflexivity.
  assert ((fun x : environ => !! (vl = None) && Q x) = !! (vl = None) && Q) as E. {
    extensionality. reflexivity.
  }
  rewrite E. rewrite VST_to_state_pred_and. extensionality e. extensionality te. extensionality m.
  rewrite VST_indep_state_pred. reflexivity.
Qed.

Definition star: genv -> corestate -> mem -> corestate -> mem -> Prop :=
  corestep_star cl_core_sem.

(* general low-equivalence *)
Definition gen_lo_equiv{Loc V: Type}(f1 f2: Loc -> label)(s1 s2: Loc -> V) :=
  forall (l: Loc), f1 l = Lo -> f2 l = Lo -> s1 l = s2 l.

Lemma weaken_gen_lo_equiv{Loc V: Type}: forall (s1 s2: Loc -> V) (f1 f1' f2 f2': Loc -> label),
  lle f1 f1' ->
  lle f2 f2' ->
  gen_lo_equiv f1 f2 s1 s2 ->
  gen_lo_equiv f1' f2' s1 s2.
Proof.
  introv Le1 Le2 LoE. unfold gen_lo_equiv in *. unfold lle in *.
  intros l E1 E2.
  pose proof (equal_f Le1 l) as Le1'. rewrite Le1' in E1.
  pose proof (lub_bot_inv (f1 l) (f1' l) E1) as C1. destruct C1 as [C1 _].
  pose proof (equal_f Le2 l) as Le2'. rewrite Le2' in E2.
  pose proof (lub_bot_inv (f2 l) (f2' l) E2) as C2. destruct C2 as [C2 _].
  apply LoE; assumption.
Qed.

(* ExtCall not considered currently *)
Definition stack_lo_equiv(s1 s2: corestate)(N1 N2: stack_clsf): Prop :=
  match s1, s2 with
  | (State e1 te1 c1), (State e2 te2 c2) =>
     e1 = e2 /\ gen_lo_equiv N1 N2 (fun i => te1 ! i) (fun i => te2 ! i)
  | _, _ => False
  end.

Lemma weaken_stack_lo_equiv: forall (s1 s2: corestate) (N1 N1' N2 N2': stack_clsf),
  lle N1 N1' ->
  lle N2 N2' ->
  stack_lo_equiv s1 s2 N1 N2 ->
  stack_lo_equiv s1 s2 N1' N2'.
Proof.
  introv Le1 Le2 SE. unfold stack_lo_equiv in *.
  destruct s1 as [e1 te1 k1 | _]; destruct s2 as [e2 te2 k2 | _]; try assumption.
  destruct SE as [Eq GE]. apply (conj Eq).
  eapply weaken_gen_lo_equiv; eassumption.
Qed.

Lemma stack_lo_equiv_change_cmd: forall e1 te1 c1 e2 te2 c2 c1' c2' N1 N2,
  stack_lo_equiv (State e1 te1 c1 ) (State e2 te2 c2 ) N1 N2 ->
  stack_lo_equiv (State e1 te1 c1') (State e2 te2 c2') N1 N2.
Proof.
  intros. unfold stack_lo_equiv in *. assumption.
Qed.

Definition heap_access(m: mem)(l: heap_loc): memval :=
  let (b, i) := l in (ZMap.get (Int.signed i) (PMap.get b (Mem.mem_contents m))).

Definition heap_lo_equiv(m1 m2: mem)(A1 A2: heap_clsf): Prop :=
  gen_lo_equiv A1 A2 (heap_access m1) (heap_access m2).

Lemma weaken_heap_lo_equiv: forall (m1 m2: mem) (A1 A1' A2 A2': heap_clsf),
  lle A1 A1' ->
  lle A2 A2' ->
  heap_lo_equiv m1 m2 A1 A2 ->
  heap_lo_equiv m1 m2 A1' A2'.
Proof.
  introv Le1 Le2 HE. unfold heap_lo_equiv in *.
  eapply weaken_gen_lo_equiv; eassumption.
Qed.

Definition same_Noneness{T: Type}(o1 o2: option T): Prop :=
  (o1 = None /\ o2 = None) \/ exists v1 v2, o1 = Some v1 /\ o2 = Some v2.

Definition simple_ifc {A : Type} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postN: A -> ret_stack_clsf) (postA: A -> ret_heap_clsf)
:= forall (x x': A) (ge: genv) (e1 e1' e2 e2': env) (te1 te1' te2 te2': temp_env)
          (m1 m1' m2 m2': mem) (k : cont) (ek ek': exitkind) (vl vl': option val),
   preP x  e1 te1 m1 ->
   preP x' e1' te1' m1' ->
   let s1  := (State e1  te1  (cons (Kseq c) k)) in
   let s1' := (State e1' te1' (cons (Kseq c) k)) in
   let s2  := (State e2  te2  (exit_cont ek  vl  k)) in
   let s2' := (State e2' te2' (exit_cont ek' vl' k)) in
   stack_lo_equiv s1 s1' (preN x) (preN x') ->
   heap_lo_equiv  m1 m1' (preA x) (preA x') ->
   star ge s1  m1  s2  m2 ->
   star ge s1' m1' s2' m2' ->
   ek = ek' /\ same_Noneness vl vl' /\
   stack_lo_equiv s2 s2' (postN x ek vl) (postN x' ek' vl') /\
   heap_lo_equiv  m2 m2' (postA x ek vl) (postA x' ek' vl').

(* TODO Could it happen that (exit_cont ek  vl  k) takes some steps involving a while loop and
   modifying some values and classifications and ends up in exactly (exit_cont ek  vl  k) again? *)
(* TODO How could we say anything about intermediate states?
   postN and postA are only applicable to the state reached after executing all of c!
   And if we allow n to be anything, it could also be too big, so that we run into k! *)

Definition ifc_core {A: Type} (Delta: tycontext)
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> ret_stack_clsf) (postA: A -> ret_heap_clsf)
:= let preP'  := fun (x: A) => VST_to_state_pred (preP x) in
   let postP' := fun (x: A) => VST_post_to_state_pred (postP x) in
   simple_ifc Delta preP' preN preA c postN postA.

Definition ifc_def (A: Type) {cs: compspecs} {Espec: OracleKind} (Delta: tycontext)
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> ret_stack_clsf) (postA: A -> ret_heap_clsf)
:= (forall x: A, @semax cs Espec Delta (preP x) c (postP x)) /\
   (ifc_core Delta preP preN preA c postP postN postA).

Notation "'ifc' [ x : A ] Delta |-- preP preN preA c postP postN postA" :=
  (ifc_def A Delta (fun x => preP)
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

(* TODO connect this to the actual VST soundness proof *)
Axiom VST_sound: forall {Espec: OracleKind} {CS: compspecs} Delta P1 c P2 ek vl k,
  semax Delta P1 c P2 ->
  forall ge e1 te1 m1 e2 te2 m2,
  VST_to_state_pred P1 e1 te1 m1 ->
  star ge (State e1 te1 (cons (Kseq c) k)) m1 (State e2 te2 (exit_cont ek vl k)) m2 ->
  VST_to_state_pred (P2 ek vl) e2 te2 m2.
