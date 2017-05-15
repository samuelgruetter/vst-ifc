Require Import veric.juicy_base.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_safety.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.expr_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import List. Import ListNotations.

Require Import examples.if1.

Definition stepN: genv -> nat -> corestate -> mem -> corestate -> mem -> Prop :=
  corestepN cl_core_sem.

Definition ge: genv := globalenv prog. (* prog is the concrete program in examples.if1 *)

Definition env0 : env := PTree.empty _.

Definition temp_env0 : temp_env := 
  (PTree.Node PTree.Leaf (Some (Vptr (BinNums.xI 24) (Int.repr 0))) PTree.Leaf).

Definition m0 := Memory.Mem.empty.

Definition main_block: Values.block := ltac:(
  let o := eval hnf in (Globalenvs.Genv.find_symbol ge (Ctypes.prog_main prog)) in
  match o with
  | Some ?b => exact b
  end).

Definition main_fun: fundef := ltac:(
  let o := eval hnf in (Globalenvs.Genv.find_funct_ptr ge main_block) in
  match o with
  | Some ?f => exact f
  end).

Definition main_ptr: val := Vptr main_block Int.zero.

Definition main_expr := (Etempvar 1%positive (Tfunction Tnil tint cc_default)).

Lemma if_Int_eq_dec: forall i (T: Type) (a b: T),
  (if Int.eq_dec i i then a else b) = a.
Proof.
  intros. destruct (Int.eq_dec i i). reflexivity. exfalso. auto.
Qed.

Goal exists n eFinal teFinal mFinal, forall k,
  stepN ge n
        (State env0 temp_env0 ((Kseq (Scall None main_expr [])) :: k)) m0
        (State eFinal teFinal k) mFinal.
Proof.
  exists 7%nat. do 3 eexists. intro k.
  unfold stepN. unfold corestepN. unfold corestep. simpl.

  (* call of main function *)
  do 2 eexists. split. {
  eapply step_call_internal.
  - simpl. reflexivity.
  - constructor. simpl. reflexivity.
  - constructor.
  - simpl. rewrite if_Int_eq_dec. reflexivity.
  - reflexivity.
  - repeat constructor; cbv; intros; repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    end; auto; discriminate.
  - repeat constructor; cbv; intros; repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    end; auto; discriminate.
  - constructor.
  - reflexivity.
  } {

  (* bool b = true; *)
  do 2 eexists. split. {
  simpl (fn_body f_main).
  repeat eapply step_seq.
  eapply step_set.
  repeat econstructor.
  } {

  (* int n = 2; *)
  do 2 eexists. split. {
  repeat eapply step_seq.
  eapply step_set.
  repeat econstructor.
  } {

  (* int m = 3; *)
  do 2 eexists. split. {
  repeat eapply step_seq.
  eapply step_set.
  repeat econstructor.
  } {

  (* if-then-else *)
  do 2 eexists. split. {
  repeat eapply step_seq.
  eapply step_ifthenelse.
  - econstructor. reflexivity.
  - reflexivity.
  } {
  simpl (if negb _ then Sset _ _ else _).
  rewrite Int.eq_false by (  rewrite Int.eq_false; intro; discriminate).
  simpl (if negb _ then Sset _ _ else _). 

  (* we're always in the then-branch *)
  do 2 eexists. split. {
  eapply step_set.
  repeat econstructor.
  } {

  (* return res; *)
  do 2 eexists. split. {
  eapply step_return.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - eexists. repeat constructor.
  - simpl. auto.
  } {
    reflexivity.
  } } } } } } }
Qed.
