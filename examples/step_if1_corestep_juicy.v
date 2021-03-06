(* This is an example showing how to use corestepN to step through a program.
   corestepN is basically just N times cl_step plus juicy memory stuff.
   If we use corestepN instead of our homemade star on top of cl_step, we have to deal
   with juicy memory stuff, but we get lemmas from sepcomp.semantics_lemmas for free,
   in particular those at the end of the file in sections corestepN and memstepN. *)

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

(* Inspired by veric.semax.jsafeN *)
Definition stepN: genv -> nat -> corestate -> juicy_mem -> corestate -> juicy_mem -> Prop :=
  corestepN (juicy_core_sem cl_core_sem).

Definition ge: genv := globalenv prog. (* prog is the concrete program in examples.if1 *)

Definition env0 : env := PTree.empty _.

Definition temp_env0 : temp_env := 
  (PTree.Node PTree.Leaf (Some (Vptr (BinNums.xI 24) (Int.repr 0))) PTree.Leaf).

(* Definition m0 := Memory.Mem.empty. *)

Parameter m0: juicy_mem.

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

Axiom admit_resource_decay_and_level: forall (m0: juicy_mem),
  exists m1,
  m_dry m0 = m_dry m1 /\
  resource_decay (nextblock (m_dry m0)) (m_phi m0) (m_phi m1) /\
  level m0 = S (level m1).

(*
Definition lvl_j := (@level juicy_mem juicy_mem_ageable).

Definition lvl_phi := (@level rmap ag_rmap).
*)

(* Overview:
   stepN is defined in this file to instantiate some parameters of
   corestepN, which is, if instantiated with (juicy_core_sem cl_core_sem), defined in terms of
   jstep, which is defined in terms of
   corestep, which is defined in terms of
   cl_step, which is the step relation we were using before in simple_ifc and in step_if1 *)

Goal exists n eFinal teFinal mFinal, forall k,
  stepN ge n
        (State env0 temp_env0 ((Kseq (Scall None main_expr [])) :: k)) m0
        (State eFinal teFinal k) mFinal.
Proof.
  exists 7%nat. do 3 eexists. intro k.
  unfold stepN. unfold corestepN. unfold corestep. unfold juicy_core_sem.

  (* call of main function *)
  destruct (admit_resource_decay_and_level m0) as [m1 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
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
  - rewrite E. constructor.
  - reflexivity.
  } } {

  (* bool b = true; *)
  clear E P.
  destruct (admit_resource_decay_and_level m1) as [m2 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  simpl (fn_body f_main).
  repeat eapply step_seq.
  rewrite E.
  eapply step_set.
  repeat econstructor.
  } }

  (* int n = 2; *)
  clear E P.
  destruct (admit_resource_decay_and_level m2) as [m3 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  repeat eapply step_seq.
  rewrite E.
  eapply step_set.
  repeat econstructor.
  } }

  (* int m = 3; *)
  clear E P.
  destruct (admit_resource_decay_and_level m3) as [m4 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  repeat eapply step_seq.
  rewrite E.
  eapply step_set.
  repeat econstructor.
  } }

  (* if-then-else *)
  clear E P.
  destruct (admit_resource_decay_and_level m4) as [m5 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  repeat eapply step_seq.
  rewrite E.
  eapply step_ifthenelse.
  - econstructor. reflexivity.
  - reflexivity.
  } } {
  simpl (if negb _ then Sset _ _ else _).
  rewrite Int.eq_false by (  rewrite Int.eq_false; intro; discriminate).
  simpl (if negb _ then Sset _ _ else _). 

  (* we're always in the then-branch *)
  clear E P.
  destruct (admit_resource_decay_and_level m5) as [m6 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  rewrite E.
  eapply step_set.
  repeat econstructor.
  } } {

  (* return res; *)
  clear E P.
  destruct (admit_resource_decay_and_level m6) as [m7 [E P]].
  do 2 eexists. split.
  { unfold jstep. refine (conj _ P).
  { unfold corestep, cl_core_sem.
  eapply step_return.
  - simpl. reflexivity.
  - simpl. rewrite E. reflexivity.
  - eexists. repeat constructor.
  - simpl. auto.
  } } {
    (* almost there: "reflexivity" complains:
       cannot instantiate "?mFinal" because "m7" is not in its scope *)
    admit.
  } } } }
Admitted.
