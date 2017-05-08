Require Import compcert.cfrontend.Clight.
Require Import veric.Clight_new.
Require Import compcert.lib.Maps. (* for PMap and ZMap *)
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import floyd.base.
Require Import floyd.canon.
Require Import ifc.ifc.
Require Import lib.LibTactics.

Local Open Scope logic.

Definition ioverridePost{A: Type}(Q: A -> environ -> mpred)(R : A -> ret_assert): A -> ret_assert :=
  fun (x: A) => (overridePost (Q x) (R x)).

Ltac split_ifc_hyps :=
  repeat match goal with
  | H: ifc_def _ _ _ _ _ _ _ _ |- _ =>
      let Hs := fresh H "s" in 
      let Hi := fresh H "i" in
      destruct H as [Hs Hi]
  end.

Lemma star_seq_inv: forall ge e1 te1 e3 te3 h t m1 m3,
  star ge (State e1 te1 (Kseq (Ssequence h t) :: nil)) m1 (State e3 te3 nil) m3 ->
  exists e2 te2 m2, star ge (State e1 te1 (Kseq h :: nil)) m1 (State e2 te2 nil) m2
                 /\ star ge (State e2 te2 (Kseq t :: nil)) m2 (State e3 te3 nil) m3.
Proof.
  intros. inverts H as Step Star. inverts Step as Step.
  pose proof (star_step _ _ _ _ _ _ _ Step Star) as H. clear Star Step s2 m2.
  remember (State e1 te1 (Kseq h :: Kseq t :: nil)) as s1.
  remember (State e3 te3 nil) as s3.
  gen Heqs1 Heqs3.
  gen e1 te1 e3 te3 h t.
  induction H.
  - (* star_refl: contradiction *)
    intros. rewrite Heqs1 in Heqs3. discriminate.
  - (* star_step *)
    intros. (* this IH is not strong enough... *)
Admitted.

(* We need lifting on top of VST's lifting... *)

Definition iand{A: Type}(P1: A -> pre_assert)(P2: A -> pre_assert): A -> pre_assert :=
  fun (x: A) => (P1 x) && (P2 x).

Definition iprop{A: Type}(P: pre_assert): A -> pre_assert := fun (_: A) => P.

Section RULES.
Context (Espec : OracleKind).
Context (CS: compspecs).

Lemma ifc_seq{T: Type}:
  forall Delta (P1 P2: T -> environ -> mpred) (P3: T -> ret_assert) h t
    (N1 N2 N3: T -> stack_clsf) (A1 A2 A3: T -> heap_clsf),
  ifc_def Delta P1 N1 A1 h (ioverridePost P2 P3) N2 A2 ->
  ifc_def (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.
Proof.
  introv H1 H2. split_ifc_hyps. split.
  - intro. apply* semax_seq.
  - unfold ifc_core, simple_ifc in *.
    intros x x' ge e1 e1' e3 e3' te1 te1' te3 te3' m1 m1' m3 m3'.
    intros Sat1 Sat1' SE1 HE1 Star1 Star1'.
    apply star_seq_inv in Star1. destruct Star1 as [e2 [te2 [m2 [Star1 Star2]]]].
    apply star_seq_inv in Star1'. destruct Star1' as [e2' [te2' [m2' [Star1' Star2']]]].
    edestruct H1i as [SE2 HE2].
    + eapply Sat1.
    + eapply Sat1'.
    + apply* stack_lo_equiv_change_cmd.
    + exact HE1.
    + exact Star1.
    + exact Star1'.
    + clear H1i. eapply H2i.
      * pose proof (VST_sound _ _ _ _ (H1s x)) as C. unfold ioverridePost in C.
        erewrite <- VST_overridePost_to_state_pred. apply* C.
      * pose proof (VST_sound _ _ _ _ (H1s x')) as C. unfold ioverridePost in C.
        erewrite <- VST_overridePost_to_state_pred. apply* C.
      * apply* stack_lo_equiv_change_cmd.
      * exact HE2.
      * exact Star2.
      * exact Star2'.
Grab Existential Variables. exact nil. exact nil. exact nil. exact nil.
Qed.

Definition inormal_ret_assert{A: Type}(P: A -> environ -> mpred): A -> ret_assert :=
  fun (x: A) => normal_ret_assert (P x).

Lemma ifc_ifthenelse: forall {T: Type} (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> stack_clsf) (A': T -> heap_clsf),
  bool_type (typeof b) = true ->
  ifc_def Delta (iand P (iprop (local (`(typed_true  (typeof b)) (eval_expr b))))) N A c1 P' N' A' ->
  ifc_def Delta (iand P (iprop (local (`(typed_false (typeof b)) (eval_expr b))))) N A c2 P' N' A' ->
  ifc_def Delta P N A (Sifthenelse b c1 c2) P' N' A'.
Admitted.

End RULES.
