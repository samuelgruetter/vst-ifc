Require Import compcert.cfrontend.Clight.
Require Import veric.Clight_new.
Require Import compcert.lib.Maps. (* for PMap and ZMap *)
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import floyd.base.
Require Import floyd.canon.
Require Import floyd.forward_lemmas.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import ifc.ifc.
Require Import lib.LibTactics.

Local Open Scope logic.

Definition ioverridePost{A: Type}(Q: A -> environ -> mpred)(R : A -> ret_assert): A -> ret_assert :=
  fun (x: A) => (overridePost (Q x) (R x)).

Ltac split_ifc_hyps :=
  repeat match goal with
  | H: ifc_def _ _ _ _ _ _ _ _ _ |- _ =>
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
  ifc_def T Delta P1 N1 A1 h (ioverridePost P2 P3) N2 A2 ->
  ifc_def T (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def T Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.
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

Lemma ifc_seq_skip{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta P N A c P' N' A' <-> ifc_def T Delta P N A (Ssequence c Sskip) P' N' A'.
Proof.
Admitted.

Definition inormal_ret_assert{A: Type}(P: A -> environ -> mpred): A -> ret_assert :=
  fun (x: A) => normal_ret_assert (P x).

Lemma ifc_ifthenelse: forall {T: Type} (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> stack_clsf) (A': T -> heap_clsf),
  bool_type (typeof b) = true ->
  ifc_def T Delta (iand P (iprop (local (`(typed_true  (typeof b)) (eval_expr b))))) N A c1 P' N' A' ->
  ifc_def T Delta (iand P (iprop (local (`(typed_false (typeof b)) (eval_expr b))))) N A c2 P' N' A' ->
  ifc_def T Delta P N A (Sifthenelse b c1 c2) P' N' A'.
Proof.
  introv Eq B1 B2.
  split_ifc_hyps. split.
  - (* VST part *)
    intro x. admit.
  - unfold ifc_core in *. unfold simple_ifc in *.
    introv Sat Sat' SE1 HE1 Star Star'.
    (* how to express and use restriction that b must not depend on Hi data? *)
Admitted.

Definition upd_stack_clsf(N: stack_clsf)(i: ident)(l: label): stack_clsf :=
  fun i0 => if Pos.eqb i0 i then l else N i0.

Definition heap_loc_eqb(l1 l2: heap_loc): bool := match l1, l2 with
  | (b1, ofs1), (b2, ofs2) => Pos.eqb b1 b2 && Z.eqb ofs1 ofs2
end.

Definition upd_heap_clsf(A: heap_clsf)(loc: heap_loc)(l: label): heap_clsf :=
  fun loc0 => if heap_loc_eqb loc0 loc then l else A loc0.

Definition val_eq_heap_loc(v: val)(l: heap_loc): Prop := match v, l with
| Vptr b1 ofs1, (b2, ofs2) => b1 = b2 /\ ofs1 = Int.repr ofs2
| _, _ => False
end.

Lemma ifc_store{T: Type}:
    forall Delta sh n (p: T -> val) P Q R (e1 e2 : expr)
      (t: type) (v0: T -> val) (v v_new: T -> reptype t)
      (hl: T -> heap_loc) (l1 l2: T -> label) (N: T -> stack_clsf) (A: T -> heap_clsf),
      (* VST preconditions: *)
      typeof e1 = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      (forall x, nth_error (R x) n = Some (data_at sh t (v x) (p x))) ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 local (`(eq (p x)) (eval_lvalue e1))) ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 local (`(eq (v0 x)) (eval_expr (Ecast e2 t)))) ->
      (forall x, JMeq (v0 x) (v_new x)) ->
      writable_share sh ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t))) ->
      (* IFC preconditions: *)
      (forall x, val_eq_heap_loc (p x) (hl x)) ->
      (forall x, clsf_expr (N x) true e1 = Some (l1 x)) ->
      (forall x, clsf_expr (N x) false e2 = Some (l2 x)) ->
      ifc [x: T] Delta |--
        (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x))))
        (N x)
        (A x)
        (Sassign e1 e2)
        (normal_ret_assert (PROPx (P x)
                           (LOCALx (Q x)
                           (SEPx (replace_nth n (R x) (data_at sh t (v_new x) (p x)))))))
        (N x)
        (upd_heap_clsf (A x) (hl x) (max_clsf (l1 x) (l2 x))).
Proof.
Admitted.

(* Old version: P, Q, R cannot depend on x!! *)
Lemma ifc_store_bad_version{T: Type}:
    forall Delta sh n (p: val) P Q R (e1 e2 : expr)
      (t: type) (v0: val) (v v_new: reptype t)
      (hl: heap_loc) (l1 l2: T -> label) (N: T -> stack_clsf) (A: T -> heap_clsf),
      (* VST preconditions: *)
      typeof e1 = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      nth_error R n = Some (data_at sh t v p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      JMeq v0 v_new ->
      writable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t)) ->
      (* IFC preconditions: *)
      val_eq_heap_loc p hl ->
      (forall x, clsf_expr (N x) true e1 = Some (l1 x)) ->
      (forall x, clsf_expr (N x) false e2 = Some (l2 x)) ->
      ifc [x: T] Delta |--
        (|>PROPx P (LOCALx Q (SEPx R)))
        (N x)
        (A x)
        (Sassign e1 e2)
        (normal_ret_assert (PROPx P (LOCALx Q (SEPx (replace_nth n R (data_at sh t v_new p))))))
        (N x)
        (upd_heap_clsf (A x) hl (max_clsf (l1 x) (l2 x))).
Abort.

End RULES.
