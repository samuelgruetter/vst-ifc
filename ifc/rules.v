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

Definition inormal_ret_assert{A: Type}(P: A -> environ -> mpred): A -> ret_assert :=
  fun (x: A) => normal_ret_assert (P x).

Section RULES.
Context {Espec : OracleKind}.
Context {CS: compspecs}.

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

Lemma ifc_skip{T: Type}:
  forall Delta P N A,
  ifc_def T Delta P N A Sskip (inormal_ret_assert P) N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. split.
  - intro x. apply semax_skip.
  - introv Sat Sat' SE HE Star Star'.
Admitted.

Lemma ifc_seq_skip{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta P N A c P' N' A' <-> ifc_def T Delta P N A (Ssequence c Sskip) P' N' A'.
Proof.
Admitted.

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

Lemma ifc_return{T: Type}:
  forall Delta R N A ret,
  ifc_def T Delta
          (fun x => (tc_expropt Delta ret (ret_type Delta) &&
                    `( R x EK_return : option val -> environ -> mpred)
                     (cast_expropt ret (ret_type Delta)) id)) N A
          (Sreturn ret)
          (fun x => R x) N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. split.
  - intro x. apply semax_return.
  - introv Sat Sat' SE HE Star Star'.
    inverts Star as Step Star.
    inverts Step. simpl in H3. discriminate.
    (* TODO H3 is a contradiction, and this points out that our simple_ifc definition is flawed:
       We cannot return if there are no further commands left to execute after the return *)
Qed.

Lemma ifc_pre{T: Type}: forall Delta P1 P1' N1 N1' A1 A1' c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x &&
                                    !! (forall i, N1 x i = N1' x i) &&
                                    !! (forall l, A1 x l = A1' x l)) ->
  ifc_def T Delta P1' N1' A1' c P2 N2 A2 ->
  ifc_def T Delta P1  N1  A1  c P2 N2 A2.
Proof.
  introv Imp H.
  assert (forall x, ENTAIL Delta, P1 x |-- P1' x) as E. {
    intro x. eapply derives_trans; [ apply Imp | ]. do 2 apply andp_left1. apply derives_refl.
  }
 split_ifc_hyps. split.
  - intro. apply semax_pre with (P' := P1' x); auto.
  - unfold ifc_core, simple_ifc in *.
    introv Sat Sat' SE HE.
    apply VST_pre_to_state_pred_commutes_imp' with (Delta := Delta) (P' := P1' x ) in Sat;
      [ | apply E ].
    apply VST_pre_to_state_pred_commutes_imp' with (Delta := Delta) (P' := P1' x') in Sat';
      [ | apply E ].
    apply* Hi.
    + replace (N1' x) with (N1 x).
      replace (N1' x') with (N1 x').
      assumption.
      (* These follow from Imp, modulo incompatibility with VST *)
      extensionality. admit.
      extensionality. admit.
    + admit. (* similar *)
Admitted.

(*
Definition upd_stack_clsf(N: stack_clsf)(i: ident)(l: label): stack_clsf :=
  fun i0 => if Pos.eqb i0 i then l else N i0.

Definition heap_loc_eqb(l1 l2: heap_loc): bool := match l1, l2 with
  | (b1, ofs1), (b2, ofs2) => Pos.eqb b1 b2 && Int.eq ofs1 ofs2
end.

Definition upd_heap_clsf(A: heap_clsf)(loc: heap_loc)(l: label): heap_clsf :=
  fun loc0 => if heap_loc_eqb loc0 loc then l else A loc0.

Definition dummy_heap_loc: heap_loc := (1%positive, Int.zero).

Definition force_heap_loc(v: val): heap_loc := 
  match v with
  | Vptr b i => (b, i)
  | _ => dummy_heap_loc
  end.
*)

Definition heap_loc_eq_val(hl: heap_loc)(v: val): bool := match hl, v with
| (b1, i1), Vptr b2 i2 => Pos.eqb b1 b2 && Int.eq i1 i2
| _, _ => false
end.

Lemma ifc_store{T: Type}:
    forall Delta sh n (p: T -> val) P Q R (e1 e2 : expr)
      (t: type) (v0: T -> val) (v v_new: T -> reptype t)
      (l1 l2: T -> label) (N: T -> stack_clsf) (A: T -> heap_clsf),
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
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 !! (clsf_expr (N x) true e1 = Some (l1 x) /\
                     clsf_expr (N x) false e2 = Some (l2 x))) ->
      ifc [x: T] Delta |--
        (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x))))
        (N x)
        (A x)
        (Sassign e1 e2)
        (normal_ret_assert (PROPx (P x)
                           (LOCALx (Q x)
                           (SEPx (replace_nth n (R x) (data_at sh t (v_new x) (p x)))))))
        (N x)
        (fun loc => if heap_loc_eq_val loc (p x) then max_clsf (l1 x) (l2 x) else A x loc).
Proof.
Admitted.

End RULES.
