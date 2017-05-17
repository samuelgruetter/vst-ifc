Require Import floyd.base.
Require Import floyd.canon.
Require Import floyd.client_lemmas.
Require Import ifc.rules.
Require Import ifc.ifc.
Require Import lib.LibTactics.

Local Open Scope logic.

Section fwd_lemmas.
Context (Espec : OracleKind).
Context {CS: compspecs}.

Lemma isequential'{T: Type}:
  forall R RN RA Delta P N A c P' N' A',
    ifc_def T Delta P N A c (inormal_ret_assert P') (normalPostClsf N') (normalPostClsf A') ->
    ifc_def T Delta P N A c (ioverridePost P' R) (overridePostClsf N' RN) (overridePostClsf A' RA).
Proof.
  intros. unfold ifc_def. unfold ioverridePost. unfold inormal_ret_assert in *.
  split_ifc_hyps. split.
  - intro. apply canon.sequential'. apply Hs.
  - unfold ifc_core, simple_ifc in *. unfold overridePostClsf in *.
    (* TODO use VST to conclude that it's EK_normal and use this to simplify the goal *)
Admitted.

Lemma ifc_seq'{T: Type}:
 forall Delta P1 N1 A1 c1 P2 N2 A2 c2 P3 N3 A3,
   ifc_def T Delta P1 N1 A1 c1 (inormal_ret_assert P2) (normalPostClsf N2) (normalPostClsf A2) ->
   ifc_def T (update_tycon Delta c1) P2 N2 A2 c2 P3 N3 A3 ->
   ifc_def T Delta P1 N1 A1 (Ssequence c1 c2) P3 N3 A3.
Proof.
  intros. apply ifc_seq with P2 N2 A2; try assumption. apply isequential'. assumption.
Qed.

(* only changes P1, but not N1 and A1 *)
Lemma ifc_pre0{T: Type}: forall Delta P1 P1' N1 A1 c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  ifc_def T Delta P1' N1 A1 c P2 N2 A2 ->
  ifc_def T Delta P1  N1 A1 c P2 N2 A2.
Proof.
  introv Imp H. split_ifc_hyps. split.
  - intro. apply* semax_pre.
  - unfold ifc_core, simple_ifc in *. intros.
    apply* Hi; apply* VST_to_state_pred_commutes_imp'.
Qed.

Lemma ifc_ifthenelse_PQR{T: Type}:
  forall (v: T -> val) Delta P Q R (b: expr) c d Post N A N' A',
    bool_type (typeof b) = true ->
    (forall x: T, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |-- 
                    (tc_expr Delta (Eunop Cop.Onotbool b tint)))  ->
    (forall x: T, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                    local (`(eq (v x)) (eval_expr b))) ->
    ifc [x: T] Delta |-- (PROPx (typed_true (typeof b) (v x) :: (P x)) (LOCALx (Q x) (SEPx (R x))))
                         (N x) (A x) c (Post x) (N' x) (A' x) ->
    ifc [x: T] Delta |-- (PROPx (typed_false (typeof b) (v x) :: (P x)) (LOCALx (Q x) (SEPx (R x))))
                         (N x) (A x) d (Post x) (N' x) (A' x) ->
    ifc [x: T] Delta |-- (PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) (N x) (A x)
                         (Sifthenelse b c d) (Post x) (N' x) (A' x).
Proof.
  introv Eq Tc Ev B1 B2.
  eapply ifc_pre0; [ | apply ifc_ifthenelse ]; unfold iand, iprop; try assumption.
  - instantiate (1:=
      (fun x => (local (`(eq (v x)) (eval_expr b))) && PROPx (P x) (LOCALx (Q x) (SEPx (R x))))).
    intro. apply andp_right; [ apply (Ev x) | ]. apply andp_left2. apply derives_refl.
  - unfold pre_assert in *. remember (fun x : T =>
     andp
     ((fun x0 : T =>
       andp (local (liftx (eq (v x0) : forall _ : val, Prop) (eval_expr b)))
         (PROPx (P x0) (LOCALx (Q x0) (SEPx (R x0))))) x)
     (local (liftx (typed_true (typeof b)) (eval_expr b)))) as f.
    rewrite <- Heqf.
    replace f
    with (fun x : T =>
      PROPx (typed_true (typeof b) (v x) :: P x) (LOCALx (Q x) (SEPx (R x)))).
    + exact B1.
    + subst f. extensionality. admit.
  - admit.
Admitted.

Lemma ifc_later_trivial{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta (fun x => (|> (P x))) N A c P' N' A' ->
  ifc_def T Delta                P      N A c P' N' A'.
Proof.
  intros. split_ifc_hyps. unfold ifc_def, ifc_core, simple_ifc in *. split.
  - intro. apply* semax_later_trivial.
  - introv Sat Sat'.
    apply VST_to_state_pred_commutes_imp with (P' := (|> P x )) in Sat ; [ | apply now_later ].
    apply VST_to_state_pred_commutes_imp with (P' := (|> P x')) in Sat'; [ | apply now_later ].
    apply* Hi.
Qed.

End fwd_lemmas.
