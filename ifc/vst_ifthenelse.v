Require Import veric.juicy_base.
Require Import msl.normalize.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.semax_congruence.
Require Import veric.Clight_lemmas.

Local Open Scope pred.
Local Open Scope nat_scope.

Section extensions.
Context (Espec : OracleKind).

Lemma funassert_update_tycon:
  forall Delta h, funassert (update_tycon Delta h) = funassert Delta.
intros; apply same_glob_funassert. rewrite glob_specs_update_tycon. auto.
Qed.

Lemma strict_bool_val_eval_expr: forall
(CS : compspecs)
(Delta : tycontext)
(b : expr)
(v: bool)
(rho : environ)
(phi : rmap)
(TC2 : (tc_expr Delta (Eunop Onotbool b (Tint I32 Signed noattr)) rho) phi)
(m : Memory.mem)
(H9 : Cop.bool_val (eval_expr b rho) (typeof b) m = Some v),
strict_bool_val (eval_expr b rho) (typeof b) = Some v.
Proof.
intros.
unfold tc_expr in TC2.
 simpl in TC2.
 rewrite denote_tc_assert_andp in TC2.
 destruct TC2 as [TC2 TC2a].
unfold strict_bool_val.
destruct v;
destruct (eval_expr b rho) eqn:H16,
 (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
 simpl in *; inv H9; auto;
 try solve [
 rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
 simpl in TC2; unfold_lift in TC2;
 unfold denote_tc_test_eq in TC2;
 rewrite H16 in TC2; destruct TC2 as [TC2 _]; simpl in TC2;
 subst; rewrite Int.eq_true; reflexivity
 ].
 - rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
   simpl in TC2; unfold_lift in TC2;
   unfold denote_tc_test_eq in TC2;
   rewrite H16 in TC2; destruct TC2 as [TC2 _]; simpl in TC2.
   unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
 - unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
 - unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
Qed.


Lemma typed_true_eval_expr: forall
(CS : compspecs)
(Delta : tycontext)
(b : expr)
(rho : environ)
(phi : rmap)
(TC2 : (tc_expr Delta (Eunop Onotbool b tint) rho) phi)
(m : Memory.mem)
(H9 : Cop.bool_val (eval_expr b rho) (typeof b) m = Some true),
typed_true (typeof b) (eval_expr b rho).
Proof.
intros.
unfold tc_expr in TC2.
 simpl in TC2.
 rewrite denote_tc_assert_andp in TC2.
 destruct TC2 as [TC2 TC2a].

unfold typed_true, strict_bool_val.
destruct (eval_expr b rho) eqn:H16,
 (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
 simpl in *; inv H9; auto;
 rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
 simpl in TC2; unfold_lift in TC2;
 unfold denote_tc_test_eq in TC2;
 rewrite H16 in TC2; destruct TC2 as [TC2 _]; simpl in TC2;
 subst; rewrite Int.eq_true; reflexivity.
Qed.

Lemma typed_false_eval_expr: forall
(CS : compspecs)
(Delta : tycontext)
(b : expr)
(rho : environ)
(phi : rmap)
(TC2 : (tc_expr Delta (Eunop Onotbool b tint) rho) phi)
(m : Memory.mem)
(H9 : Cop.bool_val (eval_expr b rho) (typeof b) m = Some false),
typed_false (typeof b) (eval_expr b rho).
Proof.
intros.
unfold tc_expr in TC2.
 simpl in TC2.
 rewrite denote_tc_assert_andp in TC2.
 destruct TC2 as [TC2 TC2a].
unfold typed_false, strict_bool_val.
destruct (eval_expr b rho) eqn:H16,
 (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
 simpl in *; inv H9; auto;
 try (rewrite negb_false_iff in H0; rewrite H0); auto.
 - rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
   simpl in TC2; unfold_lift in TC2;
   unfold denote_tc_test_eq in TC2;
   rewrite H16 in TC2; destruct TC2 as [TC2 _]; simpl in TC2.
   unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
 - unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
 - unfold Cop.bool_val in H0; simpl in H0; if_tac in H0; inv H0.
Qed.

Lemma semax_ifthenelse3 {CS: compspecs}:
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Espec Delta (fun rho => P rho && !! expr_true b rho) c R ->
     semax Espec Delta (fun rho => P rho && !! expr_false b rho) d R ->
     semax Espec Delta
              (fun rho => tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) rho && P rho)
              (Sifthenelse b c d) R.
Proof.
intros.
rewrite semax_unfold in H0, H1 |- *.
intros.
specialize (H0 psi _ _ TS HGG Prog_OK k F).
specialize (H1 psi _ _ TS HGG Prog_OK k F).

spec H0. { intros i te' ?.  apply H2; simpl; auto. intros i0; destruct (H4 i0); intuition.
left; clear - H5.
unfold modifiedvars. simpl.
 apply modifiedvars'_union. left; apply H5. }

spec H1. { intros i te' ?.  apply H2; simpl; auto.
 clear - H4; intros i0; destruct (H4 i0); intuition.
 left.
 unfold modifiedvars. simpl.
 apply modifiedvars'_union. right; apply H. }

assert (H3then: app_pred
       (rguard Espec psi (exit_tycon c Delta')  (frame_ret_assert R F) k) w). {
clear - H3.
intros ek vl tx vx; specialize (H3 ek vl tx vx).
cbv beta in H3.
eapply subp_trans'; [ | apply H3].
apply derives_subp; apply andp_derives; auto.
- apply andp_derives; auto.
  unfold exit_tycon; simpl. destruct ek; simpl; auto.
  intros ? [? ?]; split; auto.
  + apply typecheck_environ_join1; auto.
    * repeat rewrite var_types_update_tycon. auto.
    * repeat rewrite glob_types_update_tycon. auto.
  + destruct (current_function k); destruct H0; split; auto.
    rewrite ret_type_join_tycon; rewrite ret_type_update_tycon in H1|-*; auto.
- repeat rewrite funassert_exit_tycon in *; auto. }

assert (H3else: app_pred
       (rguard Espec psi (exit_tycon d Delta') (frame_ret_assert R F) k) w). {
clear - H3.
intros ek vl tx vx; specialize (H3 ek vl tx vx).
eapply subp_trans'; [ | apply H3].
apply derives_subp; apply andp_derives; auto.
- apply andp_derives; auto.
  unfold exit_tycon; simpl. destruct ek; simpl; auto.
  intros ? [? ?]; split; auto.
  + apply typecheck_environ_join2 with Delta'; auto;
    apply tycontext_evolve_update_tycon.
  + destruct (current_function k); destruct H0; split; auto.
    rewrite ret_type_join_tycon; rewrite ret_type_update_tycon in H1|-*; auto.
- repeat rewrite funassert_exit_tycon in *; auto. }

specialize (H0 H3then).
specialize (H1 H3else).
clear Prog_OK H3 H3then H3else.
intros tx vx; specialize (H0 tx vx); specialize (H1 tx vx).
remember (construct_rho (filter_genv psi) vx tx) as rho.
slurp.
rewrite <- fash_and.
intros ? ?. clear w H0.
revert a'.
apply fash_derives.
intros w [? ?].
intros ?w ? [[?TC  ?] ?].
assert (typecheck_environ Delta rho) as TC_ENV. {
  destruct TC as [TC _].
  eapply typecheck_environ_sub; eauto.
}
apply extend_sepcon_andp in H4; auto.
destruct H4 as [TC2 H4].
pose proof TC2 as TC2'.
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
(*hnf in TC2'.*)
destruct H4 as [w1 [w2 [? [? ?]]]].
specialize (H0 w0 H3).
specialize (H1 w0 H3).
unfold expr_true, expr_false, Cnot in *.
intros ora jm Hge Hphi.
generalize (eval_expr_relate _ _ _ _ _ b jm HGG Hge (guard_environ_e1 _ _ _ TC)); intro.
assert (TCS := typecheck_expr_sound _ _ w0 _ (guard_environ_e1 _ _ _ TC) TC2').
 unfold tc_expr in TC2'.
 simpl in TC2'.
 rewrite denote_tc_assert_andp in TC2'.
 destruct TC2' as [TC2' TC2'a].
assert (exists b': bool, Cop.bool_val (eval_expr b rho) (typeof b) (m_dry jm) = Some b'). {
clear - TS TC H TC2 TC2' TC2'a TCS Hphi.
 simpl in TCS. unfold_lift in TCS.
 unfold Cop.bool_val;
 destruct (eval_expr b rho) eqn:H15;
 simpl; destruct (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
    intuition; simpl in *; try rewrite TCS; eauto;
 rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2';
 simpl in TC2'; unfold_lift in TC2'; rewrite H15 in TC2';
 subst; rewrite tc_test_eq0; eauto.
} clear TCS.

(* typechecking proof *)
destruct H9 as [b' ?].
apply wlog_safeN_gt0; intro.
subst w0.
change (level (m_phi jm)) with (level jm) in H10.
revert H10; case_eq (level jm); intros; [ omegaContradiction | ].
apply levelS_age1 in H10. destruct H10 as [jm' ?].
clear H11.
apply (@safe_step'_back2  _ _ _ _ _ _ _ _ psi ora _ jm
        (State vx tx (Kseq (if b' then c else d) :: k)) jm' _).
{ split3.
  - rewrite <- (age_jm_dry H10); econstructor; eauto.
  - apply age1_resource_decay; auto.
  - apply age_level; auto. }
change (level (m_phi jm)) with (level jm).
replace (level jm - 1)%nat with (level jm' ) by (apply age_level in H10; omega).
eapply @age_safe; try apply H10.
rewrite <- Hge in *.
pose proof (strict_bool_val_eval_expr _ _ _ _ _ _ TC2 _ H9) as C.
destruct b'.
{ eapply H0; auto.
split; auto.
split; auto.
rewrite andp_comm.
unfold lift1.
rewrite prop_true_andp. { do 2 econstructor; split3; eauto. }
apply C. }
{ eapply H1; auto.
split; auto.
split; auto.
unfold lift1.
rewrite andp_comm; rewrite prop_true_andp. { do 2 econstructor; split3; eauto. }
apply C. }
Qed.

End extensions.
