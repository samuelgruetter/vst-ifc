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
Require Import ifc.simple_vst_store_lemmas.
Require Import ifc.ifc.
Require Import List. Import ListNotations.
Require Import lib.LibTactics.

Local Open Scope logic.

Definition ioverridePost{A: Type}(Q: A -> environ -> mpred)(R : A -> ret_assert): A -> ret_assert :=
  fun (x: A) => (overridePost (Q x) (R x)).

Definition overridePostClsf{A C: Type}(Q: A -> C)(R: A -> exitkind -> option val -> C)
: A -> exitkind -> option val -> C
:= fun (x: A) (ek: exitkind) (vl: option val) => if eq_dec ek EK_normal then Q x else R x ek vl.

Ltac split_ifc_hyps :=
  repeat match goal with
  | H: ifc_def _ _ _ _ _ _ _ _ _ |- _ =>
      let Hs := fresh H "s" in 
      let Hi := fresh H "i" in
      destruct H as [Hs Hi]
  end.

Lemma star_seq_inv: forall ge e1 te1 e3 te3 h t m1 m3 c ek3 vl3,
  star ge (State e1 te1 (Kseq (Ssequence h t) :: c)) m1 (State e3 te3 (exit_cont ek3 vl3 c)) m3 ->
  exists e2 te2 m2 ek2 vl2,
  star ge (State e1 te1 (Kseq h :: Kseq t :: c)) m1 (State e2 te2 (exit_cont ek2 vl2 (Kseq t :: c))) m2
 /\ star ge (State e2 te2 (exit_cont ek2 vl2 (Kseq t :: c))) m2 (State e3 te3 (exit_cont ek3 vl3 c)) m3
 /\ (ek2 = EK_normal \/ (ek2 = ek3 /\ vl2 = vl3)).
Proof.
(* old proof
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
*)
Admitted.

(* We need lifting on top of VST's lifting... *)

Definition iand{A: Type}(P1: A -> pre_assert)(P2: A -> pre_assert): A -> pre_assert :=
  fun (x: A) => (P1 x) && (P2 x).

Definition iprop{A: Type}(P: pre_assert): A -> pre_assert := fun (_: A) => P.

Definition inormal_ret_assert{A: Type}(P: A -> environ -> mpred): A -> ret_assert :=
  fun (x: A) => normal_ret_assert (P x).

Definition normalPostClsf{A Loc: Type}(Q: A -> Loc -> label)
: A -> exitkind -> option val -> Loc -> label
:= fun (x: A) (ek: exitkind) (vl: option val) => if eq_dec ek EK_normal then Q x else bot.

Lemma star_null:
  forall ge s s' m m',
  star ge s m s' m' ->
  forall e te c e' te', s = (State e te c) /\
  s' = (State e' te' c) ->
  e' = e /\ te' = te /\ m' = m.
Proof.
Admitted. (* TODO: Not sure that this is true: if I have a while loop for instance,
what does the semantics do? *)

Section RULES.
Context {Espec : OracleKind}.
Context {CS: compspecs}.

Arguments stack_lo_equiv _ _ _ _: simpl never.

Lemma ifc_seq{T: Type}:
  forall Delta h t
    (P1 P2: T -> environ -> mpred) (P3: T -> ret_assert)
    (N1 N2: T -> stack_clsf) (N3: T -> ret_stack_clsf)
    (A1 A2: T -> heap_clsf) (A3: T -> ret_heap_clsf),
  ifc_def T Delta P1 N1 A1 h (ioverridePost P2 P3) (overridePostClsf N2 N3) (overridePostClsf A2 A3) ->
  ifc_def T (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def T Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.
Proof.
  introv H1 H2. split_ifc_hyps. split.
  - intro. apply* semax_seq.
  - unfold ifc_core, simple_ifc in *.
    intros x x' ge e1 e1' e3 e3' te1 te1' te3 te3' m1 m1' m3 m3' c'.
    introv Sat1 Sat1' SE1 HE1 Star1 Star1'.
    apply star_seq_inv in Star1.
    apply star_seq_inv in Star1'.
    destruct Star1  as [e2  [te2  [m2  [ek2  [vl2  [Star1  [Star2  EE ]]]]]]].
    destruct Star1' as [e2' [te2' [m2' [ek2' [vl2' [Star1' [Star2' EE']]]]]]].
    edestruct H1i as [Eek [Nvl [SE2 HE2]]].
    + eapply Sat1.
    + eapply Sat1'.
    + apply* stack_lo_equiv_change_cmd.
    + exact HE1.
    + exact Star1.
    + exact Star1'.
    + clear H1i. subst ek2'.
      destruct ek2.
      { pose proof (VST_sound _ _ _ _ EK_normal vl2 (Kseq t :: c') (H1s x)) as C.
        pose proof (VST_sound _ _ _ _ EK_normal vl2' (Kseq t :: c') (H1s x')) as C'.
        unfold ioverridePost in C, C'.
        erewrite VST_overridePost_to_state_pred in C, C'.
        eapply H2i.
        * edestruct C as [? ?]; eassumption.
        * edestruct C' as [? ?]; eassumption.
        * apply* stack_lo_equiv_change_cmd.
        * exact HE2.
        * exact Star2.
        * exact Star2'. }
      { unfold overridePostClsf in *; simpl in *.
        destruct EE  as [? | [? ?]]; [discriminate | subst ek  vl2  ].
        destruct EE' as [? | [? ?]]; [discriminate | subst ek' vl2' ].
        refine (conj eq_refl (conj Nvl _)).
        simpl exit_cont in *.
        eapply star_null in Star2 ; [ | eapply (conj eq_refl eq_refl) ].
        eapply star_null in Star2'; [ | eapply (conj eq_refl eq_refl) ].
        destruct Star2  as [? [? ?]]; subst e2  te2  m2 .
        destruct Star2' as [? [? ?]]; subst e2' te2' m2'.
        apply (conj SE2 HE2). }
      { unfold overridePostClsf in *; simpl in *.
        destruct EE  as [? | [? ?]]; [discriminate | subst ek  vl2  ].
        destruct EE' as [? | [? ?]]; [discriminate | subst ek' vl2' ].
        refine (conj eq_refl (conj Nvl _)).
        simpl exit_cont in *.
        eapply star_null in Star2 ; [ | eapply (conj eq_refl eq_refl) ].
        eapply star_null in Star2'; [ | eapply (conj eq_refl eq_refl) ].
        destruct Star2  as [? [? ?]]; subst e2  te2  m2 .
        destruct Star2' as [? [? ?]]; subst e2' te2' m2'.
        apply (conj SE2 HE2). }
      { unfold overridePostClsf in *; simpl in *.
        destruct EE  as [? | [? ?]]; [discriminate | subst ek  vl2  ].
        destruct EE' as [? | [? ?]]; [discriminate | subst ek' vl2' ].
        refine (conj eq_refl (conj Nvl _)).
        simpl exit_cont in *.
        eapply star_null in Star2 ; [ | eapply (conj eq_refl eq_refl) ].
        eapply star_null in Star2'; [ | eapply (conj eq_refl eq_refl) ].
        destruct Star2  as [? [? ?]]; subst e2  te2  m2 .
        destruct Star2' as [? [? ?]]; subst e2' te2' m2'.
        apply (conj SE2 HE2). }
Grab Existential Variables. exact nil. exact nil. exact nil. exact nil.
Qed.

(* What's the inbuilt lemma? *)
Lemma blah{A : Type}:
  forall (a : A) b,
  (cons a b) = b -> False.
  intros a b.
Proof.
  induction b as [| a' b' IH].
  - intros H. inversion H.
  - intros H. inversion H. subst.
  apply IH. apply H2.
Qed.
(* "Search (?h :: ?t = ?t)." only gives the above lemma, so probably that doesn't exist already *)

Lemma star_skip_elim00:
  forall ge e te c m e' te' m',
  star ge (State e te (Kseq Sskip :: c)) m (State e' te' c) m' ->
  e' = e /\ te' = te /\ m' = m.
Proof.
  intros. unfold star, corestep_star in H. destruct H as [n H].
  destruct n as [| n].
  - inversion H. subst. exfalso. eapply blah. eassumption.
  - remember (State e te (Kseq Sskip :: c)) as s.
    remember (State e' te' c) as s'.
(* ugh. from Step and Star conclude star from c to c,
        use that to conclude the equalities. *)
Admitted.

(* TODO not sure if this holds *)
Lemma star_skip_elim: forall ge e1 te1 k m1 e2 te2 m2 ek vl,
  star ge (State e1 te1 (Kseq Sskip :: k)) m1
          (State e2 te2 (exit_cont ek vl k)) m2 ->
  e1 = e2 /\ te1 = te2 /\ m1 = m2 /\ ek = EK_normal /\ vl = None.
Admitted.

Lemma ifc_skip{T: Type}:
  forall Delta P N A,
  ifc_def T Delta P N A Sskip (inormal_ret_assert P) (normalPostClsf N) (normalPostClsf A).
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. split.
  - intro x. apply semax_skip.
  - introv Sat Sat' SE HE Star Star'.
    eapply star_skip_elim in Star. destruct Star as [? [? [? [? ?]]]]; subst.
    eapply star_skip_elim in Star'. destruct Star' as [? [? [? [? ?]]]]; subst.
    refine (conj eq_refl (conj _ (conj _ _))).
    + unfold same_Noneness. left. auto.
    + unfold stack_lo_equiv.
      unfold stack_lo_equiv in SE.
      apply SE.
    + apply HE.
Qed.

Lemma ifc_seq_skip{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta P N A c P' N' A' <-> ifc_def T Delta P N A (Ssequence c Sskip) P' N' A'.
Proof.
Admitted.

Lemma ifc_ifthenelse: forall {T: Type} (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> ret_stack_clsf) (A': T -> ret_heap_clsf),
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
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf)
        (retExpr: option expr) (retVal: option val),
(* TODO this is an equality between two things of type "environ -> mpred", probably not what we want *)
  (cast_expropt retExpr (ret_type Delta)) = `retVal ->
  ifc_def T Delta
          (fun (x: T) => tc_expropt Delta retExpr (ret_type Delta) &&
                         R x EK_return retVal)
          (fun (x: T) => N x EK_return retVal)
          (fun (x: T) => A x EK_return retVal)
          (Sreturn retExpr)
          R N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. split.
  - intro x. 
    pose proof (semax_return Delta (R x) retExpr) as C.
    assert (forall rho, cast_expropt retExpr (ret_type Delta) rho = retVal) as H'. {
      rewrite H. intro. reflexivity.
    }
    unfold liftx in C. unfold lift_uncurry_open in C. simpl in C. unfold lift in C.
    assert ((fun x0 : environ =>
       tc_expropt Delta retExpr (ret_type Delta) x0 &&
       R x EK_return (cast_expropt retExpr (ret_type Delta) x0) x0) =
       (fun x0 : environ =>
       tc_expropt Delta retExpr (ret_type Delta) x0 &&
       R x EK_return retVal x0)) as E. {
      extensionality. f_equal. f_equal. apply H'.
    }
    rewrite E in C. clear E. apply C.
  - introv Sat Sat' SE HE Star Star'.
    (* TODO... *)
Admitted.

Lemma ifc_pre{T: Type}: forall Delta P1 P1' N1 N1' A1 A1' c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
  ifc_def T Delta P1' N1' A1' c P2 N2 A2 ->
  ifc_def T Delta P1  N1  A1  c P2 N2 A2.
Proof.
  introv E Imp H.
  split_ifc_hyps. split.
  - intro. apply semax_pre with (P' := P1' x); auto.
  - unfold ifc_core, simple_ifc in *.
    introv Sat Sat' SE HE. 
    pose proof (VST_to_state_pred_commutes_imp' _ _ _ (E x) _ _ _ Sat) as Sat0.
    pose proof (VST_to_state_pred_commutes_imp' _ _ _ (E x') _ _ _ Sat') as Sat'0.
    pose proof (VST_to_state_pred_commutes_imp _ _ (Imp x) _ _ _ Sat) as Sat00.
    pose proof (VST_to_state_pred_commutes_imp _ _ (Imp x') _ _ _ Sat') as Sat'00.
    rewrite VST_indep_state_pred in Sat00. destruct Sat00 as [LeA LeN].
    rewrite VST_indep_state_pred in Sat'00. destruct Sat'00 as [LeA' LeN'].
    apply* Hi.
    + apply* weaken_stack_lo_equiv.
    + apply* weaken_heap_lo_equiv.
Qed.

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

(* FIXME: move to ifc.ifc or better yet find out whether
          there already exists a definition of terminating
          executions over the semantics we're using so we
          don't have to reinvent the wheel *)
Lemma bigstep_null:
    forall ge e te e' te' m m' c',
    star ge (State e te []) m (State e' te' c') m' ->
    m' = m /\ e' = e /\ te' = te /\ c' = [].
Admitted. (*
Proof.
  intros.
  inversion H; subst.
  - auto.
  - inversion H0.
Qed.
*)

Lemma bigstep_sassign:
    forall ge e te e1 e2 m e' te' m' k, 
    star ge (State e te (cons (Kseq (Sassign e1 e2)) k)) m (State e' te' k) m' ->
    exists loc ofs v1 v2, 
      Clight.eval_lvalue ge e te m e1 loc ofs /\
      type_is_volatile (typeof e1) = false /\
      Clight.eval_expr ge e te m e2 v2 /\
      assign_loc ge (typeof e1) m loc ofs v1 m' /\
      Cop.sem_cast v2 (typeof e2) (typeof e1) m = Some v1.
Admitted. (*
Proof.
  intros.
  inverts H as Step Star.
  - exfalso. eapply blah. apply Step.
  - inverts Step.
    eapply star_null in Star.
    2: auto.
    destruct Star as [? [? ?]]; subst.
  do 4 eexists. eauto.
Qed.
*)

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
      ifc_def T Delta
        (fun x => (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x)))))
        N
        A
        (Sassign e1 e2)
        (fun x => (normal_ret_assert (PROPx (P x)
                                     (LOCALx (Q x)
                                     (SEPx (replace_nth n (R x) (data_at sh t (v_new x) (p x))))))))
        (normalPostClsf N)
        (normalPostClsf (fun x loc =>
           if heap_loc_eq_val loc (p x) then lub (l1 x) (l2 x) else A x loc)).
Proof.
  introv EqT ByVal Volatile GetR Eval1 Eval2 JM Wsh Tc Ifc.
  unfold ifc_def. split.
  - intros x.
    eapply semax_SC_field_store_without_paths; eauto.
  - unfold ifc_core. unfold simple_ifc.
    introv Sat Sat' SE HE Star Star'.
(*
    eapply bigstep_sassign in Star.
    destruct Star as [loc [ofs [v1 [v2 [HEval1 [HVolatile [HEval2 [HALoc HCast]]]]]]]].
    eapply bigstep_sassign in Star'.
    destruct Star' as [loc' [ofs' [v1' [v2' [HEval1' [HVolatile' [HEval2' [HALoc' HCast']]]]]]]].
    (* OK now have semantic information about the effect
       of the store statement which we need to use to
       prove the infoflow conditions *)
*)
Admitted.

End RULES.
