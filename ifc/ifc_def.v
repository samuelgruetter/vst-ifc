Require Import ifc.clight_semantics.
Require Export ifc.ifc_sig.
Require Import ifc.simple_vst_store_lemmas.
Require Import veric.Clight_new.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import ifc.vst_ifthenelse.
Require Import floyd.client_lemmas.
Require Import floyd.sc_set_load_store.
Require Import List. Import ListNotations.

Local Open Scope logic.

(* TODO connect this to the actual VST soundness proof *)
Axiom VST_sound: forall {Espec: OracleKind} {CS: compspecs} Delta P1 c P2 ek vl k,
  semax Delta P1 c P2 ->
  forall ge e1 te1 m1 e2 te2 m2,
  VST_to_state_pred P1 e1 te1 m1 ->
  star ge (State e1 te1 (cons (Kseq c) k)) m1 (State e2 te2 (exit_cont ek vl k)) m2 ->
  VST_to_state_pred (P2 ek vl) e2 te2 m2.

Module IFC : IFC_SIG.

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

Arguments stack_lo_equiv _ _ _ _: simpl never.

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

(* TODO doesn't hold *)
Axiom Delta_always_typechecks: forall Delta P Q,
  ENTAIL Delta, P |-- Q -> P |-- Q.

Definition cont_eq (s s' : corestate): Prop :=
  match s, s' with
  | (State e te k), (State e' te' k') => k = k' 
  | _, _ => True end.

Definition starN: genv -> nat -> corestate -> mem -> corestate -> mem -> Prop :=
  corestepN cl_core_sem.

Definition sync (ge : genv) (e e' : env) (te te' : temp_env) (m m' : mem) (k : cont): Prop :=
  forall s2 m2 n, starN ge n (State e te k) m s2 m2 ->
    exists s2' m2', starN ge n (State e' te' k) m' s2' m2' /\ cont_eq s2 s2'.

Definition iguard {A : Type}
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (k: cont)
:= forall (x x': A) (ge: genv) (e1 e1': env) (te1 te1': temp_env)
          (m1 m1': mem),
   preP x  e1 te1 m1 ->
   preP x' e1' te1' m1' ->
   let s1  := (State e1  te1  k) in
   let s1' := (State e1' te1' k) in
   stack_lo_equiv s1 s1' (preN x) (preN x') ->
   heap_lo_equiv  m1 m1' (preA x) (preA x') ->
   sync ge e1 e1' te1 te1' m1 m1' k.

Lemma weaken_iguard{T : Type}: forall Delta (P1 P1': T -> pre_assert) N1 N1' A1 A1' k,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, ENTAIL Delta, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
  iguard (lft1 VST_to_state_pred P1') N1' A1' k ->
  iguard (lft1 VST_to_state_pred P1) N1 A1 k.
Proof.
  introv Imp Le IG. unfold iguard in *.
  introv Sat Sat' SE HE.
  pose proof (VST_to_state_pred_commutes_imp' _ _ _ (Imp x) _ _ _ Sat) as Sat0.
  pose proof (VST_to_state_pred_commutes_imp' _ _ _ (Imp x') _ _ _ Sat') as Sat'0.
  pose proof (VST_to_state_pred_commutes_imp _ _
             (Delta_always_typechecks _ _ _ (Le x)) _ _ _ Sat) as Sat00.
  pose proof (VST_to_state_pred_commutes_imp _ _
             (Delta_always_typechecks _ _ _ (Le x')) _ _ _ Sat') as Sat'00.
  rewrite VST_indep_state_pred in Sat00. destruct Sat00 as [LeA LeN].
  rewrite VST_indep_state_pred in Sat'00. destruct Sat'00 as [LeA' LeN'].
  eapply IG.
  - eapply Sat0.
  - eapply Sat'0.
  - apply* weaken_stack_lo_equiv.
  - apply* weaken_heap_lo_equiv.
Qed.

Lemma weaken_iguard0{T : Type}: forall Delta (P1 P1': T -> pre_assert) N1 A1 k,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  iguard (lft1 VST_to_state_pred P1') N1 A1 k ->
  iguard (lft1 VST_to_state_pred P1) N1 A1 k.
Proof.
  introv Imp IG. eapply weaken_iguard; [ eapply Imp | | eapply IG ].
  intro. apply prop_right. split; apply lle_refl.
Qed.

Definition irguard {A : Type}
  (postP: A -> exitkind -> option val -> state_pred) (postN: A -> ret_stack_clsf)
  (postA: A -> ret_heap_clsf) (k: cont): Prop
:= forall (ek: exitkind) (vl: option val),
  iguard (fun (x: A) => postP x ek vl)
         (fun (x: A) => postN x ek vl)
         (fun (x: A) => postA x ek vl)
         (exit_cont ek vl k).

Definition simple_ifc {A : Type} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> exitkind -> option val -> state_pred) (postN: A -> ret_stack_clsf)
  (postA: A -> ret_heap_clsf)
:= forall (k: cont), irguard postP postN postA k -> iguard preP preN preA (Kseq c :: k).

Definition simple_ifc_old {A : Type} (Delta: tycontext)
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
   simple_ifc Delta preP' preN preA c postP' postN postA.

Definition ifc_def (A: Type) {cs: compspecs} {Espec: OracleKind} (Delta: tycontext)
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> ret_stack_clsf) (postA: A -> ret_heap_clsf)
:= (forall x: A, @semax cs Espec Delta (preP x) c (postP x)) /\
   (ifc_core Delta preP preN preA c postP postN postA).

Ltac split_ifc_hyps :=
  repeat match goal with
  | H: ifc_def _ _ _ _ _ _ _ _ _ |- _ =>
      let Hs := fresh H "s" in 
      let Hi := fresh H "i" in
      destruct H as [Hs Hi]
  end.

Section RULES.
Context {Espec : OracleKind}.
Context {CS: compspecs}.

Lemma ifc_seq{T: Type}:
  forall Delta h t
    (P1 P2: T -> environ -> mpred) (P3: T -> ret_assert)
    (N1 N2: T -> stack_clsf) (N3: T -> ret_stack_clsf)
    (A1 A2: T -> heap_clsf) (A3: T -> ret_heap_clsf),
  ifc_def T Delta P1 N1 A1 h 
          (lft2 overridePost P2 P3) (overridePostClsf N2 N3) (overridePostClsf A2 A3) ->
  ifc_def T (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def T Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.
Proof.
  introv H1 H2. split_ifc_hyps. split.
  - intro. apply* semax_seq.
  - unfold ifc_core, simple_ifc in *.
    intros k RG.
    cut (iguard (fun x : T => VST_to_state_pred (P1 x)) N1 A1
           (Kseq h :: Kseq t :: k)). {
      unfold iguard. clear. introv G Sat Sat' SE HE Star.
      unfold starN in Star.
      destruct n as [|n].
      - simpl in Star. inversion Star. subst s2 m2.
        exists (State e1' te1' (Kseq (Ssequence h t) :: k)) m1'.
        simpl. apply (conj eq_refl eq_refl).
      - simpl in Star. destruct Star as [s11 [m11 [Step Star]]].
        inversion Step. subst.
        specialize (G _ _ ge _ _ _ _ _ _ Sat Sat').
        spec G. { eapply stack_lo_equiv_change_cmd. eassumption. }
        specialize (G HE).
        unfold sync in G.
        specialize (G s2 m2 (S n)).
        spec G. { unfold starN. simpl. eauto. }
        destruct G as [s2' [m2' [Star' CE]]]. exists s2' m2'.
        refine (conj _ CE).
        simpl in Star'. destruct Star' as [s11' [m11' [Step' Star']]].
        simpl. exists s11' m11'. refine (conj _ Star').
        apply step_seq. apply Step'.
    }
    apply H1i.
    unfold irguard, overridePost, overridePostClsf, lft2, VST_post_to_state_pred. intros.
    destruct (eq_dec ek EK_normal) as [E | NE].
    + subst ek. simpl. eapply weaken_iguard0; [ | eapply H2i ].
      * instantiate (1 := Delta). intro. apply andp_left2. simpl. intro rho.
        apply andp_left2. apply derives_refl.
      * exact RG.
    + replace (exit_cont ek vl (Kseq t :: k)) with (exit_cont ek vl k)
        by (destruct ek; simpl; congruence).
      unfold irguard in RG. specialize (RG ek vl). apply RG.
Qed.

Lemma ifc_skip{T: Type}:
  forall Delta P N A,
  ifc_def T Delta P N A Sskip (lft1 normal_ret_assert P) (normalPostClsf N) (normalPostClsf A).
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
  (forall x, ENTAIL Delta, P x |-- !! (clsf_expr (N x) b = Some Lo)) ->
  ifc_def T Delta (lft2 andp P (lft0 (local (`(typed_true  (typeof b)) (eval_expr b)))))
          N A c1 P' N' A' ->
  ifc_def T Delta (lft2 andp P (lft0 (local (`(typed_false (typeof b)) (eval_expr b)))))
          N A c2 P' N' A' ->
  ifc_def T Delta (lft2 andp (lft0 (tc_expr Delta (Eunop Onotbool b tint))) P) N A
         (Sifthenelse b c1 c2) P' N' A'.
Proof.
  introv Eq Cl B1 B2.
  split_ifc_hyps. split.
  - (* VST part *)
    intro x. unfold lft0, lft2 in *. apply* semax_ifthenelse.
  - unfold ifc_core in *. unfold simple_ifc in *.
    introv Sat Sat' SE1 HE1 Star Star'.
    apply invert_star in Star. apply invert_star in Star'.
    destruct Star as [E | Plus]; destruct Star' as [E' | Plus'].
    (* cases where at least one doesn't step, annoying *)
    + admit.
    + admit.
    + admit.
    (* case where both do at least one step: *)
    + apply invert_ifthenelse in Plus . destruct Plus  as [b0  [b00  [Ev  [Bv  Star ]]]].
      apply invert_ifthenelse in Plus'. destruct Plus' as [b0' [b00' [Ev' [Bv' Star']]]].
      assert (b00 = b00') as EqCond by admit. (* TODO obtain this from Cl *)
      subst b00'.
      destruct b00.
      * apply* B1i.
        { eapply VST_to_state_pred_commutes_imp'; [ | eapply Sat ]. instantiate (1 := Delta).
          unfold lft0, lft2 in *.
          apply andp_right.
          - do 2 apply andp_left2. apply derives_refl.
          - rewrite <- andp_assoc. apply andp_left1.
unfold local, liftx, lift1, lift. simpl.
unfold typed_true.
intro rho. apply andp_left2. 

(* here, we have "tc_expr ... |-- ", but in strict_bool_val_eval_expr int vst_ifthenelse.v, we
   need "(tc_expr ...) phi" where phi is an rmap *)
Admitted.

Lemma ifc_loop{T: Type}: forall Delta Inv1P Inv1N Inv1A Inv2P Inv2N Inv2A incr body RetP RetN RetA,
  ifc_def T Delta Inv1P Inv1N Inv1A
    body
    (lft2 loop1_ret_assert Inv2P RetP) (loop1_ret_clsf Inv2N RetN) (loop2_ret_clsf Inv2A RetA) ->
  ifc_def T Delta Inv2P Inv2N Inv2A
    incr
    (lft2 loop2_ret_assert Inv1P RetP) (loop1_ret_clsf Inv1N RetN) (loop2_ret_clsf Inv1A RetA) ->
  ifc_def T Delta Inv1P Inv1N Inv1A (Sloop body incr) RetP RetN RetA.
Proof.
  introv Body Incr.
  split_ifc_hyps. split.
  - intro. apply* semax_loop.
  - unfold ifc_core in *. unfold simple_ifc in *. introv Sat Sat' SE HE Star Star'.
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
    apply invert_star in Star. destruct Star as [E | Plus].
    + inversion E as [E2 E1]. inversion E2 as [[E3 E4 E5]].
      (* note: inversion also rewrote "exit_cont ..." to "Kseq ... :: k" below the line *)
      pose proof (return_exit_cont _ _ _ _ E5). subst.
      apply invert_star in Star'. destruct Star' as [E' | Plus'].
      * inversion E' as [E2' E1']. inversion E2' as [[E3' E4' E5']].
        (* note: inversion also rewrote "exit_cont ..." to "Kseq ... :: k" below the line *)
        pose proof (return_exit_cont _ _ _ _ E5'). subst.
        refine (conj eq_refl (conj _ (conj _ _))).
        { admit. } { Fail apply SE. (*


      pose proof (return_exit_cont _ _ _ _ E5) as C.
      destruct C as [E0 [Eq | [i [f [e [t [ k' Eq]]]]]]].
      * subst. simpl in E5.
    apply invert_star_return in Star .
    destruct Star as [k' [te' [ve' [v' [f' [optid' [te'' [m11 [Eqk [Ekm [EqRe EqO]]]]]]]]]]].
    apply invert_star_return in Star'.
    destruct Star' as
      [k'0 [te'0 [ve'0 [v'0 [f'0 [optid'0 [te''0 [m110 [Eqk0 [Ekm0 [EqRe0 EqO0]]]]]]]]]]].
    rewrite Eqk in Eqk0. inversion Eqk0. subst optid'0 f'0 ve'0 te'0 k'0. clear Eqk0.
     TODO... *)
Admitted.

Lemma ifc_pre{T: Type}: forall Delta P1 P1' N1 N1' A1 A1' c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, ENTAIL Delta, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
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
    pose proof (VST_to_state_pred_commutes_imp _ _
           (Delta_always_typechecks _ _ _ (Imp x)) _ _ _ Sat) as Sat00.
    pose proof (VST_to_state_pred_commutes_imp _ _
           (Delta_always_typechecks _ _ _ (Imp x')) _ _ _ Sat') as Sat'00.
    rewrite VST_indep_state_pred in Sat00. destruct Sat00 as [LeA LeN].
    rewrite VST_indep_state_pred in Sat'00. destruct Sat'00 as [LeA' LeN'].
    apply* Hi.
    + apply* weaken_stack_lo_equiv.
    + apply* weaken_heap_lo_equiv.
Qed.

Lemma clsf_expr_sound{T: Type}: 
forall Delta ge P Q R N e l A e1 te1 m1 e1' te1' m1' v v' x x' k1 k1',
  (forall x : T,
     ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))
     |-- !! (clsf_expr (N x) e = Some (l x))) ->
  VST_to_state_pred (|> PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) e1 te1 m1 ->
  VST_to_state_pred (|> PROPx (P x') (LOCALx (Q x') (SEPx (R x')))) e1' te1' m1' ->
  stack_lo_equiv (State e1 te1 k1) (State e1' te1' k1') (N x) (N x') ->
  heap_lo_equiv m1 m1' (A x) (A x') ->
  Clight.eval_expr ge e1 te1 m1 e v ->
  Clight.eval_expr ge e1' te1' m1' e v' ->
  v = v'.
Admitted.

Lemma ifc_set{T: Type}:
forall Delta id P Q R (N: T -> stack_clsf) (A: T -> heap_clsf) (e2: expr) l2 t v,
  typeof_temp Delta id = Some t ->
  is_neutral_cast (implicit_deref (typeof e2)) t = true ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     local (`(eq (v x)) (eval_expr e2))) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     tc_expr Delta e2) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     !! (clsf_expr (N x) e2 = Some (l2 x))) ->
  ifc_def T Delta
    (fun x => (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x))))) N A
    (Sset id e2)
    (fun x => (normal_ret_assert (PROPx (P x) 
           (LOCALx (temp id (v x) :: remove_localdef_temp id (Q x)) (SEPx (R x))))))
    (normalPostClsf (fun x i => if Pos.eqb i id then l2 x else N x i))
    (normalPostClsf A).
Proof.
  introv EqT Nc Ev0 Tc Cl. rename v into v0.
  unfold ifc_def. split.
  - intros x. apply* semax_SC_set.
  - unfold ifc_core. unfold simple_ifc.
    introv Sat Sat' SE HE Star Star'.
    assert (ek = EK_normal) by admit. assert (ek' = EK_normal) by admit. (* <-- TODO *)
    subst ek ek'. simpl exit_cont in *.
    apply invert_set_too_strong in Star.
    apply invert_set_too_strong in Star'.
    destruct Star as [? [? [v [? Ev]]]]. subst e0 m2 te2.
    destruct Star' as [? [? [v' [? Ev']]]]. subst e2' m2' te2'.
    unfold normalPostClsf. simpl.
    refine (conj eq_refl (conj _ (conj _ HE))).
    + admit. (* same_Noneness *)
    + pose proof SE as SE0. unfold stack_lo_equiv in SE. destruct SE as [E SE]. refine (conj E _).
      unfold gen_lo_equiv. intros l Lo1 Lo2.
      do 2 rewrite PTree.gsspec. destruct (peq l id) as [Eq | Ne].
      * subst l. simpl in Lo1, Lo2. rewrite Pos.eqb_refl in *.
        f_equal. eapply clsf_expr_sound;
          [ exact Cl | exact Sat | exact Sat' | .. ]; eassumption.
      * rewrite <- Pos.eqb_neq in Ne. rewrite Ne in Lo1, Lo2. apply SE; assumption.
Qed.

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
                 !! (clsf_lvalue (N x) e1 = Some (l1 x) /\
                     clsf_expr   (N x) e2 = Some (l2 x))) ->
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

End IFC.

Export IFC.

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

