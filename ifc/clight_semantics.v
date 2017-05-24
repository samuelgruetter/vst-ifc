Require Export lib.LibTactics.
Require Export compcert.cfrontend.Clight.
Require Export veric.Clight_new.
Require Export veric.semax. (* for exit_cont *)
Require Export veric.tycontext. (* for exit_kind *)
Require Import compcert.lib.Maps.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export sepcomp.semantics.
Require Export sepcomp.semantics_lemmas.
From compcert Require Export Clightdefs.

Require Import List. Import ListNotations.

Definition star: genv -> corestate -> mem -> corestate -> mem -> Prop :=
  corestep_star cl_core_sem.

Definition plus: genv -> corestate -> mem -> corestate -> mem -> Prop :=
  corestep_plus cl_core_sem.

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

Lemma star_null:
  forall ge s s' m m',
  star ge s m s' m' ->
  forall e te c e' te', s = (State e te c) /\
  s' = (State e' te' c) ->
  e' = e /\ te' = te /\ m' = m.
Proof.
Admitted. (* TODO: Not sure that this is true: if I have a while loop for instance,
what does the semantics do? *)

Lemma star_nochange: forall ge e1 te1 e2 te2 k m1 m2,
  star ge (State e1 te1 (Kseq (Sloop Sskip Sskip) :: k)) m1
          (State e2 te2 (Kseq (Sloop Sskip Sskip) :: k)) m2 ->
  e2 = e1 /\ te2 = te1 /\ m2 = m1.
Proof.
  intros.
  remember (State e1 te1 (Kseq (Sloop Sskip Sskip) :: k)) as s1.
  remember (State e2 te2 (Kseq (Sloop Sskip Sskip) :: k)) as s2.
  gen e1 te1 e2 te2 k Heqs1 Heqs2.
  unfold star, corestep_star in H. destruct H as [n H].
  induction n; intros; subst.
  - simpl in H. inversion H. auto.
  - simpl in H. destruct H as [s11 [m11 [Step Star]]].
    inversion Step. subst m11 s11. subst.
    (* continue inversion on Star, will need IH on (n-2) *)
Abort. (* should work *)

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

Lemma invert_star: forall ge s1 m1 s3 m3,
  star ge s1 m1 s3 m3 ->
  s1 = s3 /\ m1 = m3 \/ plus ge s1 m1 s3 m3.
Proof.
  introv Star. unfold star in Star. unfold corestep_star in Star. destruct Star as [n StepN].
  destruct n as [|n].
  - simpl in StepN. inversion StepN; subst. left. auto.
  - simpl in StepN. right. destruct StepN as [s2 [m2 [Step Star]]].
    unfold plus. unfold corestep_plus. eexists. simpl. eauto.
Qed.

Lemma invert_plus: forall ge s1 m1 s3 m3,
  plus ge s1 m1 s3 m3 ->
  exists s2 m2, cl_step ge s1 m1 s2 m2 /\ star ge s2 m2 s3 m3.
Proof.
  introv Plus. unfold plus in Plus. unfold corestep_plus in Plus. destruct Plus as [n StepN].
  simpl in StepN. destruct StepN as [s2 [m2 [Step Star]]].
  unfold star. unfold corestep_star. eauto.
Qed.

(*
Lemma invert_star00: forall ge s1 m1 s3 m3,
  star ge s1 m1 s3 m3 ->
  s1 = s3 /\ m1 = m3 \/ exists s2 m2, cl_step ge s1 m1 s2 m2 /\ star ge s2 m2 s3 m3.
Proof.
  introv Star. unfold star in Star. unfold corestep_star in Star. destruct Star as [n StepN].
  destruct n as [|n].
  - simpl in StepN. inversion StepN; subst. left. auto.
  - simpl in StepN. right. destruct StepN as [s2 [m2 [Step Star]]].
    unfold star. unfold corestep_star. eauto.
Qed.
*)

Lemma invert_plus_return: forall ge e1 te1 m1 e2 te2 m2 k k' retExpr,
  plus ge (State e1 te1 (Kseq (Sreturn retExpr) :: k)) m1
          (State e2 te2 k') m2 ->
  exists k' te' ve' v' f optid te'' m11,
    call_cont k = Kcall optid f ve' te' :: k' /\
    Mem.free_list m1 (blocks_of_env ge e1) = Some m11 /\
    match retExpr with
     | Some a =>
         exists v,
         Clight.eval_expr ge e1 te1 m1 a v /\
         Cop.sem_cast v (typeof a) (fn_return f) m1 = Some v'
     | None => v' = Vundef
     end /\
    match optid with
     | Some id => True /\ te'' = PTree.set id v' te'
     | None => True /\ te'' = te'
     end.
Proof.
  introv Plus. apply invert_plus in Plus. destruct Plus as [s11 [m11 [Step Star]]].
  inversion Step; subst.
  repeat eexists; try eassumption.
Qed.

(*
Lemma invert_star_return: forall ge e1 te1 m1 e2 te2 m2 k k' retExpr,
  star ge (State e1 te1 (Kseq (Sreturn retExpr) :: k)) m1
          (State e2 te2 k') m2 ->
  e1 = e2 /\ te1 = te2 /\ (Kseq (Sreturn retExpr) :: k) = k' /\ m1 = m2 \/
  exists k' te' ve' v' f optid te'' m11,
    call_cont k = Kcall optid f ve' te' :: k' /\
    Mem.free_list m1 (blocks_of_env ge e1) = Some m11 /\
    match retExpr with
     | Some a =>
         exists v,
         Clight.eval_expr ge e1 te1 m1 a v /\
         Cop.sem_cast v (typeof a) (fn_return f) m1 = Some v'
     | None => v' = Vundef
     end /\
    match optid with
     | Some id => True /\ te'' = PTree.set id v' te'
     | None => True /\ te'' = te'
     end.
Proof.
  introv Star. apply invert_star in Star. destruct Star as [[Eqs Eqm] | [s11 [m11 [Step Star]]]].
  - left. inversion Eqs; subst. auto.
  - right. inversion Step; subst.
    repeat eexists; try eassumption.
Qed.

Lemma invert_star_return00: forall ge e1 te1 m1 e2 te2 m2 ek vl k retExpr,
  star ge (State e1 te1 (Kseq (Sreturn retExpr) :: k)) m1
          (State e2 te2 (exit_cont ek vl k)) m2 ->
  exists k' te' ve' v' f optid te'' m11,
    call_cont k = Kcall optid f ve' te' :: k' /\
    Mem.free_list m1 (blocks_of_env ge e1) = Some m11 /\
    match retExpr with
     | Some a =>
         exists v,
         Clight.eval_expr ge e1 te1 m1 a v /\
         Cop.sem_cast v (typeof a) (fn_return f) m1 = Some v'
     | None => v' = Vundef
     end /\
    match optid with
     | Some id => True /\ te'' = PTree.set id v' te'
     | None => True /\ te'' = te'
     end.
Proof.
  introv Star. apply invert_star in Star. destruct Star as [[Eqs Eqm] | [s11 [m11 [Step Star]]]].
  - destruct ek; inversion Eqs; subst.
    * exfalso. eapply blah. eassumption.
    * admit. (* contradiction H2 *)
    * admit. (* contradiction H2 *)
    * admit. (* contradiction H2 *)
  - inversion Step; subst.
    repeat eexists; try eassumption.
Qed.
*)

(*
Lemma exit_cont_length: forall k ek vl,
  length (exit_cont ek vl k) <= length k.
Proof.
  intro k. induction k; intros.
  - destruct ek; simpl. omega.
Qed.
*)

Definition fooooooooo := 1.

Lemma continue_cont_length: forall k,
  length (continue_cont k) <= S (length k).
Proof.
  intro k. induction k.
  - simpl. omega.
  - simpl. destruct a; simpl; omega.
Qed.

Lemma break_cont_length: forall k,
  length (break_cont k) <= length k.
Proof.
  intro k. induction k; simpl.
  - omega.
  - destruct a; simpl; omega.
Qed.

Lemma call_cont_length: forall k,
  length (call_cont k) <= length k.
Proof.
  intro k. induction k; simpl.
  - omega.
  - destruct a; simpl; omega.
Qed.

(* add "(eval r) = vl" in conclusion? -> No, because this is for the 0-step case *)
Lemma return_exit_cont_stronger: forall k r ek vl,
  Kseq (Sreturn r) :: k = exit_cont ek vl k ->
  ek = EK_return /\ (k = [] \/ exists i f e t k', k = Kcall i f e t :: k').
(*
  ek = EK_return /\ (
    (k = []) \/
    (vl = None) \/
    (exists i f e t v k', k = Kcall None (zap_fn_return f) e (PTree.set i v t) :: k' /\ vl = Some v)).
*)
Proof.
  intros. destruct k as [|a k].
  - destruct ek; simpl in H; try discriminate. auto.
  - destruct ek; simpl in H.
    + exfalso. eapply blah. eassumption.
    + destruct a.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (break_cont_length k).
        simpl in H. omega.
      * apply (f_equal (@length cont')) in H. exfalso. simpl in H. omega.
      * discriminate.
      * apply (f_equal (@length cont')) in H. exfalso. simpl in H. omega.
      * discriminate.
    + destruct a.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (continue_cont_length k).
        simpl in H. omega.
      * discriminate.
      * discriminate.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (continue_cont_length k).
        simpl in H. omega.
      * discriminate.
    + apply (conj eq_refl). right.
      remember (match a with
          | Kseq _ => call_cont k
          | Kloop1 _ _ => call_cont k
          | Kloop2 _ _ => call_cont k
          | Kswitch => call_cont k
          | Kcall _ _ _ _ => a :: k
          end) as M.
      destruct vl.
      * destruct M; try discriminate.
        destruct c.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in HeqM. exfalso. pose proof (call_cont_length M).
           simpl in HeqM. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in HeqM. exfalso. pose proof (call_cont_length M).
           simpl in HeqM. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in HeqM. exfalso. pose proof (call_cont_length M).
           simpl in HeqM. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in HeqM. exfalso. pose proof (call_cont_length M).
           simpl in HeqM. omega.
        ++ destruct l.
           ** inversion H; subst. repeat eexists. (* not a contradiction *)
           ** inversion H; subst. repeat eexists. (* not a contradiction *)
      * destruct a.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in H2. exfalso. pose proof (call_cont_length k).
           simpl in H2. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in H2. exfalso. pose proof (call_cont_length k).
           simpl in H2. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in H2. exfalso. pose proof (call_cont_length k).
           simpl in H2. omega.
        ++ inversion H; subst.
           apply (f_equal (@length cont')) in H2. exfalso. pose proof (call_cont_length k).
           simpl in H2. omega.
        ++ repeat eexists. (* not a contradiction *)
Qed.

Lemma return_exit_cont: forall k r ek vl,
  Kseq (Sreturn r) :: k = exit_cont ek vl k -> ek = EK_return.
Proof.
  intro k. induction k; intros.
  - destruct ek; simpl in H; try discriminate. reflexivity.
  - destruct ek; simpl in H.
    + exfalso. eapply blah. eassumption.
    + destruct a.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (break_cont_length k).
        simpl in H. omega.
      * apply (f_equal (@length cont')) in H. exfalso. simpl in H. omega.
      * discriminate.
      * apply (f_equal (@length cont')) in H. exfalso. simpl in H. omega.
      * discriminate.
    + destruct a.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (continue_cont_length k).
        simpl in H. omega.
      * discriminate.
      * discriminate.
      * apply (f_equal (@length cont')) in H. exfalso. pose proof (continue_cont_length k).
        simpl in H. omega.
      * discriminate.
    + reflexivity.
Qed.

(*
Lemma exit_cont_eq_false: forall k c ek vl,
  c :: k = exit_cont ek vl k -> False.
Proof.
  intro k. induction k; intros.
  - destruct ek; simpl in H; try discriminate. admit. (* false *)
  - destruct ek; simpl in H. eapply blah. eassumption. admit.
Qed.
*)

(*
Lemma no_add_skip: forall n2 n1 ge e te k m e' te' m' s2 m2,
  corestepN cl_core_sem ge n1 (State e te k) m s2 m2 ->
  corestepN cl_core_sem ge n2 s2 m2 (State e' te' (Kseq Sskip :: k)) m' ->
  False.
Proof.
  intro n2. induction n2; intros.
  - inversion H0. subst. unfold corestepN in H0.
*)

Lemma no_add_skip: forall n ge e te k m e' te' m',
  corestepN cl_core_sem ge n (State e te k) m (State e' te' (Kseq Sskip :: k)) m' ->
  False.
Proof.
  intro n. induction n; intros.
  - inversion H. eapply blah. symmetry. eassumption.
  - simpl in H. destruct H as [c2 [m2 [Step Star]]].
Abort.

Lemma invert_no_step: forall ge e te k e' te' m m',
  star ge (State e te (Kseq Sskip :: k)) m (State e' te' (Kseq Sskip :: k)) m' ->
  m' = m /\ e' = e /\ te' = te.
Proof.
  intros. unfold star, corestep_star in H. destruct H as [n Step].
  destruct n.
  - simpl in Step. inversion Step. auto.
  - simpl in Step. destruct Step as [c2 [m2 [Step Star]]].
    inversion Step. subst.
    assert (star ge (State e te k) m (State e' te' (Kseq Sskip :: k)) m') as Step2. {
      unfold star, corestep_star. exists (S n). simpl. eauto.
    }
    unfold star, corestep_star in Step2.
    (* would need no_add_skip, which probably doesn't hold *)
Abort.

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

Lemma invert_ifthenelse: forall ge e1 te1 m1 cond c1 c2 k s2 m2,
  plus ge (State e1 te1 (Kseq (Sifthenelse cond c1 c2) :: k)) m1 s2 m2 ->
  exists v b, Clight.eval_expr ge e1 te1 m1 cond v /\
              Cop.bool_val v (typeof cond) m1 = Some b /\
              star ge (State e1 te1 (Kseq (if b then c1 else c2) :: k)) m1 s2 m2.
Proof.
  introv Pl. apply invert_plus in Pl. destruct Pl as [s1' [m1' [Step Star]]].
  inversion Step. subst. rename m1' into m1. eauto.
Qed.

Lemma invert_set: forall ge e1 te1 id e k m1 s2 m2,
  plus ge (State e1 te1 (Kseq (Sset id e) :: k)) m1 s2 m2 ->
  exists v, star ge (State e1 (PTree.set id v te1) k) m1 s2 m2 /\
            Clight.eval_expr ge e1 te1 m1 e v.
Proof.
  introv Plus. apply invert_plus in Plus.
  destruct Plus as [s11 [m11 [Step Star]]].
  inversion Step. subst m11. subst. eauto.
Qed.

(* TODO doesn't hold because it needs star_null *)
Lemma invert_set_too_strong: forall ge e1 te1 e2 te2 id e k m1 m2,
  star ge (State e1 te1 (Kseq (Sset id e) :: k)) m1 (State e2 te2 k) m2 ->
  e2 = e1 /\ m2 = m1 /\ 
  exists v, te2 = (PTree.set id v te1) /\ Clight.eval_expr ge e1 te1 m1 e v.
Proof.
  introv Star. apply invert_star in Star.
  destruct Star as [[Eq1 Eq2] | Plus].
  - inversion Eq1. exfalso. eapply blah. eassumption.
  - apply invert_plus in Plus. destruct Plus as [s11 [m11 [Step Star]]].
    inversion Step. subst m11. subst.
    eapply star_null in Star; [ | eauto ]. (* TODO star_null doesn't hold *)
    destruct Star as [? [? ?]]. subst. eauto.
Qed.
