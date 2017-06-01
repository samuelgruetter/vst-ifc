Require Import ifc.clight_semantics.
Require Export ifc.ifc_sig.
Require Import ifc.simple_vst_store_lemmas.
Require Import veric.Clight_new.
Require Import veric.semax_lemmas.
Require Import sepcomp.closed_safety.
Require Import veric.semax.
Require Import floyd.base.
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

Definition starN: genv -> nat -> corestate -> mem -> corestate -> mem -> Prop :=
  corestepN cl_core_sem.

(*
Fixpoint cont_equiv (ge: genv) (m m': mem) (k k' : cont) {struct k}: Prop :=
match k, k' with
  | Kseq s         :: t, Kseq s'            :: t' => s = s' /\ cont_equiv ge m m' t t'
  | Kloop1 s1 s2   :: t, Kloop1 s1' s2'     :: t' => s1 = s1' /\ s2 = s2' /\ cont_equiv ge m m' t t'
  | Kloop2 s1 s2   :: t, Kloop2 s1' s2'     :: t' => s1 = s1' /\ s2 = s2' /\ cont_equiv ge m m' t t'
  | Kswitch        :: t, Kswitch            :: t' => cont_equiv ge m m' t t'
  | Kcall i f e te :: t, Kcall i' f' e' te' :: t' =>
      i = i' /\ f = f' /\ sync ge e te t m e' te' t' m'
  | _, _ => False
  end
with cs_cont_equiv (ge: genv) (m m': mem) (s s' : corestate) {struct s}: Prop :=
  match s, s' with
  | (State e te k), (State e' te' k') => cont_equiv ge m m' k k'
  | ext, ext' => ext = ext'
    (* if we put True, it's not transitive, and if we put False, it's not reflexive *)
  end
with sync (ge : genv) (e1 : env) (te1 : temp_env) (k1 : cont) (m1 : mem)
                      (e1': env) (te1': temp_env) (k1': cont) (m1': mem): Prop
:= forall n e2  te2  k2  m2 , starN ge n (State e1  te1  k1 ) m1  (State e2  te2  k2 ) m2  ->
     exists e2' te2' k2' m2', starN ge n (State e1' te1' k1') m1' (State e2' te2' k2') m2'
                           /\ cont_equiv ge m2 m2' k2 k2' (* <-- recursive call with universally
  quantified k2 is not decreasing! *)
.
*)
(*
with sync (ge : genv) (s1: corestate) (m1: mem) (s1': corestate) (m1': mem) {struct s1}: Prop :=
  cs_cont_equiv ge m1 m1' s1 s1' ->
  forall s2 m2 n, starN ge n s1 m1 s2 m2 ->
    exists s2' m2', starN ge n s1' m1' s2' m2' /\ cs_cont_equiv ge m2 m2' s2 s2'.
*)

Definition cont'_equiv (k k' : cont'): Prop := match k, k' with
  | Kseq s, Kseq s' => s = s'
  | Kloop1 s1 s2, Kloop1 s1' s2' => s1 = s1' /\ s2 = s2'
  | Kloop2 s1 s2, Kloop2 s1' s2' => s1 = s1' /\ s2 = s2'
  | Kswitch, Kswitch => True
  | Kcall i f e te, Kcall i' f' e' te' => i = i' /\ f = f' (* not requiring e = e' /\ te = te' *)
  | _, _ => False
  end.

Lemma cont'_equiv_refl: forall k, cont'_equiv k k.
Proof. intro k. unfold cont'_equiv. destruct k; auto. Qed.

Lemma cont'_equiv_sym: forall k k', cont'_equiv k k' -> cont'_equiv k' k.
Proof. introv CE. unfold cont'_equiv in *. destruct k; destruct k'; intuition. Qed.

Lemma cont'_equiv_trans: forall k1 k2 k3,
  cont'_equiv k1 k2 -> cont'_equiv k2 k3 -> cont'_equiv k1 k3.
Proof.
  introv CE12 CE23. unfold cont'_equiv in *.
  destruct k1; destruct k2; destruct k3; intuition; congruence.
Qed.

Definition cont_head_equiv (k k': cont): Prop := match k, k' with
  | h :: _, h' :: _ => cont'_equiv h h' (* no requirements on tail *)
  | nil, nil => True
  | _, _ => False
  end.

Lemma cont_head_equiv_refl: forall k, cont_head_equiv k k.
Proof. intro k. pose proof cont'_equiv_refl. induction k; simpl; auto. Qed.

Lemma cont_head_equiv_sym: forall k1 k2, cont_head_equiv k1 k2 -> cont_head_equiv k2 k1.
Proof.
  introv CE. destruct k1; destruct k2; auto.
  simpl in *. apply cont'_equiv_sym. assumption.
Qed.

Lemma cont_head_equiv_trans: forall k1 k2 k3,
  cont_head_equiv k1 k2 -> cont_head_equiv k2 k3 -> cont_head_equiv k1 k3.
Proof.
  introv CE12 CE23. destruct k1; destruct k2; destruct k3; simpl in *; auto.
  + contradiction.
  + apply* cont'_equiv_trans.
Qed.

Fixpoint cont_equiv (k k': cont): Prop := match k, k' with
  | h :: t, h' :: t' => cont'_equiv h h' /\ cont_equiv t t'
  | nil, nil => True
  | _, _ => False
  end.

Lemma cont_equiv_refl: forall k, cont_equiv k k.
Proof. intro k. pose proof cont'_equiv_refl. induction k; simpl; auto. Qed.

Lemma cont_equiv_sym: forall k1 k2, cont_equiv k1 k2 -> cont_equiv k2 k1.
Proof.
  intro k1. induction k1; introv CE; destruct k2; auto.
  inversion CE. simpl. apply cont'_equiv_sym in H. auto.
Qed.

Lemma cont_equiv_trans: forall k1 k2 k3, cont_equiv k1 k2 -> cont_equiv k2 k3 -> cont_equiv k1 k3.
Proof.
  intro k1. induction k1; introv CE12 CE23; destruct k2; destruct k3; auto;
  simpl in *; try contradiction.
  destruct CE12 as [? CE12]. destruct CE23 as [? CE23]. split.
  + apply* cont'_equiv_trans.
  + eapply IHk1; eassumption.
Qed.

Definition cs_cont_head_equiv (s s' : corestate): Prop :=
  match s, s' with
  | (State e te k), (State e' te' k') => cont_head_equiv k k'
  | ext, ext' => ext = ext'
    (* if we put True, it's not transitive, and if we put False, it's not reflexive *)
  end.

Lemma cs_cont_head_equiv_refl: forall s, cs_cont_head_equiv s s.
Proof. pose proof cont_head_equiv_refl. intro s; destruct s; simpl; auto. Qed.

Lemma cs_cont_head_equiv_sym: forall s1 s2, cs_cont_head_equiv s1 s2 -> cs_cont_head_equiv s2 s1.
Proof. introv CE. destruct s1; destruct s2; simpl in *; auto. apply* cont_head_equiv_sym. Qed.

Lemma cs_cont_head_equiv_trans: forall s1 s2 s3,
  cs_cont_head_equiv s1 s2 ->
  cs_cont_head_equiv s2 s3 ->
  cs_cont_head_equiv s1 s3.
Proof.
  introv CE12 CE23.
  pose proof cont_head_equiv_trans.
  destruct s1; destruct s2; destruct s3; simpl in *; eauto; congruence.
Qed.

Definition cs_cont_equiv (s s' : corestate): Prop :=
  match s, s' with
  | (State e te k), (State e' te' k') => cont_equiv k k'
  | ext, ext' => ext = ext'
    (* if we put True, it's not transitive, and if we put False, it's not reflexive *)
  end.

Lemma cs_cont_equiv_refl: forall s, cs_cont_equiv s s.
Proof. pose proof cont_equiv_refl. intro s; destruct s; simpl; auto. Qed.

Lemma cs_cont_equiv_sym: forall s1 s2, cs_cont_equiv s1 s2 -> cs_cont_equiv s2 s1.
Proof. introv CE. destruct s1; destruct s2; simpl in *; auto. apply* cont_equiv_sym. Qed.

Lemma cs_cont_equiv_trans: forall s1 s2 s3,
  cs_cont_equiv s1 s2 ->
  cs_cont_equiv s2 s3 ->
  cs_cont_equiv s1 s3.
Proof.
  introv CE12 CE23.
  pose proof cont_equiv_trans.
  destruct s1; destruct s2; destruct s3; simpl in *; eauto; congruence.
Qed.

Lemma starN_fun: forall {ge n s m s1 m1 s2 m2},
  starN ge n s m s1 m1 ->
  starN ge n s m s2 m2 ->
  s1 = s2 /\ m1 = m2.
Proof.
  introv Star1 Star2.
  edestruct corestep_star_fun with (sem := cl_core_sem).
  + unfold corestep_fun. simpl. introv Step1 Step2.
    pose proof (cl_corestep_fun _ _ _ _ _ _ _ Step1 Step2) as P.
    inversion P. auto.
  + eapply Star1.
  + eapply Star2.
  + auto.
Qed.

(*
Definition can_simulate (ge : genv) (s1: corestate) (m1: mem) (s1': corestate) (m1': mem): Prop :=
  forall s2 m2 n, starN ge n s1 m1 s2 m2 ->
    exists s2' m2', starN ge n s1' m1' s2' m2' /\ cs_cont_equiv s2 s2'.

Definition sync (ge : genv) (s1: corestate) (m1: mem) (s2: corestate) (m2: mem): Prop :=
  cs_cont_equiv s1 s2 /\
  can_simulate ge s1 m1 s2 m2 /\
  can_simulate ge s2 m2 s1 m1.
*)

Definition sync (ge : genv) (s1: corestate) (m1: mem) (s1': corestate) (m1': mem): Prop :=
  forall s2 m2 n, starN ge n s1 m1 s2 m2 ->
    exists s2' m2', starN ge n s1' m1' s2' m2' /\ cs_cont_head_equiv s2 s2'.

(*
Reset sync.

Definition sync (ge : genv) (e1 : env) (te1 : temp_env) (m1 : mem)
                            (e1': env) (te1': temp_env) (m1': mem): Prop
:= forall k1 k1', cont_equiv k1 k1' ->
   forall n e2  te2  k2  m2 , starN ge n (State e1  te1  k1 ) m1  (State e2  te2  k2 ) m2  ->
     exists e2' te2' k2' m2', starN ge n (State e1' te1' k1') m1' (State e2' te2' k2') m2'
                           /\ cont_equiv k2 k2'.
*)

Lemma sync_to_cs_cont_head_equiv: forall ge s1 m1 s1' m1',
  sync ge s1 m1 s1' m1' -> cs_cont_head_equiv s1 s1'.
Proof.
  unfold sync. introv Sy. specialize (Sy s1 m1 O). simpl in Sy.
  specialize (Sy eq_refl). destruct Sy as [x [y [Eq CE]]]. inversion Eq. subst x y.
  assumption.
Qed.

Lemma sync_refl: forall (ge : genv) (s1: corestate) (m1 : mem),
  sync ge s1 m1 s1 m1.
Proof.
  intros. unfold sync.
  introv Star. pose proof cs_cont_head_equiv_refl. eauto.
Qed.

Lemma sync_sym: forall (ge : genv) (s1 s1': corestate) (m1 m1' : mem),
  sync ge s1 m1 s1' m1' -> sync ge s1' m1' s1 m1.
Abort. (* Doesn't hold, but we don't need it. *)

Lemma sync_trans: forall ge s1 s2 s3 m1 m2 m3,
  sync ge s1 m1 s2 m2 -> sync ge s2 m2 s3 m3 -> sync ge s1 m1 s3 m3.
Proof.
  introv Sy12 Sy23. unfold sync in *.
  intros s1' m1' n Star1.
  specialize (Sy12 _ _ _ Star1).
  destruct Sy12 as [s2' [m2' [Star2 CE12']]].
  specialize (Sy23 _ _ _ Star2).
  destruct Sy23 as [s3' [m3' [Star3 CE23']]].
  pose proof cs_cont_head_equiv_trans. eauto.
Qed.

Definition iguard {A : Type}
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (k k': cont)
:= forall (x x': A) (ge: genv) (e1 e1': env) (te1 te1': temp_env)
          (m1 m1': mem),
   preP x  e1 te1 m1 ->
   preP x' e1' te1' m1' ->
   let s1  := (State e1  te1  k ) in
   let s1' := (State e1' te1' k') in
   stack_lo_equiv s1 s1' (preN x) (preN x') ->
   heap_lo_equiv  m1 m1' (preA x) (preA x') ->
   sync ge s1 m1 s1' m1'.

Lemma weaken_iguard{T : Type}: forall Delta (P1 P1': T -> pre_assert) N1 N1' A1 A1' k k',
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, ENTAIL Delta, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
  iguard (lft1 VST_to_state_pred P1') N1' A1' k k' ->
  iguard (lft1 VST_to_state_pred P1) N1 A1 k k'.
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

Lemma weaken_iguard0{T : Type}: forall Delta (P1 P1': T -> pre_assert) N1 A1 k k',
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  iguard (lft1 VST_to_state_pred P1') N1 A1 k k' ->
  iguard (lft1 VST_to_state_pred P1) N1 A1 k k'.
Proof.
  introv Imp IG. eapply weaken_iguard; [ eapply Imp | | eapply IG ].
  intro. apply prop_right. split; apply lle_refl.
Qed.

Definition irguard {A : Type}
  (postP: A -> exitkind -> option val -> state_pred) (postN: A -> ret_stack_clsf)
  (postA: A -> ret_heap_clsf) (k k': cont): Prop
:= forall (ek: exitkind) (vl: option val), (* TOOD should vl depend on (x: A) ? *)
  iguard (fun (x: A) => postP x ek vl)
         (fun (x: A) => postN x ek vl)
         (fun (x: A) => postA x ek vl)
         (exit_cont ek vl k )
         (exit_cont ek vl k').

Definition simple_ifc {A : Type} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> exitkind -> option val -> state_pred) (postN: A -> ret_stack_clsf)
  (postA: A -> ret_heap_clsf)
:= forall (k k': cont),
     irguard postP postN postA k k' ->
     iguard preP preN preA (Kseq c :: k) (Kseq c :: k').

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

Definition syncPlus ge s1 m1 s1' m1' :=
  forall s2 m2 n, starN ge (S n) s1 m1 s2 m2 ->
    exists s2' m2', starN ge (S n) s1' m1' s2' m2' /\ cs_cont_head_equiv s2 s2'.

(* Note that there's only one c *)
Lemma sync_syncPlus:
  forall (ge : genv) (e e': env) (te te': temp_env) (c: cont') (k k': cont) (m m' : mem),
  sync     ge (State e te (c :: k)) m (State e' te' (c :: k')) m' <->
  syncPlus ge (State e te (c :: k)) m (State e' te' (c :: k')) m'.
Proof.
  unfold syncPlus, sync. split.
  + introv Sy Star. apply* Sy.
  + introv Sp Star. destruct n as [|n].
    - simpl in Star. inversion Star. subst s2 m2.
      do 2 eexists. simpl. apply (conj eq_refl). apply cont'_equiv_refl.
    - apply* Sp.
Qed.

Definition cont_step_equiv(k k': cont): Prop :=
  forall ge e te m s2 m2,
    cl_step ge (State e te k) m s2 m2 <-> cl_step ge (State e te k') m s2 m2.

Ltac cont_step_equiv_tac :=
  unfold cont_step_equiv; (split; let Step := fresh "Step" in introv Step);
  [ inversion Step; subst; assumption
  | constructor; assumption ].

Lemma seq_step_equiv: forall s1 s2 k,
  cont_step_equiv (Kseq (Ssequence s1 s2) :: k) (Kseq s1 :: Kseq s2 :: k).
Proof. cont_step_equiv_tac. Qed.

Lemma skip_step_equiv: forall k,
  cont_step_equiv (Kseq Sskip :: k) k.
Proof. cont_step_equiv_tac. Qed.

Lemma continue_step_equiv: forall k,
  cont_step_equiv (Kseq Scontinue :: k) (continue_cont k).
Proof. cont_step_equiv_tac. Qed.

Lemma break_step_equiv: forall k,
  cont_step_equiv (Kseq Sbreak :: k) (break_cont k).
Proof. cont_step_equiv_tac. Qed.

Definition relate_retVal_and_retExpr ge e1 te1 m1 f retVal retExpr :=
        match retExpr with
        | Some a =>
            exists v' v,
            retVal = Some v' /\
            Clight.eval_expr ge e1 te1 m1 a v /\
            Cop.sem_cast v (typeof a) (fn_return f) m1 = Some v'
        | None => retVal = None
        end.

Lemma return_step_equiv: forall ge f retVal retExpr e te k m s2 m2,
  current_function k = Some f ->
  relate_retVal_and_retExpr ge e te m f retVal retExpr ->
  cl_step ge (State e te (exit_cont EK_return retVal k)) m s2 m2 ->
  cl_step ge (State e te (Kseq (Sreturn retExpr) :: k)) m s2 m2.
Proof.
    unfold cont_step_equiv. introv Cf R Step.
    simpl in Step.
    destruct retVal.
    + simpl in Step.
      destruct (call_cont k) eqn: E.
      * inv Step. simpl in H3. discriminate.
      * destruct c.
        { exfalso; clear - E.
          revert c0 E; induction k; try destruct a; simpl; intros; try discriminate; eauto. }
        { exfalso; clear - E.
          revert c0 E; induction k; try destruct a; simpl; intros; try discriminate; eauto. }
        { exfalso; clear - E.
          revert c0 E; induction k; try destruct a; simpl; intros; try discriminate; eauto. }
        { exfalso; clear - E.
          revert c0 E; induction k; try destruct a; simpl; intros; try discriminate; eauto. }
        { destruct l.
          - inversion Step. subst. simpl in H3. inversion H3. subst.
            eapply step_return; try eassumption; simpl; try eassumption.
            unfold relate_retVal_and_retExpr in R.
            assert (current_function k = Some f0) as Cf0. {
              eapply semax_call.call_cont_current_function. eassumption.
            }
            rewrite Cf0 in Cf. inv Cf.
            destruct retExpr.
            + destruct R as [v' [v0 [Eq R]]]. inversion Eq. eexists. eapply R.
            + inversion R.
          - inversion Step. subst. simpl in H3. inversion H3. subst.
            eapply step_return; try eassumption; simpl; try eassumption.
            unfold relate_retVal_and_retExpr in R.
            assert (current_function k = Some f1) as Cf1. {
              eapply semax_call.call_cont_current_function. eassumption.
            }
            rewrite Cf1 in Cf. inv Cf.
            destruct retExpr.
            + destruct R as [v' [v0 [Eq R]]]. inversion Eq. eexists. eapply R.
            + inversion R.
        }
    + destruct retExpr as [retExpr|].
      - unfold relate_retVal_and_retExpr in R.
        destruct R as [? [? [? R]]]. discriminate.
      - inversion Step. subst.
        rewrite veric.semax_call.call_cont_idem in H3.
        eapply step_return; eauto.
Qed.

Lemma sync_change_cont: forall ge e e' te te' m m' k1 k2 k1' k2',
  cont_step_equiv k1  k2 ->
  cont_step_equiv k1' k2' ->
  cont_head_equiv k1 k1' ->
  sync ge (State e te k2) m (State e' te' k2') m' ->
  sync ge (State e te k1) m (State e' te' k1') m'.
Proof.
  introv SE SE' CE1 Sy. unfold sync in *. introv Star. destruct n as [|n]; simpl in Star.
  - inversion Star. subst s2 m2. do 2 eexists. simpl starN. apply (conj eq_refl).
    simpl. apply CE1.
  - destruct Star as [s21 [m21 [Step1 Star1]]].
    specialize (Sy s2 m2 (S n)).
    spec Sy. {
      simpl. exists s21 m21. refine (conj _ Star1).
      unfold cont_step_equiv in SE.
      edestruct SE as [? _]. eauto.
    }
    destruct Sy as [s2' [m2' [Star' CE]]].
    simpl in Star'. destruct Star' as [s11' [m11' [Step' Star']]].
    exists s2' m2'. refine (conj _ CE).
    simpl. edestruct SE' as [_ ?]. eauto.
Qed.

(*
Lemma sync_step: forall ge e1 e1' te1 te1' m1 m1' k1 e2 e2' te2 te2' m2 m2' k2,
  cl_step ge (State e1  te1  k1) m1  (State e2  te2  k2) m2  ->
  cl_step ge (State e1' te1' k1) m1' (State e2' te2' k2) m2' ->
  sync ge e2 e2' te2 te2' m2 m2' k2 ->
  sync ge e1 e1' te1 te1' m1 m1' k1.
Proof.
  introv Step Step' Sy. unfold sync in *.
  intros s3 m3 n Star.
  destruct n as [|n].
  - simpl in Star. inversion Star. subst s3 m3.
    do 2 eexists. simpl. eapply (conj eq_refl). apply cont_equiv_refl.
  - simpl in Star. destruct Star as [s11 [m11 [Step2 Star]]].
    assert ((s11, m11) = ((State e2 te2 k2), m2)) as E by apply* cl_corestep_fun.
    inversions E. clear Step2.
    specialize (Sy _ _ _ Star).
    destruct Sy as [s3' [m3' [Star' CE]]].
    exists s3' m3'. refine (conj _ CE).
    simpl. exists (State e2' te2' k2) m2'. eauto.
Qed.
*)

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
    intros k k' RG.
    cut (iguard (fun x : T => VST_to_state_pred (P1 x)) N1 A1
           (Kseq h :: Kseq t :: k )
           (Kseq h :: Kseq t :: k')
    ). {
      unfold iguard. clear. introv G Sat Sat' SE HE.
      specialize (G _ _ ge _ _ _ _ _ _ Sat Sat' SE HE).
      apply sync_change_cont with (k2  := (Kseq h :: Kseq t :: k ))
                                  (k2' := (Kseq h :: Kseq t :: k')).
      - apply seq_step_equiv.
      - apply seq_step_equiv.
      - simpl. reflexivity.
      - exact G.
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
      replace (exit_cont ek vl (Kseq t :: k')) with (exit_cont ek vl k')
        by (destruct ek; simpl; congruence).
      unfold irguard in RG. specialize (RG ek vl). apply RG.
Qed.

Lemma ifc_skip{T: Type}:
  forall Delta P N A,
  ifc_def T Delta P N A Sskip (lft1 normal_ret_assert P) (normalPostClsf N) (normalPostClsf A).
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. split.
  - intro x. apply semax_skip.
  - unfold irguard. introv IG.
    specialize (IG EK_normal None).
    unfold normalPostClsf, VST_post_to_state_pred, lft1, normal_ret_assert in IG.
    simpl in IG.
    unfold iguard in *.
    introv Sat Sat' SE HE.
    specialize (IG x x' ge e1 e1' te1 te1' m1 m1').
    spec IG. {
      eapply VST_to_state_pred_commutes_imp; [ | eapply Sat ].
      simpl. intro rho. apply andp_right.
      - apply prop_right. reflexivity.
      - apply andp_right.
        + apply prop_right. reflexivity.
        + apply derives_refl.
    }
    spec IG. {
      eapply VST_to_state_pred_commutes_imp; [ | eapply Sat' ].
      simpl. intro rho. apply andp_right.
      - apply prop_right. reflexivity.
      - apply andp_right.
        + apply prop_right. reflexivity.
        + apply derives_refl.
    }
    specialize (IG SE HE).
    apply sync_change_cont with (k2 := k) (k2' := k').
    + apply skip_step_equiv.
    + apply skip_step_equiv.
    + reflexivity.
    + exact IG.
Qed.

Lemma ifc_seq_skip{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta P N A c P' N' A' <-> ifc_def T Delta P N A (Ssequence c Sskip) P' N' A'.
Proof.
Admitted.

Lemma eval_bool_true: forall b bb ge e1 te1 m1,
  Clight.eval_expr ge e1 te1 m1 b bb ->
  Cop.bool_val bb (typeof b) m1 = Some true ->
  VST_to_state_pred (local (` (typed_true (typeof b)) (eval_expr b))) e1 te1 m1.
Admitted.

Lemma eval_bool_false: forall b bb ge e1 te1 m1,
  Clight.eval_expr ge e1 te1 m1 b bb ->
  Cop.bool_val bb (typeof b) m1 = Some false ->
  VST_to_state_pred (local (` (typed_false (typeof b)) (eval_expr b))) e1 te1 m1.
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
    introv RG.
    specialize (B1i k k' RG). specialize (B2i k k' RG).
    unfold iguard in *.
    introv Sat Sat' SE HE.
    introv Star. destruct n as [|n]; simpl in Star.
    { inversion Star. subst s2 m2. simpl starN. do 2 eexists.
      apply (conj eq_refl). simpl. reflexivity. }
    destruct Star as [s11 [m11 [Step Star]]].
    inversion Step. subst m11. subst. rename v1 into bb, H8 into Ev, H9 into Bv, b0 into bbb.
    assert (Bv' : Cop.bool_val bb (typeof b) m1' = Some bbb) by admit. (* TODO by Lo-eq *)
    assert (Ev' : Clight.eval_expr ge e1' te1' m1' b bb) by admit. (* TODO by Lo-eq *)
    specialize (B1i x x' ge e1 e1' te1 te1' m1 m1').
    specialize (B2i x x' ge e1 e1' te1 te1' m1 m1').
    unfold lft0, lft2 in *. repeat rewrite VST_to_state_pred_and in *.
    destruct Sat as [Tcb Sat]. destruct Sat' as [Tcb' Sat'].
    destruct bbb.
    + (* then-branch *)
      clear B2s B2i.
      unfold lft0, lft2 in *. repeat rewrite VST_to_state_pred_and in *.
      spec B1i. { apply (conj Sat). apply* eval_bool_true. }
      spec B1i. { apply (conj Sat'). apply* eval_bool_true. }
      spec B1i. { apply* stack_lo_equiv_change_cmd. }
      specialize (B1i HE).
      unfold sync in B1i.
      specialize (B1i _ _ _ Star).
      destruct B1i as [s2' [m2' [Star' CE2]]].
      exists s2' m2'. refine (conj _ CE2).
      simpl. do 2 eexists. split.
      * apply* step_ifthenelse.
      * simpl. apply Star'.
    + (* else-branch *)
      clear B1s B1i.
      unfold lft0, lft2 in *. repeat rewrite VST_to_state_pred_and in *.
      spec B2i. { apply (conj Sat). apply* eval_bool_false. }
      spec B2i. { apply (conj Sat'). apply* eval_bool_false. }
      spec B2i. { apply* stack_lo_equiv_change_cmd. }
      specialize (B2i HE).
      unfold sync in B2i.
      specialize (B2i _ _ _ Star).
      destruct B2i as [s2' [m2' [Star' CE2]]].
      exists s2' m2'. refine (conj _ CE2).
      simpl. do 2 eexists. split.
      * apply* step_ifthenelse.
      * simpl. apply Star'.
Grab Existential Variables. apply nil. apply nil. apply nil. apply nil.
Qed.

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
  - unfold ifc_core in *. unfold simple_ifc in *. introv RG.
    clear Bodys Incrs.
    unfold irguard.
    unfold iguard. introv Sat Sat' SE HE.
Admitted. (*
    introv CE Star. simpl in Star. destruct Star as [s11 [m11 [Step Star]]].
    inversion Step. subst s11 m11. subst.
    (* specialize (Incri (* what? *)) *)

    specialize (Bodyi (Kseq Scontinue :: Kloop1 body incr :: k)).
    spec Bodyi. {
      unfold irguard. intros ek vl.
      unfold loop1_ret_assert, loop2_ret_assert, loop1_ret_clsf,
             loop2_ret_clsf, lft2, VST_post_to_state_pred.
      destruct ek; simpl.
      + (* EK_normal *)

Admitted.
*)

Lemma sync_exit_cont_to_head_equiv: forall ge e1 te1 k e1' te1' k' m1 m1' ek retVal,
  sync ge (State e1  te1  (exit_cont ek retVal k )) m1
          (State e1' te1' (exit_cont ek retVal k')) m1' ->
  cont_head_equiv k k'.
Proof.
  introv Sy. unfold sync in Sy. destruct ek; simpl in Sy.
  + (* EK_normal *)
    apply sync_to_cs_cont_head_equiv in Sy. simpl in Sy. assumption.
  + (* EK_break *)
    edestruct Sy as [s1'' [m1'' [Star0 CE]]]. {
      instantiate (3 := 0%nat). simpl. reflexivity.
    }
    simpl in Star0. inversion Star0. subst m1'' s1''. clear Star0.
    simpl in CE.
    (* Doesn't hold at all because exit_cont chops off head of k/k' *)
Abort.

Lemma destruct_call_cont: forall k,
  call_cont k = nil \/ exists optid f e te k', call_cont k = Kcall optid f e te :: k'.
Proof.
  intro k. induction k.
  - left. reflexivity.
  - destruct IHk.
    * destruct a; simpl; auto.
      right. do 5 eexists. reflexivity.
    * right. destruct a; simpl; eauto. do 5 eexists. reflexivity.
Qed.

Lemma and_left_proves_right: forall (P Q: Prop),
  P -> (P -> Q) -> P /\ Q.
Proof. intuition. Qed.

(* Note: Sbreak is not a step by itself: One cl_step does the break + one more command. *)
Lemma ifc_break{T: Type}:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf),
  ifc_def T Delta
          (fun (x: T) => R x EK_break None)
          (fun (x: T) => N x EK_break None)
          (fun (x: T) => A x EK_break None)
          Sbreak
          R N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. apply and_left_proves_right.
  - intro x. apply semax_break.
  - introv Sound RG. unfold irguard, iguard in *.
    introv Sat Sat' SE HE.
    specialize (RG EK_break None x x' ge e1 e1' te1 te1' m1 m1').
    unfold VST_post_to_state_pred in RG. simpl in RG.
    specialize (RG Sat Sat' SE HE).
    apply sync_change_cont with (k2 := (break_cont k)) (k2' := (break_cont k')).
    + apply break_step_equiv.
    + apply break_step_equiv.
    + simpl. reflexivity.
    + exact RG.
Qed.

(* Note: Scontinue is not a step by itself: One cl_step does the continue + one more command. *)
Lemma ifc_continue{T: Type}:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf),
  ifc_def T Delta
          (fun (x: T) => R x EK_continue None)
          (fun (x: T) => N x EK_continue None)
          (fun (x: T) => A x EK_continue None)
          Scontinue
          R N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. apply and_left_proves_right.
  - intro x. apply semax_continue.
  - introv Sound RG. unfold irguard, iguard in *.
    introv Sat Sat' SE HE.
    specialize (RG EK_continue None x x' ge e1 e1' te1 te1' m1 m1').
    unfold VST_post_to_state_pred in RG. simpl in RG.
    specialize (RG Sat Sat' SE HE).
    apply sync_change_cont with (k2 := (continue_cont k)) (k2' := (continue_cont k')).
    + apply continue_step_equiv.
    + apply continue_step_equiv.
    + simpl. reflexivity.
    + exact RG.
Qed.

(* If we look at step_call_internal, we see that it adds another return at the end of
   the function body.
   Does that mean that every function returns twice? No
*)

Lemma ifc_return{T: Type}:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf)
        (retExpr: option expr) (retVal: option val),
(* TODO this is an equality between two things of type "environ -> mpred", probably 
not what we want *)
  (cast_expropt retExpr (ret_type Delta)) = `retVal ->
  ifc_def T Delta
          (fun (x: T) => tc_expropt Delta retExpr (ret_type Delta) &&
                         R x EK_return retVal)
          (fun (x: T) => N x EK_return retVal)
          (fun (x: T) => A x EK_return retVal)
          (Sreturn retExpr)
          R N A.
Proof.
  intros. unfold ifc_def, ifc_core, simple_ifc. apply and_left_proves_right.
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
  - introv Sound RG.
    assert (HH: @semax CS Espec = @semax.semax CS Espec) by admit. (* TODO import transparent def *)
    rewrite HH in Sound. clear HH. rewrite semax_unfold in Sound.
    (* TODO "Sound" might be useful to prove soundness stuff below, but for the moment,
       we don't use it *) clear Sound.
    unfold irguard in RG. unfold iguard in *.
    introv Sat Sat' SE HE. unfold sync. introv Star.
    specialize (RG EK_return retVal x x' ge e1 e1' te1 te1' m1 m1').
    unfold VST_post_to_state_pred in RG.
    spec RG. {
      eapply VST_to_state_pred_commutes_imp; [ | eapply Sat ].
      apply andp_left2. apply derives_refl.
    }
    spec RG. {
      eapply VST_to_state_pred_commutes_imp; [ | eapply Sat' ].
      apply andp_left2. apply derives_refl.
    }
    specialize (RG SE HE).
    unfold sync in RG.
    specialize (RG s2 m2 n).
    spec RG. { Fail apply Star. (* TODO need the other direction as well *) }
    destruct RG as [s2' [m2' [Star' CE]]].
    exists s2' m2'. refine (conj _ CE).
    destruct n as [|n].
    + inversion Star. subst s2 m2. inversion Star'. subst s2' m2'. simpl.
      simpl in CE. (* destruct retVal; destruct (call_cont k'); try inversion CE. *) admit.
    + simpl. cbn - [exit_cont] in Star'.
      destruct Star' as [s11' [m11' [Step' Star']]].
      exists s11' m11'.
      refine (conj _ Star').
      eapply return_step_equiv; [ | | eapply Step' ].
      (* TODO invert Star to Step and Star, and transport from first execution to second *)
      admit. admit.
Grab Existential Variables.
(* TODO once we have filled all the gaps, these should be determined. *)
Admitted.

Lemma ifc_pre{T: Type}: forall Delta P1 P1' N1 N1' A1 A1' c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, ENTAIL Delta, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
  ifc_def T Delta P1' N1' A1' c P2 N2 A2 ->
  ifc_def T Delta P1  N1  A1  c P2 N2 A2.
Proof.
  introv E Imp H.
  split_ifc_hyps. split.
  - intro. apply canon.semax_pre with (P' := P1' x); auto.
  - unfold ifc_core, simple_ifc in *.
    introv RG.
    eapply weaken_iguard.
    + exact E.
    + exact Imp.
    + apply Hi. apply RG.
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

Lemma eval_expr_equiv: forall Delta P Q R v0 e2 ge e1 te1 m1 v,
  VST_to_state_pred (|> PROPx P (LOCALx Q (SEPx R))) e1 te1 m1 ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
      |-- local (` (eq v0) (eval_expr e2)) ->
  Clight.eval_expr ge e1 te1 m1 e2 v ->
  v0 = v.
Admitted. (* TODO what about "|>"? *)

Lemma update_state_and_Q: forall P Q R e1 te1 m1 v id,
  VST_to_state_pred (|> PROPx P (LOCALx Q (SEPx R))) e1 te1 m1 ->
  VST_to_state_pred
    (PROPx P (LOCALx (temp id v :: remove_localdef_temp id Q) (SEPx R)))
    e1 (PTree.set id v te1) m1.
Admitted. (* TODO does not hold with "|>" in hypothesis but not in conclusion *)

Lemma transport_eval_expr: forall {T: Type}
  (P : T -> list Prop)
  (Q : T -> list localdef)
  (R : T -> list mpred)
  (N : T -> stack_clsf)
  (A : T -> heap_clsf)
  x x' ge e1 te1 k1 m1 e1' te1' k1' m1' E v0,
  VST_to_state_pred (|> PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) e1 te1 m1 ->
  VST_to_state_pred (|> PROPx (P x') (LOCALx (Q x') (SEPx (R x')))) e1' te1' m1' ->
  stack_lo_equiv (State e1 te1 k1) (State e1' te1' k1') (N x) (N x') ->
  heap_lo_equiv m1 m1' (A x) (A x') ->
  Clight.eval_expr ge e1 te1 m1 E (v0 x) ->
  Clight.eval_expr ge e1' te1' m1' E (v0 x').
Admitted. (* TODO what about "|>"? *)

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
    introv RG. unfold iguard. introv Sat Sat' SE HE.
    unfold sync. introv Star.
    destruct n as [|n]; simpl in Star.
    + inversion Star. subst s2 m2. simpl. do 2 eexists. apply (conj eq_refl). reflexivity.
    + destruct Star as [s11 [m11 [Step Star]]].
      inversion Step. subst m11 s11. subst.
      rename H7 into Ev.
      assert (v0 x = v) as Eqv. {
        eapply eval_expr_equiv. eapply Sat. eapply Ev0. apply Ev.
      }
      unfold irguard in RG.
      specialize (RG EK_normal None). unfold iguard in RG.
      unfold VST_post_to_state_pred, normal_ret_assert, sync, exit_cont in RG.
      specialize (RG x x' ge e1 e1' (PTree.set id (v0 x) te1) (PTree.set id (v0 x') te1') m1 m1').
      spec RG. {
        rewrite VST_to_state_pred_and. split.
        - rewrite VST_indep_state_pred. reflexivity.
        - rewrite VST_to_state_pred_and. split.
          + rewrite VST_indep_state_pred. reflexivity.
          + apply update_state_and_Q. apply Sat.
      }
      spec RG. {
        rewrite VST_to_state_pred_and. split.
        - rewrite VST_indep_state_pred. reflexivity.
        - rewrite VST_to_state_pred_and. split.
          + rewrite VST_indep_state_pred. reflexivity.
          + apply update_state_and_Q. apply Sat'.
      }
      spec RG. {
        unfold normalPostClsf. simpl.
        (* TODO that's the actual IFC part *)
        admit.
      }
      specialize (RG HE).
      rewrite <- Eqv in Star.
      specialize (RG _ _ _ Star).
      destruct RG as [s2' [m2' [Star' CE]]].
      exists s2' m2'. refine (conj _ CE).
      simpl. do 2 eexists. refine (conj _ Star').
      apply step_set.
      rewrite <- Eqv in Ev.
      eapply transport_eval_expr. apply Sat. apply Sat'. apply SE. apply HE. apply Ev.
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

