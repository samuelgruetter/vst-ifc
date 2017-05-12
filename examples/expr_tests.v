Require Import floyd.proofauto.

(* from VST/progs/verif_load_demo.v: 
The expression "&pps[i].right" contains an Ederef, but still does not do any memory loads.
*)
Definition _int_pair := 4%positive.
Definition _pair_pair := 5%positive.
Definition _right := 6%positive.
Definition _i := 7%positive.
Definition _pps := 8%positive.
Definition test1: expr :=
         (Eaddrof
           (Efield
              (Ederef
                 (Ebinop Oadd
                    (Etempvar _pps (tptr (Tstruct _pair_pair noattr)))
                    (Etempvar _i tint) (tptr (Tstruct _pair_pair noattr)))
                 (Tstruct _pair_pair noattr)) _right
              (Tstruct _int_pair noattr)) (tptr (Tstruct _int_pair noattr))).

(* "pps[i].right" without the addrof: *)
Definition test2: expr :=
            Efield
              (Ederef
                 (Ebinop Oadd
                    (Etempvar _pps (tptr (Tstruct _pair_pair noattr)))
                    (Etempvar _i tint) (tptr (Tstruct _pair_pair noattr)))
                 (Tstruct _pair_pair noattr)) _right
              (Tstruct _int_pair noattr).

Goal forall e0, test1 = e0.
intro. unfold test1.
match goal with
| |- ?e = _ => no_loads_expr e false
end.
Abort.

Goal forall e0, test2 = e0.
intro. unfold test2.
Fail match goal with
| |- ?e = _ => no_loads_expr e false
end.
match goal with
| |- ?e = _ => no_loads_expr e true
end.
Abort.

(* Exercise: rewrite no_loads_expr from VST/floyd/forward.v from Ltac to Gallina: *)

Require Import ifc.clsf_expr.

Fixpoint no_loads_expr(e: expr)(as_lvalue: bool): bool := match e with
  | Econst_int _ _ => true
  | Econst_float _ _ => true
  | Econst_single _ _ => true
  | Econst_long _ _ => true
  (* var means global var, whose access is always handled like a heap access *)
  | Evar _ t => as_lvalue || is_array_type t
  (* tempvar means local var, whose access is handled like a stack access *)
  | Etempvar _ _ => true
  | Ederef e1 t => as_lvalue && no_loads_expr e1 true
  | Eaddrof e1 _ => no_loads_expr e1 true
  | Eunop _ e1 _ => no_loads_expr e1 as_lvalue
  | Ebinop _ e1 e2 _ => no_loads_expr e1 as_lvalue && no_loads_expr e2 as_lvalue
  | Ecast e1 _ => no_loads_expr e1 as_lvalue
  | Efield e1 _ t => (as_lvalue || is_array_type t) && no_loads_expr e1 true 
  | Esizeof _ _ => true
  | Ealignof _ _ => true
  end.

Goal no_loads_expr test1 false = true. reflexivity. Qed.
Goal no_loads_expr test2 false = false. reflexivity. Qed.
Goal no_loads_expr test2 true = true. reflexivity. Qed.

Lemma sanity_test: forall N e as_lvalue,
  clsf_expr N as_lvalue e = None <-> no_loads_expr e as_lvalue = false.
Proof.
  intros N e. induction e; intro; split; intro; simpl in *; 
  [ discriminate | discriminate | discriminate | discriminate |
    discriminate | discriminate | discriminate | discriminate | .. ].
  Ltac destr1 := match goal with
  | H: (if ?C then _ else _ ) = _ |- _ => let E := fresh "E" in destruct C eqn: E; try rewrite H
  | H: _ |- _ => apply andb_false_iff in H
  | H: _ |- _ => apply andb_true_iff in H
  | H: _ |- _ => apply orb_false_iff in H
  | H: _ |- _ => apply orb_true_iff in H
  end.
  (* Evar *)
  - destr1; congruence.
  - rewrite H. reflexivity.
  (* Etempvar *)
  - discriminate.
  - discriminate.
  (* Ederef *)
  - specialize (IHe as_lvalue). destruct IHe as [IH1 IH2]. apply andb_false_iff.
    destruct as_lvalue.
    + right. auto.
    + left. auto.
  - destr1. destruct H.
    + rewrite H. reflexivity.
    + destruct as_lvalue. 
      * edestruct IHe. auto.
      * reflexivity.
  (* Eaddrof *)
  - edestruct IHe; auto.
  - edestruct IHe; auto.
  (* Eunop *)
  - edestruct IHe; auto.
  - edestruct IHe; auto.
  (* Ebinop *)
  - apply andb_false_iff.
    destruct (clsf_expr N as_lvalue e1) eqn: E1;
    destruct (clsf_expr N as_lvalue e2) eqn: E2.
    + discriminate.
    + right. edestruct IHe2. eauto.
    + left. edestruct IHe1. eauto.
    + left. edestruct IHe1. eauto.
  - destr1.
    destruct (clsf_expr N as_lvalue e1) eqn: E1;
    destruct (clsf_expr N as_lvalue e2) eqn: E2;
    try reflexivity.
    destruct H.
    + destruct (IHe1 as_lvalue). specialize (H1 H). congruence.
    + destruct (IHe2 as_lvalue). specialize (H1 H). congruence.
  (* Ecast *)
  - destruct (IHe as_lvalue). auto.
  - destruct (IHe as_lvalue). auto.
  (* Efield *)
  - apply andb_false_iff. destr1.
    + right. edestruct IHe; eapply H0; assumption.
    + left. reflexivity.
  - destr1. destruct H; destruct (as_lvalue || is_array_type t)%bool eqn: E.
    + discriminate.
    + reflexivity.
    + edestruct IHe. eapply H1. assumption.
    + reflexivity.
  (* Esizeof *)
  - discriminate.
  - discriminate.
  (* Ealignof *)
  - discriminate.
  - discriminate.
Qed.
