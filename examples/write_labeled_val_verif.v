Require Import floyd.proofauto.
Require Import examples.write_labeled_val.
Require Import ifc.ifc.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition body: statement := ltac:(let r := eval simpl in f_write_labeled_val.(fn_body) in exact r).

Parameter Delta: tycontext.

Instance Espec: OracleKind. Admitted.

Axiom ifc_core0_always_holds: forall {A: Type} Delta P c Q, @ifc_core0 A Delta P c Q.

(* We need lifting on top of VST's lifting... *)

Definition andProp{A: Type}(P1: A -> ifc_pre)(P2: pre_assert): A -> ifc_pre := fun (x: A) =>
  match (P1 x) with
  | (p, n, a) => (p && P2, n, a)
  end.

Lemma ifc_ifthenelse: forall {A: Type} {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (P: A -> ifc_pre) (b: expr) (c1 c2: statement) (Q: A -> ifc_post),
  bool_type (typeof b) = true ->
  ifc_def Delta (andProp P (local (`(typed_true (typeof b)) (eval_expr b)))) c1 Q ->
  ifc_def Delta (andProp P (local (`(typed_false (typeof b)) (eval_expr b)))) c2 Q ->
  ifc_def Delta P (Sifthenelse b c1 c2) Q.
Admitted.

Lemma verif_write_labeled_val:
  ifc [v: int, b: int, highptr: val, lowptr: val] Delta |-- (
    PROP (b = Int.zero \/ b = Int.one)
    LOCAL (temp _v (Vint v); temp _b (Vint b); temp _highptr highptr; temp _lowptr lowptr)
    SEP (data_at_ Ews tint highptr; data_at_ Ews tint lowptr),
    fun i => PMap.get i 
      (PMap.set _v (if Int.eq b Int.zero then Lo else Hi)
      (PMap.set _b Lo
      (PMap.set _highptr Hi
      (PMap.set _lowptr Lo
      (PMap.init Hi))))),
    fun loc => Hi
  ) body (normal_ret_assert (
    PROP (b = Int.zero \/ b = Int.one)
    LOCAL (temp _v (Vint v); temp _b (Vint b); temp _highptr highptr; temp _lowptr lowptr)
    SEP (data_at_ Ews tint highptr; data_at_ Ews tint lowptr)),
    fun i => Hi,
    fun loc => Hi
  ).
Proof.
  unfold body. apply ifc_ifthenelse; try reflexivity.
  - (* then-branch *)
    unfold ifc_def. split.
    + (* VST part *)
      intros. destruct x as [[[v b] highptr] lowptr].
      unfold semax0. simpl. admit.
    + (* IFC part *)
      apply ifc_core0_always_holds.
  - (* else-branch *)
    admit.
Admitted.
