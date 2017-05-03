Require Import ifc.ifc.
Require Import floyd.proofauto.
Require Import examples.write_labeled_val.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition body: statement := ltac:(let r := eval simpl in f_write_labeled_val.(fn_body) in exact r).

Parameter Delta: tycontext.

Instance Espec: OracleKind. Admitted.

Axiom ifc_core0_always_holds: forall {T: Type} Delta P N A c P' N' A',
  @ifc_core T Delta P N A c P' N' A'.

(* We need lifting on top of VST's lifting... *)

Definition iand{A: Type}(P1: A -> pre_assert)(P2: A -> pre_assert): A -> pre_assert :=
  fun (x: A) => (P1 x) && (P2 x).

Definition iprop{A: Type}(P: pre_assert): A -> pre_assert := fun (_: A) => P.

Lemma ifc_ifthenelse: forall {T: Type} {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> stack_clsf) (A': T -> heap_clsf),
  bool_type (typeof b) = true ->
  ifc_def Delta (iand P (iprop (local (`(typed_true  (typeof b)) (eval_expr b))))) N A c1 P' N' A' ->
  ifc_def Delta (iand P (iprop (local (`(typed_false (typeof b)) (eval_expr b))))) N A c2 P' N' A' ->
  ifc_def Delta P N A (Sifthenelse b c1 c2) P' N' A'.
Admitted.

(* alternative: give an explicit constructor name
Record MyMetaVars: Type := mkMyMetaVars { v: int; b: int; highptr: val; lowptr: val }.
Check (mkMyMetaVars Int.zero Int.zero Vundef Vundef).
*)

(* simpler: no constructor name, and use {| ... |} to construct record *)
Record MyMetaVars: Type := { v: int; b: int; highptr: val; lowptr: val }.
(* Check {| v := Int.zero; b := Int.zero; highptr := Vundef; lowptr := Vundef |}. *)

Set Printing Projections. (* to get x.(b) instead of (b x) in output *)

Lemma verif_write_labeled_val:
  ifc [x: MyMetaVars] Delta |--
   (PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
    LOCAL (
      temp _v (Vint x.(v)); temp _b (Vint x.(b)); temp _highptr x.(highptr); temp _lowptr x.(lowptr)
    )
    SEP (data_at_ Ews tint x.(highptr); data_at_ Ews tint x.(lowptr)))
   (fun i => PMap.get i 
      (PMap.set _v (if Int.eq x.(b) Int.zero then Lo else Hi)
      (PMap.set _b Lo
      (PMap.set _highptr Hi
      (PMap.set _lowptr Lo
      (PMap.init Hi))))))
   (fun loc => Hi)
   body
   (normal_ret_assert (
    PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
    LOCAL (
      temp _v (Vint x.(v)); temp _b (Vint x.(b)); temp _highptr x.(highptr); temp _lowptr x.(lowptr)
    )
    SEP (data_at_ Ews tint x.(highptr); data_at_ Ews tint x.(lowptr))))
   (fun i => Hi)
   (fun loc => Hi).
Proof.
  unfold body. apply ifc_ifthenelse; try reflexivity; unfold iand, iprop.
  - (* then-branch *)
    unfold ifc_def. split.
    + (* VST part *)
      intros. destruct x as [v b highptr lowptr] eqn: E.
      match goal with
      | _ : x = ?m |- _ => simpl (_ m)
      end. clear E.
      admit.
    + (* IFC part *)
      apply ifc_core0_always_holds.
  - (* else-branch *)
    admit.
Admitted.
