Require Import ifc.rules.
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

(* alternative: give an explicit constructor name
Record MyMetaVars: Type := mkMyMetaVars { v: int; b: int; highptr: val; lowptr: val }.
Check (mkMyMetaVars Int.zero Int.zero Vundef Vundef).
*)

(* simpler: no constructor name, and use {| ... |} to construct record *)
Record MyMetaVars: Type := { v: int; b: int; highptr: val; lowptr: val }.
(* Check {| v := Int.zero; b := Int.zero; highptr := Vundef; lowptr := Vundef |}. *)

Set Printing Projections. (* to get x.(b) instead of (b x) in output *)

Definition write_labeled_val_spec: ifc_funspec := {|
  functional_spec :=
    DECLARE _write_labeled_val
    WITH x: MyMetaVars
    PRE [ _v OF tint, _b OF tbool, _highptr OF (tptr tint), _lowptr OF (tptr tint) ]
     (PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
      LOCAL (
        temp _v (Vint x.(v)); temp _b (Vint x.(b)); temp _highptr x.(highptr); temp _lowptr x.(lowptr)
      )
      SEP (data_at_ Ews tint x.(highptr); data_at_ Ews tint x.(lowptr)))
    POST [ tvoid ]
      (PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
       LOCAL (
         temp _v (Vint x.(v)); temp _b (Vint x.(b)); temp _highptr x.(highptr); temp _lowptr x.(lowptr)
       )
       SEP (data_at_ Ews tint x.(highptr); data_at_ Ews tint x.(lowptr)));
  ifc_stack_pre :=
    (fun (x: MyMetaVars) (i: ident) => PMap.get i 
      (PMap.set _v (if Int.eq x.(b) Int.zero then Lo else Hi)
      (PMap.set _b Lo
      (PMap.set _highptr Hi
      (PMap.set _lowptr Lo
      (PMap.init Hi))))));
  ifc_heap_pre :=
    (fun (x: MyMetaVars) (loc: heap_loc) => Hi);
  ifc_stack_post :=
    (fun (x: MyMetaVars) (i: ident) => Hi);
  ifc_heap_post :=
    (fun (x: MyMetaVars) (loc: heap_loc) => Hi)
|}.

Definition Gprog: funspecs := [].

Lemma verif_write_labeled_val:
  ifc_body Vprog Gprog f_write_labeled_val write_labeled_val_spec.
Proof.
  unfold write_labeled_val_spec. hnf. intros. clear ts.
  simpl (fn_body _).
  (* TODO rule for Ssequence *)
  replace (Ssequence
   (Sifthenelse (Etempvar _b tbool)
      (Sassign (Ederef (Etempvar _highptr (tptr tint)) tint)
         (Etempvar _v tint))
      (Sassign (Ederef (Etempvar _lowptr (tptr tint)) tint)
         (Etempvar _v tint))) (Sreturn None))
  with (Sifthenelse (Etempvar _b tbool)
      (Sassign (Ederef (Etempvar _highptr (tptr tint)) tint)
         (Etempvar _v tint))
      (Sassign (Ederef (Etempvar _lowptr (tptr tint)) tint)
         (Etempvar _v tint))) by admit.
  apply ifc_ifthenelse; try reflexivity; unfold iand, iprop.
  - (* then-branch *)
    unfold ifc_def. split.
    + (* VST part *)
      intros. destruct x as [v b highptr lowptr] eqn: E.
      match goal with
      | _ : x = ?m |- _ => simpl (_ m)
      end. clear E.
      simplify_func_tycontext. abbreviate_semax.
      (* forward. still fails *)
      admit.
    + (* IFC part *)
      apply ifc_core0_always_holds.
  - (* else-branch *)
    admit.
Admitted.

Lemma verif_write_labeled_val_body_only:
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
