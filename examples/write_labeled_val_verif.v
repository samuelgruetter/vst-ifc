Require Import ifc.simple_vst_store_lemmas.
Require Import ifc.proofauto.
Require Import examples.write_labeled_val.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition body: statement := ltac:(let r := eval simpl in f_write_labeled_val.(fn_body) in exact r).

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
      (PROP () LOCAL () SEP (
         data_at Ews tint (if Int.eq x.(b) Int.zero then Vundef else Vint x.(v)) x.(highptr);
         data_at Ews tint (if Int.eq x.(b) Int.zero then Vint x.(v) else Vundef) x.(lowptr)
       ));
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

Lemma verif_write_labeled_val_VST:
  semax_body Vprog Gprog f_write_labeled_val write_labeled_val_spec.(functional_spec).
Proof.
  start_function.
  unfold POSTCONDITION, abbreviate.
Abort.

Lemma verif_write_labeled_val:
  ifc_body Vprog Gprog f_write_labeled_val write_labeled_val_spec.
Proof.
  istart_function.

  (* setoid_rewrite <- lower_sepcon. setoid_rewrite instead of just rewrite is supposed to work under
     binders, but it takes forever *)
  match goal with
  | |- ifc_def _ _ (fun (x: ?T) (rho: ?E) => sepcon (?A ?R) (?B ?R)) _ _ _ _ _ _ =>
       replace (fun (x: T) (rho: E) => sepcon (A R) (B R))
          with (fun (x: T) (rho: E) => (sepcon A B) R)
            by (do 2 extensionality; apply lower_sepcon)
  end.

  match goal with
  | |- ifc_def _ _ (fun (x: ?T) (rho: ?E) => ?A rho) _ _ _ _ _ _ =>
       (* note: we also have to include mention x, because A depends on x *)
       replace (fun (x: T) (rho: E) => A rho)
          with (fun (x: T) => A)
            by (extensionality; reflexivity)
  end.

  match goal with
  | |- ifc_def _ _ (fun (x: ?T) => ?A * emp) _ _ _ _ _ _ =>
       (* note: we also have to include mention x, because A depends on x *)
       replace (fun (x: T) => A * emp)
          with (fun (x: T) => A)
            by (extensionality; symmetry; apply sepcon_emp)
  end.

  eapply ifc_seq' with
    (P2 := fun x => (PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
     LOCAL (temp _v (Vint x.(v)); temp _b (Vint x.(b));
     temp _highptr x.(highptr); temp _lowptr x.(lowptr))
     SEP (
       (* "interesting" join condition to be provided manually: *)
       data_at Ews tint (if Int.eq x.(b) Int.zero then Vundef else Vint x.(v)) x.(highptr);
       data_at Ews tint (if Int.eq x.(b) Int.zero then Vint x.(v) else Vundef) x.(lowptr))
     ))
    (N2 := fun x => (fun i : ident =>
            (PMap.set _v (if Int.eq x.(b) Int.zero then Lo else Hi)
            (PMap.set _b Lo
            (PMap.set _highptr Hi (PMap.set _lowptr Lo (PMap.init Hi))))) !! i))
    (A2 := fun x => (fun _ : heap_loc => Hi)).
  {
  (* Note: even though the precondition is not explicitly written in the form
     "fun x: MyMetaVars => PROP (P x) LOCAL (Q x) SEP (R x)", where P, Q, R are functions, but
     rather in the form "fun x: MyMetaVars => PROP P LOCAL Q SEP R", where P, Q, R are terms in which
     x is a free variable, we still can apply ifc_ifthenelse_PQR, which expects a goal in the first
     form, because Coq's unification algorithm is strong enough to match this. *)
  eapply ifc_ifthenelse_PQR; try reflexivity; unfold iand, iprop.
  - (* typechecking the condition *)
    intro. entailer!.
  - (* evaluating the condition *)
    intro. entailer. (* NOTE floyd: entailer! produces a false goal here, so we have to use entailer *)
  - (* then-branch *)
    unfold ifc_def. split.
    + (* VST part *)
      start_VST.
      Intros. destruct H0; try contradiction. subst b0.
      (* NOTE: this is the unmodified "forward" of VST! *)
      forward.
      entailer!.
    + (* IFC part *)
      apply ifc_core0_always_holds.
  - (* else-branch *)
    unfold ifc_def. split.
    + (* VST part *)
      start_VST.
      Intros. clear H0. subst b0.
      (* test: apply a simpler store lemma, semax_SC_field_store_without_paths, manually *)
      rewrite -> semax_seq_skip.
      eapply semax_seq'. {
        hoist_later_in_pre.
        eapply semax_SC_field_store_without_paths with (n := 1%nat);
          auto; try reflexivity; auto; entailer!.
      }
      fwd_result. fwd_skip. entailer!.
      (* end of test, and it was only 7 lines *)
    + (* IFC part *)
      apply ifc_core0_always_holds.
  } {
  unfold ifc_def. split.
  + (* VST part *)
    intros. forward.
  + (* IFC part *)
    apply ifc_core0_always_holds.
  }
Qed.
