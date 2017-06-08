Require Import ifc.simple_vst_store_lemmas.
Require Import ifc.proofauto.
Require Import ifc.canon_lift_notation.
Require Import examples.write_labeled_val.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition body: statement := ltac:(let r := eval simpl in f_write_labeled_val.(fn_body) in exact r).

(* alternative: give an explicit constructor name
Record MyMetaVars: Type := mkMyMetaVars { v: int; b: int; highptr: val; lowptr: val }.
Check (mkMyMetaVars Int.zero Int.zero Vundef Vundef).
*)

(* simpler: no constructor name, and use {| ... |} to construct record *)
Record MyMetaVars: Type := { v: int; b: int; highptr: val; lowptr: val }.
(* Check {| v := Int.zero; b := Int.zero; highptr := Vundef; lowptr := Vundef |}. *)

Set Printing Projections. (* to get x.(b) instead of (b x) in output *)

(* to get "_ =? _" notation on ident without having to write (_ =? _)%positive *)
Local Open Scope positive.
(* to avoid silly simpl *)
Arguments Pos.eqb: simpl never. 

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
    (fun (x: MyMetaVars) (i: ident) =>
          if i =? _v then (if Int.eq x.(b) Int.zero then Lo else Hi)
     else if i =? _b then Lo
     else if i =? _highptr then Hi
     else if i =? _lowptr then Lo
     else Hi
    );
  ifc_heap_pre :=
    (fun (x: MyMetaVars) (loc: heap_loc) =>
          if heap_loc_eq_val loc x.(lowptr) then Lo
     else if heap_loc_eq_val loc x.(highptr) then Hi
     else Hi);
  ifc_stack_post :=
    (fun (x: MyMetaVars) (ek: exitkind) (vl: option val) (i: ident) => Hi);
  ifc_heap_post :=
    (fun (x: MyMetaVars) (ek: exitkind) (vl: option val) (loc: heap_loc) =>
          if heap_loc_eq_val loc x.(lowptr) then Lo
     else if heap_loc_eq_val loc x.(highptr) then Hi
     else Hi)
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
  | |- ifc_def _ _ (fun (x: ?T) => (?A * emp)%logic) _ _ _ _ _ _ =>
       (* note: we also have to include mention x, because A depends on x *)
       replace (fun (x: T) => (A * emp)%logic)
          with (fun (x: T) => A)
            by (extensionality; symmetry; apply sepcon_emp)
  end.

  match goal with
  | |- ifc_def _ _ (fun (x: ?T) => PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ _ _ _ _ =>
       change (fun (x : T) => PROPx P (LOCALx Q (SEPx R)))
         with (lft2 PROPx (fun (x : T) => P)
               (lft2 LOCALx (fun (x: T) => Q)
                (lft1 SEPx (fun (x: T) => R))))
  end.

  repeat (match goal with
  | |- context [ fun (x: ?T) => ?f (@?h x) (@?t x) ] =>
     assert (E: (fun (x: T) => f (h x) (t x)) = (lft2 f h t)) by reflexivity
  end; simpl in E; rewrite E; clear E).

  repeat match goal with
  | |- context [ fun (x: ?T) => ?b ] => change (fun (x: T) => b) with (@lft0 T _ b)
  end.

  repeat match goal with
  | |- context [ fun (x: ?T) => ?f x ] => change (fun (x: T) => f x) with f
  end.

  match goal with
  | |- context [ fun (x: ?T) => ?f (@?h x) ] =>
     assert (E: (fun (x: T) => f (h x)) = (lft1 f h)) by reflexivity
  end. simpl in E. (* rewrite E. anomaly *) clear E.

  change (
ifc_def MyMetaVars Delta (lft2 PROPx
       (lft2 cons
          (lft2 or (lft2 eq b (lft0 Int.zero)) (lft2 eq b (lft0 Int.one)))
          (lft0 []))
       (lft2 LOCALx
          (lft2 cons (lft2 temp (lft0 _v) (lft1 Vint (fun x : MyMetaVars => x.(v))))
             (lft2 cons
                (lft2 temp (lft0 _b) (lft1 Vint (fun x : MyMetaVars => x.(b))))
                (lft2 cons (lft2 temp (lft0 _highptr) highptr)
                   (lft2 cons (lft2 temp (lft0 _lowptr) lowptr) (lft0 [])))))
          (lft1 SEPx
             (lft2 cons (lft2 (data_at_ Ews) (lft0 tint) highptr)
                (lft2 cons (lft2 (data_at_ Ews) (lft0 tint) lowptr) (lft0 []))))))
(fun (x : MyMetaVars) (i : ident) =>
   if i =? _v
   then if Int.eq x.(b) Int.zero then Lo else Hi
   else
    if i =? _b
    then Lo
    else
     if i =? _highptr
     then Hi
     else if i =? _lowptr then Lo else Hi)
  (fun (x : MyMetaVars) (loc : heap_loc) =>
   if heap_loc_eq_val loc x.(lowptr)
   then Lo
   else
    if heap_loc_eq_val loc x.(highptr)
    then Hi
    else Hi)
  (Ssequence
     (Sifthenelse (Etempvar _b tbool)
        (Sassign (Ederef (Etempvar _highptr (tptr tint)) tint)
           (Etempvar _v tint))
        (Sassign (Ederef (Etempvar _lowptr (tptr tint)) tint)
           (Etempvar _v tint))) (Sreturn None))
  (fun x : MyMetaVars =>
   frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP ( )
         LOCAL ()
         SEP (data_at Ews tint
                (if Int.eq x.(b) Int.zero
                 then Vundef
                 else Vint x.(v)) x.(highptr);
         data_at Ews tint
           (if Int.eq x.(b) Int.zero
            then Vint x.(v)
            else Vundef) x.(lowptr))))
     (LiftSepLog' mpred).(@emp (environ -> mpred) (LiftNatDed' mpred)))
  (lft0 (lft0 (lft0 (lft0 Hi))))
  (fun (x : MyMetaVars) (_ : exitkind) (_ : option val) (loc : heap_loc) =>
   if heap_loc_eq_val loc x.(lowptr)
   then Lo
   else
    if heap_loc_eq_val loc x.(highptr)
    then Hi
    else Hi)).

  repeat match goal with
  | |- context [ fun (x: ?T) => ?f x ] => change (fun (x: T) => f x) with f
  end.

  (* Look at goal here: It is in (iPROP ... iLOCAL ... iSEP ...) form *)

  evar (newN: MyMetaVars -> stack_clsf).
  eapply ifc_seq' with
    (P2 := fun x => (PROP (x.(b) = Int.zero \/ x.(b) = Int.one)
     LOCAL (temp _v (Vint x.(v)); temp _b (Vint x.(b));
     temp _highptr x.(highptr); temp _lowptr x.(lowptr))
     SEP (
       (* "interesting" join condition to be provided manually: *)
       data_at Ews tint (if Int.eq x.(b) Int.zero then Vundef else Vint x.(v)) x.(highptr);
       data_at Ews tint (if Int.eq x.(b) Int.zero then Vint x.(v) else Vundef) x.(lowptr))
     ))
    (N2 := newN)
    (A2 := (fun (x: MyMetaVars) (loc: heap_loc) =>
          if heap_loc_eq_val loc x.(lowptr) then Lo
     else if heap_loc_eq_val loc x.(highptr) then Hi
     else Hi)); subst newN.
  {
  (* Note: even though the precondition is not explicitly written in the form
     "fun x: MyMetaVars => PROP (P x) LOCAL (Q x) SEP (R x)", where P, Q, R are functions, but
     rather in the form "fun x: MyMetaVars => PROP P LOCAL Q SEP R", where P, Q, R are terms in which
     x is a free variable, we still can apply ifc_ifthenelse_PQR, which expects a goal in the first
     form, because Coq's unification algorithm is strong enough to match this. *)
  eapply ifc_ifthenelse_PQR; try reflexivity; unfold lft0, lft2.
  - (* prove we're not branching on high data *)
    intro. entailer!.
    (* Note: entailer! simplified clsf_expr and the classification function automatically *)
  - (* typechecking the condition *)
    intro. entailer!.
  - (* evaluating the condition *)
    intro. entailer. (* NOTE floyd: entailer! produces a false goal here, so we have to use entailer *)
  - (* then-branch *)
    apply ifc_later_trivial.
    rewrite -> ifc_seq_skip. eapply ifc_seq'. {
        eapply ifc_store with (n := 0%nat); try reflexivity; try intro x.
      + entailer!.
      + entailer.
      + apply JMeq_refl.
      + auto.
      + entailer!.
      + assert_PROP (isptr x.(highptr)) as IP. { entailer!. }
        destruct x.(highptr); try contradiction. clear IP.
        (* TODO floyd: the two lines above would not be necessary if entailer! gave me
           isptr instead of only is_pointer_or_null. *)
        entailer!.
    } {
      simpl update_tycon. simpl. unfold lft1.
      eapply ifc_pre; [ | | eapply ifc_skip ].
      - intro. entailer!.
        destruct H0.
        + exfalso. apply H. apply H0.
        + rewrite H0. simpl. cancel.
      - intro. assert_PROP (x.(highptr) <> x.(lowptr)) as NA by entailer!.
        entailer!.
        split.
        + apply lle_refl.
        + apply lle_pointwise. intro loc. clear H H0.
          destruct (heap_loc_eq_val loc x.(highptr)) eqn: E.
          * destruct (heap_loc_eq_val loc x.(lowptr)) eqn: E2.
            { exfalso. apply NA. apply* heap_loc_eq_val_trans. }
            { apply lle_refl. }
          * apply lle_refl.
  }
  - (* else-branch *)
    apply ifc_later_trivial.
    rewrite -> ifc_seq_skip. eapply ifc_seq'. {
        eapply ifc_store with (n := 1%nat); try reflexivity; try intro x.
      + entailer!.
      + entailer.
      + apply JMeq_refl.
      + auto.
      + entailer!.
      + assert_PROP (isptr x.(lowptr)) as IP. { entailer!. }
        destruct x.(lowptr); try contradiction. clear IP.
        (* TODO floyd: the two lines above would not be necessary if entailer! gave me
           isptr instead of only is_pointer_or_null. *)
        entailer!.
    } {
      simpl update_tycon. simpl. unfold lft1.
      eapply ifc_pre; [ | | eapply ifc_skip ].
      - intro. destruct (Int.eq x.(b) Int.zero) eqn: E.
        + rewrite E. entailer!.
        + Intros. rewrite H in E. rewrite Int.eq_true in E. discriminate.
      - intro. Intros. clear H0. entailer!. split.
        + apply lle_refl.
        + apply lle_pointwise. intro loc. rewrite H. simpl.
          destruct (heap_loc_eq_val loc x.(lowptr)) eqn: E; apply lle_refl.
  } } {
  eapply ifc_pre; [ | | eapply ifc_return with (retVal := None) ].
  - intro. entailer!.
  - intro. apply prop_right. split.
    + unfold_lft.
      progress change (fun _ : ident => Hi)
      with (@top (ident -> lattice.label) (@LiftLattice ident lattice.label LoHi)).
      apply lle_top.
    + apply lle_refl.
  - reflexivity.
  }
Qed.
