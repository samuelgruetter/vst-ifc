Require Import floyd.base.
Require Import floyd.canon.
Require Import floyd.client_lemmas.
Require Import ifc.ifc_def.
Require Import ifc.canon_lift_notation.
Require Import ifc.notation.
Require Import lib.LibTactics.

Local Open Scope logic.

Section fwd_lemmas.
Context (Espec : OracleKind).
Context {CS: compspecs}.

Require Import floyd.nested_field_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.


Instance iLiftNatDed' T A {ND: NatDed T}: NatDed (Tend A T) := LiftNatDed _ _.

Lemma ifc_load_lifted{T: Type}: 
  forall Delta P Q R (N: T -> stack_clsf) (A: T -> heap_clsf) sh n id e
  (t t_root: type) (gfs0 gfs1 gfs: T -> list gfield) (l1 l2: T -> label)
  (p q: T -> val) (v : T -> val)
  (* dependent types FTW: *)
  (v' : forall (x: T), reptype (nested_field_type t_root (gfs0 x))),
  (* VST preconditions: *)
  typeof_temp Delta id = Some t ->
  is_neutral_cast (typeof e) t = true ->
  type_is_volatile (typeof e) = false ->

  (* this is a lifted "derives" over (x: T), note that no "forall x" is needed because that's
     defined by the field "derives" of "LiftNatDed" *)
  (lft0 (local (tc_environ Delta))) &&
  (lft2 PROPx P (lft2 LOCALx Q (lft1 SEPx R)))
  |-- (lft1 local (fun x: T => (`( eq (q x)) (eval_lvalue e)))) ->

  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     !! ((q x) = field_address t_root (gfs x) (p x))) ->
  (forall x, typeof e = nested_field_type t_root (gfs x)) ->
  (forall x, (gfs x) = (gfs1 x) ++ (gfs0 x)) ->
  (forall x, nth_error (R x) n = Some (field_at sh t_root (gfs0 x) (v' x) (p x))) ->
  readable_share sh ->
  (forall x, JMeq (proj_reptype (nested_field_type t_root (gfs0 x)) (gfs1 x) (v' x)) (v x)) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
    (tc_lvalue Delta e) &&
    local `(tc_val (typeof e) (v x))) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
    (!! legal_nested_field t_root (gfs x))) ->
  (* IFC preconditions: *)
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 !! (clsf_lvalue (N x) e = Some (l1 x) /\
                    (forall bl ofs, (q x) = Vptr bl ofs -> A x (bl, ofs) = (l2 x)))) ->
  ifc_def T Delta
    (fun x => (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x)))))
    N
    A
    (Sset id e)
    (fun x => (normal_ret_assert (PROPx (P x) 
                                 (LOCALx (temp id (v x) :: remove_localdef_temp id (Q x))
                                 (SEPx (R x))))))
    (normalPostClsf (fun x id0 =>
           if Pos.eqb id0 id then lub (l1 x) (l2 x) else N x id0))
    (normalPostClsf A).
Proof.
exact ifc_load.
(*
unfold_lft.
introv H1 H2 H3 HH.
apply (ifc_load _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 HH).
*)

(*
(iLiftNatDed' mpred int)
(LiftNatDed' mpred)

(@LiftNatDed' mpred Nveric)


Instance LiftNatDed' T {ND: NatDed T}: NatDed (Tend environ T) := LiftNatDed _ _.

Instance LiftNatDed' T {ND: NatDed T}: NatDed (LiftEnviron T) := LiftNatDed _ _.

(@LiftNatDed' mpred Nveric)
*)
Qed.

Lemma isequential'{T: Type}:
  forall R RN RA Delta P N A c P' N' A',
    ifc_def T Delta P N A c (lft1 normal_ret_assert P') (normalPostClsf N') (normalPostClsf A') ->
    ifc_def T Delta P N A c (lft2 overridePost P' R) (overridePostClsf N' RN) (overridePostClsf A' RA).
Proof.
(*
  intros. unfold ifc_def. unfold ioverridePost. unfold inormal_ret_assert in *.
  split_ifc_hyps. split.
  - intro. apply canon.sequential'. apply Hs.
  - unfold ifc_core, simple_ifc in *. unfold overridePostClsf in *.
    (* TODO use VST to conclude that it's EK_normal and use this to simplify the goal *)
*)
Admitted.

Lemma ifc_seq'{T: Type}:
 forall Delta P1 N1 A1 c1 P2 N2 A2 c2 P3 N3 A3,
   ifc_def T Delta P1 N1 A1 c1 (lft1 normal_ret_assert P2) (normalPostClsf N2) (normalPostClsf A2) ->
   ifc_def T (update_tycon Delta c1) P2 N2 A2 c2 P3 N3 A3 ->
   ifc_def T Delta P1 N1 A1 (Ssequence c1 c2) P3 N3 A3.
Proof.
  intros. apply ifc_seq with P2 N2 A2; try assumption. apply isequential'. assumption.
Qed.

(* only changes P1, but not N1 and A1 *)
Lemma ifc_pre0{T: Type}: forall Delta P1 P1' N1 A1 c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  ifc_def T Delta P1' N1 A1 c P2 N2 A2 ->
  ifc_def T Delta P1  N1 A1 c P2 N2 A2.
Proof.
  introv Imp H. eapply ifc_pre; try eassumption.
  intro. apply prop_right. split; apply lle_refl.
Qed.

Lemma ifc_ifthenelse_PQR{T: Type}:
  forall (v: T -> val) Delta P Q R (b: expr) c d Post N A N' A',
    bool_type (typeof b) = true ->
    (forall x: T, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                     !! (clsf_expr (N x) b = Some Lo)) ->
    (forall x: T, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |-- 
                    (tc_expr Delta (Eunop Cop.Onotbool b tint)))  ->
    (forall x: T, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                    local (`(eq (v x)) (eval_expr b))) ->
    ifc [x: T] Delta |-- (PROPx (typed_true (typeof b) (v x) :: (P x)) (LOCALx (Q x) (SEPx (R x))))
                         (N x) (A x) c (Post x) (N' x) (A' x) ->
    ifc [x: T] Delta |-- (PROPx (typed_false (typeof b) (v x) :: (P x)) (LOCALx (Q x) (SEPx (R x))))
                         (N x) (A x) d (Post x) (N' x) (A' x) ->
    ifc [x: T] Delta |-- (PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) (N x) (A x)
                         (Sifthenelse b c d) (Post x) (N' x) (A' x).
Proof.
  introv Eq Cl Tc Ev B1 B2.
  eapply ifc_pre0; [ | apply ifc_ifthenelse ]; unfold lft0, lft2; try assumption.
  - intro. apply andp_right.
    + apply Tc.
    + apply andp_left2. apply derives_refl.
  - apply Cl.
  - unfold pre_assert in *. (* <- in implicit arguments *) remember (fun x : T =>
      andp ((fun x0 : T => PROPx (P x0) (LOCALx (Q x0) (SEPx (R x0)))) x)
       (local (liftx (typed_true (typeof b)) (eval_expr b)))) as f.
    replace f
    with (fun x : T =>
      PROPx (typed_true (typeof b) (v x) :: P x) (LOCALx (Q x) (SEPx (R x)))).
    + exact B1.
    + subst f. extensionality. admit. (* from Ev and rewriting *)
  - unfold pre_assert in *. (* <- in implicit arguments *) remember (fun x : T =>
      andp ((fun x0 : T => PROPx (P x0) (LOCALx (Q x0) (SEPx (R x0)))) x)
       (local (liftx (typed_false (typeof b)) (eval_expr b)))) as f.
    replace f
    with (fun x : T =>
      PROPx (typed_false (typeof b) (v x) :: P x) (LOCALx (Q x) (SEPx (R x)))).
    + exact B2.
    + subst f. extensionality. admit. (* from Ev and rewriting *)
Qed.

Lemma ifc_later_trivial{T: Type}:
  forall Delta P N A c P' N' A',
  ifc_def T Delta (fun x => (|> (P x))) N A c P' N' A' ->
  ifc_def T Delta                P      N A c P' N' A'.
Proof.
  intros. apply ifc_pre0 with (P1' := (fun x => (|> (P x)))); [ | assumption ].
  intro. apply andp_left2. apply now_later.
Qed.

End fwd_lemmas.
