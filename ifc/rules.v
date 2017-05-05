Require Import compcert.cfrontend.Clight.
Require Import veric.Clight_new.
Require Import compcert.lib.Maps. (* for PMap and ZMap *)
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import floyd.base.
Require Import ifc.ifc.
Require Import lib.LibTactics.

Local Open Scope logic.

Definition ioverridePost{A: Type}(Q: A -> environ -> mpred)(R : A -> ret_assert): A -> ret_assert :=
  fun (x: A) => (overridePost (Q x) (R x)).

Ltac split_ifc_hyps :=
  repeat match goal with
  | H: ifc_def _ _ _ _ _ _ _ _ |- _ =>
      let Hs := fresh H "s" in 
      let Hi := fresh H "i" in
      destruct H as [Hs Hi]
  end.

(* We need lifting on top of VST's lifting... *)

Definition iand{A: Type}(P1: A -> pre_assert)(P2: A -> pre_assert): A -> pre_assert :=
  fun (x: A) => (P1 x) && (P2 x).

Definition iprop{A: Type}(P: pre_assert): A -> pre_assert := fun (_: A) => P.

Section RULES.
Context (Espec : OracleKind).
Context (CS: compspecs).

Lemma ifc_seq{T: Type}:
  forall Delta (P1 P2: T -> environ -> mpred) (P3: T -> ret_assert) h t
    (N1 N2 N3: T -> stack_clsf) (A1 A2 A3: T -> heap_clsf),
  ifc_def Delta P1 N1 A1 h (ioverridePost P2 P3) N2 A2 ->
  ifc_def (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.
Proof.
  introv H1 H2. split_ifc_hyps. split.
  - intro. apply* semax_seq.
  - unfold ifc_core, simple_ifc in *.
    intros x x' ge e1 e1' te1 te1' s3 s3' m1 m3 m1' m3' n.
    intros Sat1 Sat1' SE1 HE1 Star1 Star1'.
    destruct n as [|n].
    + (* 0 steps *)
      inversion Star1. subst s s3 m m3.
      inversion Star1'. subst s s3' m m3'.
      specialize (H1i x x' ge e1 e1' te1 te1').
      specialize (H1i (State e1 te1 (Kseq h :: nil)) (State e1' te1' (Kseq h :: nil))).
(*
      specialize (H1i m1 m1 m1' m1' 0 Sat1 Sat1').
      specialize (H1i (stack_lo_equiv_change_cmd _ _ _ _ _ _ _ _ _ _ SE1) HE1).
      specialize (H1i (star_refl _ _ _) (star_refl _ _ _)).
      destruct H1i as [SE2 HE2].
      specialize (H2i x x' ge e1 e1' te1 te1').
      specialize (H2i (State e1 te1 (Kseq h :: nil)) (State e1' te1' (Kseq h :: nil))).
*)

(* star does not mean "execute until done", so execution can be anywhere inside h or t,
   which seems difficult to reason about!
   TODO first just define exec to go until empty cont list *)

Admitted.

Lemma ifc_ifthenelse: forall {T: Type} (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> stack_clsf) (A': T -> heap_clsf),
  bool_type (typeof b) = true ->
  ifc_def Delta (iand P (iprop (local (`(typed_true  (typeof b)) (eval_expr b))))) N A c1 P' N' A' ->
  ifc_def Delta (iand P (iprop (local (`(typed_false (typeof b)) (eval_expr b))))) N A c2 P' N' A' ->
  ifc_def Delta P N A (Sifthenelse b c1 c2) P' N' A'.
Admitted.

End RULES.
