Require Import floyd.base.
Require Import floyd.canon.
Require Import ifc.rules.
Require Import ifc.ifc.
Require Import lib.LibTactics.

Section fwd_lemmas.
Context (Espec : OracleKind).
Context (CS: compspecs).

Lemma isequential'{T: Type}:
  forall R Delta P N A c P' N' A',
    @ifc_def T CS Espec Delta P N A c (inormal_ret_assert P') N' A' ->
    @ifc_def T CS Espec Delta P N A c (ioverridePost P' R) N' A'.
Proof.
  intros. unfold ifc_def. unfold ioverridePost. unfold inormal_ret_assert in *.
  split_ifc_hyps. split.
  - intro. apply canon.sequential'. apply Hs.
  - unfold ifc_core, simple_ifc in *. assumption. (* note: ifc_core currently ignores postcondition *)
Qed.

Lemma ifc_seq'{T: Type}:
 forall Delta P1 N1 A1 c1 P2 N2 A2 c2 P3 N3 A3,
   @ifc_def T CS Espec Delta P1 N1 A1 c1 (inormal_ret_assert P2) N2 A2 ->
   @ifc_def T CS Espec (update_tycon Delta c1) P2 N2 A2 c2 P3 N3 A3 ->
   @ifc_def T CS Espec Delta P1 N1 A1 (Ssequence c1 c2) P3 N3 A3.
Proof.
  intros. apply ifc_seq with P2 N2 A2; try assumption. apply isequential'. assumption.
Qed.

End fwd_lemmas.
