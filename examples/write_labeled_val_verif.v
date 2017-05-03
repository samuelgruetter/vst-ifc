Require Import floyd.proofauto.
Require Import examples.write_labeled_val.
Require Import ifc.ifc.

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

Lemma verif_write_labeled_val:
  ifc [v: int, b: int, highptr: val, lowptr: val] Delta |--
   (PROP (b = Int.zero \/ b = Int.one)
    LOCAL (temp _v (Vint v); temp _b (Vint b); temp _highptr highptr; temp _lowptr lowptr)
    SEP (data_at_ Ews tint highptr; data_at_ Ews tint lowptr))
   (fun i => PMap.get i 
      (PMap.set _v (if Int.eq b Int.zero then Lo else Hi)
      (PMap.set _b Lo
      (PMap.set _highptr Hi
      (PMap.set _lowptr Lo
      (PMap.init Hi))))))
   (fun loc => Hi)
   body
   (normal_ret_assert (
    PROP (b = Int.zero \/ b = Int.one)
    LOCAL (temp _v (Vint v); temp _b (Vint b); temp _highptr highptr; temp _lowptr lowptr)
    SEP (data_at_ Ews tint highptr; data_at_ Ews tint lowptr)))
   (fun i => Hi)
   (fun loc => Hi).
Proof.
  unfold body. apply ifc_ifthenelse; try reflexivity.
  - (* then-branch *)


(* The ifc notation is not applicable here, and we have to do the following transformation: *)
  unfold iprop.
  match goal with
  | |- context [ iand ?P1 ?P2 ] => match P1 with
    | (fun (x: ?A1 * ?A2 * ?A3 * ?A4) =>
       let '(p3, x4) := x in let '(p2, x3) := _ in let '(x1, x2) := _ in ?bb1) => match P2 with
       | (fun x' => ?bb2) => let r := constr:(fun (x': A1*A2*A3*A4) => 
         let '(x1, x2, x3, x4) := x' in bb1 && bb2) in
         assert (iand P1 P2 = r) as E by (
           extensionality; destruct x0 as [[[x1 x2] x3] x4]; reflexivity
         );
         idtac
      end
    end
  end.
  rewrite E. clear E.

(* Now finally the notation works again! 

But note that the variable names were lost, they now have the default names x1, x2, x3, x4 instead
of v, b, highptr, lowptr.

The problem was that we had to turn

(fun x => let ... in P1) && (fun x => let ... in P2)
into
(fun x => let ... in (P1 && P2))

Note: we cannot write lemmas like these, because P1 and P2 contain free variables!

Lemma distrib_lets21: forall {T1 R: Type} (f: T1 -> T1 -> R) P1 P2,
    f (fun (x: T1) => let y := x in P1)
      (fun (x: T1) => let y := x in P2)
    = (fun (x: T1) => let y := x in (f P1 P2)).


Lemma distrib_lets24: forall {T1 T2 T3 T4 R: Type} (f: (T1*T2*T3*T4) -> (T1*T2*T3*T4) -> R) P1 P2,
    f (fun (x: (T1*T2*T3*T4)) => let (p3, x4) := x in let (p2, x3) := p3 in let (x1,x2) := p2 in P1)
      (fun (x: (T1*T2*T3*T4)) => let (p3, x4) := x in let (p2, x3) := p3 in let (x1,x2) := p2 in P2)
= (fun (x: (T1*T2*T3*T4)) => let (p3, x4) := x in let (p2, x3) := p3 in let (x1,x2) := p2 in (f P1 P2)).

*)


    unfold ifc_def. split.
    + (* VST part *)
      intros. destruct x as [[[v b] highptr] lowptr].
      admit.
    + (* IFC part *)
      apply ifc_core0_always_holds.
  - (* else-branch *)
    admit.
Admitted.
