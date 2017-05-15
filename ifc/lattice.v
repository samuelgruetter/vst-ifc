Require Import msl.Extensionality.

(* https://en.wikipedia.org/wiki/Lattice_(order) *)

Class Lattice (A: Type) := mkLattice {
  top : A;
  bot : A;
  glb : A -> A -> A;
  lub : A -> A -> A;
  glb_top_r : forall (a: A), glb a top = a;
  lub_bot_r : forall (a: A), lub a bot = a;
  glb_commut : forall (a b: A), glb a b = glb b a;
  lub_commut : forall (a b: A), lub a b = lub b a;
  glb_assoc : forall (a b c: A), glb a (glb b c) = glb (glb a b) c;
  lub_assoc : forall (a b c: A), lub a (lub b c) = lub (lub a b) c;
  glb_absorb : forall (a b: A), glb a (lub a b) = a;
  lub_absorb : forall (a b: A), lub a (glb a b) = a;
}.

Section LatticeFacts.

Context {A: Type}.
Context {LA: Lattice A}.

Lemma glb_idempotent: forall (a: A), glb a a = a.
Proof.
  intros. transitivity (glb a (lub a (glb a a))).
  - f_equal. symmetry. apply lub_absorb.
  - f_equal. apply glb_absorb.
Qed.

Lemma lub_idempotent: forall (a: A), lub a a = a.
Proof.
  intros. transitivity (lub a (glb a (lub a a))).
  - f_equal. symmetry. apply glb_absorb.
  - f_equal. apply lub_absorb.
Qed.

Lemma glb_top_l: forall (a: A), glb top a = a.
Proof. intro. rewrite glb_commut. apply glb_top_r. Qed.

Lemma lub_bot_l: forall (a: A), lub bot a = a.
Proof. intro. rewrite lub_commut. apply lub_bot_r. Qed.

Lemma glb_bot_l: forall (a: A), glb bot a = bot.
Proof.
  intro. transitivity (glb bot (lub bot a)).
  - f_equal. symmetry. apply lub_bot_l.
  - apply glb_absorb.
Qed.

Lemma lub_top_l: forall (a: A), lub top a = top.
Proof.
  intro. transitivity (lub top (glb top a)).
  - f_equal. symmetry. apply glb_top_l.
  - apply lub_absorb.
Qed.

Lemma lub_top_r: forall (a: A), lub a top = top.
Proof. intro. rewrite lub_commut. apply lub_top_l. Qed.

Lemma glb_bot_r : forall (a: A), glb a bot = bot.
Proof. intro. rewrite glb_commut. apply glb_bot_l. Qed. 

(* "lattice-lessthan-or-equal" *)
Definition lle(a b: A): Prop := b = lub a b.

Lemma double_lle_eq: forall (a b: A), lle a b -> lle b a -> a = b.
Proof.
  intros a b Le1 Le2. unfold lle in *. rewrite Le1. rewrite lub_commut. apply Le2.
Qed.

Lemma lle_lub_l: forall (a b: A), lle a (lub a b).
Proof.
  intros. unfold lle. rewrite lub_assoc. rewrite lub_idempotent. reflexivity.
Qed.

Lemma lle_lub_r: forall (a b: A), lle b (lub a b).
Proof.
  intros. unfold lle. rewrite lub_commut. rewrite lub_assoc. rewrite lub_idempotent. reflexivity.
Qed.

Lemma lle_bot_inv: forall (a: A), lle a bot -> a = bot.
Proof. intros. unfold lle in *. rewrite H. symmetry. apply lub_bot_r. Qed.

Lemma lub_bot_inv: forall (a b: A), lub a b = bot -> a = bot /\ b = bot.
Proof.
  intros.
  pose proof (lle_lub_l a b) as C. rewrite H in C. apply lle_bot_inv in C.
  pose proof (lle_lub_r a b) as D. rewrite H in D. apply lle_bot_inv in D.
  apply (conj C D).
Qed.

Lemma lle_top: forall (a: A), lle a top.
Proof. intro. unfold lle. symmetry. apply lub_top_r. Qed.

Lemma lle_refl: forall (a: A), lle a a.
Proof. intro. unfold lle. symmetry. apply lub_idempotent. Qed.

End LatticeFacts.


Inductive label : Set := Lo | Hi.

Instance LoHi : Lattice label := {|
  top := Hi;
  bot := Lo;
  glb := fun l1 l2 => match l1 with
         | Hi => l2
         | Lo => Lo
         end;
  lub := fun l1 l2 => match l1 with
         | Lo => l2
         | Hi => Hi
         end
|}.
- intro a. destruct a; reflexivity.
- intro a. destruct a; reflexivity.
- intros a b. destruct a; destruct b; reflexivity.
- intros a b. destruct a; destruct b; reflexivity.
- intros a b c. destruct a; destruct b; destruct c; reflexivity.
- intros a b c. destruct a; destruct b; destruct c; reflexivity.
- intros a b. destruct a; destruct b; reflexivity.
- intros a b. destruct a; destruct b; reflexivity.
Defined.

Instance LiftLattice {T A: Type} (LA: Lattice A): Lattice (T -> A) := {|
  top := fun (x: T) => (@top A LA);
  bot := fun (x: T) => (@bot A LA);
  glb := fun (a b: T -> A) => (fun (x: T) => @glb A LA (a x) (b x));
  lub := fun (a b: T -> A) => (fun (x: T) => @lub A LA (a x) (b x));
|}.
- intro. extensionality. apply glb_top_r.
- intro. extensionality. apply lub_bot_r.
- intros. extensionality. apply glb_commut.
- intros. extensionality. apply lub_commut.
- intros. extensionality. apply glb_assoc.
- intros. extensionality. apply lub_assoc.
- intros. extensionality. apply glb_absorb.
- intros. extensionality. apply lub_absorb.
Defined.

(* Now we have lub and glb available for any number of lifting levels:

Check (glb (fun (i: nat) => Hi) (fun (i: nat) => Lo)).
Check (glb (fun (x: nat) (i: nat*nat) => Hi) (fun (x: nat) (i: nat*nat) => Lo)).
Eval simpl in (lub (fun (x: nat) (i: nat*nat) => Hi) (fun (x: nat) (i: nat*nat) => Lo)).
Eval simpl in (lub (fun (x: nat) (i: nat*nat) => Lo) (fun (x: nat) (i: nat*nat) => Lo)).

Including all the lemmas!
*)

Section LiftLatticeFacts.

Context {T: Type}.
Context {A: Type}.
Context {LA: Lattice A}.

Lemma lle_pointwise: forall (f1 f2: T -> A), lle f1 f2 <-> forall (x: T), lle (f1 x) (f2 x).
Proof.
  split.
  - intros. unfold lle in *. pose proof (equal_f H) as C. apply C.
  - intro. unfold lle in *. extensionality. apply H.
Qed.

End LiftLatticeFacts.

(* Basically just a lattice on A, but with an additional element "None" sitting on top
   of the whole lattice.
   We chose to put "None" at the top because it means absence of classification information,
   in which case we have to assume that it is classified as Hi, which is top. *)
Instance OptionLattice {A: Type} (LA: Lattice A): Lattice (option A) := {|
  top := (@None A);
  bot := Some (@bot A LA);
  glb := fun (oa ob: option A) => match oa, ob with
         | None  , None   => None
         | Some a, None   => Some a
         | None  , Some b => Some b
         | Some a, Some b => Some (@glb A LA a b)
         end;
  lub := fun (oa ob: option A) => match oa, ob with
         | Some a, Some b => Some (@lub A LA a b)
         | _, _ => None
         end;
|}.
- intro a. destruct a; reflexivity.
- intro a. destruct a; try reflexivity. f_equal. apply lub_bot_r.
- intros a b. destruct a; destruct b; try reflexivity. f_equal. apply glb_commut.
- intros a b. destruct a; destruct b; try reflexivity. f_equal. apply lub_commut.
- intros a b c. destruct a; destruct b; destruct c; try reflexivity. f_equal. apply glb_assoc.
- intros a b c. destruct a; destruct b; destruct c; try reflexivity. f_equal. apply lub_assoc.
- intros a b. destruct a; destruct b; try reflexivity. f_equal. apply glb_absorb.
- intros a b. destruct a; destruct b; try reflexivity; f_equal.
  + apply lub_absorb.
  + apply lub_idempotent.
Defined.
