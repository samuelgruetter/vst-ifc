Require Import msl.Extensionality.

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
