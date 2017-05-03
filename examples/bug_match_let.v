
(* https://coq.inria.fr/bugs/show_bug.cgi?id=5486 *)

Goal forall (p: nat*nat), let (a, b) := p in a < b.
intro p.
match goal with
| |- ?G1 =>
  match G1 with
  |                  (let (x1, x2) := ?c in ?body) =>
    let G2 := constr:(let (x1, x2) :=  c in  body) in
    assert (G1 <-> G2)
  end
end.
(* a and b were swapped! *)
Abort.

Goal forall (p: nat*bool), let (a, b) := p in (if b then a = a else a <> a).
intro p.
match goal with
| |- ?G1 =>
  match G1 with
  |                  (let 'pair x1 x2 := ?c in ?body) =>
    let G2 := constr:(let 'pair x1 x2 :=  c in  body) in
    assert (G1 <-> G2)
  end
end.
(* If we use the notation
'pair x1 x2
or
'(x1, x2)
instead of
(x1, x2)
then it works, but the names a, b are replaced by the default names x1, x2, which is undesirable,
because it makes the expressions less readable. *)
Abort.
