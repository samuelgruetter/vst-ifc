Require Import ifc.ifc_def.

Definition iPROPx{T: Type} := (@lft1 T _ _ PROPx).

Section iPropLocalSep.

Context {T: Type}.

Definition PROPx (P: list (T -> Prop)): forall (Q: environ->mpred), environ->mpred :=
     andp (prop (fold_right and True P)).

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z) (at level 10).
Notation "'PROP' ()   z" :=   (PROPx nil z) (at level 10).
Notation "'PROP' ( )   z" :=   (PROPx nil z) (at level 10).

Definition LOCALx (Q: list localdef) : forall (R: environ->mpred), environ->mpred :=
                 andp (local (fold_right (`and) (`True) (map locald_denote Q))).

Notation " 'LOCAL' ( )   z" := (LOCALx nil z)  (at level 9).
Notation " 'LOCAL' ()   z" := (LOCALx nil z)  (at level 9).

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z)
         (at level 9).

Definition SEPx (R: list mpred) : environ->mpred :=
    fun _ => (fold_right_sepcon R).
Arguments SEPx R _ : simpl never.

Notation " 'SEP' ( x ; .. ; y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8).

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8).
Notation " 'SEP' () " := (SEPx nil) (at level 8).

End IPropLocalSep.
