Require Import ifc.ifc_def.

Notation "'itemp' n v" := (lft2 temp (lft0 n) v) (at level 2).
Notation "'iPROP' ( x ; .. ; y )   z" :=
  (lft2 PROPx (lft2 cons x%type .. (lft2 cons y%type (lft0 nil)) ..) z) (at level 10).
Notation " 'iLOCAL' ( x ; .. ; y )   z" :=
  (lft2 LOCALx (lft2 cons x%type .. (lft2 cons y%type (lft0 nil)) ..) z)
         (at level 9).
Notation " 'iSEP' ( x ; .. ; y )" :=
  (lft1 SEPx (lft2 cons x%logic .. (lft2 cons y%logic (lft0 nil)) ..))
         (at level 8).

