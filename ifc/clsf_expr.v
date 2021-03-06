From compcert Require Export Clightdefs.
Require Export ifc.lattice.

Local Open Scope bool.

Definition is_array_type(t: type): bool := match t with
  | Tarray _ _ _ => true
  | _ => false
  end.

(* Only accepts expressions without memory access -- otherwise it returns None.
   Inspired by no_loads_expr in examples/expr_test.v *)
Fixpoint clsf_expr_lr(as_lvalue: bool)(N: ident -> label)(e: expr): option label := match e with
  | Econst_int _ _ => Some Lo
  | Econst_float _ _ => Some Lo
  | Econst_single _ _ => Some Lo
  | Econst_long _ _ => Some Lo
  (* var means global var, whose access is always handled like a heap access.
     However, if we only take the address, we can classify it as Lo because the address of a global
     var is the same in all executions *)
  | Evar _ t => if as_lvalue || is_array_type t then Some Lo else None
  (* tempvar means local var, whose access is handled like a stack access *)
  | Etempvar name _ => Some (N name)
  | Ederef e1 t => if as_lvalue then clsf_expr_lr true N e1 else None
  | Eaddrof e1 _ => clsf_expr_lr true N e1
  | Eunop _ e1 _ => clsf_expr_lr as_lvalue N e1
  | Ebinop _ e1 e2 _ => lub (clsf_expr_lr as_lvalue N e1) (clsf_expr_lr as_lvalue N e2)
  | Ecast e1 _ => clsf_expr_lr as_lvalue N e1
  | Efield e1 _ t => if as_lvalue || is_array_type t then clsf_expr_lr true N e1 else None
  (* These two only contain types, therefore Lo *)
  | Esizeof _ _ => Some Lo
  | Ealignof _ _ => Some Lo
  end.

Definition clsf_expr := clsf_expr_lr false.
Definition clsf_lvalue := clsf_expr_lr true.
