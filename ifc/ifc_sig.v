(* In this file, P, N, A are separate, rather than a triple *)

Require Export lib.LibTactics.
Require Export compcert.cfrontend.Clight.
Require Export veric.Clight_new.
Require Export compcert.lib.Maps. (* for PMap and ZMap *)
Require Export compcert.common.Events.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export sepcomp.semantics.
Require Export sepcomp.semantics_lemmas.
Require Export veric.semax.
Require Export floyd.base.
Require Export floyd.canon.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.client_lemmas.
Require Export ifc.clsf_expr.
Require Import floyd.nested_field_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import List. Import ListNotations.

Local Open Scope logic.

Definition stack_clsf := ident -> label.

Definition ret_stack_clsf := exitkind -> option val -> stack_clsf.

Definition heap_loc := (positive * int)%type. (* block id and offset *)

Definition heap_clsf := heap_loc -> label.

Definition ret_heap_clsf := exitkind -> option val -> heap_clsf.

(* TODO this should match VST, i.e. we should have "state_pred = environ->mpred" for preconditions,
   and for postconditions, it's ret_assert in VST
   TODO or as a first step, maybe use environ instead of env and temp_env, and
   construct_rho: genviron -> env -> temp_env -> environ
 *)
Definition state_pred := env -> temp_env -> mem -> Prop.

Definition pre_assert := environ -> mpred.
(* "ret_assert := exitkind -> option val -> environ -> mpred" is already defined by VST *)

(* TODO get rid of these *)
Parameter VST_to_state_pred : pre_assert -> state_pred.
Definition VST_post_to_state_pred : ret_assert -> exitkind -> option val -> state_pred :=
  fun R ek vl => VST_to_state_pred (R ek vl).

Lemma VST_overridePost_to_state_pred00: forall Q R ek vl,
  VST_to_state_pred (overridePost Q R ek vl) =
  if eq_dec ek EK_normal
  then VST_to_state_pred (fun rho : environ => !! (vl = None) && Q rho)
  else VST_to_state_pred (R ek vl).
Proof.
  unfold overridePost. intros. destruct ek; reflexivity.
Qed.

Axiom VST_to_state_pred_commutes_imp: forall P P',
  (P |-- P') ->
  (forall e te m, VST_to_state_pred P e te m -> VST_to_state_pred P' e te m).

Axiom VST_to_state_pred_commutes_imp': forall Delta P P',
  (ENTAIL Delta, P |-- P') ->
  (forall e te m, VST_to_state_pred P e te m -> VST_to_state_pred P' e te m).

Axiom VST_indep_state_pred00: forall P e te m,
  VST_to_state_pred (!! P) e te m -> P.

Axiom VST_indep_state_pred: forall P,
  VST_to_state_pred (!! P) = fun e te m => P.

Axiom VST_to_state_pred_and: forall (P Q: environ -> mpred),
  VST_to_state_pred (P && Q) = 
  (fun e te m => VST_to_state_pred P e te m /\ VST_to_state_pred Q e te m).

Lemma VST_overridePost_to_state_pred: forall Q R ek vl,
  VST_to_state_pred (overridePost Q R ek vl) =
  if eq_dec ek EK_normal
  then fun e te m => vl = None /\ VST_to_state_pred Q e te m
  else VST_to_state_pred (R ek vl).
Proof.
  unfold overridePost. intros. destruct ek; simpl; try reflexivity.
  assert ((fun x : environ => !! (vl = None) && Q x) = !! (vl = None) && Q) as E. {
    extensionality. reflexivity.
  }
  rewrite E. rewrite VST_to_state_pred_and. extensionality e. extensionality te. extensionality m.
  rewrite VST_indep_state_pred. reflexivity.
Qed.

Definition lft0 {T} {B} (r: B) : T -> B := fun _ => r.
Definition lft1 {T} {A1 B} (f: A1 -> B) (a1: T -> A1) : T -> B := fun x => f (a1 x).
Definition lft2 {T} {A1 A2 B} (f: A1 -> A2 -> B) (a1: T -> A1) (a2: T -> A2):
   T -> B := fun x => f (a1 x) (a2 x).
Definition lft3 {T} {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B)
     (a1: T -> A1) (a2: T -> A2) (a3: T -> A3) :  T -> B :=
     fun x => f (a1 x) (a2 x) (a3 x).
Definition lft4 {T} {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B)
     (a1: T -> A1) (a2: T -> A2) (a3: T -> A3)(a4: T -> A4):  T -> B :=
     fun x => f (a1 x) (a2 x) (a3 x) (a4 x).

Ltac unfold_lft := repeat unfold lft0, lft1, lft2, lft3, lft4.

Definition overridePostClsf{A C: Type}(Q: A -> C)(R: A -> exitkind -> option val -> C)
: A -> exitkind -> option val -> C
:= fun (x: A) (ek: exitkind) (vl: option val) => if eq_dec ek EK_normal then Q x else R x ek vl.

Definition normalPostClsf{A Loc: Type}(Q: A -> Loc -> label)
: A -> exitkind -> option val -> Loc -> label
:= fun (x: A) (ek: exitkind) (vl: option val) => if eq_dec ek EK_normal then Q x else bot.

Definition loop1_ret_clsf{A Loc: Type}
(Inv: A -> Loc -> label)(R: A -> exitkind -> option val -> Loc -> label)
: A -> exitkind -> option val -> Loc -> label :=
 fun x ek vl =>
 match ek with
 | EK_normal => match vl with
   | None => Inv x
   | _ => bot
   end
 | EK_break => R x EK_normal None
 | EK_continue => match vl with
   | None => Inv x
   | _ => bot
   end
 | EK_return => R x EK_return vl
 end.

Definition loop2_ret_clsf{A Loc: Type}
(Inv: A -> Loc -> label)(R: A -> exitkind -> option val -> Loc -> label)
: A -> exitkind -> option val -> Loc -> label :=
 fun x ek vl =>
 match ek with
 | EK_normal => match vl with
   | None => Inv x
   | _ => bot
   end
 | EK_break => bot
 | EK_continue => bot
 | EK_return => R x EK_return vl
 end.

Definition heap_loc_eq_val(hl: heap_loc)(v: val): bool := match hl, v with
| (b1, i1), Vptr b2 i2 => Pos.eqb b1 b2 && Int.eq i1 i2
| _, _ => false
end.

Lemma heap_loc_eq_val_trans: forall loc v1 v2,
  heap_loc_eq_val loc v1 = true ->
  heap_loc_eq_val loc v2 = true ->
  v1 = v2.
Proof.
  introv HE1 HE2. destruct loc as [b i]. unfold heap_loc_eq_val in *.
  destruct v1; destruct v2; try discriminate.
  apply andb_true_iff in HE1. destruct HE1 as [E1 E2].
  apply andb_true_iff in HE2. destruct HE2 as [E3 E4].
  apply Pos.eqb_eq in E1. apply int_eq_e in E2.
  apply Pos.eqb_eq in E3. apply int_eq_e in E4.
  congruence.
Qed.

Module Type IFC_SIG.

Parameter ifc_def: forall (A: Type) {cs: compspecs} {Espec: OracleKind} (Delta: tycontext)
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> ret_stack_clsf) (postA: A -> ret_heap_clsf), Prop.

Section RULES.
Context {Espec : OracleKind}.
Context {CS: compspecs}.
Context {T: Type}.

Axiom ifc_seq:
  forall Delta h t
    (P1 P2: T -> environ -> mpred) (P3: T -> ret_assert)
    (N1 N2: T -> stack_clsf) (N3: T -> ret_stack_clsf)
    (A1 A2: T -> heap_clsf) (A3: T -> ret_heap_clsf),
  ifc_def T Delta P1 N1 A1 h 
          (lft2 overridePost P2 P3) (overridePostClsf N2 N3) (overridePostClsf A2 A3) ->
  ifc_def T (update_tycon Delta h) P2 N2 A2 t P3 N3 A3 ->
  ifc_def T Delta P1 N1 A1 (Ssequence h t) P3 N3 A3.

Axiom ifc_skip:
  forall Delta P N A,
  ifc_def T Delta P N A Sskip (lft1 normal_ret_assert P) (normalPostClsf N) (normalPostClsf A).

Axiom ifc_seq_skip:
  forall Delta P N A c P' N' A',
  ifc_def T Delta P N A c P' N' A' <-> ifc_def T Delta P N A (Ssequence c Sskip) P' N' A'.

Axiom ifc_ifthenelse: forall (Delta: tycontext) 
  (P: T -> pre_assert) (N: T -> stack_clsf) (A: T -> heap_clsf)
  (b: expr) (c1 c2: statement)
  (P': T -> ret_assert) (N': T -> ret_stack_clsf) (A': T -> ret_heap_clsf),
  bool_type (typeof b) = true ->
  (forall x, ENTAIL Delta, P x |-- !! (clsf_expr (N x) b = Some Lo)) ->
  ifc_def T Delta (lft2 andp P (lft0 (local (`(typed_true  (typeof b)) (eval_expr b)))))
          N A c1 P' N' A' ->
  ifc_def T Delta (lft2 andp P (lft0 (local (`(typed_false (typeof b)) (eval_expr b)))))
          N A c2 P' N' A' ->
  ifc_def T Delta (lft2 andp (lft0 (tc_expr Delta (Eunop Onotbool b tint))) P) N A
         (Sifthenelse b c1 c2) P' N' A'.

Axiom ifc_loop: forall Delta Inv1P Inv1N Inv1A Inv2P Inv2N Inv2A incr body RetP RetN RetA,
  ifc_def T Delta Inv1P Inv1N Inv1A
    body
    (lft2 loop1_ret_assert Inv2P RetP) (loop1_ret_clsf Inv2N RetN) (loop2_ret_clsf Inv2A RetA) ->
  ifc_def T Delta Inv2P Inv2N Inv2A
    incr
    (lft2 loop2_ret_assert Inv1P RetP) (loop1_ret_clsf Inv1N RetN) (loop2_ret_clsf Inv1A RetA) ->
  ifc_def T Delta Inv1P Inv1N Inv1A (Sloop body incr) RetP RetN RetA.

Axiom ifc_break:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf),
  ifc_def T Delta
          (fun (x: T) => R x EK_break None)
          (fun (x: T) => N x EK_break None)
          (fun (x: T) => A x EK_break None)
          Sbreak
          R N A.

Axiom ifc_continue:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf),
  ifc_def T Delta
          (fun (x: T) => R x EK_continue None)
          (fun (x: T) => N x EK_continue None)
          (fun (x: T) => A x EK_continue None)
          Scontinue
          R N A.

Axiom ifc_return:
  forall Delta (R: T -> ret_assert) (N: T -> ret_stack_clsf) (A: T -> ret_heap_clsf)
        (retExpr: option expr) (retVal: option val),
(* TODO this is an equality between two things of type "environ -> mpred", probably not what we want *)
  (cast_expropt retExpr (ret_type Delta)) = `retVal ->
  ifc_def T Delta
          (fun (x: T) => tc_expropt Delta retExpr (ret_type Delta) &&
                         R x EK_return retVal)
          (fun (x: T) => N x EK_return retVal)
          (fun (x: T) => A x EK_return retVal)
          (Sreturn retExpr)
          R N A.

Axiom ifc_pre: forall Delta P1 P1' N1 N1' A1 A1' c P2 N2 A2,
  (forall x, ENTAIL Delta, P1 x |-- P1' x) ->
  (forall x, ENTAIL Delta, P1 x |-- !! (lle (N1 x) (N1' x) /\ lle (A1 x) (A1' x))) ->
  ifc_def T Delta P1' N1' A1' c P2 N2 A2 ->
  ifc_def T Delta P1  N1  A1  c P2 N2 A2.

Axiom ifc_post: forall Delta P1 N1 A1 c P2 P2' N2 N2' A2 A2',
  (forall x ek vl, ENTAIL (exit_tycon c Delta ek), P2' x ek vl |-- P2 x ek vl) ->
  (forall x ek vl, ENTAIL (exit_tycon c Delta ek), P2' x ek vl |--
    !! (lle (N2' x ek vl) (N2 x ek vl) /\ lle (A2' x ek vl) (A2 x ek vl))) ->
  ifc_def T Delta P1 N1 A1 c P2' N2' A2' ->
  ifc_def T Delta P1 N1 A1 c P2  N2  A2.

Axiom ifc_set: forall Delta id P Q R (N: T -> stack_clsf) (A: T -> heap_clsf) (e2: expr) l2 t v,
  typeof_temp Delta id = Some t ->
  is_neutral_cast (implicit_deref (typeof e2)) t = true ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     local (`(eq (v x)) (eval_expr e2))) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     tc_expr Delta e2) ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     !! (clsf_expr (N x) e2 = Some (l2 x))) ->
  ifc_def T Delta
    (fun x => (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x))))) N A
    (Sset id e2)
    (fun x => (normal_ret_assert (PROPx (P x) 
           (LOCALx (temp id (v x) :: remove_localdef_temp id (Q x)) (SEPx (R x))))))
    (normalPostClsf (fun x i => if Pos.eqb i id then l2 x else N x i))
    (normalPostClsf A).

Axiom ifc_load: forall Delta P Q R (N: T -> stack_clsf) (A: T -> heap_clsf) sh n id e
  (t t_root: type) (gfs0 gfs1 gfs: T -> list gfield) (l1 l2: T -> label)
  (p q: T -> val) (v : T -> val)
  (* dependent types FTW: *)
  (v' : forall (x: T), reptype (nested_field_type t_root (gfs0 x))),
  (* VST preconditions: *)
  typeof_temp Delta id = Some t ->
  is_neutral_cast (typeof e) t = true ->
  type_is_volatile (typeof e) = false ->
  (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
     local (`(eq (q x)) (eval_lvalue e))) ->
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

Axiom ifc_store:
    forall Delta sh n (p: T -> val) P Q R (e1 e2 : expr)
      (t: type) (v0: T -> val) (v v_new: T -> reptype t)
      (l1 l2: T -> label) (N: T -> stack_clsf) (A: T -> heap_clsf),
      (* VST preconditions: *)
      typeof e1 = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      (forall x, nth_error (R x) n = Some (data_at sh t (v x) (p x))) ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 local (`(eq (p x)) (eval_lvalue e1))) ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 local (`(eq (v0 x)) (eval_expr (Ecast e2 t)))) ->
      (forall x, JMeq (v0 x) (v_new x)) ->
      writable_share sh ->
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t))) ->
      (* IFC preconditions: *)
      (forall x, ENTAIL Delta, PROPx (P x) (LOCALx (Q x) (SEPx (R x))) |--
                 !! (clsf_lvalue (N x) e1 = Some (l1 x) /\
                     clsf_expr   (N x) e2 = Some (l2 x))) ->
      ifc_def T Delta
        (fun x => (|>PROPx (P x) (LOCALx (Q x) (SEPx (R x)))))
        N
        A
        (Sassign e1 e2)
        (fun x => (normal_ret_assert (PROPx (P x)
                                     (LOCALx (Q x)
                                     (SEPx (replace_nth n (R x) (data_at sh t (v_new x) (p x))))))))
        (normalPostClsf N)
        (normalPostClsf (fun x loc =>
           if heap_loc_eq_val loc (p x) then lub (l1 x) (l2 x) else A x loc)).

End RULES.

End IFC_SIG.
