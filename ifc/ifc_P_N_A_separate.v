(* [UNUSED] In this file, P, N, A are separate, rather than a triple *)

Require Import compcert.cfrontend.Clight.
Require Import veric.Clight_new.
Require Import examples.if1.
Require Import compcert.lib.Maps. (* for PMap and ZMap *)
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import veric.semax.
Require Import floyd.base.

Definition simplestate := (corestate * mem)%type.

Inductive label : Set := Lo | Hi.

Definition stack_clsf := ident -> label.

Definition heap_loc := (positive * Z)%type. (* block id and offset *)

Definition heap_clsf := heap_loc -> label.

(* TODO this should match VST, i.e. we should have "state_pred = environ->mpred" *)
Definition state_pred := corestate -> mem -> Prop.

Definition pre_assert := environ -> mpred.
(* "ret_assert := exitkind -> option val -> environ -> mpred" is already defined by VST *)

(* TODO get rid of these *)
Parameter VST_pre_to_state_pred : pre_assert -> state_pred.
Parameter VST_post_to_state_pred : ret_assert -> state_pred.

Definition simple_ifc {A : Set} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> state_pred) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= forall (x1 x2: A) (c1 c2 : corestate) (m1 m2: mem),
   preP x1 c1 m1 -> preP x2 c2 m2 -> True. (* TODO *)

Definition ifc_core {A: Set} (Delta: tycontext) 
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= let preP'  := fun (x: A) => VST_pre_to_state_pred (preP x) in
   let postP' := fun (x: A) => VST_post_to_state_pred (postP x) in
   simple_ifc Delta preP' preN preA c postP' postN postA.

Definition ifc_def {A: Set} {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= (forall x: A, @semax cs Espec Delta (preP x) c (postP x)) /\
   (ifc_core Delta preP preN preA c postP postN postA).

Notation "'ifc' '[' x : A ']'  'semax' Delta preP preN preA c postP postN postA" :=
  (@ifc_def A _ _ Delta (fun x => preP) (fun x => preN) (fun x => preA)
                        c
                        (fun x => postP) (fun x => postN) (fun x => postA))
  (at level 200,
   x at level 0, A at level 0, Delta at level 0,
   preP at level 0, preN at level 0, preA at level 0,
   c at level 0,
   postP at level 0, postN at level 0, postA at level 0).

Parameter D1: tycontext.
Parameter P1: pre_assert.
Parameter Q1: ret_assert.
Definition N1: stack_clsf := fun i => if Pos.testbit i 0 then Lo else Hi.
Definition A1: heap_clsf := fun l => let (b, ofs) := l in if Z.testbit ofs 0 then Lo else Hi.
Require Import floyd.proofauto.
Instance CompSpecs : compspecs. admit. Admitted.
Instance Espec: OracleKind. Admitted.
Definition t1 := ifc [ a : nat ] semax D1 P1 N1 A1 Sskip (fun _ => fun _ => !! (a = a)) N1 A1.
Print t1.

(* recursive binders only work for fun and forall, but not for match or let, so we have to write
   one definition for each arity *)

Notation "'ifc' '[' x1 : A1 , x2 : A2 ']'  'semax' Delta preP preN preA c postP postN postA" :=
  (@ifc_def (A1*A2) _ _ Delta
     (fun x => let (x1,x2) := x in preP)
     (fun x => let (x1,x2) := x in preN)
     (fun x => let (x1,x2) := x in preA)
     c
     (fun x => let (x1,x2) := x in postP)
     (fun x => let (x1,x2) := x in postN)
     (fun x => let (x1,x2) := x in postA))
(at level 200,
 x1 at level 0, A1 at level 0,
 x2 at level 0, A2 at level 0,
 Delta at level 0,
 preP at level 0, preN at level 0, preA at level 0,
 c at level 0,
 postP at level 0, postN at level 0, postA at level 0).

Definition t2 := ifc [a : nat, b: nat] semax D1 P1 N1 A1 Sskip (fun _ => fun _ => !! (a = b)) N1 A1.
Print t2.
