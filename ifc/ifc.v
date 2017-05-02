Require Export compcert.cfrontend.Clight.
Require Export veric.Clight_new.
Require Export examples.if1.
Require Export compcert.lib.Maps. (* for PMap and ZMap *)
Require Export compcert.common.Events.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memory.
Require Export veric.semax.
Require Export floyd.base.
Require Import List. Import ListNotations.

Definition simplestate := (corestate * mem)%type.

Inductive label : Set := Lo | Hi.

Definition stack_clsf := ident -> label.

Definition heap_loc := (positive * Z)%type. (* block id and offset *)

Definition heap_clsf := heap_loc -> label.

(* TODO this should match VST, i.e. we should have "state_pred = environ->mpred" for preconditions,
   and for postconditions, it's ret_assert in VST *)
Definition state_pred := corestate -> mem -> Prop.

Definition pre_assert := environ -> mpred.
(* "ret_assert := exitkind -> option val -> environ -> mpred" is already defined by VST *)

Definition ifc_pre := (pre_assert * stack_clsf * heap_clsf)%type.
Definition ifc_post := (ret_assert * stack_clsf * heap_clsf)%type.

(* TODO get rid of these *)
Parameter VST_pre_to_state_pred : pre_assert -> state_pred.
Parameter VST_post_to_state_pred : ret_assert -> state_pred.

Inductive star (ge: genv): corestate -> mem -> corestate -> mem -> Prop :=
  | star_refl: forall s m,
      star ge s m s m
  | star_step: forall s1 m1 s2 m2 s3 m3,
      cl_step ge s1 m1 s2 m2 ->
      star ge s2 m2 s3 m3 ->
      star ge s1 m1 s3 m3.

(* general low-equivalence *)
Definition gen_lo_equiv{Loc V: Type}(f1 f2: Loc -> label)(s1 s2: Loc -> V) :=
  forall (l: Loc), f1 l = Lo -> f2 l = Lo -> s1 l = s2 l.

(* ExtCall not considered currently *)
Definition stack_lo_equiv(s1 s2: corestate)(N1 N2: stack_clsf): Prop :=
  match s1, s2 with
  | (State e1 te1 c1), (State e2 te2 c2) =>
     e1 = e2 /\ c1 = c2 /\ gen_lo_equiv N1 N2 (fun i => te1 ! i) (fun i => te2 ! i)
  | _, _ => False
  end.

Definition heap_access(m: mem)(l: heap_loc): memval := 
  let (b, i) := l in (ZMap.get i (PMap.get b (Mem.mem_contents m))).

Definition heap_lo_equiv(m1 m2: mem)(A1 A2: heap_clsf): Prop :=
  gen_lo_equiv A1 A2 (heap_access m1) (heap_access m2).

Definition simple_ifc {A : Type} (Delta: tycontext)
  (preP: A -> state_pred) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> state_pred) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= forall (x1 x2: A) (ge: genv) (e1 e2: env) (te1 te2: temp_env) (s1' s2': corestate)
          (m1 m1' m2 m2': mem),
   let s1 := (State e1 te1 [Kseq c]) in
   let s2 := (State e2 te2 [Kseq c]) in
   preP x1 s1 m1 ->
   preP x2 s2 m2 ->
   stack_lo_equiv s1 s2 (preN x1) (preN x2) ->
   heap_lo_equiv  m1 m2 (preA x1) (preA x2) ->
   star ge s1 m1 s1' m1' ->
   star ge s2 m2 s2' m2' ->
   stack_lo_equiv s1' s2' (postN x1) (postN x2) /\ heap_lo_equiv m1 m2 (postA x1) (postA x2).

Definition ifc_core {A: Type} (Delta: tycontext) 
  (preP: A -> pre_assert) (preN: A -> stack_clsf) (preA: A -> heap_clsf)
  (c: statement)
  (postP: A -> ret_assert) (postN: A -> stack_clsf) (postA: A -> heap_clsf)
:= let preP'  := fun (x: A) => VST_pre_to_state_pred (preP x) in
   let postP' := fun (x: A) => VST_post_to_state_pred (postP x) in
   simple_ifc Delta preP' preN preA c postP' postN postA.

Definition proj13f {A T1 T2 T3: Type} (f: A -> (T1 * T2 * T3)): A -> T1 :=
  fun (x: A) => match f x with
  | (f, _, _) => f
  end.

Definition proj23f {A T1 T2 T3: Type} (f: A -> (T1 * T2 * T3)): A -> T2 :=
  fun (x: A) => match f x with
  | (_, f, _) => f
  end.

Definition proj33f {A T1 T2 T3: Type} (f: A -> (T1 * T2 * T3)): A -> T3 :=
  fun (x: A) => match f x with
  | (_, _, f) => f
  end.

Definition ifc_core0 {A: Type} (Delta: tycontext) (P: A -> ifc_pre) (c: statement) (Q: A -> ifc_post) :=
  ifc_core Delta (proj13f P) (proj23f P) (proj33f P)
                 c
                 (proj13f Q) (proj23f Q) (proj33f Q).

Definition semax0 {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (P: ifc_pre) (c: statement) (Q: ifc_post)
:= semax Delta (fst (fst P)) c (fst (fst Q)).

Definition ifc_def {A: Type} {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) 
  (P: A -> ifc_pre) (c: statement) (Q: A -> ifc_post)
:= (forall x: A, semax0 Delta (P x) c (Q x)) /\
   (ifc_core0 Delta P c Q).

(*
Notation "'ifc' [ x : A ] Delta |-- P c Q" :=
  (@ifc_def A _ _ Delta (fun x => P) c (fun x => Q))
  (at level 200,
   x at level 0, A at level 0, Delta at level 0,
   P at level 0, c at level 0, Q at level 0).
*)

(* recursive binders only work for fun and forall, but not for match or let, so we have to write
   one definition for each arity *)

Notation "'ifc' [ x1 : A1 , x2 : A2 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2) _ _ Delta (fun x => match x with (x1,x2) => P end)
                              c
                              (fun x => match x with (x1,x2) => Q end))
(at level 200,
 x1 at level 0, x2 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).

Notation "'ifc' [ x1 : A1 , x2 : A2 , x3 : A3 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2*A3) _ _ Delta
            (fun x => match x with (x1,x2,x3) => P end)
            c
            (fun x => match x with (x1,x2,x3) => Q end))
(at level 200,
 x1 at level 0, x2 at level 0, x3 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).

Notation "'ifc' [ x1 : A1 , x2 : A2 , x3 : A3 , x4 : A4 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2*A3*A4) _ _ Delta
            (fun x => let (p3, x4) := x in let (p2, x3) := p3 in let (x1, x2) := p2 in P)
            c
            (fun x => let (p3, x4) := x in let (p2, x3) := p3 in let (x1, x2) := p2 in Q))
(at level 200,
 x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).

(*
Notation "'ifc' [ x1 : A1 , x2 : A2 , x3 : A3 , x4 : A4 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2*A3*A4) _ _ Delta
            (fun x => match x with (x1,x2,x3,x4) => P end)
            c
            (fun x => match x with (x1,x2,x3,x4) => Q end))
(at level 200,
 x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).
*)

Notation "'ifc' [ x1 : A1 , x2 : A2 , x3 : A3 , x4 : A4 , x5 : A5 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2*A3*A4*A5) _ _ Delta
            (fun x => match x with (x1,x2,x3,x4,x5) => P end)
            c
            (fun x => match x with (x1,x2,x3,x4,x5) => Q end))
(at level 200,
 x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).

Notation "'ifc' [ x1 : A1 , x2 : A2 , x3 : A3 , x4 : A4 , x5 : A5 , x6 : A6 ] Delta |-- P c Q" :=
  (@ifc_def (A1*A2*A3*A4*A5*A6) _ _ Delta
            (fun x => match x with (x1,x2,x3,x4,x5,x6) => P end)
            c
            (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q end))
(at level 200,
 x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0,
 Delta at level 0, P at level 0, c at level 0, Q at level 0).
