Require Import compcert.cfrontend.Clight.
Require Import veric.Clight_new.
Require Import examples.if1.
Require Import compcert.lib.Maps. (* for PMap and ZMap *)
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

(* cl_step : genv -> corestate -> mem -> corestate -> mem -> Prop *)

Inductive star (ge: genv): corestate -> mem -> corestate -> mem -> Prop :=
  | star_refl: forall s m,
      star ge s m s m
  | star_step: forall s1 m1 s2 m2 s3 m3,
      cl_step ge s1 m1 s2 m2 ->
      star ge s2 m2 s3 m3 ->
      star ge s1 m1 s3 m3.

Definition ge: genv := globalenv prog.

Definition m0 := Memory.Mem.empty.

Definition env0 : env := PTree.empty _.

Definition temp_env0 : temp_env := PTree.empty _.

Definition main_block: Values.block := ltac:(
  let o := eval hnf in (Globalenvs.Genv.find_symbol ge (Ctypes.prog_main prog)) in
  match o with
  | Some ?b => exact b
  end).

Definition main_fun: fundef := ltac:(
  let o := eval hnf in (Globalenvs.Genv.find_funct_ptr ge main_block) in
  match o with
  | Some ?f => exact f
  end).

Definition main_ptr: val := Vptr main_block Int.zero.

Definition cs0: corestate.
  set (o := (cl_initial_core ge main_ptr nil)).
  unfold cl_initial_core, main_ptr in o.
  change (Globalenvs.Genv.find_funct_ptr ge main_block) with (Some main_fun) in o.
  simpl in o.
  (* TODO why does this take forever??
     let r := eval cbv in (Int.eq_dec Int.zero Int.zero) in idtac r. *)
  match goal with
  | _ := if _ then Some ?X else _ |- _ => pose X as S
  end.
  clear o.
  cbv -[empty_env] in S.
  fold Ctypes.noattr in S.
  fold compcert.exportclight.Clightdefs.tint in S.
  fold AST.cc_default in S.
  (* "exact S" does not keep simplifications, so we copy-paste instead. *)
Abort.

(* copy-pasting from above gives this, which contains an infinite loop at the end,
   probably to make sure that it can take n steps for all n, but that's not what we want
Definition s0: corestate :=
  State empty_env
       (PTree.Node PTree.Leaf (Some (Vptr (BinNums.xI 24) (Int.repr 0)))
          PTree.Leaf)
       (Kseq
          (Scall None
             (Etempvar BinNums.xH
                (Ctypes.Tfunction Ctypes.Tnil Clightdefs.tint AST.cc_default))
             nil) :: Kseq (Sloop Sskip Sskip) :: nil)%list.
*)

Definition s0: corestate :=
  State empty_env
       (PTree.Node PTree.Leaf (Some (Vptr (BinNums.xI 24) (Int.repr 0)))
          PTree.Leaf)
       (Kseq
          (Scall None
             (Etempvar BinNums.xH
                (Ctypes.Tfunction Ctypes.Tnil Clightdefs.tint AST.cc_default))
             nil) :: nil)%list.

(* too slow because of (Int.eq_dec Int.zero Int.zero)! 
Definition cs0: corestate := ltac:(
  let o := eval cbv in (cl_initial_core ge main_ptr nil) in
  match o with
  | Some ?c => exact c
  end).
*)

Lemma if_Int_eq_dec: forall i (T: Type) (a b: T),
  (if Int.eq_dec i i then a else b) = a.
Proof.
  intros. destruct (Int.eq_dec i i). reflexivity. exfalso. auto.
Qed.

Goal exists envFinal temp_envFinal mFinal,
  star ge s0 m0 (State envFinal temp_envFinal nil (*empty cont list means done!*)) mFinal.
Proof.
  do 3 eexists. unfold s0, m0.
  eapply star_step.
  {
  eapply step_call_internal.
  - simpl. reflexivity.
  - constructor. simpl. reflexivity.
  - constructor.
  - simpl. rewrite if_Int_eq_dec. reflexivity.
  - reflexivity.
  - repeat constructor; cbv; intros; repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    end; auto; discriminate.
  - repeat constructor; cbv; intros; repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    end; auto; discriminate.
  - constructor.
  - reflexivity.
  }
  simpl (fn_body f_main).
  eapply star_step.
  {
  repeat eapply step_seq.
  eapply step_set.
  repeat econstructor.
  }
  eapply star_step.
  {
  eapply step_seq.
  eapply step_set.
  repeat econstructor.
  }
  eapply star_step.
  {
  eapply step_seq.
  eapply step_set.
  repeat econstructor.
  }
  eapply star_step.
  {
  eapply step_seq.
  eapply step_ifthenelse.
  - econstructor. reflexivity.
  - reflexivity.
  }
  simpl (if negb _ then Sset _ _ else _).
  rewrite Int.eq_false by (  rewrite Int.eq_false; intro; discriminate).
  simpl (if negb _ then Sset _ _ else _). (* we're always in the then-branch *)
  eapply star_step.
  {
  eapply step_set.
  repeat econstructor.
  }
  eapply star_step.
  {
  eapply step_return.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - eexists. repeat constructor.
  - simpl. auto.
  }
  eapply star_refl.
Qed.
