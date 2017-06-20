Require Import compcert.cfrontend.ClightBigstep.
Require Import veric.seplog.
Require Import veric.tycontext.
Require Import veric.semax.

Definition myassert := environ -> mem -> Prop.
Definition myretassert := exitkind -> option val -> myassert.

Definition apply_outcome(R: myretassert)(o: outcome): myassert :=
  match o with
  | Out_break    => R EK_break None
  | Out_continue => R EK_continue None
  | Out_normal   => R EK_normal None
  | Out_return r => match r with
    | Some (v,t) => R EK_return (Some v)
    | None       => R EK_return None
    end
  end.

Definition mysemax(P: myassert)(c: statement)(R: myretassert) :=
  forall (ge: genv) (e : env) (te1 : temp_env) (m1 : mem),
    let rho1 := (construct_rho (filter_genv ge) e te1) in
    P rho1 m1 ->
    exists te2 m2 tr oc,
      exec_stmt ge e te1 m1 c tr te2 m2 oc /\
      let rho2 := (construct_rho (filter_genv ge) e te2) in
      apply_outcome R oc rho2 m2.

(* Note: the above definition guarantees termination, if we don't want to do that,
   we could add "or it diverges" using execinf_stmt *)
