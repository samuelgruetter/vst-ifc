Require Import floyd.base.
Require Import floyd.canon.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.loadstore_field_at.
Require Import floyd.loadstore_mapsto.
Require Import floyd.mapsto_memory_block.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

(*
In VST, there are four layers of store lemmas, each layer proven in terms of the previous one:
   0) semax_store (basic VeriC)
   1) semax_store_nth_ram
   2) semax_max_path_field_store_nth_ram, semax_no_path_field_store_nth_ram
   3) semax_SC_field_store (used by the tactics)
Moreover, 2) and 3) support storing to a nested field inside an arbitrary nesting of
array and structs. 
This feature (& the accompanying complexity) is removed by the lemmas of this file.
*)

Section RULES.
Context (Espec : OracleKind).
Context (CS: compspecs).

Local Open Scope logic.

Lemma nested_field_type_nil: forall t , (nested_field_lemmas.nested_field_type t nil) = t.
Admitted. (* TODO probably doesn't hold because of sideconditions *)

Lemma field_address_nil: forall t a, (nested_field_lemmas.field_address t nil a) = a.
Admitted. (* TODO probably doesn't hold because of sideconditions *)

(* 2) *)
Lemma semax_no_path_field_store_nth_ram_really_no_path:
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t: type) (a v : val) (v' : reptype t),
      type_is_by_value (typeof e1) = true ->
      writable_share sh ->
      type_is_volatile (typeof e1) = false ->
      typeof e1 = t ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- (data_at_ sh t a * (data_at sh t v' a -* Post))%logic ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq a) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof e1)))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e1) && 
        (tc_expr Delta (Ecast e2 (typeof e1))) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros until 0. intros ByVal Wsh Volatile EqT JM GetR F Evale1 Evale2 Tc.
  rewrite EqT in ByVal.
  eapply semax_store_nth_ram with (p := a).
  + exact EqT.
  + exact Evale1.
  + rewrite <- EqT. exact Evale2.
  + exact GetR.
  + exact Wsh.
  + eapply RAMIF_PLAIN.trans; [exact F |].
    unfold data_at_. unfold field_at_. unfold data_at. unfold mapsto_.
    pose proof (mapsto_field_at_ramify sh t nil Vundef
      (default_val (nested_field_lemmas.nested_field_type t nil))
      v v' a) as C.
    pose proof ByVal as ByVal'.
    rewrite <- (nested_field_type_nil t) in ByVal.
    rewrite EqT in Volatile.
    rewrite <- (nested_field_type_nil t) in Volatile.
    specialize (C ByVal Volatile).
    assert (E: JMeq Vundef (default_val (nested_field_lemmas.nested_field_type t nil))). {
      rewrite (nested_field_type_nil t). apply JMeq_sym.
      apply data_at_rec_lemmas.by_value_default_val. exact ByVal'.
    }
    specialize (C E JM). clear E. eapply derives_trans; [eapply C |].
    clear - Espec.
    rewrite (nested_field_type_nil t). rewrite field_address_nil. apply derives_refl.
  + rewrite <- EqT. exact Tc.
Qed.

(* 3) in terms of directly 0) *)
Lemma semax_SC_field_store_without_paths:
    forall Delta sh n (p: val) P Q R (e1 e2 : expr)
      (t: type) (v0: val) (v v_new: reptype t),
      typeof e1 = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      nth_error R n = Some (data_at sh t v p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      JMeq v0 v_new ->
      writable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (data_at sh t v_new p)))))).
Proof.
  intros until 0.
  intros EqT ByVal Volatile GetR EvalLhs EvalRhs DEq Wsh Tc.
  subst t.
  eapply semax_pre_simple; [| eapply semax_post'; [| apply semax_store; eauto]].
  + apply later_left2.
    apply andp_right;  [subst; auto |].
    simpl lifted.
    change  (@LiftNatDed environ mpred Nveric)
      with (@LiftNatDed' mpred Nveric).
    rewrite (add_andp _ _ EvalLhs).
    rewrite (add_andp _ _ EvalRhs).
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    rewrite !(andp_comm _ (local _)).
    rewrite <- (andp_dup (local (`(eq p) (eval_lvalue e1)))), andp_assoc.
    do 3 rewrite <- local_sepcon_assoc2. rewrite <- local_sepcon_assoc1.
    eapply derives_trans.
    - apply sepcon_derives; [| apply derives_refl].
      remember (typeof e1) as t1.
(*    remember (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * `(mapsto sh t1 p v0 -* R))%logic as V.
      instantiate (1 := `(mapsto_ sh (typeof e1)) (eval_lvalue e1) * `(mapsto sh t1 p v -* Post)).
      unfold local, lift1; unfold_lift; intro rho; simpl.
      subst t1.
      normalize.
    - rewrite sepcon_assoc.
      apply derives_refl.
  + rewrite <- sepcon_assoc.
    rewrite !local_sepcon_assoc2, <- !local_sepcon_assoc1.
    erewrite SEP_replace_nth_isolate with (Rn' := Post), <- insert_SEP by eauto.
    apply sepcon_derives; auto.
    change (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))
      with (eval_expr (Ecast e2 (typeof e1))).
    Opaque eval_lvalue eval_expr.
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    Transparent eval_lvalue eval_expr.
    subst t1.
    apply modus_ponens_wand.
*)
Abort.

(* 3) in terms of 2) *)
Lemma semax_SC_field_store_without_paths:
    forall Delta sh n (p: val) P Q R (e1 e2 : expr)
      (t: type) (v0: val) (v v_new: reptype t),
      typeof e1 = t ->
      type_is_by_value t = true ->
      type_is_volatile t = false ->
      nth_error R n = Some (data_at sh t v p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq v0) (eval_expr (Ecast e2 t))) ->
      JMeq v0 v_new ->
      writable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_lvalue Delta e1) && 
         (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (data_at sh t v_new p)))))).
Proof.
  intros until 0.
  intros EqT ByVal Volatile GetR EvalLhs EvalRhs DEq Wsh Tc.
  subst t.
  eapply semax_no_path_field_store_nth_ram_really_no_path.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: reflexivity.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: eassumption.
  2: eassumption.
  1: apply cancel_emp_wand. cancel.
Qed.

End RULES.
