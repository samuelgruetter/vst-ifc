Require Export ifc.rules.
Require Export ifc.proofauto_lemmas.
Require Export ifc.ifc.
Require Export floyd.proofauto.

(* not used (yet?) *)
Lemma istart_function_aux1:
  forall {T: Type} (Espec: OracleKind) {cs: compspecs} Delta R1 P N A Q N' A' R c Post,
   @ifc_def T cs Espec Delta (fun rho => (PROPx P (LOCALx Q (SEPx (R1::R))))) N A c Post N' A' ->
   @ifc_def T cs Espec Delta (fun rho => ((PROPx P (LOCALx Q (SEPx R))) * `R1)) N A c Post N' A'.
Proof.
intros.
rewrite sepcon_comm. rewrite insert_SEP. apply H.
Qed.

(* This tactic is carefully tuned to avoid proof blowups,
  both in execution and in Qed *)
Ltac isimplify_func_tycontext :=
match goal with |- ifc_def ?DD _ _ _ _ _ _ _ =>
  match DD with context [(func_tycontext ?f ?V ?G)] =>
    (*ensure_no_augment_funspecs;*)
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (Delta := @abbreviate tycontext (func_tycontext f V G));
    change (func_tycontext f V G) with Delta;
    unfold func_tycontext, make_tycontext in Delta;
    let DS := fresh "Delta_specs" in let DS1 := fresh "DS1" in 
    pose (DS1 := make_tycontext_s G);
    pose (DS := @abbreviate (PTree.t funspec) DS1);
    change (make_tycontext_s G) with DS in Delta;
    hnf in DS1;
    cbv beta iota delta [ptree_set] in DS1;
    subst DS1;
    cbv beta iota zeta delta - [abbreviate DS] in Delta;
    check_ground_Delta
  end
end.

Ltac iprocess_stackframe_of :=
 match goal with |- context [ stackframe_of ?F ] =>
   let sf := fresh "sf" in set (sf:= stackframe_of F);
     unfold stackframe_of in sf; simpl map in sf; subst sf
  end;
 (*repeat
   match goal with |- context [ _ * fold_right sepcon emp (var_block _ (?i,_) :: _) ] =>
     match goal with
     | n: name i |- _ => simple apply var_block_lvar2;
       [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | clear n; intro n ]
     | |- _ =>    simple apply var_block_lvar2;
       [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros ?lvar0 ]
     end
    end;*)
  match goal with |- ifc_def _ ?Pre _ _ _ _ _ _ =>
     let p := fresh "p" in set (p := Pre);
     rewrite <- (@emp_sepcon (environ->mpred) _ _ _ (fold_right _ _ _));
     subst p
  end;
  (*repeat (simple apply postcondition_var_block;
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |  ]);*)
 change (fold_right sepcon emp (@nil (environ->mpred))) with
   (@emp (environ->mpred) _ _);
 rewrite ?sepcon_emp, ?emp_sepcon.

Ltac istart_function :=
 match goal with |- ifc_body ?V ?G ?F ?spec =>
    let s := eval hnf in spec.(functional_spec) in
    match s with
    | (DECLARE _ WITH u : unit
          PRE  [] main_pre _ nil u
          POST [ tint ] main_post _ nil u) => idtac
    | _ => check_canonical_funspec s
   end;
   let spec' := eval hnf in spec in
   let F' := eval hnf in F in
   change (ifc_body V G F' spec')
 end;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 hnf;
 intros; clear;
 simpl fn_body; simpl fn_return;
 (* simplifies complex implicit arg of sepcon to mpred *)
 simpl functors.MixVariantFunctor._functor in *;
 isimplify_func_tycontext;
 iprocess_stackframe_of.

(* TODO this code from VST's start_function is not yet translated to ifc:

 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
   match Pre with
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   (*simpl fn_body; (*done*)*) simpl fn_params (*; simpl fn_return (*done*)*)
 end;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 (*try expand_main_pre;*)
 (*repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)*)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax;
 clear_Delta_specs_if_leaf_function.
*)
