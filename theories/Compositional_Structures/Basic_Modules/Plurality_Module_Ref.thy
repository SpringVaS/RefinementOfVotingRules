theory Plurality_Module_Ref
  imports 
          "Verified_Voting_Rule_Construction.Plurality_Rule"
           "Component_Types/Elimination_Module_Ref"
begin


definition plur_score_ref :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "plur_score_ref x A p = (wc_fold p x)"

definition plurality_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "plurality_ref A pl \<equiv> do {
   scores <- (pre_compute_scores plur_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma plur_score_refine_weak:
  fixes A :: "'a set"
  shows "(uncurry plurality_ref, uncurry (RETURN oo plurality)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (intro frefI nres_relI, unfold comp_apply, clarsimp simp del: plurality.simps, 
        rename_tac A pr pl)
  fix A :: "'a set"
  fix pr pl
  assume fina: "finite A"
  assume profrel: "(pl, pr) \<in> profile_on_A_rel A"
  from profrel have profl: "profile_l A ppl" using profile_prop_list
    by blast
  from profrel have prel: "(ppl, ppr) \<in> profile_rel" 
    using profile_type_ref by blast
  from  profl prel alteq wc_fold_correct 
  show "wc_fold ppl x' \<le> SPEC (\<lambda>c. (c, win_count ppr x) \<in> nat_rel)"
    by fastforce
qed


context profile_complete
begin

theorem plurality_elim_correct:
  shows "(plurality_monadic A pl, (SPEC (\<lambda> em. em = plurality_mod A pr))) 
  \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (unfold plurality_monadic_def plurality_mod.simps)
  from fina nempa have arel: "(A, A) \<in> \<langle>Id\<rangle>alt_set_rel" 
    unfolding alt_set_rel_def using in_br_conv[symmetric]
    by (simp add: brI)
  from profrel have prel: " (pl, pr) \<in> profile_rel" using profile_type_ref by blast
  have prec: "pre_compute_scores plur_score_mon A pl 
          \<le> SPEC (\<lambda> map. map = pre_computed_map plur_score A pr)"
  using plur_score_refine_weak[where A = A]
      compute_scores_correct_weak_evalref[THEN nres_relD, THEN refine_IdD]
  by fastforce 
  from arel prel show "(pre_compute_scores plur_score_mon A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl),
     SPEC (\<lambda>em. em = max_eliminator plur_score A pr))
    \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
   using prec max_eliminator_ref_correct[THEN fun_relD] specify_left[where M = 
        "\<Down> (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel) 
  (SPEC (\<lambda>res. res = max_eliminator plur_score A pr))"
       and m = "pre_compute_scores plur_score_mon A pl"
       and \<Phi> = "(\<lambda>map. map = pre_computed_map plur_score A pr)"
       and f = "(\<lambda>scores. max_eliminator_ref scores A pl)"] 
  nres_relI nres_relD
   by blast 
qed
   


sepref_definition plurality_elim_sepref is
  "uncurry plurality_ref":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_ref_def  max_eliminator_ref_def plur_score_ref_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)

  apply sepref_dbg_keep
  done



end
end