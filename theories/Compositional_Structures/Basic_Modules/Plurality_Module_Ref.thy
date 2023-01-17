theory Plurality_Module_Ref
  imports "Verified_Voting_Rule_Construction.Plurality_Module"
           "Component_Types/Elimination_Module_Ref"
begin


fun plur_score_mon :: "'a Evaluation_Function_Ref" where
  "plur_score_mon x A p = (wc_fold p x)"

definition plurality_monadic :: "'a Electoral_Module_Ref" where
  "plurality_monadic A pl \<equiv> do {
   scores <- (pre_compute_scores plur_score_mon A pl);
   max_eliminator_ref scores A pl
}"

lemma plur_score_refine_weak:
  fixes A :: "'a set"
  shows "((\<lambda> x. plur_score_mon x A), (\<lambda> x p. RETURN ( plur_score x A p)))
    \<in> evalf_profA_rel A"
  apply refine_vcg
proof (unfold plur_score_mon.simps plur_score.simps, rename_tac x' x ppl ppr)
  fix  x':: 'a 
  fix x:: 'a 
  fix ppl ppr
  assume altid: "(x', x) \<in> Id"
  from this have alteq: "x' = x" by simp
  assume profrel: "(ppl, ppr) \<in> profile_on_A_rel A"
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
   

end


sepref_definition plurality_elim_sepref is
  "uncurry plurality_monadic":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_monadic_def  max_eliminator_ref.simps plur_score_mon.simps
    less_eliminator_ref.simps  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
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