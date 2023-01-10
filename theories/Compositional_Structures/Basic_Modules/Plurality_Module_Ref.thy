theory Plurality_Module_Ref
  imports "Verified_Voting_Rule_Construction.Plurality_Module"
           "Component_Types/Elimination_Module_Ref"
begin


fun plur_score_mon :: "'a Evaluation_Function_Ref" where
  "plur_score_mon x A p = (wc_fold p x)"

definition plarility_monadic :: "'a Electoral_Module_Ref" where
  "plarility_monadic A pl \<equiv> do {
   scores <- (pre_compute_scores plur_score_mon A pl);
   max_eliminator_ref scores A pl
}"

context voting_session
begin

lemma plur_score_refine:
  shows "plur_score_mon x A pl \<le> SPEC (\<lambda> ps. ps =  plur_score x A pr)"
proof (unfold plur_score_mon.simps plur_score.simps)
  from profrel have profl: "profile_l A pl" using profile_prop_list
    by blast
  from profrel have prel: "(pl, pr) \<in> profile_rel" 
    using profile_type_ref by blast
  from  profl prel wc_fold_correct 
  show "wc_fold pl x \<le> SPEC (\<lambda>ps. ps = win_count pr x)"
    by fastforce
qed

lemma plurality_elim_correct:
  shows "plarility_monadic A pl \<le> SPEC (\<lambda> res. res = plurality_mod A pr)"
  unfolding plarility_monadic_def max_eliminator_ref.simps less_eliminator_ref.simps  
  elimination_module_ref_def eliminate_def
proof (refine_vcg, unfold plurality_mod.simps)

  oops

end


sepref_definition plurality_elim_sepref is
  "uncurry plarility_monadic":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plarility_monadic_def  max_eliminator_ref.simps plur_score_mon.simps
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