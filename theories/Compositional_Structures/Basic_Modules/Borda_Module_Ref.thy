theory Borda_Module_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Module"
           "Component_Types/Elimination_Module_Ref"
begin

fun borda_score_mon :: "'a Evaluation_Function_Ref" where
  "borda_score_mon x A p =
    sum_impl (prefer_count_monadic_imp p x) A"


definition borda_ref :: "'a Electoral_Module_Ref" where
  "borda_ref A pl \<equiv> do {
   scores <- (pre_compute_scores borda_score_mon A pl);
   max_eliminator_ref scores A pl
}"

lemma borda_score_correct:
  fixes A:: "'a set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
  shows "borda_score_mon x A pl \<le> SPEC (\<lambda> sc. sc = (borda_score x A pr))"
  unfolding borda_score_mon.simps borda_score.simps
  by (refine_vcg fina sum_impl_correct prefer_count_monadic_imp_correct  profrel)
 

lemma borda_ref_correct:          
  shows "(uncurry borda_ref, uncurry (RETURN oo borda)) \<in> 
  [\<lambda> (A, _). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding borda_ref_def
proof (intro frefI nres_relI,  clarsimp simp add: set_rel_id prod_rel_id simp del: borda.simps,
    unfold borda.simps comp_apply SPEC_eq_is_RETURN(2)[symmetric], rename_tac A pl pr,
refine_vcg)
  fix A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  note csc = compute_scores_correct[where efnref = borda_score_mon and efn= borda_score
and A = A and pl = pl
      and pr = pr]
  from fina prel this borda_score_correct have 
    precompborda: "pre_compute_scores borda_score_mon A pl
  \<le> SPEC (\<lambda>map. map = pre_computed_map borda_score A pr)" by fastforce
  note maxelim = max_eliminator_ref_correct[where efn = borda_score and A = A and pl = pl
      and pr = pr]
  from fina prel this have mid: "(\<And>x. x = pre_computed_map borda_score A pr \<Longrightarrow>
          max_eliminator_ref x A pl \<le> SPEC (\<lambda>x. x = max_eliminator borda_score A pr))"
    by blast
   show "  pre_compute_scores borda_score_mon A pl
       \<le> SPEC (\<lambda>scores. max_eliminator_ref scores A pl \<le> SPEC (\<lambda>x. x = max_eliminator borda_score A pr))"
     using precompborda  mid
       SPEC_cons_rule[where m = "pre_compute_scores borda_score_mon A pl" and
\<Psi> = "(\<lambda>scores. max_eliminator_ref scores A pl \<le> SPEC (\<lambda>x. x = max_eliminator borda_score A pr))"
  and \<Phi> = "(\<lambda> map. map = (pre_computed_map borda_score A pr))"]
     by blast
qed 


sepref_definition borda_elim_sepref is
  "uncurry borda_ref":: 
    "alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding borda_ref_def  max_eliminator_ref_def borda_score_mon.simps sum_impl_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
    prefer_count_monadic_imp_def[abs_def] is_less_preferred_than_mon_def[abs_def]
    rank_mon_def[abs_def] index_mon_def[abs_def]
    short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "RETURN ({}, {}, \<hole>)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ({}, \<hole>, _)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ( \<hole>, _, _)" hs.fold_custom_empty) 
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)
  apply sepref_dbg_keep
  done

lemmas borda_elim_sepref_correct [sepref_fr_rules]
  = borda_elim_sepref.refine[FCOMP borda_ref_correct]



end