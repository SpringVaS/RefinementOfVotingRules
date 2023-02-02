theory Condorcet_Module_Ref
  imports "Verified_Voting_Rule_Construction.Condorcet_Module"
           "Component_Types/Elimination_Module_Ref"
begin

definition condorcet_score_ref :: "'a Evaluation_Function_Ref" where
  "condorcet_score_ref x A p = do {
    is_x_cond_winner <- (condorcet_winner_monadic A p x);
    RETURN (if (is_x_cond_winner) then 1 else 0)}"


definition condorcet_ref :: "'a Electoral_Module_Ref" where
  "condorcet_ref A pl \<equiv> do {
   scores <- (pre_compute_scores condorcet_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma condorcet_score_ref_correct:
  fixes A:: "'a set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
    and profpropl: "profile_l A pl"
  shows "condorcet_score_ref x A pl \<le> SPEC (\<lambda> sc. sc = (condorcet_score x A pr))"
  unfolding condorcet_score_ref_def condorcet_score.simps
  apply (refine_vcg assms condorcet_winner_monadic_correct)
  by auto


context fixed_alts 

begin
sepref_definition condorcet_elim_sepref is
  "uncurry condorcet_ref":: 
  "alts_set_impl_assn\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding condorcet_ref_def  max_eliminator_ref_def condorcet_score_ref_def 
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
    condorcet_winner_monadic_def[abs_def]  wins_monadic_def[abs_def] prefer_count_monadic_imp_def
    is_less_preferred_than_mon_def[abs_def] rank_mon_def[abs_def] index_mon_def[abs_def]
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


theorem condorcet_ref_correct:
  shows "(condorcet_ref,  (RETURN oo condorcet)) \<in> 
  elec_mod_fixed_alts_rel"
proof (unfold condorcet_ref_def condorcet.simps, refine_vcg, auto simp only: in_br_conv set_rel_id prod_rel_id finite_set_rel_def,
    rule refine_IdI, unfold comp_apply SPEC_eq_is_RETURN(2)[symmetric] , rename_tac pl pr)
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume profrel: "(pl, pr) \<in> profile_on_A_rel Alts"
  assume fina: "finite Alts"
  from profrel have prel: "(pl, pr) \<in> profile_rel" using
      profile_type_ref by blast
  from profrel have profpl: "profile_l Alts pl" using profile_prop_list by blast
  from fina prel profpl  have 
  "\<forall>a\<in>Alts. condorcet_score_ref a Alts pl \<le> SPEC (\<lambda>score. score = condorcet_score a Alts pr)"
    using condorcet_score_ref_correct
    by metis
  from this prel fina  have  precompcond: "pre_compute_scores condorcet_score_ref Alts pl
  \<le> SPEC (\<lambda>map. map = pre_computed_map condorcet_score Alts pr)" using
    compute_scores_correct
    by blast
  note maxelim = max_eliminator_ref_correct[where efn = condorcet_score and A = Alts and pl = pl
      and pr = pr]
  from fina prel this have mid: "(\<And>x. x = pre_computed_map condorcet_score Alts pr \<Longrightarrow>
          max_eliminator_ref x Alts pl \<le> SPEC (\<lambda>x. x = max_eliminator condorcet_score Alts pr))"
    by blast
   show "pre_compute_scores condorcet_score_ref Alts pl \<bind> (\<lambda>scores. max_eliminator_ref scores Alts pl)
       \<le> SPEC (\<lambda>x. x = max_eliminator condorcet_score Alts pr)"
     unfolding comp_apply SPEC_eq_is_RETURN(2)[symmetric] 
     apply refine_vcg
     using precompcond  mid
       SPEC_cons_rule[where m = "pre_compute_scores condorcet_score_ref Alts pl" and
\<Psi> = "(\<lambda>scores. max_eliminator_ref scores Alts pl \<le> SPEC (\<lambda>x. x = max_eliminator condorcet_score Alts pr))"
  and \<Phi> = "(\<lambda> map. map = (pre_computed_map condorcet_score Alts pr))"]
     by blast 
qed 

term "(condorcet_ref,  (RETURN oo condorcet))"


lemmas cond_ref[sepref_fr_rules] = condorcet_elim_sepref.refine[FCOMP condorcet_ref_correct]

end

lemmas cond = fixed_alts.condorcet_ref_correct

end