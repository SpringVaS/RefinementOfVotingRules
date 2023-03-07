theory Pairwise_Majority_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Pairwise_Majority_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin


sepref_definition pairwise_majority_rule_direct is "uncurry (elector_opt (RETURN oo condorcet))"
  :: "elec_mod_sep_rel nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

lemmas opt_seq_pmc = elector_opt_correct[of condorcet]
lemmas opt_seq_pmct_aux = pairwise_majority_rule_direct.refine[FCOMP opt_seq_pmc]

lemma opt_pmc_correct:
  shows "(uncurry pairwise_majority_rule_direct, 
          uncurry (RETURN oo (pairwise_majority_rule:: (nat Electoral_Module))))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding pairwise_majority_rule.simps
  using  condorcet_sound opt_seq_pmct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  by metis

declare opt_pmc_correct [sepref_fr_rules]


export_code clist convert_list_to_hash_set pairwise_majority_rule_direct in Scala_imp

end