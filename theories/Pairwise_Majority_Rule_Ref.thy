theory Pairwise_Majority_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Pairwise_Majority_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

definition pairwise_majority_rule_sep where
  "pairwise_majority_rule_sep \<equiv> elector_sep condorcet_elim_sep"


interpretation pairwise_majority_rule_impl: 
    elector_sepref condorcet_ref condorcet_elim_sep condorcet
  apply unfold_locales
  subgoal using condorcet_elim_sep.refine .
  subgoal using condorcet_sound .
  subgoal apply (intro frefI) using condorcet_ref_correct[THEN frefD] by auto
  done

lemma  pairwise_majority_rule_correct [sepref_fr_rules]:
  shows "(uncurry pairwise_majority_rule_sep, uncurry (RETURN oo pairwise_majority_rule))
   \<in> [\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn id_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn id_assn"
  unfolding pairwise_majority_rule_sep_def pairwise_majority_rule.simps 
    using pairwise_majority_rule_impl.elector_sep_correct .

sepref_definition pairwise_majority_rule_direct is "uncurry (seq_opt condorcet elect_module
  )"
  :: "elec_mod_sep_rel nat_assn"
  unfolding seq_opt_def
  apply sepref_dbg_keep
  done

lemmas opt_seq_pmc = seq_opt_correct[OF condorcet_sound elect_mod_sound]
lemmas opt_seq_pmct_aux = pairwise_majority_rule_direct.refine[FCOMP opt_seq_pmc]

lemma opt_pmc_correct:
  shows "(uncurry pairwise_majority_rule_direct, uncurry (RETURN oo (pairwise_majority_rule:: (nat Electoral_Module))))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding pairwise_majority_rule.simps elector.simps 
  using  opt_seq_pmct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  by metis


export_code clist convert_list_to_hash_set pairwise_majority_rule_direct in Scala_imp

end