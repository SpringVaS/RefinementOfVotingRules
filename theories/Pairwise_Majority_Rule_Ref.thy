(*  File:       Pairwise_Majority_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>


section \<open>Refined Pairwise Majority Rule\<close>

theory Pairwise_Majority_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Pairwise_Majority_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

subsection \<open>Refinement to Imperative/HOL\<close>

sepref_definition pairwise_majority_rule_direct_imp is 
  "uncurry (elector_opt ((condorcet)))" :: "elec_mod_seprel nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  by sepref

subsection \<open>Correctness\<close>


lemma opt_pmc_correct:
  shows "(uncurry pairwise_majority_rule_direct_imp, uncurry (RETURN 
    oo (pairwise_majority_rule:: (nat Electoral_Module))))
  \<in> elec_mod_seprel nat_assn"
  using pairwise_majority_rule_direct_imp.refine
  unfolding pairwise_majority_rule.simps elector_opt_eq
  .

declare opt_pmc_correct [sepref_fr_rules]

subsection \<open>Properties in Separation Logic\<close>

theorem pmc_impl_condorcet:
  shows "finite_profile A p \<and> condorcet_winner A p w \<Longrightarrow>
  <(alts_set_impl_assn nat_assn) A hs *
            (list_assn (ballot_assn nat_assn)) p hp> pairwise_majority_rule_direct_imp hs hp 
  < \<lambda>r. \<exists>\<^sub>Ares. (result_impl_assn (nat_assn)) res r * 
    \<up> (res = ({w}, A - {w}, {})) >\<^sub>t"
  using opt_pmc_correct[THEN hfrefD, THEN hn_refineD, of "(A, p)" "(hs, hp)"]
  apply (clarsimp simp del: condorcet_winner.simps pairwise_majority_rule.simps)
  apply (erule cons_rule[rotated -1])
  apply (sep_auto simp add : hn_ctxt_def pure_def simp del : condorcet_winner.simps pairwise_majority_rule.simps)
  apply (sep_auto simp add: hn_ctxt_def simp del : condorcet_winner.simps pairwise_majority_rule.simps)
  using condorcet_condorcet condorcet_consistency_3
  by (metis)

export_code clist convert_list_to_hash_set pairwise_majority_rule_direct_imp in Scala_imp


end