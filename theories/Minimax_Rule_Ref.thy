(*  File:       Pairwise_Majority_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>


section \<open>Refined Pairwise Majority Rule\<close>

theory Minimax_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Minimax_Rule"
          "Compositional_Structures/Basic_Modules/Minimax_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

subsection \<open>Refinement to Imperative/HOL\<close>

sepref_definition minimax_rule_imp is 
  "uncurry (elector_opt ((minimax)))" :: "elec_mod_seprel nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

subsection \<open>Correctness\<close>


lemma minimax_rule_imp_correct:
  shows "(uncurry minimax_rule_imp, uncurry (RETURN 
    oo (minimax_rule:: (nat Electoral_Module))))
  \<in> elec_mod_seprel id_assn"
  using minimax_rule_imp.refine
  unfolding minimax_rule.simps elector_opt_eq
  .

declare minimax_rule_imp_correct [sepref_fr_rules]

subsection \<open>Properties in Separation Logic\<close>

theorem minimax_rule_imp_condorcet:
  shows "finite_profile A p \<and> condorcet_winner A p w \<Longrightarrow>
  <(alts_set_impl_assn nat_assn) A hs *
            (list_assn (ballot_assn nat_assn)) p hp> minimax_rule_imp hs hp 
  < \<lambda>r. \<exists>\<^sub>Ares. (result_impl_assn (nat_assn)) res r * 
    \<up> (res = ({w}, A - {w}, {})) >\<^sub>t"
  using minimax_rule_imp_correct[THEN hfrefD, THEN hn_refineD, of "(A, p)" "(hs, hp)"]
  apply (clarsimp simp del: condorcet_winner.simps minimax_rule.simps)
  apply (erule cons_rule[rotated -1])
  apply (sep_auto simp add : hn_ctxt_def pure_def simp del : condorcet_winner.simps minimax_rule.simps)
  apply (sep_auto simp add: hn_ctxt_def simp del : condorcet_winner.simps minimax_rule.simps)
  using minimax_condorcet condorcet_consistency3
  by (metis)

export_code clist convert_list_to_hash_set minimax_rule_imp in Scala_imp


end