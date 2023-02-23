section \<open>Black's Rule\<close>

theory Blacks_Rule_Ref
  imports"Verified_Voting_Rule_Construction.Blacks_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Sequential_Composition_Ref"
begin


subsection \<open>Definition\<close>

sepref_definition blacks_rule_direct is "uncurry (seq_opt condorcet borda)"
  :: "elec_mod_sep_rel nat_assn"
  unfolding seq_opt_def
  apply sepref_dbg_keep
  done

lemmas opt_seq_blacks = seq_opt_correct[OF condorcet_sound borda_sound]
lemmas opt_blacks_correct_aux = blacks_rule_direct.refine[FCOMP opt_seq_blacks]

lemma blacks_direct_correct:
  shows "(uncurry blacks_rule_direct, uncurry (RETURN oo (blacks_rule:: (nat Electoral_Module))))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding blacks_rule.simps
  using  opt_blacks_correct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  by metis

declare opt_pmc_correct [sepref_fr_rules]


end
