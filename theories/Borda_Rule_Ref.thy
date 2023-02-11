theory Borda_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

definition borda_rule_sep where
  "borda_rule_sep A p \<equiv> elector_sep borda_elim_sep (A, p)"

interpretation borda_rule_impl: elector_ref borda_ref borda_elim_sep borda
  apply unfold_locales
  subgoal using borda_elim_sep.refine .
  subgoal using borda_sound .
  subgoal apply (intro frefI) using borda_ref_correct[THEN frefD] by auto
  done

lemmas borda_rule_correct = borda_rule_impl.elector_sep_correct

end