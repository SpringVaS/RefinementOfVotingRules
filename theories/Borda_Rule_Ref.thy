theory Borda_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

definition borda_rule_sep where
  "borda_rule_sep A p \<equiv> elector_sep borda_elim_sepref (A, p)"


end