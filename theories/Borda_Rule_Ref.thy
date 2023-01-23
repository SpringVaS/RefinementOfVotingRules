theory Borda_Rule_Ref         
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

definition borda_rule_ref :: "'a Electoral_Module_Ref" where
  "borda_rule_ref A p \<equiv> elector_ref borda_monadic A p"


end