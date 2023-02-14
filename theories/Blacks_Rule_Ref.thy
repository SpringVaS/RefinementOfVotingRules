section \<open>Black's Rule\<close>

theory Blacks_Rule_Ref
  imports"Verified_Voting_Rule_Construction.Blacks_Rule"
          Pairwise_Majority_Rule_Ref
          Borda_Rule_Ref
begin


subsection \<open>Definition\<close>

definition blacks_rule_sep where
  "blacks_rule_sep \<equiv> (pairwise_majority_rule_sep) \<triangleright>sep borda_rule_sep"


end
