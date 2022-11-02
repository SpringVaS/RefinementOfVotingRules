theory Profile_Sepref
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
    Counting_Functions_Code
    Refine_Imperative_HOL.IICF

begin

definition profile_invar :: "'a Profile_List \<Rightarrow> bool " where
    "profile_invar \<equiv> (profile_l (A::'a set))"

abbreviation "profile_rel \<equiv> br pl_to_pr_\<alpha> (profile_l A)"

abbreviation "profile_assn \<equiv> array_assn (array_assn id_assn)"

definition index_mon_imp

end