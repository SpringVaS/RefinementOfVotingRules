theory Profile_Sepref
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
    Counting_Functions_Code
    Refine_Imperative_HOL.IICF

begin

definition "ballot_rel A \<equiv> br pl_\<alpha> (ballot_on A)"


definition "ballot_assn A \<equiv> hr_comp (array_assn id_assn) (ballot_rel A)"

sepref_definition idx_imp is 
  "uncurry index_mon" :: "(array_assn nat_assn)\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding index_mon_def[abs_def] index_mon_inv_def[abs_def]
  apply (sepref_dbg_keep)
  supply [[goals_limit=1]] \<comment> \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
      apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep

  by sepref
  


definition "profile_rel A \<equiv> br pl_to_pr_\<alpha> (profile_l A)"



abbreviation "profile_impl_assn \<equiv> array_assn (array_assn id_assn)"

definition "profile_assn A
    \<equiv> hr_comp profile_impl_assn (profile_rel A)"

end