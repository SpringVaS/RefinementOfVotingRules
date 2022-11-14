theory Profile_Sepref
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
    Counting_Functions_Code
    Refine_Imperative_HOL.IICF

begin

definition "ballot_rel A \<equiv> br pl_\<alpha> (ballot_on A)"


definition "ballot_assn A \<equiv> hr_comp (array_assn id_assn) (ballot_rel A)"

(*abbreviation "cand_assn \<equiv> nat_assn"*)


sepref_definition idx_imp is 
  "uncurry index_mon" :: "(array_assn id_assn)\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding index_mon_def index_mon_inv_def
  by sepref
 (*supply [[goals_limit = 1]]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep \<comment> \<open>(1) We get stuck at an equals operation\<close>
               apply sepref_dbg_trans_step_keep *)

 



(*export_code idx_imp in OCaml_imp module_name IndexCompute*)

thm idx_imp.refine

lemmas idx_imp_correct = idx_imp.refine[FCOMP index_mon_refine]

export_code idx_imp in Scala_imp

sepref_definition rank_imp is
  "uncurry rank_mon" :: "(array_assn nat_assn)\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn)"
  unfolding rank_mon_def[abs_def] index_mon_def[abs_def]
  by sepref

lemmas rank_imp_correct = rank_imp.refine[FCOMP rank_mon_refine]



definition "profile_rel A \<equiv> br pl_to_pr_\<alpha> (profile_l A)"

(*abbreviation "profile_impl_assn \<equiv> array_assn (array_assn nat_assn)"

definition "profile_assn A
    \<equiv> hr_comp profile_impl_assn (profile_rel A)"*)


sepref_definition win_count_imp_sep is
  "uncurry win_count_imp_array" :: "(array_assn (array_assn id_assn))\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn)"
  unfolding win_count_imp_array_def[abs_def] wc_list_invar_def[abs_def]  short_circuit_conv
  apply sepref_dbg_keep
  done

export_code win_count_imp_sep in Scala_imp


end