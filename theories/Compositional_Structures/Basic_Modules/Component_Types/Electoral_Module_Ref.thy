theory Electoral_Module_Ref                      
  imports "Social_Choice_Types/Profile_Array"
          "Social_Choice_Types/Result_Ref"
          "Verified_Voting_Rule_Construction.Electoral_Module"
begin

type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> 'a Result"

definition electoral_module_r :: " 'a Electoral_Module_Ref \<Rightarrow> bool" where
  "electoral_module_r mr \<equiv> \<forall> A p. finite_profile_a A p \<longrightarrow> well_formed A (mr A p)"

(*lemma elec_mod_r_refine:
  "(Electoral_Module_Ref, Electoral_Module) \<in> Id \<rightarrow> (br pa_to_pr (profile_a A)) \<rightarrow> 
    (br res_\<alpha> (\<lambda> (e, r, d). ls.invar e \<and> ls.invar r \<and> ls.invar d))"
  apply (refine_rcg)
  apply (auto simp add: 
    ls.correct  refine_rel_defs)
  unfolding profile_a_def profile_l_def pa_to_pr_def pr1_\<alpha>.simps pl_\<alpha>_def 
proof 
  oops*)



(*definition em_\<alpha> :: "'a Electoral_Module_Ref  \<Rightarrow> 
   'a Electoral_Module" where
  "em_\<alpha> mr = (\<lambda> A p. (res_\<alpha> (mr A (p))))"*)

end