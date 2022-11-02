theory Electoral_Module_Ref                      
  imports "Social_Choice_Types/Profile_Array"
          "Social_Choice_Types/Result_Ref"
          "Verified_Voting_Rule_Construction.Electoral_Module"
begin                            

type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> 'a Result"

definition electoral_module_r :: " 'a Electoral_Module_Ref \<Rightarrow> bool" where
  "electoral_module_r mr \<equiv> \<forall> A pa. finite_profile_a A pa \<longrightarrow> well_formed A (mr A pa)"

lemma em_corres:
  fixes A :: "'a set" and pa :: "'a Profile_Array"
  assumes "(em_r, em) \<in> (Id \<rightarrow> (br pa_to_pr (profile_a A)) \<rightarrow> Id)" 
      and " (profile_a A pa)"
  shows "(em_r A pa) = (em A (pa_to_pr pa))"
using assms proof (-)
  assume p: "profile_a A pa"
  assume "(em_r, em) \<in> Id \<rightarrow> br pa_to_pr (profile_a A) \<rightarrow> Id"
  from p this show "em_r A pa = em A (pa_to_pr pa)"
    by (metis (no_types, opaque_lifting) in_br_conv pair_in_Id_conv tagged_fun_relD_none)
qed

lemma em_onA:
  fixes A :: "'a set" 
  assumes "(em_r A, em A) \<in> (br pa_to_pr (profile_a A)) \<rightarrow> Id" 
    and " (profile_a A pa)"
  shows "(em_r A pa) = (em A (pa_to_pr pa))"
  by (metis assms(1) assms(2) brI pair_in_Id_conv tagged_fun_relD_rhs)

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