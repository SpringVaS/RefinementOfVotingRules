theory Electoral_Module_Ref                      
  imports "Verified_Voting_Rule_Construction.Profile_List"
          "Social_Choice_Types/Result_Ref"
          "Verified_Voting_Rule_Construction.Electoral_Module"
           Refine_Imperative_HOL.IICF
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

definition electoral_module_r :: " 'a Electoral_Module_Ref \<Rightarrow> bool" where
  "electoral_module_r mr \<equiv> \<forall> A pa. well_formed A (mr A pa)"

lemma em_corres:
  fixes A :: "'a set" and pa :: "'a Profile_List"
  assumes "(em_r, em) \<in> (Id \<rightarrow> (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> Id)" 
      and " (profile_l A pa)"
  shows "(em_r A pa) = (em A (pl_to_pr_\<alpha> pa))"
using assms proof (-)
  assume p: "profile_l A pa"
  assume "(em_r, em) \<in> Id \<rightarrow> br pl_to_pr_\<alpha> (profile_l A) \<rightarrow> Id"
  from p this show "em_r A pa = em A (pl_to_pr_\<alpha> pa)"
    by (metis (no_types, opaque_lifting) in_br_conv pair_in_Id_conv tagged_fun_relD_none)
qed

lemma em_onA:
  fixes A :: "'a set" 
  assumes "(em_r A, em A) \<in> (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> Id" 
    and " (profile_l A pa)"
  shows "(em_r A pa) = (em A (pl_to_pr_\<alpha> pa))"
  by (metis assms(1) assms(2) brI pair_in_Id_conv tagged_fun_relD_rhs)


type_synonym 'a Electoral_Module_SepRef = "nat set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result"
end