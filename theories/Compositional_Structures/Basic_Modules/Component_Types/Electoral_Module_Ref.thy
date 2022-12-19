theory Electoral_Module_Ref                      
  imports "Verified_Voting_Rule_Construction.Profile_List"
          "Social_Choice_Types/RefinementList"
          "Verified_Voting_Rule_Construction.Electoral_Module"
           Refine_Imperative_HOL.IICF
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

locale voting_session =
  fixes A:: "'a set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A" and 
    nempa: "A \<noteq> {}" (* This precondition is necessary to refine Elimination Modules
                      that use Min/Max set operators *) 
    and profrel: "(pl, pr) \<in> profile_on_A_rel A"

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


end