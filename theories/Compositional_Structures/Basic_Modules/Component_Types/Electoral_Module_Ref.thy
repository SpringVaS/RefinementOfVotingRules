theory Electoral_Module_Ref                      
  imports "Verified_Voting_Rule_Construction.Profile_List"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
           Refine_Imperative_HOL.IICF
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_relb :: "('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_relb \<equiv> Id \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"

abbreviation  "elec_mod_rel \<equiv> \<langle>\<langle>\<langle>Id\<rangle>set_rel, profile_rel\<rangle>fun_rel, \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel\<rangle>fun_rel"


end