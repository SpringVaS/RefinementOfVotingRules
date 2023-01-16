theory Electoral_Module_Ref                      
  imports "Verified_Voting_Rule_Construction.Profile_List"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
           Refine_Imperative_HOL.IICF
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_relb :: "('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_relb \<equiv> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"

definition em_rel :: "('a Electoral_Module_Ref \<times> 'a Electoral_Module) set" 
  where em_rel_def:
  "em_rel \<equiv> {(emref,em).(emref, (\<lambda> A pro. SPEC (\<lambda> res. res = (em A pro)))) 
  \<in> elec_mod_relb}"

end