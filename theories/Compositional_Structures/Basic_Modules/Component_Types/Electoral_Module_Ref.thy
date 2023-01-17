theory Electoral_Module_Ref                      
  imports "Verified_Voting_Rule_Construction.Profile_List"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
           Refine_Imperative_HOL.IICF
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_relb :: "('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_relb \<equiv> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel 
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"

definition em_rel :: "('a Electoral_Module_Ref \<times> 'a Electoral_Module) set" 
  where em_rel_def:
  "em_rel \<equiv> {(emref,em).(emref, (\<lambda> A pro. SPEC (\<lambda> res. res = (em A pro)))) 
  \<in> elec_mod_relb}"


definition elect_ref ::
  "'a Result \<Rightarrow> 'a set nres" where
  "elect_ref result \<equiv> do {
    RETURN (elect_r (result))}
  "

abbreviation "profile_impl_assn \<equiv> (list_assn (arl_assn nat_assn))"

abbreviation "alts_set_impl_assn \<equiv> (hs.assn nat_assn)"

abbreviation "result_impl_assn \<equiv> alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn"

definition "alts_assn \<equiv> hr_comp (hs.assn nat_assn) (\<langle>nat_rel\<rangle>alt_set_rel)"

definition "profile_assn \<equiv> (list_assn (hr_comp (list_assn nat_assn) ballot_rel))"

abbreviation "result_assn \<equiv> hr_comp (hs.assn nat_assn) (\<langle>nat_rel\<rangle>set_rel) \<times>\<^sub>a
                               hr_comp (hs.assn nat_assn) (\<langle>nat_rel\<rangle>set_rel) \<times>\<^sub>a
                               hr_comp (hs.assn nat_assn) (\<langle>nat_rel\<rangle>set_rel)"


sepref_definition elect_sepref is 
  "elect_ref" :: 
   "(result_impl_assn)\<^sup>d \<rightarrow>\<^sub>a (hs.assn nat_assn)"
  unfolding elect_ref_def
  apply sepref_dbg_keep
  done


end