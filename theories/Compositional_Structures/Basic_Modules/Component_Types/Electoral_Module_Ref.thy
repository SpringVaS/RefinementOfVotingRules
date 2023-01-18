theory Electoral_Module_Ref                      
  imports "Social_Choice_Types/Profile_List_Monadic"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_relb :: "('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_relb \<equiv> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel 
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"

definition em_rel :: "('a Electoral_Module_Ref \<times> 'a Electoral_Module) set" 
  where em_rel_def:
  "em_rel \<equiv> {(emref,em).(emref, (\<lambda> A pro. SPEC (\<lambda> res. res = (em A pro)))) 
  \<in> elec_mod_relb}"

abbreviation "ballot_impl_assn \<equiv> (arl_assn nat_assn)"

abbreviation "profile_impl_assn \<equiv> (list_assn ballot_impl_assn)"

abbreviation "alts_set_impl_assn \<equiv> (hs.assn nat_assn)"

abbreviation "result_impl_assn \<equiv> alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn"

definition "alts_assn \<equiv> hr_comp alts_set_impl_assn (\<langle>nat_rel\<rangle>alt_set_rel)"

definition "ballot_assn \<equiv> (hr_comp ballot_impl_assn ballot_rel)"

definition "profile_assn \<equiv> (list_assn ballot_assn)"

abbreviation "result_assn \<equiv> alts_assn \<times>\<^sub>a
                              alts_assn \<times>\<^sub>a
                               alts_assn"

definition elect_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a  Profile_List \<Rightarrow> 'a set nres" where
  "elect_monadic m A p \<equiv> do {
    result <- m A p;
    RETURN (elect_r result)
  }"

definition defer_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a  Profile_List \<Rightarrow> 'a set nres" where
  "defer_monadic m A p \<equiv> do {
    result <- m A p;
    RETURN (defer_r result)
  }"

definition reject_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a  Profile_List \<Rightarrow> 'a set nres" where
  "reject_monadic m A p \<equiv> do {
    result <- m A p;
    RETURN (reject_r result)
  }"


lemma elect_check_correct:
shows "(elect_monadic, (\<lambda> e A p. SPEC (\<lambda> rem. rem = (elect e A p)))) \<in> 
    em_rel \<rightarrow> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>Id\<rangle>alt_set_rel\<rangle>nres_rel"
  apply (refine_rcg)
  unfolding elect_monadic_def em_rel_def
  apply clarify
  oops

locale sepref_access =
  fixes mod1 :: "nat Electoral_Module_Ref"
  fixes mod1_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    mod1_impl: "(uncurry mod1_impl, uncurry mod1)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "sepref_access mod1 mod1_impl" by unfold_locales


sepref_register "mod1" :: "nat Electoral_Module_Ref"

declare mod1_impl [sepref_fr_rules]

schematic_goal elect_impl:
  "(uncurry ?c, uncurry (elect_monadic mod1)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_monadic_def
  by sepref

concrete_definition (in -) elect_sep uses sepref_access.elect_impl
  prepare_code_thms (in -) elect_sep_def
lemmas elect_impl_refine = elect_sep.refine[OF this_loc]

schematic_goal defer_impl:
  "(uncurry ?c, uncurry (defer_monadic mod1)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding defer_monadic_def
  by sepref

concrete_definition (in -) defer_sep uses sepref_access.defer_impl
  prepare_code_thms (in -) defer_sep_def
  lemmas defer_impl_refine = defer_sep.refine[OF this_loc]

schematic_goal reject_impl:
  "(uncurry ?c, uncurry (reject_monadic mod1)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding reject_monadic_def
  by sepref

concrete_definition (in -) reject_sep uses sepref_access.reject_impl
  prepare_code_thms (in -) reject_sep_def
  lemmas reject_impl_refine = reject_sep.refine[OF this_loc]


end

thm "elect_sep_def"
thm "elect_sep.refine"

end