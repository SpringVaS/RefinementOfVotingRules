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

definition elect_ref ::
  "nat set \<Rightarrow> nat Profile_List \<Rightarrow> nat set nres" where
  "elect_ref A p \<equiv> do {
    result <- mod1 A p;
    RETURN (elect_r result)}
  "

lemma elect_monadic_refine:
  fixes em:: "nat Electoral_Module"
  assumes "(mod1,(\<lambda> A p. SPEC (\<lambda> rem. rem = em A p))) \<in> elec_mod_relb"
  shows "(elect_ref, (\<lambda> A p. SPEC (\<lambda> rem. rem = (elect em A p)))) \<in> 
    \<langle>nat_rel\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>nat_rel\<rangle>alt_set_rel\<rangle>nres_rel"
  unfolding elect_ref_def
proof (refine_vcg, rename_tac A' A pl pr)
   fix A' A:: "nat set"
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume arel: "(A', A) \<in> \<langle>nat_rel\<rangle>alt_set_rel"
  assume prel: " (pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  note assms[THEN fun_relD,THEN fun_relD, THEN nres_relD, where x2 = A' and x'2 = A
      and x1 = pl and x'1 = pr]
  from this have "  mod1 A' pl
  \<le>  (SPEC (\<lambda>rem. rem = em A pr)) " using refine_IdD prod_rel_id set_rel_id
    using arel prel by fastforce  
  from this arel prel  show " mod1 A' pl \<bind> (\<lambda>result. RETURN (elect_r result))
       \<le> \<Down> (\<langle>nat_rel\<rangle>alt_set_rel) (SPEC (\<lambda>rem. rem = elect em A pr))"
    using specify_left
    sorry
qed
  


sepref_register "mod1" :: "nat Electoral_Module_Ref"

declare mod1_impl [sepref_fr_rules]

schematic_goal elect_impl:
  "(uncurry ?c, uncurry elect_ref) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_ref_def
  by sepref

concrete_definition (in -) elect_sep uses sepref_access.elect_impl
  prepare_code_thms (in -) elect_sep_def
  lemmas elect_impl_refine = elect_sep.refine[OF this_loc]

end

term "sepref_access.elect_ref"

end