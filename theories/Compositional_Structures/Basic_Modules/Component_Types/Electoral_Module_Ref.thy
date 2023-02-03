theory Electoral_Module_Ref                      
  imports "Social_Choice_Types/Profile_List_Monadic"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_rel_orig :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result)) set" where
  "elec_mod_rel_orig R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_rel_orig_nres :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres) \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_rel_orig_nres R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_rel_ref :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result) \<times> ('a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result)) set" where
  "elec_mod_rel_ref R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel , 
  \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_data_rel :: "('a \<times> 'a) set \<Rightarrow> 
('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_data_rel R \<equiv> \<langle>R\<rangle>finite_set_rel \<rightarrow> profile_rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel"

definition em_prof_nres ::
  "('a \<times> 'a) set \<Rightarrow> ('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result)) set"
  where em_prof_nres_internal_def: "em_prof_nres R \<equiv> 
  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,RETURN(em A pr)) \<in> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel}"

lemma em_prof_nres_def[refine_rel_defs]: 
  "\<langle>R\<rangle>em_prof_nres \<equiv>  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,RETURN(em A pr)) \<in> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel}"
  by (simp add: em_prof_nres_internal_def relAPP_def)



definition aux_set_copy :: "'a set \<Rightarrow> 'a set nres" where
  "aux_set_copy A \<equiv>  FOREACH A
     (\<lambda> x cp. RETURN (insert x cp)) {}"

lemma aux_set_copy_correct:
  fixes A :: "'a set"
  assumes fina: "finite A"
  shows "aux_set_copy A \<le> SPEC(\<lambda> set. set = A)"
  unfolding aux_set_copy_def
  apply (refine_vcg FOREACH_rule[where I = "\<lambda>it s. s = A - it"])
  by (auto simp add: fina)



definition elect_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a set nres" where
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


lemma elect_monadic_correct_aux:
  fixes A :: "'a set"
  and emref :: "'a Electoral_Module_Ref"
  and em :: "'a Electoral_Module"
  assumes emrefc: "emref A pl \<le> SPEC (\<lambda> res. res = em A pr)"
  shows "elect_monadic emref A pl \<le> SPEC (\<lambda> es. es = (elect em A pr))"
  unfolding elect_monadic_def
  apply refine_vcg
  unfolding SPEC_eq_is_RETURN(2)[symmetric]
  using emrefc
  by (simp add: SPEC_trans) 

lemma elect_monadic_correct_unin:
  fixes alt_rel :: "('a set \<times> 'a set) set"
  and profrel :: "('a Profile_List \<times> 'a Profile) set"
  and R :: "('a \<times> 'a) set"
  and emref :: "'a Electoral_Module_Ref"
  and em :: "'a Electoral_Module"
  (*assumes emrefc: "(emref, RETURN oo em) \<in> alt_rel \<rightarrow> profrel 
                                    \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r\<langle>Id\<rangle>set_rel\<rangle>nres_rel"*)
  shows "(elect_monadic, RETURN ooo (elect)) \<in>
    {(emref, em).(emref, RETURN oo em) \<in> alt_rel \<rightarrow> profrel 
                                    \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r\<langle>Id\<rangle>set_rel\<rangle>nres_rel } \<rightarrow>
   alt_rel \<rightarrow> profrel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding elect_monadic_def comp_apply
proof (refine_vcg, clarsimp, rename_tac emref em A' A pl pr)
  fix A' A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix emref :: "'a Electoral_Module_Ref"
  fix em :: "'a Electoral_Module"
  assume arel: "(A', A) \<in> alt_rel"
  assume prel: "(pl, pr) \<in> profrel"
  assume emrefc : "(emref, \<lambda>x xa. RETURN (em x xa)) \<in> alt_rel \<rightarrow> profrel \<rightarrow> \<langle>Id\<rangle>nres_rel "
  from arel prel have "emref A' pl \<le> SPEC (\<lambda> res. res = em A pr)"
    using emrefc[THEN fun_relD, THEN fun_relD, THEN nres_relD] 
    unfolding comp_apply SPEC_eq_is_RETURN(2)[symmetric] 
    by simp
  from this show " emref A' pl \<le> SPEC (\<lambda>result. elect_r result = elect em A pr)"
    using order.trans by fastforce
qed
    


locale set_select_imp = 
  fixes mod1_ref :: "nat Electoral_Module_Ref"
  fixes mod1_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    mod1_impl: "(uncurry mod1_impl, uncurry mod1_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"
begin

lemma this_loc: "set_select_imp  mod1_ref mod1_impl" by unfold_locales

sepref_register "mod1_ref" :: "'a Electoral_Module_Ref"

declare mod1_impl [sepref_fr_rules]

sepref_definition  "elect_sep" is
 "uncurry (elect_monadic mod1_ref)" 
:: "(alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_monadic_def
  apply sepref_dbg_keep
  done

concrete_definition (in -) elect_sepi uses set_select_imp.elect_sep_def
  prepare_code_thms (in -) "elect_sepi_def"
  lemmas elect_sepi_refine = elect_sepi.refine[OF this_loc]

schematic_goal defer_impl:
  "(uncurry ?c, uncurry (defer_monadic mod1_ref)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding defer_monadic_def
  by sepref

concrete_definition (in -) defer_sep uses set_select_imp.defer_impl
  prepare_code_thms (in -) "defer_sep_def"
  lemmas defer_impl_refine = defer_sep.refine[OF this_loc]

schematic_goal reject_impl:
  "(uncurry ?c, uncurry (reject_monadic mod1_ref)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k 
      \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding reject_monadic_def
  by sepref

concrete_definition (in -) reject_sep uses set_select_imp.reject_impl
  prepare_code_thms (in -) reject_sep_def
  lemmas reject_impl_refine = reject_sep.refine[OF this_loc]

end

end