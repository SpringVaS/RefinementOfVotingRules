theory Electoral_Module_Ref                      
  imports "Social_Choice_Types/Profile_List_Monadic"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

abbreviation elec_mod_rel_orig :: "('a \<times> 'a) set \<Rightarrow> 
  ('a Electoral_Module \<times> 'a Electoral_Module) set" where
  "elec_mod_rel_orig R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_rel_orig_nres :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres) \<times> ('a::{default, linorder, heap, hashable} set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_rel_orig_nres R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_rel_ref :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result) \<times> ('a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result)) set" where
  "elec_mod_rel_ref R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel , 
  \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_data_rel :: "('a \<times> 'a) set \<Rightarrow> 
('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_data_rel R \<equiv> \<langle>R\<rangle>set_rel \<rightarrow> profile_rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel"

(*definition em_prof_nres ::
  "('a \<times> 'a) set \<Rightarrow> ('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result)) set"
  where em_prof_nres_internal_def: "em_prof_nres R \<equiv> 
  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,RETURN(em A pr)) \<in> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel}"

lemma em_prof_nres_def[refine_rel_defs]: 
  "\<langle>R\<rangle>em_prof_nres \<equiv>  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,RETURN(em A pr)) \<in> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel}"
  by (simp add: em_prof_nres_internal_def relAPP_def)*)





definition elect_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a set nres" where
  "elect_monadic m A p \<equiv> do {
    (mel, mrej, mdef) <- m A p;
    RETURN (mel)
  }"

definition defer_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a  Profile_List \<Rightarrow> 'a set nres" where
  "defer_monadic m A p \<equiv> do {
    (mel, mrej, mdef) <- m A p;
    RETURN (mrej)
  }"

definition reject_monadic ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a set \<Rightarrow> 'a  Profile_List \<Rightarrow> 'a set nres" where
  "reject_monadic m A p \<equiv> do {
    (mel, mrej, mdef) <- m A p;
    RETURN (mdef)
  }"


lemma elect_monadic_correct_aux:
  fixes A :: "'a set"
  and emref :: "'a Electoral_Module_Ref"
  and em :: "'a Electoral_Module"
  assumes emrefc: "emref A pl \<le> SPEC (\<lambda> res. res = em A pr)"
  shows "elect_monadic emref A pl \<le> SPEC (\<lambda> es. es = (elect em A pr))"
  unfolding elect_monadic_def
  apply refine_vcg
  using emrefc unfolding
RETURN_SPEC_conv[symmetric]  using  SPEC_trans  case_prod_beta'
  by (metis (mono_tags) RETURN_rule order_class.order_eq_iff)

  

lemma elect_monadic_correct:
  fixes emref :: "'a Electoral_Module_Ref"
  and em :: "'a Electoral_Module"
  assumes emrefc: "(uncurry emref, uncurry (RETURN oo em)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
  shows "(uncurry (elect_monadic emref), uncurry (RETURN oo (elect em))) \<in>
    ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
  unfolding elect_monadic_def comp_apply
proof (intro frefI, clarsimp, refine_vcg, rename_tac A pl pr)
  fix A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profa: "profile A pr"
  have " emref A pl \<le> RETURN (em A pr)"
    using fina prel profa emrefc[THEN frefD, THEN nres_relD] by auto
  thus "emref A pl
       \<le> SPEC (\<lambda>x. (case x of (mel, mrej, mdef) \<Rightarrow> RETURN mel) \<le> SPEC (\<lambda>c. (c, elect em A pr) \<in> Id))"
     using emrefc unfolding
       RETURN_SPEC_conv[symmetric]  using  SPEC_trans  case_prod_beta' IdI RETURN_rule
     by (metis (no_types, lifting) )
 
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