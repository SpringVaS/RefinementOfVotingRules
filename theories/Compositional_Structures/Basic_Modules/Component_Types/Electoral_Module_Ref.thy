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

abbreviation elec_mod_relb :: "('a \<times> 'a) set \<Rightarrow> 
('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" where
  "elec_mod_relb R \<equiv> \<langle>R\<rangle>finite_set_rel \<rightarrow> profile_rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel"

abbreviation
jopoiodo :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>
('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set" 
where "jopoiodo R A' \<equiv> \<langle>R\<rangle>finite_set_rel \<rightarrow> (profile_on_A_rel A')
  \<rightarrow> \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel" 

definition em_prof_nres ::
  "('a \<times> 'a) set \<Rightarrow> ('a Electoral_Module_Ref \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)) set"
  where em_prof_nres_internal_def: "em_prof_nres R \<equiv> 
  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,em A pr) \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel}"

lemma em_prof_nres_def[refine_rel_defs]: 
  "\<langle>R\<rangle>em_prof_nres \<equiv>  {(emref, em). \<forall> (A', A) \<in> \<langle>R\<rangle>finite_set_rel.
  \<forall> (pl, pr) \<in> profile_on_A_rel (A').
   (emref A' pl ,em A pr) \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel}"
  by (simp add: em_prof_nres_internal_def relAPP_def)

abbreviation elec_mod_relb_prof ::
    "('a \<times> 'a) set
     \<Rightarrow> (('a set \<times> 'a list list \<Rightarrow> ('a set \<times> 'a set \<times> 'a set) nres) \<times>
         ('a set \<times> ('a \<times> 'a) set list \<Rightarrow> ('a set \<times> 'a set \<times> 'a set) nres)) set"
 where "elec_mod_relb_prof R \<equiv> \<langle>\<langle>R\<rangle>alt_and_profile_rel,
 \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel\<rangle>fun_rel"

lemma weak_ref_correct:
  assumes "(emref, RETURN oo em) \<in> elec_mod_relb Id"
  shows "(uncurry emref, uncurry (RETURN oo em)) \<in> elec_mod_relb_prof Id"
proof (clarsimp, rename_tac A' pl A pr, rule nres_relI)
   fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume arel: "((A', pl), A,pr) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  from arel have altrel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel " using unfold_alt_profile_alt_rel
    by blast
  from arel have prel: "(pl, pr) \<in> profile_rel " using unfold_alt_profile_prof_rel
    by blast
  from altrel prel show "emref A' pl \<le> \<Down> Id (RETURN (em A pr))"
    using assms[THEN fun_relD, THEN fun_relD, THEN nres_relD] unfolding comp_apply
    by simp
qed

definition em_rel :: "('a \<times> 'a) set \<Rightarrow> ('a Electoral_Module_Ref \<times> 'a Electoral_Module) set" 
  where em_rel_internal_def:
  "em_rel R \<equiv> {(emref,em).(emref, RETURN oo em) 
  \<in> elec_mod_relb R}"

lemma em_rel_def[refine_rel_defs]:
  "\<langle>R\<rangle>em_rel \<equiv> {(emref,em).(emref, RETURN oo em) 
  \<in> elec_mod_relb R}"
  by (simp add: em_rel_internal_def relAPP_def)

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


lemma elect_monadic_correct:
shows "(elect_monadic, RETURN ooo elect) \<in> 
    \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (unfold elect_monadic_def em_rel_def, refine_rcg, clarsimp, 
        rename_tac emref em A' A pl pr)
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix emref :: "'a Electoral_Module_Ref"
  fix em :: "'a Electoral_Module"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume emrel: "(emref, RETURN \<circ>\<circ> em) \<in> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel prel emrel[THEN fun_relD,THEN fun_relD,THEN nres_relD, THEN refine_IdD] 
  have "emref A' pl \<le> SPEC (\<lambda> res. res = em A pr)" using SPEC_eq_is_RETURN(2) comp_apply 
    by metis
  from this show " emref A' pl \<bind> (\<lambda>result. RETURN (elect_r result)) \<le> RETURN (elect em A pr)"
    using specify_left[where m = "emref A' pl" and \<Phi> = "\<lambda> res. res = (em A pr)"]
    by fastforce
qed


lemma defer_monadic_correct:
shows "(defer_monadic, RETURN ooo defer) \<in> 
    \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (unfold defer_monadic_def em_rel_def, refine_rcg, clarsimp, 
        rename_tac emref em A' A pl pr)
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix emref :: "'a Electoral_Module_Ref"
  fix em :: "'a Electoral_Module"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume emrel: "(emref, RETURN \<circ>\<circ> em) \<in> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel prel emrel[THEN fun_relD,THEN fun_relD,THEN nres_relD, THEN refine_IdD] 
  have "emref A' pl \<le> SPEC (\<lambda> res. res = em A pr)" using SPEC_eq_is_RETURN(2) comp_apply 
    by metis
  from this show " emref A' pl \<bind> (\<lambda>result. RETURN (defer_r result)) \<le> RETURN (defer em A pr)"
    using specify_left[where m = "emref A' pl" and \<Phi> = "\<lambda> res. res = (em A pr)"]
    by fastforce
qed

lemma reject_monadic_correct:
shows "(reject_monadic, RETURN ooo reject) \<in> 
    \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (unfold reject_monadic_def em_rel_def, refine_rcg, clarsimp, 
        rename_tac emref em A' A pl pr)
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix emref :: "'a Electoral_Module_Ref"
  fix em :: "'a Electoral_Module"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume emrel: "(emref, RETURN \<circ>\<circ> em) \<in> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel prel emrel[THEN fun_relD,THEN fun_relD,THEN nres_relD, THEN refine_IdD] 
  have "emref A' pl \<le> SPEC (\<lambda> res. res = em A pr)" using SPEC_eq_is_RETURN(2) comp_apply 
    by metis
  from this show " emref A' pl \<bind> (\<lambda>result. RETURN (reject_r result)) \<le> RETURN (reject em A pr)"
    using specify_left[where m = "emref A' pl" and \<Phi> = "\<lambda> res. res = (em A pr)"]
    by fastforce
qed




locale set_select_imp =
  fixes mod1 :: "nat Electoral_Module"       
  fixes mod1_ref :: "nat Electoral_Module_Ref"
  fixes mod1_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    mod1_refine: "(mod1_ref, mod1) \<in> \<langle>nat_rel\<rangle>em_rel" and
    mod1_impl: "(uncurry mod1_impl, uncurry mod1_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "set_select_imp mod1 mod1_ref mod1_impl" by unfold_locales


sepref_register "mod1_ref" :: "nat Electoral_Module_Ref"

declare mod1_impl [sepref_fr_rules]

schematic_goal elect_impl:
  "(uncurry ?c, uncurry (elect_monadic mod1_ref)) 
    \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_monadic_def
  by sepref


concrete_definition (in -) elect_sep uses set_select_imp.elect_impl
  prepare_code_thms (in -) elect_sep_def
lemmas elect_impl_refine = elect_sep.refine[OF this_loc]


lemmas elect_sep_correct = 
elect_impl_refine[FCOMP elect_monadic_correct[THEN fun_relD, where x' = mod1]]

schematic_goal defer_impl:
  "(uncurry ?c, uncurry (defer_monadic mod1_ref)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding defer_monadic_def
  by sepref

concrete_definition (in -) defer_sep uses set_select_imp.defer_impl
  prepare_code_thms (in -) defer_sep_def
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
         
term "elect_sep"
thm "set_select_imp.elect_sep_correct"



end