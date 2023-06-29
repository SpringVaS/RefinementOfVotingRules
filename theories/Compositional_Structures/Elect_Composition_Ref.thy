(*  File:       Elect_Composition_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          "Verified_Voting_Rule_Construction.Elect_Composition"
          Sequential_Composition_Ref
begin

definition elector_opt :: "('a Electoral_Module) \<Rightarrow> 
  'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres" where
    "elector_opt m A p \<equiv> do { 
      let (e, r, d) = m A p;
      RETURN (e \<union> d,r,{}) }"

lemma elector_opt_correct: 
  fixes m :: "'a Electoral_Module"
shows "(uncurry (elector_opt (m)), uncurry (RETURN oo (elector m))) \<in>
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding elector_opt_def
  apply (intro frefI nres_relI) apply clarsimp
   apply (refine_vcg)
  by auto

lemma elector_opt_eq:
  shows "elector_opt \<equiv> (RETURN \<circ>\<circ>\<circ> (elector))"
  unfolding elector_opt_def elector.simps
  sequential_composition'.simps comp_apply
  apply auto
  by (simp add: case_prod_beta')
  

(*lemma elector_opt_correct_nres: 
  fixes m_opt :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)"
fixes m :: "'a Electoral_Module"
assumes em_m: "electoral_module m" 
assumes mref: "(uncurry m_opt, uncurry (RETURN oo m)) \<in>  
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
   \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
shows "(uncurry (elector_opt (m)), uncurry ((elector m))) \<in>
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding elector_opt_def
  apply (intro frefI nres_relI) apply clarsimp
proof (rename_tac A p, refine_vcg, unfold SPEC_eq_is_RETURN)
  fix A :: "'a set"
  fix p :: "'a Profile"
  assume fina: "finite A"
  assume prof: "profile A p"
  have mret: "m_opt A p \<le> RETURN (m A p)"
     using mref[THEN frefD, THEN nres_relD] fina prof
     by clarsimp
  thus " m_opt A p
           \<le> SPEC (\<lambda>x. (case x of (e, r, d) \<Rightarrow> RETURN (e \<union> d, r, {}))
                        \<le> RETURN (elect m A p \<union> defer m A p, reject m A p, {}))"
    by (simp add: case_prod_beta' order_trans)
qed*)

locale Elector_Impl =
  fixes m :: "'a::{default, heap, hashable} Electoral_Module"
  fixes m_sep :: "'a::{default, heap, hashable} Electoral_Module_Sep"
  assumes em_m: "electoral_module m" 
  assumes m_sep_correct: "(uncurry m_sep, uncurry (RETURN oo m)) \<in> elec_mod_seprel id_assn"
begin
   
  lemma this_loc: "Elector_Impl m m_sep " by unfold_locales

  sepref_register m

  declare m_sep_correct[sepref_fr_rules]

schematic_goal elector_sepimpl:
  "(uncurry ?f2, uncurry (elector_opt m)) \<in> elec_mod_seprel id_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  by sepref

concrete_definition elector_sep_uc uses Elector_Impl.elector_sepimpl
  prepare_code_thms elector_sep_uc_def
lemmas  elector_sep_ucp_refine = elector_sep_uc.refine[OF this_loc]

schematic_goal elector_sep_curried:
 "?curried = curry (elector_sep_uc m_sep)" by auto

concrete_definition (in -) elector_sep uses Elector_Impl.elector_sep_curried

  theorem seqcomp_sep_correct:
  shows "(uncurry (elector_sep m_sep), uncurry (RETURN oo (elector m))) \<in> elec_mod_seprel id_assn"
    using elector_sep_ucp_refine[FCOMP elector_opt_correct]
    unfolding elector_sep_def
    by (simp)

end

end