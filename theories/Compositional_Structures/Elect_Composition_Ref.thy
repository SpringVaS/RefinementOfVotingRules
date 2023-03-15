(*  File:       Elect_Composition_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          "Verified_Voting_Rule_Construction.Elect_Composition"
          Sequential_Composition_Ref
begin

definition elector_opt :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres) \<Rightarrow> 
  'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres" where
  "elector_opt m A p \<equiv> do { 
      (e, r, d) <- m A p;
      RETURN (e \<union> d,r,{}) }"

lemma elector_opt_correct: 
  fixes m :: "'a Electoral_Module"
  assumes em_m: "electoral_module m" 
shows "(uncurry (elector_opt (RETURN oo m)), uncurry (RETURN oo (elector m))) \<in>
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding elector_opt_def
  apply (intro frefI nres_relI) apply clarsimp
  using assms apply (refine_vcg)
  by auto

lemma elector_opt_correct_nres: 
  fixes m_opt :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres)"
fixes m :: "'a Electoral_Module"
assumes em_m: "electoral_module m" 
assumes mref: "(uncurry m_opt, uncurry (RETURN oo m)) \<in>  
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
   \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
shows "(uncurry (elector_opt (m_opt)), uncurry (RETURN oo (elector m))) \<in>
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
qed
   

end