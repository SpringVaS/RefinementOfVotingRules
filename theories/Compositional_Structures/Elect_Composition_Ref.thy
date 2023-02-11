theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          "Verified_Voting_Rule_Construction.Elect_Composition"
          Sequential_Composition_Ref
begin


definition  
  "elector_sep m \<equiv> m \<triangleright>sep elect_module_sep"

thm "elector_sep_def"

locale elector_impl =  
  fixes m_ref :: "'a::{default, linorder, hashable, heap} Electoral_Module_Ref"
  fixes m_sep :: "('a, unit) hashtable
      \<Rightarrow> ('a array \<times> nat) list
         \<Rightarrow> (('a, unit) hashtable \<times> ('a, unit) hashtable \<times> ('a, unit) hashtable) Heap"
  assumes 
    m_impl: "(uncurry m_sep, uncurry m_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"


locale elector_ref = elector_impl +
  fixes m :: "nat Electoral_Module"
assumes module_m: "electoral_module m"
assumes m_ref_correct: "(uncurry m_ref, uncurry (RETURN oo m)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel\<rangle>nres_rel)" 
begin

lemmas m_t_ref = m_impl[FCOMP m_ref_correct]

interpretation elector: sequence_refine m_ref m_sep elect_module_ref elect_module_sep m elect_module
  apply unfold_locales
  subgoal using m_impl .
  subgoal  using elect_module_sep.refine .
  subgoal using module_m.
  subgoal by simp
  subgoal using m_ref_correct.
  subgoal apply (intro frefI nres_relI) 
    using elect_module_ref_correct[THEN frefD, THEN nres_relD]
    unfolding comp_apply by auto
  done

interpretation elector:  seqcomp_impl m_ref m_sep elect_module_ref elect_module_sep
  apply unfold_locales .

lemmas elector_sep_refine =  elector.seqt_sep_refine

lemmas elector_sep_correct =  elector.sequence_correct

end

end