theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          "Verified_Voting_Rule_Construction.Elect_Composition"
          Sequential_Composition_Ref
begin


definition  
  "elector_sep m \<equiv> m \<triangleright>sep elect_module_sep"

thm "elector_sep_def"

locale elector_impl =  
  fixes m_ref :: "'a::{default, hashable, heap} Electoral_Module_Ref"
  fixes m_sep :: "('a::{default, hashable, heap}, unit) hashtable
      \<Rightarrow> ('a::{default, hashable, heap} array \<times> nat) list
         \<Rightarrow> (('a::{default, hashable, heap}, unit) hashtable
   \<times> ('a::{default, hashable, heap}, unit) hashtable \<times> ('a::{default, hashable, heap}, unit) hashtable) Heap"
  assumes 
    m_impl: "(uncurry m_sep, uncurry m_ref)
        \<in> (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
      \<rightarrow>\<^sub>a result_impl_assn id_assn"


locale elector_sepref = elector_impl +
  fixes m :: "'a::{default, hashable, heap}  Electoral_Module"
assumes module_m: "electoral_module m"
assumes m_ref_correct: "(uncurry m_ref, uncurry (RETURN oo m)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)" 
begin

lemmas m_t_ref = m_impl[FCOMP m_ref_correct]

interpretation elector: sequence_sepref m_ref m_sep elect_module_ref elect_module_sep m elect_module
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


lemmas elector_sep_correct_aux =  elector.sequence_correct

lemma elector_sep_correct:
  shows "(uncurry (elector_sep m_sep), uncurry (RETURN oo elector m))
      \<in> [\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn id_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn id_assn"                                               
  unfolding elector_sep_def elector.simps 
  using elector_sep_correct_aux by simp


end

end