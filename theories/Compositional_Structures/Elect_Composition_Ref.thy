theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          "Verified_Voting_Rule_Construction.Elect_Composition"
          Sequential_Composition_Ref
begin


definition  
  "elector_sep m \<equiv> m \<triangleright>sep elect_module_sep"

lemma elector_sep_impl: "seqcomp_impl m_ref m_impl elect_module_ref elect_module_sep"
  apply unfold_locales
proof -
  show "(uncurry elect_module_sep, uncurry elect_module_ref)
    \<in> (hs.assn nat_assn)\<^sup>k *\<^sub>a
       profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a hs.assn nat_assn \<times>\<^sub>a hs.assn nat_assn \<times>\<^sub>a hs.assn nat_assn"
    using elect_module_sep.refine by simp
next

  oops

interpretation electori:  seqcomp_impl m_ref m_impl elect_module_ref elect_module_sep

  oops


end