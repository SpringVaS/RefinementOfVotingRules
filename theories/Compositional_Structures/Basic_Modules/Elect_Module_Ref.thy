theory Elect_Module_Ref
  imports "Verified_Voting_Rule_Construction.Elect_Module"
    "Component_Types/Electoral_Module_Ref"

begin

fun elect_module_ref :: "'a Electoral_Module_Ref" where
  "elect_module_ref A p = RETURN (A, {}, {})"

lemma elect_module_ref_correct:
  shows "(elect_module_ref, (\<lambda> A p. RETURN (elect_module A p)))
      \<in> elec_mod_relb"
  unfolding elect_module_ref.simps elect_module.simps
  apply refine_vcg
  by auto

sepref_definition em_sep is 
  "uncurry elect_module_ref" :: "(hs.assn nat_assn)\<^sup>d *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k
    \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding elect_module_ref.simps
  apply (rewrite in "\<hole>" hs.fold_custom_empty)+
  by sepref

end