theory Elect_Module_Ref
  imports "Verified_Voting_Rule_Construction.Elect_Module"
    "Component_Types/Electoral_Module_Ref"

begin

 \<comment> \<open>The elect module should not return just the reference to all alternatives
  but a deep copy\<close>

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



fun elect_module_ref :: "'a Electoral_Module_Ref" where
  "elect_module_ref A p = do {
   B <- aux_set_copy A;
   RETURN (B,{},{})
}"

lemma elect_module_ref_correct:
  shows "(uncurry elect_module_ref, uncurry (RETURN oo elect_module))
      \<in> [\<lambda> (A, _). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding elect_module_ref.simps elect_module.simps aux_set_copy_def
  apply (intro frefI fun_relI nres_relI) unfolding comp_apply
  apply clarsimp
proof (rename_tac A pl pr)
  fix A:: "'a set"
  fix pl pr 
 assume fina: "finite A"
  from fina show "FOREACH A (\<lambda>x cp. RETURN (insert x cp)) {} \<bind> (\<lambda>B. RETURN (B, {}, {})) \<le> RETURN (A, {}, {})"
    apply (refine_vcg)
    apply (auto)
    using aux_set_copy_correct aux_set_copy_def
    by (metis singleton_conv)
qed

  

sepref_definition elect_module_sep is 
  "uncurry elect_module_ref" :: "(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k
    \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding elect_module_ref.simps aux_set_copy_def
  apply (rewrite in "\<hole>" hs.fold_custom_empty)+
  by sepref



lemmas elect_elect_module_sep_correct = elect_module_sep.refine[FCOMP elect_module_ref_correct]

declare elect_elect_module_sep_correct[sepref_fr_rules]

end