theory Elect_Module_Ref
  imports "Verified_Voting_Rule_Construction.Elect_Module"
    "Component_Types/Electoral_Module_Ref"

begin

 \<comment> \<open>The elect module should not return just the reference to all alternatives
  but a deep copy\<close>

fun elect_module_ref :: "'a Electoral_Module_Ref" where
  "elect_module_ref A p = do {
   B <- aux_set_copy A;
   RETURN (B,{},{})
}"

lemma elect_module_ref_correct:
  shows "(elect_module_ref, (\<lambda> A p. SPEC (\<lambda> res. res= elect_module A p)))
      \<in> elec_mod_relb Id"
  unfolding elect_module_ref.simps elect_module.simps aux_set_copy_def
  apply (intro fun_relI)
proof (rename_tac A' A pl pr)
  fix A' A:: "'a set"
  fix pl pr 
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A" by (auto simp add: alt_set_rel_def in_br_conv)
  from fina have refid: "(FOREACH A' (\<lambda>x cp. RETURN (insert x cp)) {} \<bind> (\<lambda>B. RETURN (B, {}, {})),
        SPEC (\<lambda>res. res = (A, {}, {})))
       \<in> \<langle>Id\<rangle>nres_rel"
    apply (refine_vcg)
    apply (simp add: aeq)
    using aux_set_copy_correct aux_set_copy_def
    by (metis singleton_conv)
    show "(FOREACH A' (\<lambda>x cp. RETURN (insert x cp)) {} \<bind> (\<lambda>B. RETURN (B, {}, {})),
        SPEC (\<lambda>res. res = (A, {}, {})))
       \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
      apply (refine_vcg)
    using refid[THEN nres_relD] prod_rel_id set_rel_id
    by simp
qed

  

sepref_definition elect_sepref is 
  "uncurry elect_module_ref" :: "(alts_set_impl_assn)\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k
    \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding elect_module_ref.simps aux_set_copy_def
  apply (rewrite in "\<hole>" hs.fold_custom_empty)+
  by sepref

lemmas elect_sepref_correct = elect_sepref.refine[FCOMP elect_module_ref_correct]

end