(*  File:       Elect_Module_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin, Karlsruhe Institute of Technology (KIT)"\<close>

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
  shows "(aux_set_copy, (RETURN o op_set_copy)) 
    \<in> [\<lambda> s. finite s]\<^sub>f \<langle>Id\<rangle>set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"  
  unfolding aux_set_copy_def comp_apply
  apply (intro frefI nres_relI, clarsimp)
proof (rename_tac A)
  fix A :: "'a set"
  assume fina: "finite A"
  show "FOREACH A (\<lambda>x cp. RETURN (insert x cp)) {} \<le> RETURN A"
    apply (refine_vcg FOREACH_rule[where I = "\<lambda> it x. 
      x = A -it"])
    by (auto simp add: fina)
qed



fun elect_module_ref :: "'a Electoral_Module_Ref" where
  "elect_module_ref A p = do {
   B \<leftarrow> aux_set_copy A;
   RETURN (B,{},{})
}"

lemma elect_module_ref_correct:
  shows "(uncurry elect_module_ref, uncurry (RETURN oo elect_module))
      \<in> [\<lambda> (A, pl). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
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
    using aux_set_copy_correct[THEN frefD, THEN nres_relD] aux_set_copy_def
    by (smt (verit, ccfv_threshold) RES_sng_eq_RETURN op_set_copy_def pair_in_Id_conv push_in_let_conv(2) refine_IdD set_rel_id_simp)
    
qed


sepref_definition hs_copy_sep is "aux_set_copy" :: 
  " (hs.assn id_assn)\<^sup>k
 \<rightarrow>\<^sub>a (hs.assn id_assn)"
  unfolding aux_set_copy_def hs.fold_custom_empty
  by sepref

lemma hs_copy_hnr_aux: "(hs_copy_sep,RETURN o op_set_copy) 
  \<in> [\<lambda> s. finite s]\<^sub>a (hs.assn id_assn)\<^sup>k \<rightarrow> hs.assn id_assn"
  using hs_copy_sep.refine[FCOMP aux_set_copy_correct] by auto
  

sepref_definition elect_module_sep is 
  "uncurry elect_module_ref" :: 
"(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k
    \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding elect_module_ref.simps aux_set_copy_def hs.fold_custom_empty 
  by sepref

lemma elect_module_sep_correct:
  shows "(uncurry elect_module_sep, uncurry (RETURN \<circ>\<circ> elect_module)) \<in>  [\<lambda>(a, b).
           finite
            a]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn id_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn id_assn"
  using
 elect_module_sep.refine[FCOMP elect_module_ref_correct]  set_rel_id hr_comp_Id2 by simp
                                                                                      

declare elect_module_sep_correct[sepref_fr_rules]

end