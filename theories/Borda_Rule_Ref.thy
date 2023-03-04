theory Borda_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

definition borda_rule_sep where
  "borda_rule_sep \<equiv> elector_sep borda_elim_sep"

                          
interpretation borda_rule_impl: elector_sepref borda_ref borda_elim_sep borda
  apply unfold_locales            
  subgoal using borda_elim_sep.refine .
  subgoal using borda_sound .
  subgoal apply (intro frefI) using borda_ref_correct[THEN frefD] by auto
  done

thm "borda_rule_impl.elector_sep_correct"

lemma  borda_rule_correct:
  shows "(uncurry borda_rule_sep, uncurry (RETURN oo borda_rule))
    \<in> [\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn id_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn id_assn"
  unfolding borda_rule_sep_def borda_rule.simps 
  using borda_rule_impl.elector_sep_correct unfolding in_br_conv well_formed_pl_def
  .
sepref_definition borda_rule_sep_direct is "uncurry (seq_opt borda elect_module
  )"
  :: "[\<lambda>(x, xa).
       finite_profile
        x xa ]\<^sub>a (hs.assn nat_assn)\<^sup>k *\<^sub>a
             (list_assn (hr_comp (ballot_impl_assn nat_assn) ballot_rel))\<^sup>k \<rightarrow> 
  result_impl_assn  nat_assn"
  unfolding seq_opt_def
  apply sepref_dbg_keep
  done

lemmas seq_borda = seq_opt_correct[OF borda_sound elect_mod_sound]
lemmas borda_rule_correct_aux = borda_rule_sep_direct.refine[FCOMP seq_borda]

lemma borda_rule_direct_correct:
  shows "(uncurry borda_rule_sep_direct, uncurry (RETURN oo (borda_rule)))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding borda_rule.simps elector.simps 
  using  borda_rule_correct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  by (metis seqcomp_alt_eq)
  

declare borda_rule_direct_correct [sepref_fr_rules]

sepref_definition borda_rule_opt_sep_direct is "uncurry (elector_opt (RETURN oo borda))"
  :: "[\<lambda>(x, xa).
       finite_profile
        x xa ]\<^sub>a (hs.assn nat_assn)\<^sup>k *\<^sub>a
             (list_assn (hr_comp (ballot_impl_assn nat_assn) ballot_rel))\<^sup>k \<rightarrow> 
  result_impl_assn  nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

lemmas borda_elect_aux = elector_opt_correct[of borda]
lemmas borda_opt_direct_correct_aux = borda_rule_opt_sep_direct.refine[FCOMP borda_elect_aux]

lemma borda_rule_opt_direct_correct:
  shows "(uncurry borda_rule_opt_sep_direct, uncurry (RETURN oo (borda_rule)))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding borda_rule.simps  using borda_opt_direct_correct_aux borda_sound
    prod_rel_id_simp set_rel_id hr_comp_Id2
  by (metis)
  

export_code convert_list_to_hash_set clist borda_rule_opt_sep_direct in Scala_imp

                                          
end