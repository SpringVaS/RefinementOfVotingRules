(*  File:       Borda_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Borda_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin



sepref_definition borda_rule_sep_direct is "uncurry (elector_opt (RETURN oo borda))"
  :: "[\<lambda>(x, xa).
       finite_profile x xa ]\<^sub>a (hs.assn nat_assn)\<^sup>k *\<^sub>a
             (list_assn (ballot_assn nat_assn))\<^sup>k \<rightarrow> 
                  result_impl_assn nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

lemmas elect_comp_borda = elector_opt_correct[OF borda_sound]
lemmas borda_rule_correct_aux = borda_rule_sep_direct.refine[FCOMP elect_comp_borda]

lemma borda_rule_direct_correct:
  shows "(uncurry borda_rule_sep_direct, uncurry (RETURN oo (borda_rule)))
  \<in> elec_mod_assn nat_assn"
  unfolding borda_rule.simps 
  using  borda_rule_correct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  by (metis)
 
declare borda_rule_direct_correct [sepref_fr_rules]

export_code convert_list_to_hash_set clist borda_rule_sep_direct in Scala_imp 

                                          
end