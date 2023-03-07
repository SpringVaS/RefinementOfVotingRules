theory Plurality_Rule_Ref
  imports Main
    Verified_Voting_Rule_Construction.Plurality_Rule
     "Compositional_Structures/Basic_Modules/Plurality_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"  

begin

sepref_definition plurality_rule_direct_sep is "uncurry (elector_opt (RETURN oo plurality_mod))"
  :: "elec_mod_sep_rel nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

lemmas opt_seq_plur = elector_opt_correct[OF plurmod_sound]
lemmas opt_plur_correct_aux = plurality_rule_direct_sep.refine[FCOMP opt_seq_plur]

lemma opt_plur_correct:
  shows "(uncurry plurality_rule_direct_sep, uncurry (RETURN oo (plurality_rule:: (nat Electoral_Module))))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding plurality_rule.simps 
  using  opt_plur_correct_aux  
    using  prod_rel_id_simp set_rel_id hr_comp_Id2
    by metis
  

declare opt_plur_correct [sepref_fr_rules]


export_code clist convert_list_to_hash_set plurality_rule_direct_sep in Scala_imp


end