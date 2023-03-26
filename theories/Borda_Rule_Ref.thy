(*  File:       Borda_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Borda_Rule_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Rule"
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"              
begin

sepref_definition borda_rule_sep_direct is "uncurry (elector_opt borda)"
  :: "elec_mod_seprel nat_assn"                                   
  unfolding elector_opt_def hs.fold_custom_empty
  by sepref

lemma borda_rule_direct_correct:
  shows "(uncurry borda_rule_sep_direct, uncurry (RETURN oo (borda_rule)))
  \<in> elec_mod_seprel nat_assn"
  using borda_rule_sep_direct.refine 
    unfolding borda_rule.simps elector_opt_eq .
 
declare borda_rule_direct_correct [sepref_fr_rules]

export_code convert_list_to_hash_set clist borda_rule_sep_direct in Scala_imp 

                                          
end