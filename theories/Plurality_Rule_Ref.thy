(*  File:       Plurality_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Refined Plurality Rule\<close>
theory Plurality_Rule_Ref
  imports Main
    Verified_Voting_Rule_Construction.Plurality_Rule
     "Compositional_Structures/Basic_Modules/Plurality_Module_Ref"  
          "Compositional_Structures/Elect_Composition_Ref"  

begin

subsection \<open>Refinement to Imperative/HOL\<close>

text \<open>The basic module for plurality has been refined. We use the simplified but correct
      elect composition to define a sythesizable definition of the plurality rule inline
      and use the sepref-tool to synthesize the implementation\<close>

sepref_definition plurality_rule_direct_sep is "uncurry (elector_opt (plurality))"
  :: "elec_mod_seprel nat_assn"
  unfolding elector_opt_def hs.fold_custom_empty
  by sepref

text \<open>Using the correctness of the elector and the refinement theorem provided by sepref we provide
      a simplified refinement relation of the plurality implementation and the abstract
       sepcification\<close>

lemma opt_plur_correct:
  shows "(uncurry plurality_rule_direct_sep, uncurry (RETURN oo (plurality_rule)))
  \<in> elec_mod_seprel nat_assn"
  unfolding plurality_rule.simps 
  using plurality_rule_direct_sep.refine unfolding elector_opt_eq .

declare opt_plur_correct [sepref_fr_rules]


export_code clist convert_list_to_hash_set plurality_rule_direct_sep in Scala_imp

end