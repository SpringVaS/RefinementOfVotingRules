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

lemmas borda_rule_correct_aux  = borda_rule_impl.elector_sep_correct

lemma  borda_rule_correct:
  shows "(borda_rule_sep, uncurry (RETURN oo borda_rule))
    \<in> [\<lambda>(A, pl).
           finite_profile A
            pl]\<^sub>a (hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel))\<^sup>k *\<^sub>a
                  (list_assn
                    (hr_comp ballot_impl_assn
                      ballot_rel))\<^sup>k \<rightarrow> hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel) \<times>\<^sub>a
                                        hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel) \<times>\<^sub>a
                                        hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel)"
  unfolding borda_rule_sep_def borda_rule.simps using borda_rule_correct_aux .


export_code borda_rule_sep in Scala_imp

definition "ttest == borda_rule_sep hs. "
                                          
end