section \<open>Black's Rule\<close>

theory Blacks_Rule_Ref
  imports"Verified_Voting_Rule_Construction.Blacks_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Sequential_Composition_Ref"
          "Compositional_Structures/Elect_Composition_Ref"
begin


subsection \<open>Definition\<close>

definition "blacks_opt \<equiv> elector_opt (seq_opt condorcet borda)"

sepref_definition blacks_rule_direct is "uncurry (elector_opt (seq_opt condorcet borda))" 
  :: "[\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn nat_assn)\<^sup>k *\<^sub>a 
    (list_assn (hr_comp (ballot_impl_assn nat_assn) ballot_rel))\<^sup>k 
        \<rightarrow> (result_impl_assn nat_assn)"
  unfolding elector_opt_def seq_opt_def hs.fold_custom_empty
  apply sepref_dbg_keep
  done

lemma emcomp: "electoral_module (sequential_composition' condorcet borda)"
  by (simp add: borda_sound condorcet_sound seqcomp_alt_eq)


lemma seq_cnd_borda_d:
  shows "(uncurry (elector_opt ((RETURN \<circ>\<circ>\<circ> sequential_composition' condorcet) borda)),
       uncurry ((RETURN \<circ>\<circ>\<circ> elector) (sequential_composition' condorcet borda)))
      \<in> [\<lambda>(A, p).
             finite_profile A
              p]\<^sub>f \<langle>Id\<rangle>set_rel \<times>\<^sub>r
                   \<langle>\<langle>Id \<times>\<^sub>r
                     Id\<rangle>set_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  using emcomp elector_opt_correct[of "(sequential_composition' condorcet borda)"] by simp

lemmas inner_black = seq_opt_correct[of condorcet borda]

lemmas outer = elector_opt_correct_nres[where m_opt= "(seq_opt condorcet borda)" 
    and m = "(sequential_composition' condorcet borda)"]

lemma comp_outer:
  shows "(uncurry (elector_opt (condorcet \<triangleright>opt borda)),
     uncurry ((RETURN \<circ>\<circ>\<circ> elector) (sequential_composition' condorcet borda)))
    \<in> [\<lambda>(A, p).
           finite_profile A
            p]\<^sub>f \<langle>Id\<rangle>set_rel \<times>\<^sub>r
                 \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof -
  have " (uncurry (condorcet \<triangleright>opt borda), uncurry ((RETURN \<circ>\<circ>\<circ> sequential_composition' condorcet) borda))
    \<in> [\<lambda>(A, p).
           finite_profile A
            p]\<^sub>f \<langle>Id\<rangle>set_rel \<times>\<^sub>r
                 \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
    using inner_black borda_sound condorcet_sound by simp
  from this show ?thesis
    using outer emcomp
    by blast
qed

lemmas opt_blacks_correct_aux = blacks_rule_direct.refine[FCOMP comp_outer]

lemma blacks_direct_correct:
  shows "(uncurry blacks_rule_direct, uncurry (RETURN oo (blacks_rule:: (nat Electoral_Module))))
  \<in> elec_mod_sep_rel nat_assn"
  unfolding blacks_rule.simps
  using  opt_blacks_correct_aux  prod_rel_id_simp set_rel_id hr_comp_Id2
  

declare opt_blacks_correct_aux [sepref_fr_rules]


end
