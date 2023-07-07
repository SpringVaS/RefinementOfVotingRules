(*  File:       Blacks_Rule_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Refined Black's Rule\<close>
                           
theory Blacks_Rule_Ref
  imports"Verified_Voting_Rule_Construction.Blacks_Rule"
          "Compositional_Structures/Basic_Modules/Condorcet_Module_Ref"  
          "Compositional_Structures/Basic_Modules/Borda_Module_Ref"  
          "Compositional_Structures/Sequential_Composition_Ref"
          "Compositional_Structures/Elect_Composition_Ref"
begin


subsection \<open>Definition\<close>

definition seqcomp_cb :: "'a::{default, heap, hashable} Electoral_Module" where 
  "seqcomp_cb \<equiv> (condorcet \<triangleright> borda)"                
definition seqcomp_cb_sep :: "'a :: {default, heap, hashable} Electoral_Module_Sep" where 
  "seqcomp_cb_sep \<equiv> (condorcet_elim_sep \<triangleright>sep borda_elim_sep_opt)"

interpretation seq_cb: Seqcomp_Impl condorcet borda condorcet_elim_sep borda_elim_sep_opt
  using condorcet_sound borda_sound condorcet_elim_sep_correct borda_elim_sep_opt_correct
  by unfold_locales

lemma seqcomp_cb_sep_correct :
  "(uncurry seqcomp_cb_sep, uncurry (RETURN oo (seqcomp_cb))) 
  \<in> elec_mod_seprel id_assn"
  using seq_cb.seqcomp_sep_correct 
  unfolding seqcomp_cb_sep_def PR_CONST_def seqcomp_cb_def
  by simp

declare seqcomp_cb_sep_correct[sepref_fr_rules]

subsection \<open>Refinement to Imperative/HOL\<close>

definition blackmod :: "'a :: {default, heap, hashable} set \<Rightarrow> ('a \<times> 'a) set list 
  \<Rightarrow> ('a set \<times> 'a set \<times> 'a set) nres" where 
  "blackmod \<equiv> elector_opt (black)"

text \<open>\<close>

sepref_definition blacks_sep is "uncurry (blackmod)"
  :: "elec_mod_seprel id_assn"
  unfolding black.simps blackmod_def elector_opt_def 
    seqcomp_cb_def[symmetric] hs.fold_custom_empty 
  by sepref

subsection \<open>Correctness\<close>

lemma blacks_sep_correct [sepref_fr_rules]:
  shows "(uncurry blacks_sep , uncurry (RETURN oo blacks_rule)) \<in> elec_mod_seprel id_assn"
  unfolding blacks_rule.simps elector.simps[symmetric] 
    seqcomp_cb_sep_def[symmetric] 
  using blacks_sep.refine 
    unfolding blackmod_def elector_opt_eq .

subsection \<open>Properties in Separation Logic\<close>

theorem black_rule_impl_condorcet:
  fixes A :: "'a::{default, heap, hashable} set" and
        p :: "'a Profile" and
        w :: 'a
  shows "finite_profile A p \<and> condorcet_winner A p w \<Longrightarrow>
  <(alts_set_impl_assn id_assn) A hs *
            (list_assn (ballot_assn id_assn)) p hp> blacks_sep hs hp 
  < \<lambda>r. \<exists>\<^sub>Ares. (result_impl_assn (id_assn)) res r * 
    \<up> (res = ({w}, A - {w}, {})) >\<^sub>t"
  using blacks_sep_correct[THEN hfrefD, THEN hn_refineD, of "(A, p)" "(hs, hp)"]
  apply (clarsimp simp del: condorcet_winner.simps blacks_rule.simps)
  apply (erule cons_rule[rotated -1])
  apply (sep_auto simp add : hn_ctxt_def pure_def simp del : condorcet_winner.simps 
        pairwise_majority_rule.simps)
  apply (sep_auto simp add: hn_ctxt_def simp del : condorcet_winner.simps blacks_rule.simps)
  proof (-)
  assume w_cond_winner: "condorcet_winner A p w"
  show "blacks_rule A p = ({w}, A - {w}, {})"
    using  w_cond_winner black_condorcet 
    unfolding condorcet_consistency_3
    by metis
qed

export_code convert_list_to_hash_set clist blacks_sep in Scala_imp

end
