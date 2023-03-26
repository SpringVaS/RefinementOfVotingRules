(*  File:       Condorcet_Module_Ref.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Condorcet_Module_Ref
  imports "Verified_Voting_Rule_Construction.Condorcet_Module"
           "Component_Types/Elimination_Module_Ref"
begin


definition condorcet_score_ref :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "condorcet_score_ref x A p = do {
    is_x_cond_winner \<leftarrow> (condorcet_winner_monadic A p x);
    RETURN (if (is_x_cond_winner) then 1 else 0)}"

definition condorcet_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "condorcet_ref A pl  \<equiv> do {
   scores \<leftarrow> (pre_compute_scores condorcet_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma condorcet_score_ref_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a::{default, heap, hashable} Profile_List" and pr:: "'a::{default, heap, hashable} Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
    and profprop: "profile A pr"
  shows "\<forall> x \<in> A. condorcet_score_ref x A pl \<le> SPEC (\<lambda> sc. sc = (condorcet_score x A pr))"
  unfolding condorcet_score_ref_def condorcet_score.simps
  apply clarify
  apply (refine_vcg assms condorcet_winner_monadic_correct)
  by auto


lemma condorcet_ref_correct:          
  shows "(uncurry condorcet_ref, uncurry (RETURN oo condorcet)) \<in> 
  ([\<lambda> (A, pl). finite_profile A                         
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>ballot_rel\<rangle>list_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (unfold condorcet_ref_def, 
    intro frefI nres_relI ,clarsimp simp del: max_eliminator.simps,
    rename_tac A pl pr)
  fix A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profp: "profile A pr"
  show " pre_compute_scores condorcet_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> RETURN (max_eliminator condorcet_score A pr)"
     unfolding condorcet.simps RETURN_SPEC_conv
     by (refine_vcg condorcet_score_ref_correct max_eliminator_ref_correct_default fina prel profp)
qed

sepref_definition condorcet_elim_sep is
  "uncurry condorcet_ref":: 
  "(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding condorcet_ref_def  max_eliminator_ref_def condorcet_score_ref_def 
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] op_set_is_empty_def[symmetric]
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "RETURN (_, _, rewrite_HOLE)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN (_, rewrite_HOLE, _)" hs.fold_custom_empty) +
  apply (rewrite in "RETURN ( rewrite_HOLE, _, _)" hs.fold_custom_empty)+ 
  apply sepref_dbg_keep
  done

lemmas cond_ref_correct_aux = condorcet_elim_sep.refine[FCOMP condorcet_ref_correct]

lemma condorcet_elim_sep_correct:
  shows "(uncurry condorcet_elim_sep, uncurry (RETURN \<circ>\<circ> condorcet))
    \<in> elec_mod_seprel id_assn"
  using cond_ref_correct_aux unfolding ballot_assn_def 
  set_rel_id hr_comp_Id2 by (simp)

declare condorcet_elim_sep_correct[sepref_fr_rules]

end