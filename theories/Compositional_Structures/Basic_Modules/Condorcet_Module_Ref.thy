theory Condorcet_Module_Ref
  imports "Verified_Voting_Rule_Construction.Condorcet_Module"
           "Component_Types/Elimination_Module_Ref"
begin


definition condorcet_score_ref :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "condorcet_score_ref x A p = do {
    is_x_cond_winner <- (condorcet_winner_monadic A p x);
    RETURN (if (is_x_cond_winner) then 1 else 0)}"

definition condorcet_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "condorcet_ref A pl  \<equiv> do {
   scores <- (pre_compute_scores condorcet_score_ref A pl);
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
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (unfold condorcet_ref_def comp_apply SPEC_eq_is_RETURN(2)[symmetric], 
    intro frefI nres_relI, clarsimp simp add: set_rel_id prod_rel_id simp del : condorcet.simps,
    rename_tac A pl pr)
  fix A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profp: "profile A pr"
  from prel fina profp  have  precompcond: "pre_compute_scores condorcet_score_ref A pl
  \<le> SPEC (\<lambda>map. map = pre_computed_map condorcet_score A pr)" using
    condorcet_score_ref_correct compute_scores_correct
    by metis
  note maxelim = max_eliminator_ref_correct[where efn = condorcet_score and A = A and pl = pl
      and pr = pr]
  from fina prel this have mid: "(\<And>x. x = pre_computed_map condorcet_score A pr \<Longrightarrow>
          max_eliminator_ref x A pl \<le> SPEC (\<lambda>x. x = max_eliminator condorcet_score A pr))"
    by blast
   have "pre_compute_scores condorcet_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> SPEC (\<lambda>x. x = condorcet A pr)"
     unfolding condorcet.simps
     apply refine_vcg
     using precompcond  mid
       SPEC_cons_rule[where m = "pre_compute_scores condorcet_score_ref A pl" and
\<Psi> = "(\<lambda>scores. max_eliminator_ref scores A pl \<le> SPEC (\<lambda>x. x = max_eliminator condorcet_score A pr))"
  and \<Phi> = "(\<lambda> map. map = (pre_computed_map condorcet_score A pr))"]
     by blast 
    thus " pre_compute_scores condorcet_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> RES {condorcet A pr}"
    by (metis singleton_conv)
qed

sepref_definition condorcet_elim_sep is
  "uncurry condorcet_ref":: 
  "(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding condorcet_ref_def  max_eliminator_ref_def condorcet_score_ref_def 
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "RETURN ({}, {}, \<hole>)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ({}, \<hole>, _)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ( \<hole>, _, _)" hs.fold_custom_empty) 
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) 
                                  else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) 
                                  else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) 
                                    else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)
  apply sepref_dbg_keep
  done


(*lemmas cond_ref_correct_aux = condorcet_elim_sep.refine[FCOMP condorcet_ref_correct]

lemma condorcet_elim_sep_correct [sepref_fr_rules]:
  shows "(uncurry condorcet_elim_sep, uncurry (RETURN \<circ>\<circ> condorcet))
    \<in> elec_mod_sep_rel id_assn"
  using cond_ref_correct_aux
  set_rel_id hr_comp_Id2 by simp*)

end