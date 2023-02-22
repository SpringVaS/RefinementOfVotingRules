theory Borda_Module_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Module"
           "Component_Types/Elimination_Module_Ref"
begin

definition borda_score_mon :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "borda_score_mon x A p =
    sum_impl (prefer_count_monadic_imp p x) A"


definition borda_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "borda_ref A pl \<equiv> do {
   scores <- (pre_compute_scores borda_score_mon A pl);
   max_eliminator_ref scores A pl
}"

lemma borda_score_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
  shows "\<forall> a \<in> A. borda_score_mon a A pl \<le> SPEC (\<lambda> sc. sc = (borda_score a A pr))"
  unfolding borda_score_mon_def borda_score.simps
  by (safe, refine_vcg fina sum_impl_correct prefer_count_monadic_imp_correct profrel)
 

lemma borda_ref_correct:          
  shows "(uncurry borda_ref, uncurry (RETURN oo borda)) \<in> 
  [\<lambda> (A, _). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (intro frefI nres_relI, clarsimp simp del: max_eliminator.simps, rename_tac A pl pr)
  fix A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  show "borda_ref A pl \<le> RETURN (max_eliminator borda_score A pr)"
    apply (unfold borda_ref_def RETURN_SPEC_conv)
    using borda_score_correct max_eliminator_ref_correct_pc fina prel
    by metis
qed


sepref_definition borda_elim_sep is
  "uncurry borda_ref":: 
    "(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding borda_ref_def  max_eliminator_ref_def borda_score_mon_def sum_impl_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "RETURN ({}, {}, \<hole>)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ({}, \<hole>, _)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ( \<hole>, _, _)" hs.fold_custom_empty) 
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)
  apply sepref_dbg_keep
  done

lemma  borda_elim_sep_correct:
  shows "(uncurry borda_elim_sep, uncurry (RETURN \<circ>\<circ> borda))
    \<in> [\<lambda>(a, b).
           finite
            a]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn id_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn id_assn"
  using borda_elim_sep.refine[FCOMP borda_ref_correct, THEN hfrefD] apply (intro hfrefI)
  using set_rel_id hr_comp_Id2 by auto

declare borda_elim_sep_correct [sepref_fr_rules]


end