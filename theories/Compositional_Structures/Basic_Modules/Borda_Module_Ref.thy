theory Borda_Module_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Module"
           "Component_Types/Elimination_Module_Ref"
begin

fun borda_score_mon :: "'a Evaluation_Function_Ref" where
  "borda_score_mon x A p =
    sum_impl (prefer_count_monadic_imp p x) A"

definition borda_monadic :: "'a Electoral_Module_Ref" where
  "borda_monadic A pl \<equiv> do {
   scores <- (pre_compute_scores borda_score_mon A pl);
   max_eliminator_ref scores A pl
}"

lemma borda_score_refine_alt:
  fixes A:: "'a set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
  shows "borda_score_mon x A pl \<le> SPEC (\<lambda> sc. sc = (borda_score x A pr))"
  unfolding borda_score_mon.simps borda_score.simps
  by (refine_vcg fina sum_impl_correct prefer_count_monadic_imp_correct  profrel)
 

lemma borda_score_correct:
  shows "(borda_score_mon, borda_score)
    \<in> evalf_rel"
  unfolding evalf_rel_def
proof (clarify, refine_rcg, unfold borda_score_mon.simps borda_score.simps, 
        rename_tac x A' A pl pr)
  fix A' A :: "'a set"
  fix x :: 'a
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  assume prel: "(pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  show "sum_impl (prefer_count_monadic_imp pl x) A' \<le> SPEC (\<lambda>sc. sc = sum (prefer_count pr x) A)"
    by (refine_vcg fina prel prefer_count_monadic_imp_correct sum_impl_correct, simp add: aeq)
qed


theorem borda_ref_correct:          
  shows "(borda_monadic,(\<lambda> A p. SPEC (\<lambda> em. em = borda A p))) \<in> elec_mod_relb"
  unfolding borda_monadic_def borda.simps
proof (clarify, rename_tac A' A pl pr)
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  assume prel: " (pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  note compute_scores_correct[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD, 
          THEN refine_IdD, where x4 = borda_score_mon and x'4 = borda_score]
  from arel prel this borda_score_correct have 
    precompborda: "pre_compute_scores borda_score_mon A' pl
  \<le> SPEC (\<lambda>map. map = pre_computed_map borda_score A pr)" by fastforce
  note maxelim = max_eliminator_ref_correct[where efn = borda_score, THEN fun_relD]
  from arel aeq prel precompborda this show "(pre_compute_scores borda_score_mon A' pl \<bind>
        (\<lambda>scores. max_eliminator_ref scores A' pl),
        SPEC (\<lambda>res. res = max_eliminator borda_score A pr))
       \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
    using specify_left[where M = 
        "\<Down> (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel) 
  (SPEC (\<lambda>res. res = max_eliminator borda_score A pr))"
       and m = "pre_compute_scores borda_score_mon A' pl"
       and \<Phi> = "(\<lambda>map. map = pre_computed_map borda_score A pr)"
       and f = "(\<lambda>scores. max_eliminator_ref scores A' pl)"]
  nres_relI nres_relD by blast
qed 

theorem borda_ref_return:
  shows "(borda_monadic, RETURN oo borda) \<in> elec_mod_relb"
  apply (refine_vcg  )
  using borda_ref_correct[THEN fun_relD, THEN fun_relD, THEN nres_relD]
    SPEC_eq_is_RETURN(2) push_in_let_conv(2)
  by (metis relAPP_def set_rel_id_simp)

sepref_definition borda_elim_sepref is
  "uncurry borda_monadic":: 
    "alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding borda_monadic_def  max_eliminator_ref.simps borda_score_mon.simps sum_impl_def
    less_eliminator_ref.simps  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
    prefer_count_monadic_imp_def[abs_def] is_less_preferred_than_mon_def[abs_def]
    rank_mon_def[abs_def] index_mon_def[abs_def]
    short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)

  apply sepref_dbg_keep

  done

term borda_elim_sepref

term "sepref_access.elect_ref borda_monadic"


lemmas borda_impl_correct = borda_elim_sepref.refine[FCOMP borda_ref_correct]




end