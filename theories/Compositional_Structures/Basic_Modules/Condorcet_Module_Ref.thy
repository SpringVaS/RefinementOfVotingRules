theory Condorcet_Module_Ref
  imports "Verified_Voting_Rule_Construction.Condorcet_Module"
           "Component_Types/Elimination_Module_Ref"
begin

fun condorcet_score_ref :: "'a Evaluation_Function_Ref" where
  "condorcet_score_ref x A p = do {
    is_x_cond_winner <- (condorcet_winner_monadic A p x);
    RETURN (if (is_x_cond_winner) then 1 else 0)}"


definition condorcet_ref :: "'a Electoral_Module_Ref" where
  "condorcet_ref A pl \<equiv> do {
   scores <- (pre_compute_scores condorcet_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma condorcet_score_correct:
  shows "(condorcet_score_ref, condorcet_score)
    \<in> evalf_rel_prof"
  unfolding evalf_rel_prof_def
proof (clarify, refine_rcg, unfold condorcet_score_ref.simps condorcet_score.simps, refine_vcg,
    rename_tac x A' pl A pr)
  fix A' A :: "'a set"
  fix x :: 'a
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume aprel: "((A', pl), A, pr) \<in> \<langle>Id\<rangle>alt_and_profile_rel" 
  from aprel have finA: "finite A" unfolding alt_and_profile_rel_def
    by (simp add: finite_set_rel_def in_br_conv)
  from aprel have prel: "(pl, pr) \<in> profile_on_A_rel A" unfolding alt_and_profile_rel_def
    by (simp add: finite_set_rel_def in_br_conv)
  show "condorcet_winner_monadic A' pl x
       \<le> SPEC (\<lambda>is_x_cond_winner.
                   RETURN (if is_x_cond_winner then 1 else 0)
                   \<le> SPEC (\<lambda>sc. sc = (if condorcet_winner A pr x then 1 else 0)))"
    using condorcet_winner_monadic_correct
      IdI apply (auto simp del: condorcet_winner.simps)
     apply (metis RES_sng_eq_RETURN RETURN_rule SPEC_trans aprel)
    by (metis (mono_tags, lifting) SPEC_cons_rule aprel singleton_conv2)
qed




context fixed_alts 

begin
sepref_definition condorcet_elim_sepref is
  "uncurry condorcet_ref":: 
  "alts_set_impl_assn\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding condorcet_ref_def  max_eliminator_ref_def condorcet_score_ref.simps 
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
    condorcet_winner_monadic_def[abs_def]  wins_monadic_def[abs_def] prefer_count_monadic_imp_def
    is_less_preferred_than_mon_def[abs_def] rank_mon_def[abs_def] index_mon_def[abs_def]
    short_circuit_conv
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




theorem condorcet_ref_correct:
  shows "(condorcet_ref,  (RETURN oo condorcet)) \<in> 
  elec_mod_fixed_alts_rel"
proof (unfold condorcet_ref_def, refine_vcg, auto simp only: in_br_conv set_rel_id prod_rel_id finite_set_rel_def,
    rule refine_IdI, unfold comp_apply SPEC_eq_is_RETURN(2)[symmetric] , rename_tac pl pr)
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume profrel: "(pl, pr) \<in> profile_on_A_rel Alts"
  assume fina: "finite Alts"
  from profrel have prel: "(pl, pr) \<in> profile_rel" using
      profile_type_ref by blast
  from fina have arel: "(Alts, Alts) \<in> \<langle>Id\<rangle>finite_set_rel" using finite_set_rel_def
    set_rel_id in_br_conv
    by (metis Id_O_R )    
  from this profrel have combrel: "((Alts,pl), Alts, pr) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
    using alt_and_profile_rel_def
    by blast
  note csc = compute_scores_correct_prof[THEN fun_relD, THEN fun_relD, THEN nres_relD,
      THEN refine_IdD]

  have scorec: "(pre_compute_scores condorcet_score_ref Alts pl)
    \<le> SPEC (\<lambda>map. map = pre_computed_map condorcet_score Alts pr)"
    using condorcet_score_correct combrel csc[where x3 = condorcet_score_ref
        and x'3 = condorcet_score and x2 = "(Alts, pl)" and x'2 = "(Alts, pr)"]
    by auto

  note maxc = max_eliminator_Id[THEN fun_relD, THEN nres_relD, THEN refine_IdD]

  show "  pre_compute_scores condorcet_score_ref Alts pl \<bind> (\<lambda>scores. max_eliminator_ref scores Alts pl)
       \<le> SPEC (\<lambda>x. x = condorcet Alts pr)" unfolding condorcet.simps
    using  prel arel  scorec  maxc[where x2 = Alts and x'2 = Alts and pl3 = pl and pr3 = pr
        and efn3 = condorcet_score]
      specify_left[where m = "pre_compute_scores condorcet_score_ref Alts pl"
        and f = "(\<lambda>scores. max_eliminator_ref scores Alts pl)"
        and M = "SPEC (\<lambda>x. x = max_eliminator condorcet_score Alts pr)"
        and \<Phi> = "(\<lambda>map. map = pre_computed_map condorcet_score Alts pr)"]
    by blast
qed 

term "(condorcet_ref,  (RETURN oo condorcet))"


lemmas cond_ref[sepref_fr_rules] = condorcet_elim_sepref.refine[FCOMP condorcet_ref_correct]

end

lemmas cond = fixed_alts.condorcet_ref_correct

end