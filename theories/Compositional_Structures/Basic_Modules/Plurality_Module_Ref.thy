theory Plurality_Module_Ref
  imports 
          "Verified_Voting_Rule_Construction.Plurality_Rule"
           "Component_Types/Elimination_Module_Ref"
begin


definition plur_score_ref :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "plur_score_ref x A p = (wc_fold p x)"

lemma plur_score_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and prel: "(pl, pr) \<in> profile_rel"
    and profp: "profile A pr"
  shows "\<forall> a \<in> A. plur_score_ref a A pl \<le> SPEC (\<lambda> sc. sc = (plur_score a A pr))"
  unfolding plur_score_ref_def plur_score.simps
proof safe
  fix a :: 'a
  from prel profp have profl: "profile_l A pl" using profile_ref by auto 
  show "wc_fold pl a \<le> SPEC (\<lambda>sc. sc = win_count pr a) "
    by (refine_vcg fina prel profl wc_fold_correct)
qed

definition pre_compute_plur_scores :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a \<rightharpoonup> nat) nres" 
  where "pre_compute_plur_scores A pl \<equiv> do {
   zeromap:: 'a Scores_Map  <- init_map A;
  nfoldli pl (\<lambda>_. True) 
    (\<lambda>ballot map. 
     RETURN (if (length ballot > 0) then do {
      let top = ballot!0;
      let scx = the (map top);
        (map(top\<mapsto>(Suc scx)))}
       else map)
    ) (zeromap)}"

lemma plurality_map_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and prel: "(pl, pr) \<in> profile_rel"
    and profp: "profile A pr"
  shows "pre_compute_plur_scores A p \<le> pre_compute_scores plur_score_ref A p"
  unfolding pre_compute_plur_scores_def pre_compute_scores_def
  plur_score_ref_def wc_fold_def
  using assms empty_map
  oops

definition plurality_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "plurality_ref A pl \<equiv> do {
   scores <- (pre_compute_scores plur_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma plurality_ref_correct:
  shows "(uncurry plurality_ref, uncurry (RETURN oo plurality_mod)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (intro frefI nres_relI,  clarsimp simp del:  plurality_mod.simps plur_score.simps,
     unfold plurality_ref_def plurality_mod.simps
     RETURN_SPEC_conv, rename_tac A pl pr)
  note max_eliminator_ref_correct_pc[where A = A and efn_ref = plur_score_ref and
       efn = plur_score]
  fix A :: "'a::{default, heap, hashable} set"
  fix pr :: "'a Profile"
  fix pl :: "'a Profile_List"
  assume fina: "finite A"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume profp: "profile A pr"
  show " pre_compute_scores plur_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> SPEC (\<lambda>x. x = max_eliminator plur_score A pr)"
    using max_eliminator_ref_correct_pc plur_score_correct fina prel profp
    by metis   
qed
   
sepref_definition plurality_elim_sep is
  "uncurry plurality_ref":: 
    "(hs.assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding plurality_ref_def  max_eliminator_ref_def plur_score_ref_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] wc_fold_def[abs_def] 
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

lemma plurality_elim_sep_correct [sepref_fr_rules]:
  shows "(uncurry plurality_elim_sep, uncurry (RETURN \<circ>\<circ> plurality_mod))
        \<in> [\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a 
    (list_assn (hr_comp (ballot_impl_assn id_assn) ballot_rel))\<^sup>k 
        \<rightarrow> (result_impl_assn id_assn)"
  using plurality_elim_sep.refine[FCOMP plurality_ref_correct]
  set_rel_id hr_comp_Id2 by simp

end