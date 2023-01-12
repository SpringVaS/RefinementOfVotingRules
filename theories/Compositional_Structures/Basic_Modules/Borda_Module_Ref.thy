theory Borda_Module_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Module"
           "Component_Types/Elimination_Module_Ref"
begin

fun borda_score_mon :: "'a Evaluation_Function_Ref" where
  "borda_score_mon x A p =
    FOREACH A (\<lambda> y sc. do {
      pcx <- prefer_count_monadic_imp p x y; 
      RETURN (sc + pcx)})
    (0::nat)"

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
  apply (refine_vcg FOREACH_rule[where I = 
          "(\<lambda>it sc. sc = (\<Sum> y \<in> (A - it). (prefer_count pr x y)))"])
     apply (auto simp add: fina simp del:  prefer_count.simps)
proof (-)
  fix xa :: 'a
  fix it :: "'a set"
  assume xit: "xa \<in> it"
  assume itA: "it \<subseteq> A"
  from profrel have "(pl, pr) \<in> profile_rel" using profile_type_ref
    by fastforce
  from this have pcref: "prefer_count_monadic_imp pl x xa 
        \<le> SPEC (\<lambda> pcxa. pcxa = prefer_count pr x xa)" 
    using prefer_count_monadic_imp_correct by fastforce
  from fina itA xit have "sum (prefer_count pr x) (A - it) + (prefer_count pr x xa)
    = sum (prefer_count pr x) (A - (it - {xa}))"
  by (metis Diff_iff ab_semigroup_add_class.add.commute finite_Diff it_step_insert_iff sum.insert)
  from pcref this show "prefer_count_monadic_imp pl x xa
       \<le> SPEC (\<lambda>pcx. sum (prefer_count pr x) (A - it) + pcx =
                      sum (prefer_count pr x) (A - (it - {xa})))"
    by (metis (mono_tags, lifting) SPEC_cons_rule)
qed


lemma borda_score_evalf_rel:
  shows "(borda_score_mon, (\<lambda> x A p. RETURN ( borda_score x A p )))
    \<in> evalf_rel"
  apply (refine_vcg)
proof (clarify, unfold borda_score_mon.simps, rename_tac  x' x A' A pl pr)
  fix A' A :: "'a set"
  fix x :: 'a
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>fset_rel"
  assume prel: "(pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: fset_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: fset_rel_def in_br_conv)
  from this 
  show "FOREACH A' (\<lambda>y sc. prefer_count_monadic_imp pl x y \<bind> (\<lambda>pcx. RETURN (sc + pcx))) 0
       \<le> SPEC (\<lambda>c. (c, borda_score x A pr) \<in> nat_rel)"
  proof (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it sc. sc = (\<Sum> y \<in> (A - it). (prefer_count pr x y)))"],
      clarsimp_all simp add: fina aeq simp del:  prefer_count.simps)
    fix xa :: 'a
    fix it :: "'a set"
    assume xit: "xa \<in> it"
    assume itA: "it \<subseteq> A"
    from prel have pcref: "prefer_count_monadic_imp pl x xa 
        \<le> SPEC (\<lambda> pcxa. pcxa = prefer_count pr x xa)" 
    using prefer_count_monadic_imp_correct by fastforce
    from fina itA xit aeq have "sum (prefer_count pr x) (A - it) + (prefer_count pr x xa)
      = sum (prefer_count pr x) (A - (it - {xa}))"
      by (metis Diff_iff ab_semigroup_add_class.add.commute finite_Diff it_step_insert_iff sum.insert)
    from pcref this show "prefer_count_monadic_imp pl x xa
       \<le> SPEC (\<lambda>pcx. sum (prefer_count pr x) (A - it) + pcx =
                      sum (prefer_count pr x) (A - (it - {xa})))"
    by (metis (mono_tags, lifting) SPEC_cons_rule)
  qed
qed



locale sepvs = voting_session 

begin                                       

lemma bcseptest:
  shows "(borda_monadic, (\<lambda> A p. RETURN (borda A p))) \<in>
    (alts_set_rel) \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg)
proof (unfold borda_monadic_def borda.simps, rename_tac Al' Al ppl ppr)
  fix Al' Al :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume "(pl, pr) \<in> profile_rel"
  assume arel: "(Al', Al) \<in> alts_set_rel"
  from this have Alid: "(Al', Al) \<in> Id"
    by (simp add: in_br_conv)
  from arel have fina: "finite Al'"   by (simp add: in_br_conv)
  from Alid have Ale: "Al' = Al" by auto
  from this  have "pre_compute_scores borda_score_mon Al' pl 
          \<le> SPEC (\<lambda> map. map = pre_computed_map borda_score Al' pr)"
  using fina borda_score_evalf_rel[where A = Al']
      compute_scores_correct[THEN nres_relD, THEN refine_IdD]
  by fastforce 


theorem borda_ref_correct:
  shows "borda_monadic A pl \<le> SPEC (\<lambda> res. res = borda A pr)"
proof (unfold borda_monadic_def borda.simps)
  have "pre_compute_scores borda_score_mon A pl 
          \<le> SPEC (\<lambda> map. map = pre_computed_map borda_score A pr)"
  using fina borda_score_evalf_rel[where A = A]
      compute_scores_correct[THEN nres_relD, THEN refine_IdD]
  by fastforce 
  from this show "pre_compute_scores borda_score_mon A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
    \<le> SPEC (\<lambda>res. res = max_eliminator borda_score A pr)"
    using max_eliminator_ref_correct[where efn = borda_score] 
      specify_left[where m = "pre_compute_scores borda_score_mon A pl"
          and \<Phi> = "(\<lambda>map. map = pre_computed_map borda_score A pr)"
          and f = "(\<lambda>scores. max_eliminator_ref scores A pl)"
          and M = "SPEC (\<lambda>res. res = max_eliminator borda_score A pr)"]
    by fastforce
qed

(*lemma bcseptest:
  shows "(borda_monadic, (\<lambda> A p. RETURN (borda A p))) \<in>
    (\<langle>Id\<rangle>set_rel O br (\<lambda>x. x) finite) \<rightarrow> profile_rel \<rightarrow>  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  apply (refine_vcg)
proof (unfold borda_monadic_def borda.simps, rename_tac Al' Al ppl ppr)
*)






abbreviation "profile_impl_assn \<equiv> (list_assn (array_assn nat_assn))"

abbreviation "alts_set_impl_assn \<equiv> (hs.assn nat_assn)"


definition "alts_set_assn 
    \<equiv> hr_comp alts_set_impl_assn alts_set_rel"

find_theorems id_assn

sepref_definition borda_elim_sepref is
  "uncurry borda_monadic":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding borda_monadic_def  max_eliminator_ref.simps borda_score_mon.simps
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


thm borda_elim_sepref.refine

end
end