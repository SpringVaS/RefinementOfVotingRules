section \<open>Elimination Module\<close>

theory Elimination_Module_Ref
  imports "Verified_Voting_Rule_Construction.Elimination_Module"
          Evaluation_Function_Ref
          Electoral_Module_Ref
Refine_Imperative_HOL.IICF
begin

text \<open>
  This is the elimination module. It rejects a set of alternatives only if
  these are not all alternatives. The alternatives potentially to be rejected
  are put in a so-called elimination set. These are all alternatives that score
  below a preset threshold value that depends on the specific voting rule.
\<close>

subsection \<open>Definition\<close>

type_synonym Threshold_Value = "nat"

type_synonym Threshold_Relation = "nat \<Rightarrow> nat \<Rightarrow> bool"





definition eliminate:: "'a Scores_Map  \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 
                          'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a set \<times> 'a set) nres" where
 "eliminate scoremap t r A p \<equiv> do {
  FOREACH (A)
    (\<lambda>x (rej, def). do {
      ASSERT (x \<in> dom scoremap);
      let scx = the (scoremap x);
      (if (r scx t) then 
          RETURN (insert x rej, def) 
      else 
          RETURN(rej, insert x def))
    }) ({}, {})

    
}"

definition elimination_module_ref :: 
"'a Scores_Map  \<Rightarrow> Threshold_Value \<Rightarrow>
Threshold_Relation \<Rightarrow> 'a Electoral_Module_Ref " 
  where
  "elimination_module_ref scores threshold r A p \<equiv> do {
    (rej, def) <- eliminate scores threshold r A p;
   if (def = {}) then
       \<comment> \<open>Here rej will be a copy of A\<close>
     RETURN({},{},rej)
    else
     RETURN ({},rej,def)
  }"


definition pre_computed_map :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a \<rightharpoonup> nat)"  where
  "pre_computed_map e Alts pro \<equiv> ((\<lambda>a. Some (e a Alts pro))|`Alts )"




context voting_session
begin

lemma compute_scores_correct:
  fixes eref :: "'a Evaluation_Function_Ref"
  and e :: "'a Evaluation_Function"
  assumes "(eref, (\<lambda> a Alts pro. RETURN (e a Alts pro))) \<in> evalf_rel"
  shows "(pre_compute_scores eref A pl, SPEC (\<lambda> map. map = pre_computed_map e A pr)) \<in> 
    \<langle>Id\<rangle>nres_rel"
  unfolding pre_compute_scores_def pre_computed_map_def
  apply (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it r. r = (\<lambda> a. Some (e a A pr))|`(A - it))"])
  apply (auto simp add: fina)
proof -
  fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda>a. Some (e a A pr)) |` (A - it))(x \<mapsto> (e x A pr)) =
                      (\<lambda>a. Some (e a A pr)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda>scx. ((\<lambda>a. Some (e a A pr)) |` (A - it))(x \<mapsto> scx) =
                   (\<lambda>a. Some (e a A pr)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = (e x A pr))"
    by (metis map_upd_eqD1)
  from profrel have prel: "(pl, pr) \<in> profile_rel" using profile_type_ref by auto
  from prel assms(1)[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD]
    this have "(eref x A pl) \<le> SPEC(\<lambda> scx. scx = (e x A pr))"
    by (metis IdI SPEC_eq_is_RETURN(2) refine_IdD set_rel_id_simp) 
  from this mapupdeq show " (eref x A pl)
       \<le> SPEC (\<lambda>scx. ((\<lambda>a. Some (e a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>a. Some (e a A pr)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 



lemma scoremax_correct:
  fixes e :: "'a Evaluation_Function"
  assumes "(eref, (\<lambda> a Alts pro. RETURN (e a Alts pro))) \<in> evalf_rel"
  shows "scoremax A (pre_computed_map e A pr) 
\<le> SPEC (\<lambda> max. max = Max {(e a A pr) | a. a \<in> A})"
  unfolding scoremax_def pre_computed_map_def
  apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). (e a A pr) \<le> max) 
      \<and> ((\<exists>a \<in> (A - it). max = (e a A pr)) \<or> max = 0))"] )
  apply (auto simp add: fina)
  subgoal by (metis Diff_iff leD nle_le order_trans)
  subgoal by (metis DiffI order_less_imp_le)
  using max_score_in[where A= A and f = "(\<lambda> x. e x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. e x A pr)"]
  subgoal by (metis (mono_tags, lifting) order_antisym_conv)
proof -
  assume "\<forall>a\<in>A. e a A pr = 0"
  from this have eq: "{e a A pr |a. a \<in> A} = {0}"
    using nempa Max_singleton by force
  have "Max {0} = 0"
    using Max_singleton by blast
  from eq this show " Max {e a A pr |a. a \<in> A} = 0"
    by simp
qed
  

end


subsection \<open>Common Eliminators\<close>
                                   
fun less_eliminator_ref :: "'a Scores_Map  \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "less_eliminator_ref e tc A p = elimination_module_ref e tc (<) A p"

fun max_eliminator_ref ::  "'a Scores_Map \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "max_eliminator_ref e A p = do {
    t <- (scoremax A e); 
    (less_eliminator_ref e t A p)
 }"

fun leq_eliminator_ref :: "'a Scores_Map \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "leq_eliminator_ref e t A p = elimination_module_ref e t (\<le>) A p"

fun min_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "min_eliminator e A p =
    leq_eliminator e (Min {e x A p | x. x \<in> A}) A p"

fun average :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                    Threshold_Value" where
  "average e A p = (\<Sum> x \<in> A. e x A p) div (card A)"

fun less_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "less_average_eliminator e A p = less_eliminator e (average e A p) A p"

fun leq_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "leq_average_eliminator e A p = leq_eliminator e (average e A p) A p"

fun plur_score :: "'a Evaluation_Function_Ref" where
  "plur_score x A p = (wc_fold p x)"

definition plur_test :: "'a Electoral_Module_Ref" where
  "plur_test A pl \<equiv> do {
   scores <- (pre_compute_scores plur_score A pl);
   max_eliminator_ref scores A pl
}"

sepref_definition plurality_elim_sepref is
  "uncurry plur_test":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plur_test_def  max_eliminator_ref.simps plur_score.simps
    less_eliminator_ref.simps  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (\<hole>, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, \<hole>, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (\<hole>, rej, def))" hs.fold_custom_empty)

  apply sepref_dbg_keep
  done
 