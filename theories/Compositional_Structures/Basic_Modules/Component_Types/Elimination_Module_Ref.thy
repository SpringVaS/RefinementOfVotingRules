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

type_synonym 'a Scores_Map = "('a \<rightharpoonup> nat)"

definition pre_compute_scores :: "'a Evaluation_Function_Ref \<Rightarrow>
 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a \<rightharpoonup> nat) nres" 
  where "pre_compute_scores ef A p \<equiv>
  FOREACH A 
    (\<lambda>x m. do {
      scx \<leftarrow> (ef x A p);
      RETURN (m(x\<mapsto>scx))
  }) (Map.empty)"

definition scoremax :: "'a set \<Rightarrow> 'a Scores_Map \<Rightarrow> nat nres" where 
 "scoremax A scores \<equiv> do {
  FOREACH (A)
    (\<lambda>x max. do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      (if (scx > max) then 
          RETURN (scx) 
      else 
          RETURN(max))
    }) (0::nat)
}"

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
     RETURN ({},{},rej)
    else
     RETURN ({},rej,def)
  }"


definition pre_computed_map :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a \<rightharpoonup> nat)"  where
  "pre_computed_map e Alts pro \<equiv> ((\<lambda>a. Some (e a Alts pro))|`Alts )"


lemma eliminate_correct:
  fixes e :: "'a Evaluation_Function"
  and A :: "'a set"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  assumes fina: "finite A"
  shows "(eliminate (pre_computed_map e A pr) t r A pl \<le> 
    SPEC (\<lambda> (rej,def). (rej,def) = ((elimination_set e t r A pr), A - (elimination_set e t r A pr))))"
  unfolding pre_computed_map_def eliminate_def
  apply (refine_vcg FOREACH_rule
      [where I = "\<lambda> it (rej, def). rej = ((elimination_set e t r A pr) - it)
                \<and> def = (A - it) - (elimination_set e t r (A) pr)"])
  by (auto simp add: fina)


context voting_session
begin

theorem elimination_module_ref_correct:
  fixes efn :: "'a Evaluation_Function"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  shows "(elimination_module_ref (pre_computed_map efn A pr) t r A pl \<le> 
            SPEC (\<lambda> em. em = (elimination_module efn t r A pr)))"
  unfolding  elimination_module_ref_def
  apply (refine_vcg eliminate_correct)
  by (auto simp add: fina)

lemma compute_scores_correct_weak_evalref:
  fixes eref :: "'a Evaluation_Function_Ref"
  and e :: "'a Evaluation_Function"
  assumes "((\<lambda> x. eref x A), (\<lambda> x p. RETURN ( e x A p))) \<in> evalf_profA_rel A"
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
  from profrel assms(1)[THEN fun_relD, THEN fun_relD, THEN nres_relD]
    this have "(eref x A pl) \<le> SPEC(\<lambda> scx. scx = (e x A pr))"
    by (metis IdI SPEC_eq_is_RETURN(2) refine_IdD) 
  from this mapupdeq show " (eref x A pl)
       \<le> SPEC (\<lambda>scx. ((\<lambda>a. Some (e a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>a. Some (e a A pr)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 


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
  "less_eliminator_ref e t A p = elimination_module_ref e t (<) A p"

fun max_eliminator_ref ::  "'a Scores_Map \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "max_eliminator_ref e A p = do {
    t <- (scoremax A e); 
    (less_eliminator_ref e t A p)
 }"

context voting_session
begin

lemma less_eliminator_correct:
  fixes efn :: "'a Evaluation_Function"
  and t :: "Threshold_Value"
  shows "(less_eliminator_ref (pre_computed_map efn A pr) t A pl \<le>
            SPEC (\<lambda> em. em = (less_eliminator efn t A pr)))"
  unfolding less_eliminator_ref.simps less_eliminator.simps
  by (refine_vcg elimination_module_ref_correct)

theorem max_eliminator_ref_correct:
  fixes efn :: "'a Evaluation_Function"
  shows "(max_eliminator_ref (pre_computed_map efn A pr) A pl \<le>
            SPEC (\<lambda> em. em = max_eliminator efn A pr))"
  unfolding max_eliminator_ref.simps max_eliminator.simps
  apply (refine_vcg scoremax_correct less_eliminator_correct)
  by auto

end

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

end