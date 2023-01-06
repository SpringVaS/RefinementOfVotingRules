section \<open>Elimination Module\<close>

theory Elimination_Module_Ref
  imports Evaluation_Function_Ref
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

type_synonym 'a Scores_Map = "('a \<rightharpoonup> nat)"

type_synonym 'a Threshold_Compute = "'a set \<Rightarrow> 'a Scores_Map \<Rightarrow> nat nres"

type_synonym 'a Electoral_Set_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a set nres"

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

lemma nbmax:
  fixes f:: "'a \<Rightarrow> nat"
  fixes alt :: 'a
  assumes aA: "alt \<in> A" and fina: "finite A"
  shows "f alt \<le> Max {f x |x. x \<in> A}"
proof -
  from aA have "f alt \<in> {f x |x. x \<in> A}" by blast
  from fina this show ?thesis using Max_ge by auto
qed

lemma nbexmax:
  fixes f:: "'a \<Rightarrow> nat"
  fixes alt :: 'a
  assumes aA: "A \<noteq> {}" and fina: "finite A"
  shows "(\<exists> alt \<in> A. f alt = Max {f x |x. x \<in> A})"
proof -
  from aA have nemp: " {f x |x. x \<in> A} \<noteq> {}" by simp
  from fina have "finite {f x |x. x \<in> A}" by simp
  from nemp this Max_in[where A = "{f x |x. x \<in> A}"]  have "Max {f x |x. x \<in> A} \<in> {f x |x. x \<in> A}"
    by blast
  from this show ?thesis by auto
qed

lemma max_compute_correct:
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
proof -
  fix a :: 'a
  assume aA: "a \<in> A"
  assume bmax: "\<forall>aa\<in>A. e aa A pr \<le> e a A pr"
  from fina have fine: "finite {e x A pr | x. x \<in> A}"
    by simp
  from nempa have nempe: "{e x A pr | x. x \<in> A} \<noteq> {}" by simp
  from fine Max_ge  have "\<forall>aa\<in>A. e aa A pr \<le> Max {e x A pr | x. x \<in> A}"
    by blast
  from this aA have emax: "e a A pr \<le> Max {e x A pr | x. x \<in> A}" by blast
  note ex = nbexmax[where f = "(\<lambda> x. e x A pr)"]
  from emax bmax ex fina nempa show "e a A pr = Max {e a A pr |a. a \<in> A}"
    by auto
next
  assume "\<forall>a\<in>A. e a A pr = 0"
  from this have eq: "{e a A pr |a. a \<in> A} = {0}"
    using nempa Max_singleton by force
  have "Max {0} = 0"
    using Max_singleton by blast
  from eq this show " Max {e a A pr |a. a \<in> A} = 0"
    by simp
qed

lemma scoremax_correct:
  assumes "A = dom scores"
  shows "scoremax A scores \<le> SPEC (\<lambda> max. max = Max {the (scores a) | a. a \<in> A})"
  unfolding scoremax_def
  apply (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it max. ((it \<noteq> A) \<longrightarrow> max = Max {the (scores a) | a. a \<in> (A - it)})
                \<and>   ((it = A) \<longrightarrow> max = 0))"] )
  using fina subgoal by simp
  subgoal by auto
  subgoal by simp
proof -
  fix x :: 'a
  fix it :: "'a set"
  assume "x \<in> it" and itsA: "it \<subseteq> A"
  from this show "x \<in> dom scores" using assms(1) by auto
next
  fix x :: 'a
  fix it :: "'a set"
  fix si :: nat
  assume xit: "x \<in> it" and itsA: "it \<subseteq> A" and xid: "x \<in> dom scores"
  assume sima: "(it \<noteq> A \<longrightarrow> si = Max {the (scores a) |a. a \<in> A - it}) \<and> (it = A \<longrightarrow> si = 0)"
  assume nmax: "si < the (scores x)"
  from fina itsA have fins: "finite (A - (it - {x}))"
    by blast 
  from this have finscores: "finite {the (scores a) |a. a \<in> A - (it - {x})}" 
    using finite_image_set[where P = "\<lambda> e. e \<in> (A - (it - {x}))" and f= "\<lambda>e. the (scores e)"]
          Collect_mem_eq[where A = "A - (it - {x})"]
    by simp
  from xit itsA have xiis: "x \<in> (A - (it - {x}))" by blast
  from this have sci: "the (scores x) \<in> {the (scores a) |a. a \<in> A - (it - {x})}"
    by blast 
  from this finscores have maxax: "the (scores x) \<le> Max {the (scores a) |a. a \<in> A - (it - {x})}"
    using Max_ge[where A = "{the (scores a) |a. a \<in> A - (it - {x})}" and 
        x = "the (scores x)"] by simp
  from this sima nmax show "the (scores x) = Max {the (scores a) |a. a \<in> A - (it - {x})}"
  proof (cases "A = it")
    case Ait: True
    from this xit  have "A - (it - {x}) = {x}"
      by blast 
    from this show ?thesis by auto
  next
    case nemp: False
    from this sima have simax: "si = Max {the (scores a) |a. a \<in> A - it}" by simp
    from this maxax nmax have "si \<le> Max {the (scores a) |a. a \<in> A - (it - {x})}" 
      by linarith
    have ext: "A - (it - {x}) = (A - it) \<union> {x}"
      using xiis by fastforce 
    from itsA xit have subsetx: "{the (scores a) |a. a \<in> A - it} 
        \<subseteq> {the (scores a) |a. a \<in> A - (it - {x})}"
      by blast
    from this finscores finite_subset have finsbas: "finite {the (scores a) |a. a \<in> A - it}"
      by blast 
    from subsetx xid sci itsA xit  have "{a. a \<in> ((A - it) \<union> {x})} = 
      {a. a \<in> (A - it)} \<union> {a. a \<in> {x}}"
      using Collect_mem_eq[where A = "(A - it) \<union> {x}"]
      using Collect_mem_eq[where A = "(A - it)"]
      using Collect_mem_eq[where A = "{x}"]
      by presburger
    from this ext
    have comp: "{the (scores a)  | a. a \<in> (A - it)} \<union> {the (scores x)} =
    {the (scores a) | a. a \<in> (A - (it - {x}))}"
      by blast
    from nemp itsA have nempset: "{the (scores a) |a. a \<in> A - it} \<noteq> {}"
      by blast
    have fsing: "finite {the (scores x)}" by blast
    have nempsing: "{the (scores x)} \<noteq> {}" by blast
    from finsbas nempset fsing nempsing have maxcomp: "Max ({the (scores a) | a. a \<in> (A - it)} \<union> {the (scores x)})
         = max (Max {the (scores a) |a. a \<in> A - it}) (the (scores x))"
      using Max_Un[where A = "{the (scores a) |a. a \<in> A - it}" and B = "{the (scores x)}"]
      by auto
    from comp have "Max ({the (scores a)  | a. a \<in> (A - it)} \<union> {the (scores x)})
        = Max {the (scores a) | a. a \<in> (A - (it - {x}))}" by simp
    from maxcomp simax this have "Max {the (scores a) | a. a \<in> (A - (it - {x}))}
        = max si (the (scores x))" by simp
    from this nmax have "Max {the (scores a) | a. a \<in> (A - (it - {x}))} = the (scores x)"
      by simp
    from this show ?thesis by simp
  qed
next
  fix x :: 'a
  fix it :: "'a set"
  fix si :: nat
  assume xit: "x \<in> it" and itsA: "it \<subseteq> A"
  assume procA: "it - {x} = A"
  from xit itsA have "it - {x} \<noteq> A" by auto
  from this procA have "False" by simp
  from this show "the (scores x) = 0" by simp
next
  fix si :: nat
  assume "({} \<noteq> A \<longrightarrow> si = Max {the (scores a) |a. a \<in> A - {}}) \<and> {} = A \<longrightarrow> si = 0"
  oops
  

end
definition eliminate:: "'a Scores_Map  \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 
                          'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a set \<times> 'a set) nres" where
 "eliminate scoremap t r A p \<equiv> do {
   FOREACH (A)
    (\<lambda>x (rej, def). do {
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
    (if (rej \<noteq> A) 
      then RETURN ({},rej,def) 
      else RETURN ({},{},A))
  }"



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
