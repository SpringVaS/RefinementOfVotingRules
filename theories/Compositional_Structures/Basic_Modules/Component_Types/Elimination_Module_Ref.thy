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
                          'a set \<Rightarrow> ('a set \<times> 'a set) nres" where
 "eliminate scoremap t r A \<equiv> do {
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
    (rej, def) <- eliminate scores threshold r A;
   if (def = {}) then
       \<comment> \<open>Here rej will be a copy of A\<close>
     RETURN ({},{},rej)
    else
     RETURN ({},rej,def)
  }"


definition pre_computed_map :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a \<rightharpoonup> nat)"  where
  "pre_computed_map e Alts pro \<equiv> ((\<lambda>a. Some (e a Alts pro))|`Alts )"


lemma eliminate_correct:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and p :: "'a Profile"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  assumes  fina: "finite A" 
  shows "eliminate (pre_computed_map efn A p) t r A
    \<le> SPEC (\<lambda> (rej,def). 
    (rej,def) = ((elimination_set efn t r A p), A - (elimination_set efn t r A p)))"
  unfolding pre_computed_map_def eliminate_def
  by (refine_vcg FOREACH_rule
      [where I = "\<lambda> it (rej, def). rej = ((elimination_set efn t r A p) - it)
                \<and> def = (A - it) - (elimination_set efn t r A p)"],auto simp add: fina)


lemma compute_scores_correct:
  fixes A :: "'a set"
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  fixes efnref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  assumes 
     fina: "finite A" and 
     prel: "(pl, pr) \<in> profile_rel" and
  efnrel:  "\<forall>a \<in> A. efnref a A pl \<le> SPEC (\<lambda>score. score = (efn a A pr))"
  shows "pre_compute_scores efnref A pl \<le>
   SPEC(\<lambda> map. map = (pre_computed_map efn A pr))"
  unfolding pre_compute_scores_def pre_computed_map_def
proof (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it r. r = (\<lambda> a. Some (efn a A pr))|`(A - it))"],
        clarsimp_all simp add: fina)
    fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda>a. Some (efn a A pr)) |` (A - it))(x \<mapsto> (efn x A pr)) =
                      (\<lambda>a. Some (efn a A pr)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda>scx. ((\<lambda>a. Some (efn a A pr)) |` (A - it))(x \<mapsto> scx) =
                   (\<lambda>a. Some (efn a A pr)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = (efn x A pr))"
    by (metis map_upd_eqD1)
  from efnrel xiA have "efnref x A pl \<le> SPEC (\<lambda>score. score = (efn x A pr))"
    by fastforce
  from this mapupdeq show "efnref x A pl
       \<le> SPEC (\<lambda>scx. ((\<lambda>a. Some (efn a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>a. Some (efn a A pr)) |` (A - (it - {x})))"
    using  it_step_insert_iff restrict_map_insert
    by presburger
qed

lemma compute_scores_correctrel:
  shows "(pre_compute_scores, (\<lambda> e A pr. SPEC(\<lambda> map. map = (pre_computed_map e A pr)))) \<in> 
   evalf_rel \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding pre_compute_scores_def pre_computed_map_def
proof (refine_vcg, rename_tac eref efun A' A pl pr )
  fix eref :: "'a Evaluation_Function_Ref" 
  fix efun :: "'a Evaluation_Function"
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume eref_refine: "(eref, efun) \<in> evalf_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  assume profrel: " (pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: finite_set_rel_def in_br_conv)
  show "       FOREACH A' (\<lambda>x m. eref x A' pl \<bind> (\<lambda>scx. RETURN (m(x \<mapsto> scx)))) Map.empty
       \<le> SPEC (\<lambda>map. map = (\<lambda>a. Some (efun a A pr)) |` A)"
  proof (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it r. r = (\<lambda> a. Some (efun a A pr))|`(A - it))"], auto simp add: aeq)
    from fina aeq  show "finite A" by (simp)
  next       
  fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> (efun x A pr)) =
                      (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda>scx. ((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> scx) =
                   (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = (efun x A pr))"
    by (metis map_upd_eqD1)
  note evalfeq
  from profrel fina aeq  eref_refine this profrel  have "(eref x A pl) \<le> SPEC(\<lambda> scx. scx = (efun x A pr))"
      using RETURN_SPEC_conv
      by (metis empty_iff xiA) 
  from this mapupdeq show " eref x A pl
       \<le> SPEC (\<lambda>scx. ((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 
qed


lemma compute_scores_correct_prof:
  shows "((\<lambda> e (A, pr). pre_compute_scores e A pr), (\<lambda> e (A, pr). SPEC(\<lambda> map. map = (pre_computed_map e A pr)))) \<in> 
   evalf_rel_prof \<rightarrow> \<langle>Id\<rangle>alt_and_profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding pre_compute_scores_def pre_computed_map_def
proof (clarify, refine_vcg, rename_tac e e_ref A' pl A pr )
  fix eref :: "'a Evaluation_Function_Ref" 
  fix efun :: "'a Evaluation_Function"
  fix A' A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a:: 'a
  assume rel: "((A', pl), A, pr) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  from rel have arel : "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel" 
    using unfold_alt_profile_alt_rel by blast
  from rel have prel: "(pl, pr) \<in> profile_rel " using unfold_alt_profile_prof_rel
    by blast
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A" by (auto simp add: finite_set_rel_def in_br_conv)
  assume eref_refine: "(eref, efun) \<in> evalf_rel_prof"
  from rel have profprop: "profile_l A pl" using aeq unfold_alt_profile_prof_prop
    by blast
  show "FOREACH A' (\<lambda>x m. eref x A' pl \<bind> (\<lambda>scx. RETURN (m(x \<mapsto> scx)))) Map.empty
       \<le> SPEC (\<lambda>map. map = (\<lambda>a. Some (efun a A pr)) |` A)"
  proof (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it r. r = (\<lambda> a. Some (efun a A pr))|`(A - it))"], auto simp add: aeq)
    from fina aeq  show "finite A" by (simp)
  next       
  fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> (efun x A pr)) =
                      (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda>scx. ((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> scx) =
                   (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = (efun x A pr))"
    by (metis map_upd_eqD1)
  note evalproffeq
  from eref_refine this rel  
    have "(eref x A pl) \<le> SPEC(\<lambda> scx. scx = (efun x A pr))"
      using RETURN_SPEC_conv 
      by (metis) 
  from this mapupdeq show " eref x A pl
       \<le> SPEC (\<lambda>scx. ((\<lambda>a. Some (efun a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>a. Some (efun a A pr)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 
qed



theorem elimination_module_ref_correct:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
    assumes fina: "finite A"  and
  "(pl, pr) \<in> profile_rel"
shows "elimination_module_ref (pre_computed_map efn A pr) t r A pl \<le>
        SPEC (\<lambda> em. em = (elimination_module efn t r A pr))"
  by (unfold elimination_module_ref_def, refine_vcg eliminate_correct,
    auto simp add: fina)
  

lemma scoremax_correct:
  fixes A :: "'a set"
  assumes fina: "finite A" and nempa: "A \<noteq> {}"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  shows "scoremax A (pre_computed_map efn A pr)
 \<le> SPEC (\<lambda> max. max = Max {(efn a A pr) | a. a \<in> A})"
proof (unfold scoremax_def pre_computed_map_def)
  show "FOREACH A
     (\<lambda>x max.
         ASSERT (x \<in> dom ((\<lambda>a. Some (efn a A pr)) |` A)) \<bind>
         (\<lambda>_. let scx = the (((\<lambda>a. Some (efn a A pr)) |` A) x)
               in if max < scx then RETURN scx else RETURN max))
     0
    \<le> SPEC (\<lambda>max. max = Max {efn a A pr |a. a \<in> A})"
    apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). (efn a A pr) \<le> max)
      \<and> ((\<exists>a \<in> (A - it). max = (efn a A pr)) \<or> max = 0))"], clarsimp_all simp add:  fina nempa,
         auto)
  using max_score_in[where A= A and f = "(\<lambda> x. efn x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. efn x A pr)"] 
  apply (metis DiffI dual_order.trans order_less_imp_le)
  using max_score_in[where A= A and f = "(\<lambda> x. efn x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. efn x A pr)"] 
proof ((metis (mono_tags, lifting) order_antisym_conv))
  assume all0: "\<forall>a\<in>A. efn a A pr = 0"
  from all0 have eq: "{efn a A pr |a. a \<in> A} = {0}"
    using nempa Max_singleton by force
  have "Max {0} = 0"
    using Max_singleton by blast
  from eq this  show " Max {efn a A pr |a. a \<in> A} = 0"
    by simp
qed
qed

subsection \<open>Common Eliminators\<close>
                                   
definition less_eliminator_ref :: "'a Scores_Map  \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "less_eliminator_ref e t A p \<equiv> elimination_module_ref e t (<) A p"

definition max_eliminator_ref ::  "'a Scores_Map \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "max_eliminator_ref e A p \<equiv>
    if (A = {}) then
      RETURN ({},{},{})
    else do {
    t <- (scoremax A e); 
    (less_eliminator_ref e t A p)
 }"

lemma less_eliminator_ref_correct:
  fixes A :: "'a set"
  and efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  assumes fina: "finite A" 
  and prel: "(pl, pr) \<in> profile_rel"
  shows "(less_eliminator_ref (pre_computed_map efn A pr) t A pl) \<le>
            SPEC (\<lambda> em. em = (less_eliminator efn t A pr))"
  unfolding less_eliminator_ref_def less_eliminator.simps
proof (-)
 show "elimination_module_ref (pre_computed_map efn A pr) t (<) A pl
       \<le> SPEC (\<lambda>em. em = elimination_module efn t (<) A pr) "
   using fina prel elimination_module_ref_correct by blast
qed

lemma max_eliminator_ref_correct:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  assumes fina: "finite A"
  assumes prel: "(pl, pr) \<in> profile_rel"
  shows "(max_eliminator_ref (pre_computed_map efn A pr) A pl
          \<le> SPEC (\<lambda> em. em = max_eliminator efn A pr))"
proof (unfold max_eliminator_ref_def, refine_vcg)
  show "A = {} \<Longrightarrow> ({}, {}, {}) = max_eliminator efn A pr" by simp
next
  assume nempa: "A \<noteq> {}"
  from fina nempa have scoremax_ins: "scoremax A (pre_computed_map efn A pr) \<le> SPEC (\<lambda>max. max = Max {efn a A pr |a. a \<in> A})"
    using scoremax_correct by blast
  have less_elim_ins: " (\<And>x. x = Max {efn a A pr |a. a \<in> A} \<Longrightarrow>
          less_eliminator_ref (pre_computed_map efn A pr) x A pl
          \<le> SPEC (\<lambda>em. em = less_eliminator efn (Max {efn a A pr |a. a \<in> A}) A pr))"
    using fina prel less_eliminator_ref_correct[where A = A and pl = pl and pr = pr and efn = efn]
    by fastforce
  show "scoremax A (pre_computed_map efn A pr)
    \<le> SPEC (\<lambda>t. less_eliminator_ref (pre_computed_map efn A pr) t A pl
                 \<le> SPEC (\<lambda>em. em = max_eliminator efn A pr))"
    unfolding max_eliminator.simps 
    using scoremax_ins less_elim_ins  SPEC_cons_rule[where m = "scoremax A (pre_computed_map efn A pr)"
      and \<Phi> = "(\<lambda>max. max = Max {efn a A pr |a. a \<in> A})"
      and \<Psi> = "(\<lambda> t. less_eliminator_ref (pre_computed_map efn A pr) t A pl
                 \<le> SPEC (\<lambda>em. em = less_eliminator efn (Max {efn a A pr |a. a \<in> A}) A pr))"]
    by blast
qed
  


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