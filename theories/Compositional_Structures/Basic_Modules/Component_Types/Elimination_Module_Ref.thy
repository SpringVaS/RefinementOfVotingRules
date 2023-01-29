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

(* Needed for Sepref Correctness Proof When uncurrying Alternatives and Profile  *)
type_synonym 'a Electoral_Module_Ref_Cur = "('a set \<times> 'a Profile_List) \<Rightarrow> 'a Result nres"


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
  fixes e :: "'a Evaluation_Function"
  and p :: "'a Profile"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  shows "((\<lambda> A. eliminate (pre_computed_map e A p) t r A), 
    (\<lambda> A. SPEC (\<lambda> (rej,def). (rej,def) = ((elimination_set e t r A p), A - (elimination_set e t r A p)))))
    \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding pre_computed_map_def eliminate_def
proof (refine_vcg, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  show " FOREACH A'
        (\<lambda>x (rej, def).
            ASSERT (x \<in> dom ((\<lambda>a. Some (e a A' p)) |` A')) \<bind>
            (\<lambda>_. let scx = the (((\<lambda>a. Some (e a A' p)) |` A') x)
                  in if r scx t then RETURN (insert x rej, def) else RETURN (rej, insert x def)))
        ({}, {})
       \<le> SPEC (\<lambda>(rej, def). (rej, def) = (elimination_set e t r A p, A - elimination_set e t r A p))"
  proof (refine_vcg FOREACH_rule
      [where I = "\<lambda> it (rej, def). rej = ((elimination_set e t r A p) - it)
                \<and> def = (A - it) - (elimination_set e t r (A) p)"], clarsimp_all simp add: fina,
        auto simp add: aeq)
  qed
qed


lemma compute_scores_correct:
  shows "(pre_compute_scores, (\<lambda> e A pr. SPEC(\<lambda> map. map = (pre_computed_map e A pr)))) \<in> 
   evalf_rel \<rightarrow> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding pre_compute_scores_def pre_computed_map_def
proof (refine_vcg, rename_tac eref efun A' A pl pr )
  fix eref :: "'a Evaluation_Function_Ref" 
  fix efun :: "'a Evaluation_Function"
  fix A' A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume eref_refine: "(eref, efun) \<in> evalf_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  assume profrel: " (pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
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
  from rel have arel : "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel" 
    using unfold_alt_profile_alt_rel by blast
  from rel have prel: "(pl, pr) \<in> profile_rel " using unfold_alt_profile_prof_rel
    by blast
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have nempa: "A \<noteq> {}" by (auto simp add: alt_set_rel_def in_br_conv)
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
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  assumes "(pl, pr) \<in> profile_rel"
shows "(\<lambda> A. (elimination_module_ref (pre_computed_map efn A pr) t r A pl),
        (\<lambda> A. SPEC (\<lambda> em. em = (elimination_module efn t r A pr))))
      \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding em_rel_def
  unfolding elimination_module_ref_def
proof (clarify, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  note elimalg = eliminate_correct[THEN fun_relD, THEN nres_relD, THEN refine_IdD,
          where x2=A' and x'2 = A]
  from arel have " (eliminate (pre_computed_map efn A' pr) t r A' \<bind>
        (\<lambda>(rej, def). if def = {} then RETURN ({}, {}, rej) else RETURN ({}, rej, def)),
        SPEC (\<lambda>em. em = elimination_module efn t r A pr))
       \<in> \<langle>Id\<rangle>nres_rel"
    by (refine_vcg elimalg, auto)
  from this show "(eliminate (pre_computed_map efn A' pr) t r A' \<bind>
        (\<lambda>(rej, def). if def = {} then RETURN ({}, {}, rej) else RETURN ({}, rej, def)),
        SPEC (\<lambda>em. em = elimination_module efn t r A pr))
       \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
    by simp
qed

lemma scoremax_correct:
  fixes e :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  shows "((\<lambda> A. scoremax A (pre_computed_map e A pr)),
 (\<lambda> A.  SPEC (\<lambda> max. max = Max {(e a A pr) | a. a \<in> A})))
  \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding scoremax_def pre_computed_map_def
proof (clarify, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have nempa: " A \<noteq> {}" by (auto simp add: alt_set_rel_def in_br_conv)
  show "(FOREACH A'
         (\<lambda>x max.
             ASSERT (x \<in> dom ((\<lambda>a. Some (e a A' pr)) |` A')) \<bind>
             (\<lambda>_. let scx = the (((\<lambda>a. Some (e a A' pr)) |` A') x)
                   in if max < scx then RETURN scx else RETURN max))
         0,
        SPEC (\<lambda>max. max = Max {e a A pr |a. a \<in> A}))
       \<in> \<langle>nat_rel\<rangle>nres_rel"
  apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). (e a A pr) \<le> max)
      \<and> ((\<exists>a \<in> (A - it). max = (e a A pr)) \<or> max = 0))"], clarsimp_all simp add: aeq fina nempa,
         auto)
  using max_score_in[where A= A and f = "(\<lambda> x. e x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. e x A pr)"] aeq
  apply (metis DiffI dual_order.trans order_less_imp_le)
  using max_score_in[where A= A and f = "(\<lambda> x. e x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. e x A pr)"] aeq
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
qed

context set_of_alternatives
begin


lemma scoremax_correct_ctx:
  shows "(scoremax A (pre_computed_map e A pr) 
\<le> SPEC (\<lambda> max. max = Max {(e a A pr) | a. a \<in> A}))"
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
 

locale profile_complete = set_of_alternatives + 
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
     profrel: "(pl, pr) \<in> profile_on_A_rel A"

context profile_complete
begin

lemma compute_scores_correct_weak_evalref:
  fixes eref :: "'a Evaluation_Function_Ref"
  and e :: "'a Evaluation_Function"
  assumes "((\<lambda> x. eref x A), (\<lambda> x p. RETURN ( e x A p))) \<in> evalf_profA_rel A"
  shows "(pre_compute_scores eref A pl, SPEC (\<lambda> map. map = pre_computed_map e A pr)) \<in> 
    \<langle>Id\<rangle>nres_rel"
  unfolding pre_compute_scores_def pre_computed_map_def
  apply (refine_vcg FOREACH_rule[where I = 
        "(\<lambda> it r. r = (\<lambda> a. Some (e a A pr))|`(A - it))"])
  apply (auto simp add: fina)
proof -
  fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda> a. Some (e a A pr)) |` (A - it))(x \<mapsto> (e x A pr)) =
                      (\<lambda> a. Some (e a A pr)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda> scx. ((\<lambda> a. Some (e a A pr)) |` (A - it))(x  \<mapsto> scx) =
                   (\<lambda> a. Some (e a A pr)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = (e x A pr))"
    by (metis map_upd_eqD1)
  from profrel have prel: "(pl, pr) \<in> profile_rel" using profile_type_ref by auto
  from profrel assms(1)[THEN fun_relD, THEN fun_relD, THEN nres_relD]
    this have "(eref x A pl) \<le> SPEC(\<lambda> scx. scx = (e x A pr))"
    by (metis IdI SPEC_eq_is_RETURN(2) refine_IdD) 
  from this mapupdeq show " (eref x A pl)
       \<le> SPEC (\<lambda> scx. ((\<lambda> a. Some (e a A pr)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda> a. Some (e a A pr)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
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

lemma less_eliminator_correct:
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  assumes prel: "(pl, pr) \<in> profile_rel"
  shows "((\<lambda> A. less_eliminator_ref (pre_computed_map efn A pr) t A pl),
            (\<lambda> A. SPEC (\<lambda> em. em = (less_eliminator efn t A pr))))
          \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding less_eliminator_ref.simps less_eliminator.simps
proof (clarify, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel prel show "(elimination_module_ref (pre_computed_map efn A' pr) t (<) A' pl,
        SPEC (\<lambda>em. em = elimination_module efn t (<) A pr))
       \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
    by (refine_vcg elimination_module_ref_correct[THEN fun_relD])
qed

theorem max_eliminator_ref_correct:
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  assumes prel: "(pl, pr) \<in> profile_rel"
  shows "((\<lambda> A. max_eliminator_ref (pre_computed_map efn A pr) A pl),
           ((\<lambda> A.  SPEC (\<lambda> em. em = max_eliminator efn A pr))))
 \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow>  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding max_eliminator_ref.simps max_eliminator.simps
proof (clarify, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  note lec = less_eliminator_correct[where efn = efn and t = "Max {efn x A pr |x. x \<in> A}",
      THEN fun_relD, where x = A' and x' = A
      and pl1 = pl and pr1 = pr, THEN nres_relD, THEN nres_relI]
  from arel prel this have elim: "(less_eliminator_ref (pre_computed_map efn A' pr) (Max {efn x A pr |x. x \<in> A}) A' pl,
   SPEC (\<lambda>em. em = less_eliminator efn (Max {efn x A pr |x. x \<in> A}) A pr))
  \<in> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel" by simp
  note sci = scoremax_correct[THEN fun_relD, THEN nres_relD, THEN refine_IdD]
  from this arel prel have maxs: "scoremax A' (pre_computed_map efn A' pr) 
    \<le> SPEC (\<lambda> maxs. maxs = (Max {efn x A pr |x. x \<in> A}))"
    by blast
  from elim maxs show "(scoremax A' (pre_computed_map efn A' pr) \<bind>
        (\<lambda>t. less_eliminator_ref (pre_computed_map efn A' pr) t A' pl),
        SPEC (\<lambda>em. em = less_eliminator efn (Max {efn x A pr |x. x \<in> A}) A pr))
       \<in>  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
    using specify_left[where M = 
        "\<Down> (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel) 
  (SPEC (\<lambda>em. em = less_eliminator efn (Max {efn x A pr |x. x \<in> A}) A pr))"
        and m = "scoremax A' (pre_computed_map efn A' pr)"
        and \<Phi> = "(\<lambda>maxs. maxs = Max {efn x A pr |x. x \<in> A})"
        and f ="(\<lambda> x. less_eliminator_ref (pre_computed_map efn A' pr) x A' pl)"]
  nres_relI nres_relD by blast

qed

lemma max_eliminator_Id:
   fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  assumes prel: "(pl, pr) \<in> profile_rel"
  shows "((\<lambda> A. max_eliminator_ref (pre_computed_map efn A pr) A pl),
           ((\<lambda> A.  SPEC (\<lambda> em. em = max_eliminator efn A pr))))
 \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow>  \<langle>Id\<rangle>nres_rel"
proof (rule fun_relI, rule nres_relI, rename_tac A' A)
  fix A' A :: "'a set"
  assume arel:  "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  thus  "max_eliminator_ref (pre_computed_map efn A' pr) A' pl
       \<le> \<Down> Id (SPEC (\<lambda>em. em = max_eliminator efn A pr))" 
    using max_eliminator_ref_correct[THEN fun_relD, THEN nres_relD] prel set_rel_id prod_rel_id
    by metis
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