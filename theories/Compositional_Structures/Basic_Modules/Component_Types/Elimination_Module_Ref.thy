(*  File:       Elimination_Module_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

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

type_synonym 'a Scores_Map = "'a \<rightharpoonup> nat"

definition init_map :: "'a set \<Rightarrow> 'a Scores_Map nres" where 
"init_map A \<equiv>
  FOREACH A 
    (\<lambda>x m. 
      RETURN (m(x\<mapsto>0::nat))) (Map.empty)"

lemma empty_map:
  fixes A :: "'a set"
  assumes 
     fina: "finite A"
  shows "init_map A \<le>
   SPEC(\<lambda> map. map =  ((\<lambda>a. Some (0::nat))|`A ))"
  unfolding init_map_def
  apply (refine_vcg FOREACH_rule [where I ="(\<lambda>it r. r = (\<lambda> a. Some (0::nat))|`(A - it))"])
  apply (auto simp add: fina)
  by (simp add: it_step_insert_iff restrict_map_insert)

definition pre_compute_scores :: "'a Evaluation_Function_Ref \<Rightarrow>
 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Scores_Map nres" 
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
    (rej, def) \<leftarrow> eliminate scores threshold r A;
   if (def = {}) then
       \<comment> \<open>Here rej will be a copy of A\<close>
     RETURN ({},{},rej)
    else
     RETURN ({},rej,def)
  }"


definition scores_map :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Scores_Map"  where
  "scores_map e Alts pro \<equiv> ((\<lambda>a. Some (e a Alts pro))|`Alts )"


lemma eliminate_correct:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and p :: "'a Profile"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
  assumes  fina: "finite A" 
  shows "eliminate (scores_map efn A p) t r A
    \<le> SPEC (\<lambda> (rej,def). 
    (rej,def) = ((elimination_set efn t r A p), A - (elimination_set efn t r A p)))"
  unfolding scores_map_def eliminate_def
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
   SPEC(\<lambda> map. map = (scores_map efn A pr))"
  unfolding pre_compute_scores_def scores_map_def
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

lemma elimination_module_ref_correct:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  and r :: "Threshold_Relation"
    assumes fina: "finite A"  and
  "(pl, pr) \<in> profile_rel"
  shows "elimination_module_ref (scores_map efn A pr) t r A pl \<le>
        SPEC (\<lambda> em. em = (elimination_module efn t r A pr))"
  by (unfold elimination_module_ref_def, refine_vcg eliminate_correct,
    auto simp add: fina)


theorem elimination_module_ref_correct_pc:
  fixes A :: "'a set"
  and efn :: "'a Evaluation_Function"
  and efn_ref :: "'a Evaluation_Function_Ref"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  and r :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes fina: "finite A" 
  and prel: "(pl, pr) \<in> profile_rel"
  and efnrel: "(efn_ref, RETURN ooo efn) \<in> efunrel"
shows "(do {
            score_map \<leftarrow> (pre_compute_scores efn_ref A pl);  
            elimination_module_ref score_map t r A pl}) \<le>
            SPEC (\<lambda> em. em = (elimination_module efn t r A pr))"
proof (refine_vcg fina prel compute_scores_correct[where efn = efn] , safe)
  fix a :: 'a
  note efnr = efnrel[THEN fun_relD,THEN fun_relD,THEN fun_relD,
        THEN nres_relD, THEN refine_IdD]
  from fina prel efnr show "efn_ref a A pl \<le> SPEC (\<lambda>score. score = efn a A pr)"
    unfolding comp_apply SPEC_eq_is_RETURN
    by force
next
  show "elimination_module_ref (scores_map efn A pr) t r A pl
         \<le> SPEC (\<lambda>em. em = elimination_module efn t r A pr)"
    using elimination_module_ref_correct fina prel
    by blast
qed

lemma scoremax_correct:
  fixes A :: "'a set"
  assumes fina: "finite A" and nempa: "A \<noteq> {}"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  shows "scoremax A (scores_map efn A pr)
 \<le> SPEC (\<lambda> max. max = Max {(efn a A pr) | a. a \<in> A})"
  unfolding scoremax_def scores_map_def
  apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). (efn a A pr) \<le> max)
      \<and> ((\<exists>a \<in> (A - it). max = (efn a A pr)) \<or> max = 0))"], clarsimp_all simp add:  fina nempa,
         auto)
  using max_score_in[where A= A and f = "(\<lambda> x. efn x A pr)"] fina nempa
            score_bounded[where A= A and f = "(\<lambda> x. efn x A pr)"] 
  subgoal by (metis DiffI dual_order.trans order_less_imp_le)
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
    t \<leftarrow> (scoremax A e); 
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
  shows "(less_eliminator_ref (scores_map efn A pr) t A pl) \<le>
            SPEC (\<lambda> em. em = (less_eliminator efn t A pr))"
  unfolding less_eliminator_ref_def less_eliminator.simps
proof (-)
 show "elimination_module_ref (scores_map efn A pr) t (<) A pl
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
  shows "(max_eliminator_ref (scores_map efn A pr) A pl
          \<le> SPEC (\<lambda> em. em = max_eliminator efn A pr))"
  apply (unfold max_eliminator_ref_def max_eliminator.simps less_eliminator_ref_def)
  apply (refine_vcg scoremax_correct fina )
   apply (simp)
  unfolding less_eliminator.simps using elimination_module_ref_correct assms
  by fastforce 
  
 
lemma max_eliminator_ref_correct_pc:
  fixes A :: "'a set"
  fixes efn :: "'a Evaluation_Function"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and scores :: "'a Scores_Map"
  assumes fina: "finite A"
  and prel: "(pl, pr) \<in> profile_rel"
  and mapc: "score_map \<le> SPEC (\<lambda> scores. scores = scores_map efn A pr)"  
  shows "(score_map \<bind> (\<lambda> scores. max_eliminator_ref scores A pl))
          \<le> SPEC (\<lambda> em. em = max_eliminator efn A pr)"
proof (refine_vcg mapc)
  fix map :: "'a Scores_Map"
  assume perfmap: "map = scores_map efn A pr"
  show "max_eliminator_ref map A pl \<le> SPEC (\<lambda>em. em = max_eliminator efn A pr)"
    unfolding perfmap using max_eliminator_ref_correct[OF fina prel] .
qed


theorem max_eliminator_ref_correct_default:
  fixes A :: "'a set"
  and efn :: "'a Evaluation_Function"
  and efn_ref :: "'a Evaluation_Function_Ref"
  and pr :: "'a Profile"
  and pl :: "'a Profile_List"
  and t :: "Threshold_Value"
  and r :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes fina: "finite A" 
  and prel: "(pl, pr) \<in> profile_rel"
  and efnrel: "\<forall>a \<in> A. efn_ref a A pl \<le> SPEC (\<lambda> score. score = efn a A pr)"
  shows "(do {
            score_map \<leftarrow> (pre_compute_scores efn_ref A pl);  
            max_eliminator_ref score_map A pl}) \<le>
            SPEC (\<lambda> em. em = (max_eliminator efn A pr))"
  by (refine_vcg compute_scores_correct max_eliminator_ref_correct_pc assms)

  


definition leq_eliminator_ref :: "'a Scores_Map \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "leq_eliminator_ref e t A p = elimination_module_ref e t (\<le>) A p"


end