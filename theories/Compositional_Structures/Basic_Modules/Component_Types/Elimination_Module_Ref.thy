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

type_synonym Threshold_Value = nat

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

definition scoremax :: "'a Threshold_Compute" where 
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
      let scx = the (scoremap x);
      (if (r scx t) then 
          RETURN (insert x rej, def) 
      else 
          RETURN(rej, insert x def))
    }) ({}, {})
}"

definition elimination_module_ref :: 
"'a Evaluation_Function_Ref \<Rightarrow> 'a Threshold_Compute \<Rightarrow>
   Threshold_Relation \<Rightarrow> 'a Electoral_Module_Ref " 
  where
  "elimination_module_ref e tc r A p \<equiv> do {
    scores <- pre_compute_scores e A p;
    threshold <- tc A scores;
    (rej, def) <- eliminate scores threshold r A p;
    (if (rej \<noteq> A) 
      then RETURN ({},rej,def) 
      else RETURN ({},{},A))
  }"



subsection \<open>Common Eliminators\<close>

fun less_eliminator_ref :: "'a Evaluation_Function_Ref \<Rightarrow> 'a Threshold_Compute \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "less_eliminator_ref e tc A p = elimination_module_ref e tc (<) A p"

fun max_eliminator_ref ::  "'a Evaluation_Function_Ref \<Rightarrow>
                            'a Electoral_Module_Ref" where
  "max_eliminator_ref e A p =
    less_eliminator_ref e (scoremax) A p"

fun leq_eliminator_ref :: "'a Evaluation_Function_Ref \<Rightarrow> 'a Threshold_Compute \<Rightarrow>
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
