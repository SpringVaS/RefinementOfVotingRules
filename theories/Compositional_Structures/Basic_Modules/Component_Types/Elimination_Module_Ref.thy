section \<open>Elimination Module\<close>

theory Elimination_Module_Ref
  imports Verified_Voting_Rule_Construction.Evaluation_Function
          Verified_Voting_Rule_Construction.Electoral_Module
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

type_synonym 'a Electoral_Set = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set"

fun elimination_set :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Set" where
 "elimination_set e t r A p = {a \<in> A . r (e a A p) t }"

fun elimination_module :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Module" where
  "elimination_module e t r A p =
      (if (elimination_set e t r A p) \<noteq> A
        then ({}, (elimination_set e t r A p), A - (elimination_set e t r A p))
        else ({},{},A))"

subsection \<open>Common Eliminators\<close>

fun less_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "less_eliminator e t A p = elimination_module e t (<) A p"

fun max_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "max_eliminator e A p =
    less_eliminator e (Max {e x A p | x. x \<in> A}) A p"

fun leq_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "leq_eliminator e t A p = elimination_module e t (\<le>) A p"

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
