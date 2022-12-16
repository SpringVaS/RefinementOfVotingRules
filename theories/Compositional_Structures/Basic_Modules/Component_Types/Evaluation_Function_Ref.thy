(*  File:       Evaluation_Function.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Evaluation Function\<close>

theory Evaluation_Function_Ref
  imports "Verified_Voting_Rule_Construction.Evaluation_Function"
    "Verified_Voting_Rule_Construction.Profile_List"
    "Social_Choice_Types/Profile_List_Monadic"
  Refine_Imperative_HOL.IICF
begin

text \<open>
  This is the evaluation function. From a set of currently eligible
  alternatives, the evaluation function computes a numerical value that is then
  to be used for further (s)election, e.g., by the elimination module.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Evaluation_Function_Ref = "'a  \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> nat nres"

abbreviation "evalf_rel \<equiv> Id \<rightarrow> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> Id"

subsection \<open>Property\<close>

text \<open>
  An Evaluation function is Condorcet-rating iff the following holds:
  If a Condorcet Winner w exists, w and only w has the highest value.
\<close>

definition condorcet_rating_ref :: "'a Evaluation_Function_Ref \<Rightarrow> bool" where
  "condorcet_rating_ref f \<equiv>
    \<forall> A p w . condorcet_winner_l A p w \<longrightarrow>
      (\<forall> l \<in> A . l \<noteq> w \<longrightarrow> f l A p < f w A p)"

(*lemma "(condorcet_rating_ref,  condorcet_rating) \<in> evalf_rel \<rightarrow> bool_rel"*)

subsection \<open>Theorems\<close>

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, w has the maximum evaluation value.
\<close>

theorem cond_winner_imp_max_eval_val:
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p w"
  shows "e w A p = Max {e a A p | a. a \<in> A}"
proof -
  let ?set = "{e a A p | a. a \<in> A}" and
      ?eMax = "Max {e a A p | a. a \<in> A}" and
      ?eW = "e w A p"
  from f_prof
  have 0: "finite ?set"
    by simp
  have 1: "?set \<noteq> {}"
    using condorcet_winner.simps winner
    by fastforce
  have 2: "?eW \<in> ?set"
    using CollectI condorcet_winner.simps winner
    by (metis (mono_tags, lifting))
  have 3: "\<forall> e \<in> ?set . e \<le> ?eW"
  proof (safe)
    fix a :: "'a"
    assume aInA: "a \<in> A"
    have "\<forall>n na. (n::nat) \<noteq> na \<or> n \<le> na"
      by simp
    with aInA show "e a A p \<le> e w A p"
      using less_imp_le rating winner
      unfolding condorcet_rating_def
      by (metis (no_types))
  qed
  from 2 3 have 4:
    "?eW \<in> ?set \<and> (\<forall>a \<in> ?set. a \<le> ?eW)"
    by blast
  from 0 1 4 Max_eq_iff
  show ?thesis
    by (metis (no_types, lifting))
qed

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, a non-Condorcet
  winner has a value lower than the maximum
  evaluation value.
\<close>

theorem non_cond_winner_not_max_eval:
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "e l A p < Max {e a A p | a. a \<in> A}"
proof -
  have "e l A p < e w A p"
    using linA loser rating winner
    unfolding condorcet_rating_def
    by metis
  also have "e w A p = Max {e a A p |a. a \<in> A}"
    using cond_winner_imp_max_eval_val f_prof rating winner
    by fastforce
  finally show ?thesis
    by simp
qed

end
