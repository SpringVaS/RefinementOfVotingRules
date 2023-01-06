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

abbreviation "evalf_rel \<equiv> Id \<rightarrow> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

lemma evalfeq:   
  fixes A:: "'a set" 
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
     pref: "(pl, pr) \<in> profile_rel" and
     evalref: "((\<lambda> a A pl . refn a A pl), (\<lambda> a A pr. RETURN (efn a A pr))) \<in> evalf_rel"
  shows "refn a A pl \<le> RETURN (efn a A pr)"
  using assms(1) assms(2)[THEN fun_relD, THEN fun_relD,THEN fun_relD, THEN nres_relD]
  by auto
  
  subsection \<open>Refined Condorcet Property\<close>

text \<open>
  An Evaluation function is Condorcet-rating iff the following holds:
  If a Condorcet Winner w exists, w and only w has the highest value.
\<close>

definition condorcet_rating_ref :: "'a Evaluation_Function_Ref \<Rightarrow> bool" where
  "condorcet_rating_ref f \<equiv>
    \<forall> A p w . condorcet_winner_l A p w \<longrightarrow>
      (\<forall> l \<in> A . l \<noteq> w \<longrightarrow> f l A p < f w A p)"

lemma cratref:
  fixes refn :: "'a Evaluation_Function_Ref"
  fixes efn  :: "'a Evaluation_Function"
  fixes A:: "'a set" and pr :: "'a Profile" and pl :: "'a Profile_List" fixes w:: 'a
  assumes pref: "(pl, pr) \<in> profile_rel"
  assumes evalref: "((\<lambda> a. refn a A pl), (\<lambda> a . RETURN (efn a A pr))) \<in> Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  shows "condorcet_rating_ref refn = condorcet_rating efn"
proof (safe, unfold condorcet_rating_ref_def condorcet_rating_def)
  assume rthes: "\<forall>A p w. condorcet_winner_l A p w \<longrightarrow> (\<forall>l\<in>A. l \<noteq> w \<longrightarrow> refn l A p < refn w A p)"
  note pref condorcet_winner_l_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD,
      where x2 = A and x'2 = A and x1 = pl and x'1 = pr]
  from this have ceq: "condorcet_winner_l A pl w = condorcet_winner A pr w"
    by (metis pair_in_Id_conv set_relI)
 (* from this evalref have "\<forall>A p w. condorcet_winner A p w \<longrightarrow> (\<forall>l\<in>A. l \<noteq> w \<longrightarrow> efn l A p < efn w A p)"*)
  from  evalref[THEN fun_relD, THEN nres_relD] refine_IdD 
  have "(efn l A pr < efn w A pr) \<longrightarrow> (refn l A pl < refn w A pl)"
  
  
  oops
 
         
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
