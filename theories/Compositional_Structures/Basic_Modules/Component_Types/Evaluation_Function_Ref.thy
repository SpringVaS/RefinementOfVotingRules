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

abbreviation "evalf_rel \<equiv> Id  \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

abbreviation "evalf_profA_rel A \<equiv> Id \<rightarrow> profile_on_A_rel A \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"


lemma evalfeq:   
  fixes A:: "'a set" 
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
     pref: "(pl, pr) \<in> profile_rel" and
     evalref: "((\<lambda> a pl . refn a A pl), (\<lambda> a pr. RETURN (efn a A pr))) \<in> evalf_rel"
  shows "refn a A pl \<le> RETURN (efn a A pr)"
  using pref evalref[THEN fun_relD,THEN fun_relD, THEN nres_relD]
  by auto
  
  subsection \<open>Refined Condorcet Property\<close>

text \<open>
  An Evaluation function is Condorcet-rating iff the following holds:
  If a Condorcet Winner w exists, w and only w has the highest value.
\<close>

definition condorcet_rating_mon_aux :: "'a Evaluation_Function_Ref
  \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "condorcet_rating_mon_aux f A p w \<equiv>
  FOREACH A (\<lambda> x b.
      if (x = w) then RETURN b
      else do {
      sw <- f w A p;
      sl <- f x A p;
      RETURN (b \<and> (sl < sw))}) (True)"
         
subsection \<open>Theorems\<close>

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, w has the maximum evaluation value.
\<close>

theorem cond_winner_imp_max_eval_val_ref:
  fixes A :: "'a set"
  fixes eref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  fixes pl :: "'a Profile_List" and pr :: "'a Profile"
  assumes profrel : "(pl, pr) \<in> profile_rel"
  assumes evalfref: "((\<lambda> a pro. eref a A pro), (\<lambda> a  pro. RETURN (efn a A pro))) \<in> evalf_rel"
  assumes
    rating: "condorcet_rating efn" and
    fina: "finite A" and profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w"
  shows "eref w A pl \<le> RETURN (Max {efn a A pr | a. a \<in> A})"
proof -
  note efeq = evalfref[THEN fun_relD, THEN fun_relD, THEN nres_relD]
  from this have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using profrel refine_IdD
    by simp
  from fina profl profrel have f_prof: "finite_profile A pr" 
    using profileref[THEN fun_relD, THEN fun_relD]
    by fastforce
  from winnerl condorcet_winner_l_correct[THEN fun_relD, THEN fun_relD,THEN fun_relD]
  profrel
  have winner: "condorcet_winner A pr w"
    by (metis pair_in_Id_conv set_rel_id)
  note efi = efeq[where x2 = w and x'2 = w and x1 = pl and x'1 = pr]
  from rating f_prof winner
  have "efn w A pr = Max {efn a A pr |a. a \<in> A}" using cond_winner_imp_max_eval_val
    by (metis (mono_tags, lifting))
  from efref this show ?thesis
    by auto      
qed

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, a non-Condorcet
  winner has a value lower than the maximum
  evaluation value.
\<close>

theorem non_cond_winner_not_max_eval_ref:
 fixes eref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  fixes pl :: "'a Profile_List" and pr :: "'a Profile"
  assumes profrel : "(pl, pr) \<in> profile_rel"
  assumes evalfref: "((\<lambda> a pro. eref a A pro), (\<lambda> a pro. RETURN (efn a A pro))) \<in> evalf_rel"
  assumes
    rating: "condorcet_rating efn" and
    fina: "finite A" and profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "do {sl <- eref l A pl; RETURN (sl < Max {efn a A pr | a. a \<in> A})} \<le> RETURN True"  
proof -
   note efeq = evalfref[THEN fun_relD, THEN fun_relD, THEN nres_relD]
  from this have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using profrel refine_IdD
    by simp
  from fina profl profrel have f_prof: "finite_profile A pr" 
    using profileref[THEN fun_relD, THEN fun_relD]
    by fastforce
  from winnerl condorcet_winner_l_correct[THEN fun_relD, THEN fun_relD,THEN fun_relD]
  profrel
  have winner: "condorcet_winner A pr w"
    by (metis pair_in_Id_conv set_rel_id)
  from f_prof winner rating linA loser have lt: "efn l A pr < Max {efn a A pr | a. a \<in> A}"
    using non_cond_winner_not_max_eval[where A= A and l = l and e = efn and w = w and p = pr]
    by simp
  from profrel efeq have "eref l A pl \<le> RETURN (efn l A pr)"
    by auto
  from this lt show ?thesis
    by (smt (verit, ccfv_threshold) RETURN_SPEC_conv pw_ords_iff(1) specify_left)
qed

end
