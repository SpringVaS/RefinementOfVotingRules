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

definition fset_rel where fset_rel_def_internal:
  "fset_rel R \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) finite)"

lemma fset_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>fset_rel \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) finite)"
  by (simp add: fset_rel_def_internal relAPP_def)

abbreviation "evalf_rel \<equiv> Id \<rightarrow> \<langle>Id\<rangle>fset_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

abbreviation "evalf_profA_rel A \<equiv> Id \<rightarrow> profile_on_A_rel A \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

definition efunrel ::
    "(('a \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> nat nres) \<times> ('a \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> nat)) set" where
"efunrel \<equiv> {(eref,e).(eref, (\<lambda> a A pro. RETURN (e a A pro))) \<in> Id \<rightarrow> \<langle>Id\<rangle>fset_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel}"

lemma evalfeq:   
  fixes A:: "'a set" 
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
    fina: "finite A" and
     pref: "(pl, pr) \<in> profile_rel" and
     evalref: "(refn, efn) \<in> efunrel"
   shows "refn a A pl \<le> RETURN (efn a A pr)"
proof (-)
  from evalref have efrel: "(refn, (\<lambda> a A pro. RETURN (efn a A pro))) \<in> evalf_rel"
  unfolding efunrel_def by simp
  from fina have "(A, A) \<in> \<langle>Id\<rangle>fset_rel" by (auto simp add: refine_rel_defs)
  from this pref efrel[THEN fun_relD, THEN fun_relD,THEN fun_relD,THEN nres_relD,THEN refine_IdD] show ?thesis 
    by fastforce
qed
  
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
  assumes evalfref: "(eref, efn) \<in> efunrel"
  assumes
    rating: "condorcet_rating efn" and
    fina: "finite A" and profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w"
  shows "eref w A pl \<le> RETURN (Max {efn a A pr | a. a \<in> A})"
proof -
  from evalfref profrel fina have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using  evalfeq
    by fastforce
  from fina profl profrel have f_prof: "finite_profile A pr" 
    using profileref[THEN fun_relD, THEN fun_relD]
    by fastforce
  from winnerl condorcet_winner_l_correct[THEN fun_relD, THEN fun_relD,THEN fun_relD]
  profrel
  have winner: "condorcet_winner A pr w"
    by (metis pair_in_Id_conv set_rel_id)
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
  assumes evalfref: "(eref, efn) \<in> efunrel"
  assumes
    rating: "condorcet_rating efn" and
    fina: "finite A" and profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "do {sl <- eref l A pl; RETURN (sl < Max {efn a A pr | a. a \<in> A})} \<le> RETURN True"  
proof -
  from evalfref have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using profrel fina evalfeq refine_IdD
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
  from profrel evalfref fina have "eref l A pl \<le> RETURN (efn l A pr)" using evalfeq
    by fastforce
  from this lt show ?thesis
    by (smt (verit, ccfv_threshold) RETURN_SPEC_conv pw_ords_iff(1) specify_left)
qed

end
