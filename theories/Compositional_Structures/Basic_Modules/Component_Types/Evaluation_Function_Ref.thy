(*  File:       Evaluation_Function.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Refinement of Evaluation Function\<close>

theory Evaluation_Function_Ref
  imports "Verified_Voting_Rule_Construction.Evaluation_Function"
    "Social_Choice_Types/Profile_List_Monadic"
  Refine_Imperative_HOL.IICF
begin

text \<open>
  In this section, we refine Evaluation Function from Verified-Voting-Rule-Construction.
  Evaluation Function are used to instantiate Elimination Modules. Elimination Modules
  are a way to formalize certain voting rules. Elimination Modules have been defined by
  Stephan Bohr. They work with a finite non-empty set of alternatives. This precondition
  is encoded in the refinement relations here.
\<close>

subsection \<open>Definition\<close>

type_synonym 'a Evaluation_Function_Ref = "'a  \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> nat nres"


abbreviation "efunrel \<equiv> Id \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

definition evalf_rel ::
    "(('a \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> nat nres) 
\<times> ('a \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> nat)) set" 
    where  evalf_rel_def:
"evalf_rel \<equiv> {(eref,e).(eref, (\<lambda> a A pro. SPEC (\<lambda> sc. sc = e a A pro))) 
  \<in> Id \<rightarrow> \<langle>Id\<rangle>finite_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel}"

definition evalf_rel_prof ::
    "(('a \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> nat nres) 
\<times> ('a \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> nat)) set" where
"evalf_rel_prof \<equiv> {(eref, e). ((\<lambda> a (A, pro). eref a A pro), 
    (\<lambda> a (A, pro). SPEC (\<lambda> sc. sc = e a A pro))) 
  \<in> Id \<rightarrow> \<langle>Id\<rangle>alt_and_profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel}"

lemma evalfeq:   
  fixes "A" :: "'a set"
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
     fina: "finite A" and 
     pref: "(pl, pr) \<in> profile_rel" and
     evalref: "(refn, efn) \<in> evalf_rel"
   shows "refn a A pl \<le> RETURN (efn a A pr)"
proof (-)
  from evalref have efrel: "(refn, (\<lambda> a A pro. SPEC (\<lambda> sc. sc = efn a A pro))) \<in> efunrel"
  unfolding evalf_rel_def by simp
  from fina  have "(A, A) \<in> \<langle>Id\<rangle>finite_set_rel" by (simp add: finite_set_rel_def in_br_conv)
  from this pref efrel[THEN fun_relD, THEN fun_relD,THEN fun_relD,THEN nres_relD,THEN refine_IdD]
  SPEC_eq_is_RETURN(2)
  show ?thesis
    by (metis IdI) 
qed

lemma evalproffeq:   
  fixes A' A :: "'a set"
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
     rel: "((A', pl), A, pr) \<in> \<langle>Id\<rangle>alt_and_profile_rel" and
     evalref: "(refn, efn) \<in> evalf_rel_prof"
   shows "refn a A pl \<le> RETURN (efn a A pr)"
proof (-)
  from evalref have efrel: "((\<lambda> a (A, pro). refn a A pro), (\<lambda> a (A, pro). SPEC (\<lambda> sc. sc = efn a A pro)))
    \<in> Id \<rightarrow> \<langle>Id\<rangle>alt_and_profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel" unfolding evalf_rel_prof_def
    by auto
  from rel have arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel" using unfold_alt_profile_alt_rel by blast
  from rel have prel: "(pl, pr) \<in> profile_rel " using unfold_alt_profile_prof_rel
    by blast
  from rel efrel[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD]
  show ?thesis unfolding SPEC_eq_is_RETURN(2)
    using arel id_same_alts by fastforce
qed

lemma drop_prof_prop: 
  assumes "(eref, e) \<in> evalf_rel"
  shows "(eref, e) \<in> evalf_rel_prof"
proof (unfold evalf_rel_prof_def, clarsimp, rule nres_relI, rule refine_IdI,
    rename_tac a A' pl A pr)
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
  from assms have "eref a A pl \<le> RETURN (e a A pr)"
    using fina prel evalfeq assms
    by metis  
  from this show "eref a A' pl \<le> RES {e a A pr}"
    by (simp add: aeq ireturn_eq)
qed



locale set_of_alternatives =
   fixes A:: "'a set" 
   assumes 
     fina: "finite A"
begin


end
  
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

context set_of_alternatives
begin

theorem cond_winner_imp_max_eval_val_ref:
  fixes eref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  fixes pl :: "'a Profile_List" and pr :: "'a Profile"
  assumes profrel : "(pl, pr) \<in> profile_rel"
  assumes evalfref: "(eref, efn) \<in> evalf_rel"
  assumes
    rating: "condorcet_rating efn" and
    profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w"
  shows "eref w A pl \<le> RETURN (Max {efn a A pr | a. a \<in> A})"
proof -
  from evalfref profrel fina  have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using  evalfeq
    by fastforce
  from fina profl profrel have f_prof: "finite_profile A pr" 
    using profile_ref
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
  assumes evalfref: "(eref, efn) \<in> evalf_rel"
  assumes
    rating: "condorcet_rating efn" and
    profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "do {sl <- eref l A pl; RETURN (sl < Max {efn a A pr | a. a \<in> A})} \<le> RETURN True"  
proof -
  from evalfref have efref: "eref w A pl \<le> RETURN (efn w A pr)"
    using profrel fina  evalfeq refine_IdD
    by simp
  from fina profl profrel have f_prof: "finite_profile A pr" 
    using profile_ref
    by fastforce
  from winnerl condorcet_winner_l_correct[THEN fun_relD, THEN fun_relD,THEN fun_relD]
  profrel
  have winner: "condorcet_winner A pr w"
    by (metis pair_in_Id_conv set_rel_id)
  from f_prof winner rating linA loser have lt: "efn l A pr < Max {efn a A pr | a. a \<in> A}"
    using non_cond_winner_not_max_eval[where A= A and l = l and e = efn and w = w and p = pr]
    by simp
  from profrel evalfref fina  have "eref l A pl \<le> RETURN (efn l A pr)" using evalfeq
    by fastforce
  from this lt show ?thesis
    by (smt (verit, ccfv_threshold) RETURN_SPEC_conv pw_ords_iff(1) specify_left)
qed

end

end
