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


abbreviation "efunrel \<equiv> Id \<rightarrow> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"

definition evalf_rel ::
    "(('a \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> nat nres) 
\<times> ('a \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set list \<Rightarrow> nat)) set" 
    where  evalf_rel_def:
"evalf_rel \<equiv> {(eref,e).(eref, (\<lambda> a A pro. SPEC (\<lambda> sc. sc = e a A pro))) 
  \<in> Id \<rightarrow> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel}"


lemma evalfeq:   
  fixes "A" :: "'a set"
  fixes pr :: "'a Profile"
  fixes pl :: "'a Profile_List"
  assumes 
     fina: "finite A" and 
     pref: "(pl, pr) \<in> profile_rel" and
     evalref: "(refn, efn) \<in> evalf_rel"
   shows "\<forall> a \<in> A. refn a A pl \<le> SPEC (\<lambda>score. score = (efn a A pr))"
proof (-)
  from evalref have efrel: "(refn, (\<lambda> a A pro. SPEC (\<lambda> sc. sc = efn a A pro))) \<in> efunrel"
  unfolding evalf_rel_def by simp
  from this pref efrel[THEN fun_relD, THEN fun_relD,THEN fun_relD,THEN nres_relD,THEN refine_IdD]
  show ?thesis
    by force   
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
      sw \<leftarrow> f w A p;
      sl \<leftarrow> f x A p;
      RETURN (b \<and> (sl < sw))}) (True)"
         
subsection \<open>Theorems\<close>

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, w has the maximum evaluation value.
\<close>


(*theorem cond_winner_imp_max_eval_val_ref:
  fixes A :: "'a set"
  fixes eref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  fixes pl :: "'a Profile_List" and pr :: "'a Profile"
  assumes fina: "finite A" 
  and profrel : "(pl, pr) \<in> profile_rel"
  and efref: "eref w A pl \<le> SPEC (\<lambda> score. score = (efn w A pr))"
  assumes
    rating: "condorcet_rating efn" and
    profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w"
  shows "eref w A pl \<le> RETURN (Max {efn a A pr | a. a \<in> A})"
proof -
  from win
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
qed*)

text \<open>
  If e is Condorcet-rating, the following holds:
  If a Condorcet Winner w exists, a non-Condorcet
  winner has a value lower than the maximum
  evaluation value.
\<close>

find_theorems "Max"

theorem non_cond_winner_not_max_eval_ref:
  fixes A :: "'a set"
  fixes eref :: "'a Evaluation_Function_Ref"
  and efn :: "'a Evaluation_Function"
  fixes pl :: "'a Profile_List" and pr :: "'a Profile"
  assumes fina: "finite A" 
  assumes profrel : "(pl, pr) \<in> profile_rel"
  and efref: "\<forall> c \<in> A. eref c A pl \<le> SPEC (\<lambda> score. score = (efn c A pr))"
  assumes
    rating: "condorcet_rating efn" and
    profl: "profile_l A pl" and
    winnerl: "condorcet_winner_l A pl w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "do {sl \<leftarrow> eref l A pl; RETURN (sl < Max {efn a A pr | a. a \<in> A})} \<le> RETURN True"  
proof -
  from winnerl have winA: "w \<in> A" by simp
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
  from  fina linA efref  show ?thesis unfolding SPEC_eq_is_RETURN(2)[symmetric]
    using specify_left[where m = "eref l A pl" and \<Phi> = "(\<lambda>score. score = efn l A pr)"
          and f = "(\<lambda>sl. SPEC (\<lambda>x. x = (sl < Max {efn a A pr |a. a \<in> A})))"
          and M= "SPEC (\<lambda>x. x = True)"]
    using lt by fastforce  

qed


end
