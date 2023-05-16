(*  File:       Ballot_Refinement.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Data Refinement for Ranking\<close>

section \<open>Preference Relation\<close>


theory Ballot_Refinement
  imports Verified_Voting_Rule_Construction.Preference_Relation
  Verified_Voting_Rule_Construction.Preference_List

  Verified_Voting_Rule_Construction.Profile
  Verified_Voting_Rule_Construction.Profile_List

  Refine_Imperative_HOL.IICF
  "HOL-Library.LaTeXsugar"

begin

subsection \<open>Refinement Relation for Ballots\<close>

  
definition ballot_rel_def [refine_rel_defs]:
  "ballot_rel \<equiv> br (pl_\<alpha>) (well_formed_pl)"

lemma sv_bal_rel: "single_valued ballot_rel"
  unfolding ballot_rel_def
  by (simp)

lemma linearorder_ref: 
  "(linear_order_on_l, linear_order_on) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> ballot_rel \<rightarrow> bool_rel"                                 
proof (refine_vcg, clarsimp_all)
  fix alts:: "'a set"
  fix bal:: "'a Preference_List" and bar:: "'a Preference_Relation"
  assume "(bal, bar) \<in> ballot_rel"
  from this show " linear_order_on_l alts bal = linear_order_on alts bar"
    using in_br_conv linorder_l_imp_rel linorder_rel_imp_l
    unfolding ballot_rel_def
    by metis
qed


text \<open>We attempted to show a completeness lemma for our refinement of linear order relations
      to lists. We have not completed it. This lemma sketches, that the abstraction relation is
      not empty.\<close>

lemma simple_list_abstraction_sketch:
  shows "([1::nat,2], {(2::nat,1::nat), (2::nat,2::nat), (1::nat,1::nat)}) \<in> ballot_rel"
  unfolding in_br_conv well_formed_pl_def ballot_rel_def pl_\<alpha>_def 
  is_less_preferred_than_l.simps by auto


abbreviation "ballot_on_A_rel A \<equiv> (br (\<lambda>x. x) (linear_order_on_l A)) O ballot_rel"

lemma ballot_prop_rel:
  fixes A:: "'a set" and l:: "'a Preference_List"
  assumes "(l,r) \<in> ballot_on_A_rel A"
  shows "(l,r) \<in> ballot_rel"
  using assms by (metis in_br_conv relcompEpair)

subsection \<open>Refinement Relation for Basic Operations\<close>

lemma aboveref:                                          
  shows "(above_l, above) \<in> ballot_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  apply (refine_vcg)                                    
  unfolding list_set_rel_def
  apply (auto) using aboveeq unfolding well_formed_pl_def in_br_conv above_l_def ballot_rel_def
  by (metis distinct_take)
  
lemma rankref: 
  shows "(rank_l, rank) \<in> ballot_rel \<rightarrow> Id \<rightarrow> nat_rel"
  apply (refine_vcg)
  apply (auto simp only: refine_rel_defs)
  using rankeq
    by fastforce

lemma is_less_preferred_than_ref:
  shows "(is_less_preferred_than_l, is_less_preferred_than) 
    \<in> Id \<rightarrow> ballot_rel \<rightarrow> Id \<rightarrow> bool_rel"
  apply (refine_vcg)
  by (auto simp only: refine_rel_defs is_less_preferred_than_eq)

subsection \<open>Refinement Relation for Profile\<close>

abbreviation  "profile_rel \<equiv> \<langle>ballot_rel\<rangle>list_rel"
abbreviation "profile_on_A_rel A \<equiv> \<langle>ballot_on_A_rel A\<rangle>list_rel"


lemma sv_prof_rel: "single_valued profile_rel"
  by (simp add: sv_bal_rel list_rel_sv)

lemma profile_rel_imp_map_ballots:
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes "(pl, pr) \<in> profile_rel"
  shows "pr = map pl_\<alpha> pl"
proof (-)
  from assms have "\<forall> i < length pl. (pl!i, pr!i) \<in> ballot_rel"
    by (simp add:  list_rel_pres_length param_nth)
  from assms this show " pr = map pl_\<alpha> pl" unfolding ballot_rel_def 
    by (metis in_br_conv  length_map list_rel_pres_length nth_equalityI nth_map) 
qed
  
lemma profile_type_ref:
  fixes A:: "'a set"
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes "(pl, pr) \<in> profile_on_A_rel A" 
  shows "(pl, pr) \<in> profile_rel"
proof standard
  from assms show "(pl, pr) \<in> profile_on_A_rel A" by simp
next
  show "profile_on_A_rel A \<subseteq> profile_rel"
  proof standard
    fix x:: "('a Profile_List \<times> 'a Profile)"
    assume lrrel: "x \<in> (profile_on_A_rel A)"
    from this have "(\<forall>i < length (fst x). (((fst x)!i), ((snd x)!i)) \<in> (ballot_on_A_rel A))"
      using list_rel_imp_same_length pair_in_Id_conv param_nth
      by (metis prod.exhaust_sel)      
    from this have "(\<forall>i < length (fst x). (((fst x)!i), ((snd x)!i)) \<in> (ballot_rel))"
      using ballot_prop_rel
      by blast
    from lrrel this show "x \<in> (profile_rel)" 
      by (metis list_rel_eq_listrel listrel_iff_nth prod.exhaust_sel relAPP_def)
  qed
qed    

lemma profile_prop_list:
  fixes A:: "'a set" 
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes "(pl,pr) \<in> profile_on_A_rel A"
  shows "profile_l A pl"
  unfolding profile_l_def
  using assms in_br_conv unfolding ballot_rel_def
  by (metis (full_types) list_rel_imp_same_length pair_in_Id_conv param_nth relcompEpair)

lemma profile_ref:
  fixes A :: "'a set"
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes prel: "(pl,pr) \<in> profile_rel"
  shows "profile_l A pl \<longleftrightarrow> profile A pr"
proof (-)
  from prel have "\<forall>idx < length pl. ((pl!idx), (pr!idx)) \<in> ballot_rel"
    using in_br_conv  unfolding  ballot_rel_def
    by (simp add: list_rel_pres_length param_nth)
  from prel this show "profile_l A pl \<longleftrightarrow> profile A pr" 
    unfolding  ballot_rel_def
     profile_def profile_l_def in_br_conv
    by (metis linorder_l_imp_rel linorder_rel_imp_l list_rel_pres_length)
qed

lemma profile_prop_rel:
  fixes A:: "'a set" and pl:: "'a Profile_List"
  assumes "(pl,pr) \<in> profile_on_A_rel A"
  shows "profile A pr"      
proof (-)
  from assms have profl: "profile_l A pl" 
    using profile_prop_list by metis
  from assms have profrel: "(pl,pr) \<in> profile_rel"
    using profile_type_ref by metis
  from profl this show "profile A pr"
    using profile_ref  unfolding ballot_rel_def
    by (simp add: in_br_conv linorder_l_imp_rel list_rel_eq_listrel listrel_iff_nth 
        profile_def profile_l_def relAPP_def)
qed

section \<open>Monadic Definition of Limiting a Single Ballot\<close>

definition "limit_monadic_inv A ballot \<equiv> \<lambda> (i, nbal).
  nbal = limit_l A (take i ballot)"


definition  limit_monadic :: "'a::{default, hashable, heap} set 
    \<Rightarrow> 'a::{default, hashable, heap} Preference_List 
      \<Rightarrow> 'a::{default, hashable, heap} Preference_List nres" where
"limit_monadic A ballot \<equiv> do {
    (i, nbal) \<leftarrow> WHILET
  (\<lambda> (i, nbal). i < length ballot) 
      (\<lambda> (i, nbal). do {
      ASSERT (i < (length ballot));
      let c = (ballot!i);
      RETURN (if (c \<in> A) then
         (i + 1, nbal @ [c])
      else
        (i + 1, nbal))
    })(0, []);
    RETURN (nbal)
  }"                          

subsection \<open>Correctness\<close>

lemma limit_l_sound:
  fixes A :: "'a set"
  fixes bal :: "'a Preference_List"
  assumes "well_formed_pl bal"
  shows "well_formed_pl (limit_l A bal)"
  using assms unfolding well_formed_pl_def
  by auto


lemma limit_monadic_refine:
  fixes A :: "'a::{default, hashable, heap} set" and bal :: "'a::{default, hashable, heap} Preference_List"
  assumes fina: "finite A" 
  shows "(limit_monadic A bal \<le> SPEC(\<lambda> lim. lim = (limit_l A bal)))"
  unfolding limit_monadic_def
  apply (refine_vcg WHILET_rule[where R = "measure (\<lambda>(i, newb). length bal - i)"
            and I = "(limit_monadic_inv A bal)"],
        auto simp add: limit_monadic_inv_def pl_\<alpha>_def  take_Suc_conv_app_nth)
  done


lemma limit_monadic_correct:
  shows "(uncurry limit_monadic, uncurry (RETURN oo limit))
      \<in> [\<lambda> (A, bal). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r ballot_rel) \<rightarrow> \<langle>ballot_rel\<rangle>nres_rel"
proof (intro frefI fun_relI nres_relI, auto simp del: limit.simps, 
      unfold SPEC_eq_is_RETURN(2)[symmetric], rename_tac A bal bar)
  fix A :: "'a set"
  fix bar :: "'a Preference_Relation"
  fix bal :: "'a Preference_List"
  assume balrel: "(bal, bar) \<in> ballot_rel"
  assume fina: "finite A"
  from balrel have wf: "well_formed_pl bal"
   using in_br_conv  unfolding  ballot_rel_def
   by metis
  from balrel have abs: "bar = pl_\<alpha> bal" unfolding   ballot_rel_def in_br_conv by simp
  from fina have refp: "(limit_monadic A bal \<le> SPEC(\<lambda> lim. lim = (limit_l A bal)))" 
      using limit_monadic_refine by blast
  from wf  have refb: "(limit_l A bal, limit A bar) \<in> ballot_rel" unfolding abs
    unfolding ballot_rel_def in_br_conv  using limit_eq limit_l_sound by blast
  from this have balref: "(SPEC (\<lambda>x. x = limit_l A bal)) \<le> \<Down> ballot_rel (SPEC (\<lambda>x. x = limit A bar))"
    by (metis (full_types) RETURN_SPEC_refine lhs_step_SPEC)
  show "limit_monadic A bal \<le> \<Down> ballot_rel (SPEC (\<lambda>x. x = limit A bar))"
    using  order_trans[OF refp balref] .
qed

subsection \<open>Separation Logic Assertions Relators for Eelectoral Module Data Type\<close>

abbreviation "ballot_impl_assn  R \<equiv> (arl_assn R)"

abbreviation "profile_impl_assn  R \<equiv> (list_assn (ballot_impl_assn R))"

abbreviation "alts_set_impl_assn  R \<equiv> (hs.assn R)"

abbreviation "result_impl_assn  R \<equiv> alts_set_impl_assn  R \<times>\<^sub>a alts_set_impl_assn  R \<times>\<^sub>a alts_set_impl_assn  R"

subsection \<open>Imperative HOL Definition of Limit Function for Ballot\<close>

text \<open>The old ballot remains valid on the heap. A new array list is created for the limited ballot.\<close>

sepref_definition limit_sep is "uncurry limit_monadic" ::
  "(hs.assn id_assn)\<^sup>k *\<^sub>a (ballot_impl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a (ballot_impl_assn id_assn)"
  unfolding limit_monadic_def[abs_def]
  apply (rewrite in "WHILET _ _ rewrite_HOLE" arl.fold_custom_empty)
  apply sepref_dbg_keep
  done




end

