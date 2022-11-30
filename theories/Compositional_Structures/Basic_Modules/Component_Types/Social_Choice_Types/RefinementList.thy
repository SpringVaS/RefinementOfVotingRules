theory RefinementList
  imports Verified_Voting_Rule_Construction.Preference_Relation
  Verified_Voting_Rule_Construction.Preference_List

  Verified_Voting_Rule_Construction.Profile
  Verified_Voting_Rule_Construction.Profile_List

  Refine_Imperative_HOL.IICF

begin

abbreviation "ballot_rel \<equiv> br (pl_\<alpha>) (well_formed_pl)"

lemma linearorder_ref: 
  "(linear_order_on_l, linear_order_on) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> ballot_rel \<rightarrow> bool_rel"                                 
proof (refine_vcg, clarsimp_all)
  fix alts:: "'a set"
  fix bal:: "'a Preference_List" and bar:: "'a Preference_Relation"
  assume "(bal, bar) \<in> ballot_rel"
  from this show " linear_order_on_l alts bal = linear_order_on alts bar"
  using in_br_conv linorder_l_imp_rel linorder_rel_imp_l
    by metis
qed
  


lemma aboveref:                                          
  shows "(above_l, above) \<in> ballot_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  apply (refine_vcg)                                    
  apply (auto simp add: refine_rel_defs)
  unfolding list_set_rel_def
  by (metis Id_O_R above_l_def aboveeq brI distinct_take list_rel_id_simp well_formed_pl_def)
  
lemma rankref: 
  shows "(rank_l, rank) \<in> ballot_rel \<rightarrow> Id \<rightarrow> nat_rel"
  apply (refine_vcg rankeq)
  apply (auto simp only: refine_rel_defs)
  using rankeq
    by metis

lemma is_less_preferred_than_ref:
  shows "(is_less_preferred_than_l, is_less_preferred_than) 
    \<in> Id \<rightarrow> ballot_rel \<rightarrow> Id \<rightarrow> bool_rel"
  apply (refine_vcg)
  by (auto simp only: refine_rel_defs less_preffered_l_rel_eq)

lemma limitref:
  shows "(limit_l, limit) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> ballot_rel \<rightarrow> ballot_rel"
  apply (refine_vcg)
  apply (auto simp add: refine_rel_defs)
  oops
  (*unfolding well_formed_pl_def pl_\<alpha>_def
  apply auto
  apply (simp_all add: member_def)
   apply clarsimp_all*)

abbreviation "profile_rel \<equiv> \<langle>ballot_rel\<rangle>list_rel"

lemma profileref:
  shows "(profile_l, profile) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> bool_rel"
  apply (refine_rcg)
 apply (clarsimp simp add: linearorder_ref)
proof (-)
  fix pl:: "'a Profile_List" 
  fix pr:: "'a Profile"
  assume prel: "(pl, pr) \<in> profile_rel"
  fix A:: "'a set"
  fix i:: nat
  from prel have "\<forall>idx < length pl. ((pl!idx), (pr!idx)) \<in> ballot_rel"
    using in_br_conv
    by (simp add: list_rel_pres_length param_nth)
  from prel this show " profile_l A pl =profile A pr" using in_br_conv  profile_def profile_l_def
    by (metis linorder_l_imp_rel linorder_rel_imp_l list_rel_pres_length)
qed

end