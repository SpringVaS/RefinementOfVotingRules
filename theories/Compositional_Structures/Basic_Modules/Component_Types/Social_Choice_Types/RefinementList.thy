theory RefinementList
  imports Verified_Voting_Rule_Construction.Preference_Relation
  Verified_Voting_Rule_Construction.Preference_List
  Refine_Imperative_HOL.IICF

begin

abbreviation "ballot_rel \<equiv> br (pl_\<alpha>) (well_formed_pl)"

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
  apply (refine_vcg rankeq)
  by (auto simp only: refine_rel_defs less_preffered_l_rel_eq)

lemma limitref:
  shows "(limit_l, limit) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> ballot_rel \<rightarrow> ballot_rel"
  apply (refine_vcg rankeq)
  apply (auto simp add: refine_rel_defs)
  unfolding well_formed_pl_def pl_\<alpha>_def
  apply auto
  apply (simp_all add: member_def)
   apply clarsimp_all
  oops
   

end