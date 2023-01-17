theory Ballot_Refinement
  imports Verified_Voting_Rule_Construction.Preference_Relation
  Verified_Voting_Rule_Construction.Preference_List

  Verified_Voting_Rule_Construction.Profile
  Verified_Voting_Rule_Construction.Profile_List

  Refine_Imperative_HOL.IICF

begin


definition alt_set_rel where alt_set_rel_def_internal:
  "alt_set_rel R \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) (\<lambda> x. finite x \<and> x \<noteq> {}))"

lemma alt_set_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>alt_set_rel \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) (\<lambda> x. finite x \<and> x \<noteq> {}))"
  by (simp add: alt_set_rel_def_internal relAPP_def)

lemma finite_alts:
  assumes "(a, a') \<in> \<langle>Id\<rangle>alt_set_rel"
  shows "finite a" using assms by (simp add: alt_set_rel_def in_br_conv)

abbreviation "ballot_rel \<equiv> br (pl_\<alpha>) (well_formed_pl)"

abbreviation "ballot_on_A_rel A \<equiv> (br (\<lambda>x. x) (linear_order_on_l A)) O ballot_rel"

lemma ballot_prop_rel:
  fixes A:: "'a set" and l:: "'a Preference_List"
  assumes "(l,r) \<in> ballot_on_A_rel A"
  shows "(l,r) \<in> ballot_rel"
  using assms by (metis in_br_conv relcompEpair)
  

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
  shows "(limit_l, limit) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> ballot_rel \<rightarrow> ballot_rel"
  apply (refine_vcg, rename_tac A' A bl br)
  apply (auto simp add: refine_rel_defs)
sorry
(*proof -
  fix A' A :: "'a set"
  fix bl :: "'a Preference_List"
  fix  br :: "'a Preference_Relation"
  assume brel: "(bl, br) \<in> ballot_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  from brel have wf: "well_formed_pl bl" by (simp add: in_br_conv)
  have "limit A br = pl_\<alpha> (limit_l A bl)"
    using brel  apply (induction bl)
     apply (auto simp add: brel wf)

  (* inductctive proof with case distinction  *) 
qed*)

definition "limit_monadic_inv A ballot \<equiv> \<lambda> (b, newb).
  b = drop (length ballot - length b) ballot
  \<and> (pl_\<alpha> newb) = limit A (pl_\<alpha> (take (length ballot - length b) ballot))"

definition  limit_monadic :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List nres" where
"limit_monadic A ballot \<equiv> do {
  (_,newb) <-  WHILEIT (limit_monadic_inv A ballot) (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body  (\<lambda> x newb. 
    RETURN  (if x \<in> A then (op_list_append newb x) else (newb)) 
  )) (ballot,[]); 
  RETURN newb}"

definition  limit_nfoldli:: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List nres" where
"limit_nfoldli A ballot \<equiv> 
  nfoldli ballot (\<lambda>_.True) 
    (\<lambda> x newb. 
    RETURN  (if x \<in> A then ( newb @ [x]) else (newb)) 
  ) []"

lemma limitnref:
  shows "(limit_nfoldli, (\<lambda> A br. SPEC(\<lambda> lim. pl_\<alpha> lim = (limit A br)))) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow>
     ballot_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding limit_nfoldli_def
  apply (refine_rcg, rename_tac A' A bl br)
proof -
  fix A' A :: "'a set"
  fix bl :: "'a Preference_List"
  fix  br :: "'a Preference_Relation"
  assume brel: "(bl, br) \<in> ballot_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  from brel have dis: "distinct bl" using in_br_conv
    by (metis well_formed_pl_def)
  show  "nfoldli bl (\<lambda>_. True) (\<lambda>x newb. RETURN (if x \<in> A' then newb @ [x] else newb)) []
       \<le> SPEC (\<lambda>lim. pl_\<alpha> lim = limit A br)"
  proof (simp add: aeq, refine_vcg nfoldli_rule[where I = 
        "(\<lambda> proc xs newb. (pl_\<alpha> newb) = (limit A (pl_\<alpha> proc))
          \<and> set newb \<subseteq> set proc)"])
    show "pl_\<alpha> [] = limit A (pl_\<alpha> [])"
    unfolding pl_\<alpha>_def
    by (simp add: List.member_def)
  next
    fix x :: 'a
    fix l1 l2 :: "'a Preference_List"
    fix si :: "'a Preference_List"
    assume blsep: "bl = l1 @ x # l2"
    assume " pl_\<alpha> si = limit A (pl_\<alpha> l1) \<and> set si \<subseteq> set l1"
    from this have sub: "set si \<subseteq> set l1" by simp
    from sub show "pl_\<alpha> (if x \<in> A then si @ [x] else si) = limit A (pl_\<alpha> (l1 @ [x]))"
      using pl_\<alpha>_def 
      apply auto
      sorry
  next
    fix si
    assume " \<not> True" 
    thus "pl_\<alpha> si = limit A br" by simp
  next
    fix si
    assume newp: "pl_\<alpha> si = limit A (pl_\<alpha> bl)"
    from brel have "br = (pl_\<alpha> bl)"
      by (simp add: in_br_conv)
    from newp this show "pl_\<alpha> si = limit A br"
      by simp
  qed
qed
 
lemma limitref:
  shows "(limit_monadic, (\<lambda> A br. SPEC(\<lambda> lim. pl_\<alpha> lim = (limit A br)))) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow>
     ballot_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding limit_monadic_def
  apply (refine_rcg, rename_tac A' A bl br)
proof -
  fix A' A :: "'a set"
  fix bl :: "'a Preference_List"
  fix  br :: "'a Preference_Relation"
  assume brel: "(bl, br) \<in> ballot_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  have "  WHILE\<^sub>T\<^bsup>limit_monadic_inv A' bl\<^esup> (FOREACH_cond (\<lambda>_. True))
        (FOREACH_body (\<lambda>x newb. RETURN (if x \<in> A' then op_list_append newb x else newb))) (bl, []) \<bind>
       (\<lambda>(_, newb). RETURN newb)
       \<le> SPEC (\<lambda>lim. pl_\<alpha> lim = limit A br) "
    apply (refine_vcg WHILET_rule)
  

sepref_definition limit_imp is "uncurry (limit_monadic)" ::
  "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a  (arl_assn nat_assn)"
  unfolding limit_monadic_def
  apply (rewrite in "\<hole>" arl.fold_custom_empty)
  apply sepref_dbg_keep
  done

abbreviation "profile_rel \<equiv> \<langle>ballot_rel\<rangle>list_rel"
abbreviation "profile_on_A_rel A \<equiv> \<langle>ballot_on_A_rel A\<rangle>list_rel"

lemma profile_rel_imp_map_ballots:
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes "(pl, pr) \<in> profile_rel"
  shows "pr = map pl_\<alpha> pl"
proof (-)
  from assms have "\<forall> i < length pl. (pl!i, pr!i) \<in> ballot_rel"
    by (simp add: list_rel_pres_length param_nth)
  from assms this show " pr = map pl_\<alpha> pl"
    by (metis in_br_conv  length_map list_rel_pres_length nth_equalityI nth_map) 
qed
  
    

lemma profile_type_ref:
  fixes A:: "'a set"
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
  fixes A:: "'a set" and pl:: "'a Profile_List"
  assumes "(pl,pr) \<in> profile_on_A_rel A"
  shows "profile_l A pl"
  unfolding profile_l_def
  using assms in_br_conv
  by (metis (full_types) list_rel_imp_same_length pair_in_Id_conv param_nth relcompEpair)

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
    using profileref
    by (simp add: in_br_conv linorder_l_imp_rel list_rel_eq_listrel listrel_iff_nth 
        profile_def profile_l_def relAPP_def)
qed


end