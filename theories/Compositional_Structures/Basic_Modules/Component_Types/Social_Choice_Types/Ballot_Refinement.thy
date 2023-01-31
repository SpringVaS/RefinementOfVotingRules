theory Ballot_Refinement
  imports Verified_Voting_Rule_Construction.Preference_Relation
  Verified_Voting_Rule_Construction.Preference_List

  Verified_Voting_Rule_Construction.Profile
  Verified_Voting_Rule_Construction.Profile_List

  Refine_Imperative_HOL.IICF

begin


definition finite_set_rel where alt_set_rel_def_internal:
  "finite_set_rel R \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) (\<lambda> x. finite x))"



(*lemma alt_set_rel_fixed_def[refine_rel_defs]: 
  "\<langle>R\<rangle>alt_set_rel_fixed A \<equiv> {(As, Bs). As = A \<and> (As, Bs) \<in> \<langle>R\<rangle>set_rel}"
  by (simp add: alt_set_rel_fixed_internal_def relAPP_def)*)

lemma finite_set_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>finite_set_rel \<equiv> (\<langle>R\<rangle>set_rel O br (\<lambda>x. x) (\<lambda> x. finite x))"
  by (simp add: alt_set_rel_def_internal relAPP_def)

definition alt_set_rel_fixed :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'a set) set"
  where alt_set_rel_fixed_internal_def:
  "alt_set_rel_fixed R A \<equiv> \<langle>R\<rangle>set_rel O br (\<lambda>x. x) (\<lambda>x. x = A) "

lemma finite_alts:
  assumes "(a, a') \<in> \<langle>R\<rangle>finite_set_rel" and "single_valued R" and "IS_LEFT_UNIQUE R"
  shows "finite a" using assms  finite_set_rel_def in_br_conv
  by (metis (no_types, lifting) IS_LEFT_UNIQUE_def Pair_inject finite_set_rel_transfer_back relcompE)

lemma id_same_alts:
  assumes "(A, A') \<in> \<langle>Id\<rangle>finite_set_rel"
  shows "A' = A"
  using assms  in_br_conv set_rel_id Id_O_R unfolding finite_set_rel_def
  by (metis (no_types, lifting))
  
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

find_theorems "sorted_wrt"


definition "limit_monadic_inv A ballot \<equiv> \<lambda> (i, nbal).
  nbal = limit_l A (take i ballot)"

definition  limit_monadic :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List nres" where
"limit_monadic A ballot \<equiv> do {
    (i, nbal) \<leftarrow> WHILEIT (limit_monadic_inv A ballot)
  (\<lambda> (i, nbal). i < length ballot) 
      (\<lambda> (i, nbal). do {
      ASSERT (i < (length ballot));
      let c = (ballot!i);
      RETURN (if (c \<in> A) then
         (i + 1, nbal @ [c])
      else
        (i + 1, nbal))
    })((0, []));
    RETURN (nbal)
  }"                          

find_theorems filter

lemma limit_monadic_refine:
  shows "(limit_monadic, (\<lambda> A bl. SPEC(\<lambda> lim. lim = (limit_l A bl)))) \<in> \<langle>Id\<rangle>finite_set_rel \<rightarrow>
      \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding limit_monadic_def
  apply (refine_rcg, rename_tac A' A bl br)
proof -
  fix A' A :: "'a set"
  fix bl :: "'a Preference_List"
  fix  br :: "'a Preference_List"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  assume bid: "(bl, br) \<in> \<langle>Id\<rangle>list_rel"
  from arel have aeq: "A' = A" by (auto simp add: finite_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: finite_set_rel_def in_br_conv)
  from bid have beq: "bl = br"
    by simp 
  show  " WHILE\<^sub>T\<^bsup>limit_monadic_inv A' bl\<^esup> (\<lambda>(i, nbal). i < length bl)
        (\<lambda>(i, nbal).
            ASSERT (i < length bl) \<bind>
            (\<lambda>_. let c = bl ! i in RETURN (if c \<in> A' then (i + 1, nbal @ [c]) else (i + 1, nbal))))
        (0, []) \<bind>
       (\<lambda>(i, nbal). RETURN nbal)
       \<le> SPEC (\<lambda>lim. lim = limit_l A br)"
    by (refine_vcg WHILEIT_rule[where R = "measure (\<lambda>(i, newb). length bl - i)"],
        auto simp add: limit_monadic_inv_def pl_\<alpha>_def beq aeq take_Suc_conv_app_nth)
qed
  

sepref_definition limit_imp is "uncurry (limit_monadic)" ::
  "(hs.assn nat_assn)\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a (arl_assn nat_assn)"
  unfolding limit_monadic_def
  apply (rewrite in "WHILEIT _ _ _ \<hole>" arl.fold_custom_empty)
  by sepref

abbreviation "profile_rel \<equiv> \<langle>ballot_rel\<rangle>list_rel"
abbreviation "profile_on_A_rel A \<equiv> \<langle>ballot_on_A_rel A\<rangle>list_rel"

term fun_rel

term "{ (f,f'). \<forall>(a,a')\<in>A. (f a, f' a')\<in>B }"

definition alt_and_profile_rel ::
  "('a \<times> 'a) set \<Rightarrow> (('a set \<times> 'a list list) \<times> 'a set \<times> ('a \<times> 'a) set list) set"
  where alt_and_profile_rel_def_internal: 
"alt_and_profile_rel R \<equiv> 
  {((A', pl),(A, pr)). (A', A) \<in> \<langle>R\<rangle>finite_set_rel
    \<and> (pl, pr) \<in> profile_on_A_rel (A')}"

lemma alt_and_profile_rel_def: 
  "\<langle>R\<rangle>alt_and_profile_rel \<equiv> {((A', pl),(A, pr)). (A', A) \<in> \<langle>R\<rangle>finite_set_rel
    \<and> (pl, pr) \<in> profile_on_A_rel (A')}"
  by (simp add: alt_and_profile_rel_def_internal relAPP_def)

lemma sv_prof_rel: "single_valued profile_rel"
  by (simp add: list_rel_sv)

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
  using assms in_br_conv
  by (metis (full_types) list_rel_imp_same_length pair_in_Id_conv param_nth relcompEpair)

lemma profile_ref:
  fixes A :: "'a set"
  fixes pl :: "'a Profile_List"
  and pr :: "'a Profile"
  assumes prel: "(pl,pr) \<in> profile_rel"
  shows "profile_l A pl = profile A pr"
proof (-)
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
    using profile_ref
    by (simp add: in_br_conv linorder_l_imp_rel list_rel_eq_listrel listrel_iff_nth 
        profile_def profile_l_def relAPP_def)
qed


lemma unfold_alt_profile_alt_rel:
  assumes "((A', pl),(A, pr)) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  shows "(A', A) \<in> \<langle>Id\<rangle>finite_set_rel"
  using assms unfolding alt_and_profile_rel_def
  by simp

lemma unfold_alt_profile_profA_rel:
  assumes "((A', pl),(A, pr)) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  shows "(pl,pr) \<in> profile_on_A_rel A'"
  using assms unfolding alt_and_profile_rel_def finite_set_rel_def
  using set_rel_id
  apply simp
  done

lemma unfold_alt_profile_prof_rel:
  assumes "((A', pl),(A, pr)) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  shows "(pl,pr) \<in> profile_rel"
proof -
  from assms have "(pl,pr) \<in> profile_on_A_rel A'"
    using unfold_alt_profile_profA_rel by blast
  from this show ?thesis using profile_type_ref
    by blast
qed

lemma unfold_alt_profile_prof_prop:
  assumes "((A', pl),(A, pr)) \<in> \<langle>Id\<rangle>alt_and_profile_rel"
  shows "profile_l A' pl"
proof -
  from assms have "(pl,pr) \<in> profile_on_A_rel A'"
    using unfold_alt_profile_profA_rel by blast
  from this show ?thesis using profile_prop_list
    by blast
qed


abbreviation "cand_impl_assn \<equiv> nat_assn"

abbreviation "ballot_impl_assn \<equiv> (arl_assn cand_impl_assn)"

abbreviation "profile_impl_assn \<equiv> (list_assn ballot_impl_assn)"

abbreviation "alts_set_impl_assn \<equiv> (hs.assn cand_impl_assn)"

abbreviation "result_impl_assn \<equiv> alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn \<times>\<^sub>a alts_set_impl_assn"

definition "alts_ref_assn \<equiv> hr_comp alts_set_impl_assn (\<langle>Id\<rangle>finite_set_rel)"
                                 

definition "ballot_ref_assn \<equiv>  hr_comp ballot_impl_assn (\<langle>Id\<rangle>list_rel)"

definition "alts_assn \<equiv> hr_comp alts_ref_assn (\<langle>Id\<rangle>set_rel)"

definition "result_set_one_step \<equiv> hr_comp alts_set_impl_assn (\<langle>Id\<rangle>set_rel)"

definition "result_set_assn \<equiv> hr_comp(result_set_one_step) (\<langle>Id\<rangle>set_rel)"


definition "ballot_assn \<equiv> hr_comp (hr_comp ballot_impl_assn ballot_rel) (\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel)"



end