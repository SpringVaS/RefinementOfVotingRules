theory Profile_Array
  imports "Verified_Voting_Rule_Construction.Profile"
  Preference_List
  "List-Index.List_Index"
  CAVA_Base.CAVA_Base 
  "Collections.Diff_Array"
begin

notation array_get ("_[[_]]" [900,0] 1000)

value "List_Index.index [1::nat,2] 858"

type_synonym 'a Profile_List = "('a Preference_List) list"

fun pr1_\<alpha> :: "'a Profile_List \<Rightarrow> 'a Profile" where
  "pr1_\<alpha> pr1 = map (Preference_List.pl_\<alpha>) pr1"

type_synonym 'a Preference_Array = "'a array"

type_synonym 'a Profile_Array = "('a Preference_Array) array"

definition profile_l :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> bool" where
  "profile_l A pr1 \<equiv> (\<forall> i::nat. i < length pr1 \<longrightarrow> 
    well_formed_pl (pr1!i) \<and> linear_order_on_l A (pr1!i))"

definition well_formed_prefa :: "'a Preference_Array \<Rightarrow> bool" where
  "well_formed_prefa pa = ((array_length pa > 0) \<and> distinct (list_of_array pa))"

lemma wfa_imp_wfl[simp]: "well_formed_prefa pa \<longrightarrow> well_formed_pl (list_of_array pa)"
  unfolding well_formed_prefa_def well_formed_pl_def
  by (simp add: array_length_list)

text \<open> Monadic definition of ballot properties \<close>

definition "index_mon_inv ballot a \<equiv> \<lambda> (i).
    (i \<le> List_Index.index ballot a)"

(* low level optimization for pref count *)
definition index_mon :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "index_mon ballot a \<equiv> do {
    i \<leftarrow> WHILET (\<lambda>(i). (i < (length ballot) \<and> ballot!i \<noteq> a)) 
      (\<lambda>(i). do {
      RETURN (i + 1)
    })(0);
    RETURN (i)
  }"                          


lemma index_mon_correct:
  shows "index_mon ballot_l a \<le> SPEC (\<lambda> r. r = List_Index.index ballot_l a)"
  unfolding index_mon_def   
  apply (intro WHILET_rule[where I="(index_mon_inv ballot_l a)" and R="measure (\<lambda>(i). length ballot_l - i)"] refine_vcg)
  unfolding index_mon_inv_def 
  apply (clarsimp_all, safe, simp_all)
proof -
  fix i
  assume notyet: "i \<le> List_Index.index ballot_l a"
  assume ir: "i < length ballot_l"
  assume notnow: "ballot_l ! i \<noteq> a"
  from notnow have "i \<noteq> List_Index.index ballot_l a"
    by (metis index_eq_iff ir)
  from notyet this show "Suc i \<le> List_Index.index ballot_l a"
    by fastforce
next
  fix i
  assume a1: "i \<le> List_Index.index ballot_l a"
  assume a2: "\<not> i < length ballot_l"
  from a2 have "i \<ge> length ballot_l" by fastforce
  from a1 this show "i = List_Index.index ballot_l a"
    using index_le_size
    by (metis le_trans verit_la_disequality)
next
  fix i
  assume "i \<le> List_Index.index ballot_l (ballot_l ! i)"
  from this show "i = List_Index.index ballot_l (ballot_l ! i)"
    by (metis index_first order_le_imp_less_or_eq)
qed

schematic_goal index_monadic_aux: "RETURN ?index_loop_based \<le> index_mon xs a"
  unfolding index_mon_def
  by (refine_transfer)

concrete_definition index_loop for xs a uses index_monadic_aux

thm index_loop_def

lemma index_loop_correct[simp]:
  shows "index_loop xs a = List_Index.index xs a"
  using order_trans[OF index_loop.refine index_mon_correct]
  by (auto simp: refine_rel_defs)

lemma index_member: "List_Index.index l a = length l \<longrightarrow> \<not>List.member l a"
  by (simp add: in_set_member index_size_conv)

fun rank_loop :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_loop ballot a = (let idx = (index_loop ballot a) in 
      if idx = (length ballot) then 0 
      else (idx + 1))" 

lemma rank_loop_eq: "rank_loop ballot a = rank_l ballot a"
proof (simp, safe)
  assume a1: "List_Index.index ballot a = length ballot"
  assume a2: "List.member ballot a"
  from a1 a2 show "False" using index_member by metis
next
  assume "List_Index.index ballot a \<noteq> length ballot"
  thus "List.member ballot a"
    by (metis in_set_member size_index_conv)
qed

definition array_index_of_mon :: "'a Preference_Array \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "array_index_of_mon ballot a \<equiv> do {
    i \<leftarrow> WHILET (\<lambda>(i). (i < (array_length ballot) \<and> ballot[[i]] \<noteq> a)) 
      (\<lambda>(i). do {
      RETURN (i + 1)
    })(0);
    RETURN (i)
  }"         

lemma array_length_idx[simp]: 
  assumes  "(array, list) \<in> (br list_of_array (\<lambda>x. True))"
  shows "\<forall>idx. idx < array_length array \<longleftrightarrow> idx < length list"
proof (safe)
  fix x1
  assume ir: "x1 < array_length array"
  from assms ir show "x1 < length list"
    by (simp add: array_length_list in_br_conv)
next
  fix x1
  assume ir: "x1 < length list"
  from assms ir show "x1 < array_length array"
    by (simp add: array_length_list in_br_conv)
qed

lemma array_access[simp]: 
  assumes  "(array, list) \<in> (br list_of_array (\<lambda>x. True))"
  shows "\<forall>i < array_length array. array[[i]] = list!i"
proof safe
  fix i
  assume "i < array_length array"
  from assms this show "array[[i]] = list!i"
    by (simp add: a_idx_it.get_correct array_length_list in_br_conv)
     
qed

lemma array_index_refine : 
  assumes "(ballot_a, ballot_l) \<in> (br list_of_array (\<lambda>x. True))"
  shows "array_index_of_mon ballot_a a \<le> \<Down>Id (index_mon ballot_l a)"
  unfolding array_index_of_mon_def index_mon_def
  apply (refine_rcg)
  apply (refine_dref_type)
proof (simp_all, safe)
  fix i
  assume "i < array_length ballot_a"
  from this assms show "i < length ballot_l" 
    by simp
next
  fix i
  assume ir: "i < array_length ballot_a"
  assume "ballot_a[[i]] \<noteq> ballot_l ! i"
  from ir assms this show "False"
    by simp
next
  fix i
  assume "i < length ballot_l"
  from this assms show "i < array_length ballot_a"
    by simp
next
  fix i
  assume ir: "i < length ballot_l"
  assume "ballot_l ! i \<noteq> ballot_a[[i]]"
  from ir assms this show "False"
    by simp
qed


definition is_less_pref_array ::"'a \<Rightarrow> 'a Preference_Array \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "is_less_pref_array x ballot y \<equiv> do {
    (i, idxx, idxy) \<leftarrow> WHILET (\<lambda>(i, ret). (i < (array_length ballot))) 
      (\<lambda>(i, idxx, idxy). do {
      let c = ballot[[i]];
      let idxx = (if (c = x) then i + 1 else 0);
      let idxy = (if (c = y) then i + 1 else 0);
      let i = i + 1;
      RETURN (i, idxx, idxy)
    })(0,0,0);
    let ret = (if (idxx = 0 \<or> idxy = 0) then False else (idxy < idxx));
    RETURN (ret)
  }"

lemma "lparray_correct" : 
  assumes "(barray, r) \<in> br (pa_to_pr) (well_formed_prefa)"
  shows "is_less_pref_array x barray y \<le> SPEC (\<lambda> lp. lp = x \<preceq>\<^sub>r y)"
  unfolding is_less_pref_array_def
  oops




text \<open> Profile Array abstraction functions \<close>

definition pa_to_pl :: "'a Profile_Array \<Rightarrow> 'a Profile_List" where
  "pa_to_pl pa = map (list_of_array) (list_of_array pa)"

definition pa_to_pr :: "'a Profile_Array \<Rightarrow> 'a Profile" where
  "pa_to_pr pa = pr1_\<alpha> (pa_to_pl pa)"

definition pl_to_pa :: "'a Profile_List \<Rightarrow> 'a Profile_Array" where
  "pl_to_pa pa = array_of_list (map (array_of_list) (pa))"

text \<open> Profile properties and refinement \<close>

definition profile_a :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> bool" where
  "profile_a A pa = profile_l A (pa_to_pl pa)"

abbreviation finite_profile_a :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> bool" where
  "finite_profile_a A pa \<equiv> finite A \<and> profile_a A pa"

lemma profile_data_refine: 
  assumes "(pl,pr)\<in>build_rel pr1_\<alpha> (profile_l A)"
  shows "profile A pr"
  unfolding profile_def
  apply(intro allI impI)
proof (-)
  fix i
  assume ir: "i < length pr"
  from ir assms have "well_formed_pl (pl ! i)" unfolding profile_l_def
    by (simp add: in_br_conv)
  from ir assms have "linear_order_on_l A (pl ! i)" unfolding profile_l_def
    by (simp add: in_br_conv) 
  from assms this show "linear_order_on A (pr ! i)" unfolding profile_l_def
    using linorder_l_imp_rel
    by (metis (mono_tags, lifting) in_br_conv ir length_map nth_map pr1_\<alpha>.simps)
qed

lemma profile_a_l: assumes "profile_a A pa"
  shows "profile_l A (pa_to_pl pa)"
  using assms profile_a_def by (metis)

lemma profile_a_rel: assumes "profile_a A pa"
  shows "profile A (pa_to_pr pa)"
  using profile_data_refine
  by (metis assms brI pa_to_pr_def profile_a_def)


text \<open>
  Monadic redifintion of counting functions.
\<close>

definition "wc_invar p0 a \<equiv> \<lambda>(r,ac).
  r \<le> length p0 
  \<and> ac = card{i::nat. i < r \<and> above (p0!i) a = {a}}"

definition win_count_mon :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_mon p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ac = ac + (if (above (p!r) a = {a}) then 1 else 0);
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"


definition win_count_mon_r :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_mon_r p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ac = ac + (if (rank (p!r) a = 1) then 1 else 0);
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"
  

(* The lemma is implicitly proven
in the win_count_mon_correct lemma *)
(* lemma wc_invar_step:
  shows "\<forall> r < length p. wc_invar p a (r, ac) \<longrightarrow> wc_invar p a (r + 1, ac + (if (above (p!r) a = {a}) then 1 else 0))"
  unfolding wc_invar_def *)

lemma win_count_mon_correct:
  shows "win_count_mon p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  unfolding win_count_mon_def win_count.simps
  apply (intro WHILET_rule[where I="(wc_invar p a)" and R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding wc_invar_def
  apply (simp_all)
  apply (erule subst)
  apply (simp)
  apply (intro conjI impI)
proof (simp_all)
  fix r :: nat
  assume le: "r < length p"
  assume atop: "above (p ! r) a = {a}"
  with atop have prep: 
         "{i. i < Suc r \<and> above (p ! i) a = {a}} 
        = {i. i < r \<and> above (p ! i) a = {a}} \<union> {r}"
    by fastforce
  then show   
         "Suc (card {i. i < r \<and> above (p ! i) a = {a}}) =
          card {i. i < Suc r \<and> above (p ! i) a = {a}}"
    by fastforce
next
  fix r :: nat
  assume "r < length p"
  assume atop: "above (p ! r) a \<noteq> {a}"
  then show "
       card {i. i < r \<and> above (p ! i) a = {a}} =
       card {i. i < Suc r \<and> above (p ! i) a = {a}}"
    by (metis less_Suc_eq)
qed

lemma carde: assumes pprofile: "profile A p"
  shows "\<forall> r < length p. (card (above (p ! r) a) = 1) = (above (p ! r) a = {a})" 
  using pprofile
    by (metis profile_def rank.simps Preference_Relation.rankone1 Preference_Relation.rankone2)
    
lemma win_count_mon_r_correct:
  assumes prof: "profile A p"
  shows "win_count_mon_r p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  unfolding win_count_mon_r_def win_count.simps
  apply (intro WHILET_rule[where I="(wc_invar p a)" and R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding wc_invar_def
  apply (simp_all)
  apply (erule subst)
  apply (simp)
proof (safe, simp_all)
  fix aa
  assume aail: "aa < length p"
  assume rank1: "card (above (p ! aa) a) = Suc 0"
  from aail prof rank1 have "above (p ! aa) a = {a}"
    by (metis One_nat_def profile_def rank.simps rankone2)
  from this have prep: 
         "{i. i < Suc aa \<and> above (p ! i) a = {a}} 
        = {i. i < aa \<and> above (p ! i) a = {a}} \<union> {aa}"
    by fastforce
  then show 
         "Suc (card {i. i < aa \<and> above (p ! i) a = {a}}) =
          card {i. i < Suc aa \<and> above (p ! i) a = {a}}"
    by simp
next
  fix aa
  assume aail: "aa < length p"
  assume rank1: "card (above (p ! aa) a) \<noteq> Suc 0"
  from aail rank1 have neq: "above (p ! aa) a \<noteq> {a}"
    by fastforce
  have seteq:
      "{i. i < Suc aa \<and> above (p ! i) a = {a}}
      ={i. i < aa \<and> above (p ! i) a = {a}} \<union> {i. i = aa \<and> above (p ! i) a = {a}}"
    by fastforce
  from neq have emp: "{i. i = aa \<and> above (p ! i) a = {a}} = {}" by blast
    from seteq emp have
    "{i. i < Suc aa \<and> above (p ! i) a = {a}} = {i. i < aa \<and> above (p ! i) a = {a}}"
    by simp
  then show "
      card {i. i < aa \<and> above (p ! i) a = {a}} =
      card {i. i < Suc aa \<and> above (p ! i) a = {a}}"
    by simp
qed

definition winsr :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> nat" where
  "winsr r a \<equiv> (if (rank r a = 1) then 1 else 0)"

definition win_count_mon_outer :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_mon_outer p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ac = ac + winsr (p!r) a;
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"

lemma win_count_mon_outer_correct:
  assumes prof: "profile A p"
  shows "win_count_mon_outer p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
proof -
  have eq: "win_count_mon_outer p a = win_count_mon_r p a"
  unfolding win_count_mon_outer_def win_count_mon_r_def winsr_def
  by fastforce
  from eq show ?thesis using win_count_mon_r_correct
    using prof by fastforce 
qed

schematic_goal wc_code_aux: "RETURN ?wc_code \<le> win_count_mon p a"
  unfolding win_count_mon_def
  by (refine_transfer)

concrete_definition win_count_code for p a uses wc_code_aux

lemma win_count_equiv: 
  shows "win_count p a = win_count_code p a"
proof -
  from order_trans[OF win_count_code.refine win_count_mon_correct] 
    have "win_count_code p a = win_count p a"
      by fastforce
  thus ?thesis by simp
qed

export_code win_count in Scala

text \<open> Data refinement \<close>

definition winsr_imp :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "winsr_imp l a \<equiv> (if (rank_l l a = 1) then 1 else 0)"

definition winsr_imp' :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "winsr_imp' l a \<equiv> (if (l!0 = a) then 1 else 0)"

lemma winsr_imp_refine:
  assumes "linear_order_on_l A l"
  assumes "(l,r)\<in>build_rel pl_\<alpha> well_formed_pl"
  shows "winsr_imp l a = (winsr r a)"
  unfolding winsr_imp_def winsr_def
  using rankeq
  by (metis assms(1) assms(2) in_br_conv) 

lemma winsr_imp'_eq:
  assumes "well_formed_pl l"
  shows "winsr_imp' l a = (winsr_imp l a)"
  unfolding winsr_imp'_def winsr_imp_def
proof (simp, safe)
  show "List_Index.index l (l ! 0) = 0"
    by (simp add: index_eqI) 
next
  assume amem: "List.member l a"
  assume anhd: "l!0 \<noteq> a"
  from amem anhd show "0 < List_Index.index l a"
    by (metis gr0I in_set_member nth_index)
next
  assume nmem: "\<not> List.member l (l!0)"
  assume fstex: "a = l ! 0"
  from nmem have "set l = {}"
    by (metis length_greater_0_conv member_def nth_mem set_empty2)
  from this have "l = []"
    using set_empty by simp
  from assms this show "False" unfolding well_formed_pl_def by simp
qed


definition win_count_imp :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ac = ac + (winsr_imp (p!r) a);
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"
  

lemma win_count_imp_refine: 
  assumes "(pl,pr)\<in>build_rel pr1_\<alpha> (profile_l A)"
  shows "win_count_imp pl a \<le> \<Down>Id (win_count_mon_outer pr a)"
  using assms unfolding win_count_imp_def win_count_mon_outer_def
  apply (refine_rcg)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply simp
  apply (auto simp add: refine_rel_defs)
  using  winsr_imp_refine
    by (metis in_br_conv profile_l_def)

theorem win_count_imp_correct:
  assumes "(pl,pr)\<in>build_rel pr1_\<alpha> (profile_l A)"
  shows "win_count_imp pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using ref_two_step[OF win_count_imp_refine win_count_mon_outer_correct] assms
    profile_data_refine by fastforce
  
  
definition win_count_imp' :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp' p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ballot = (p!r);
    let ac = ac + winsr_imp' ballot a;
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"


lemma win_count_imp'_refine: assumes "profile_l A pl"
  shows "win_count_imp' pl a \<le> \<Down>Id (win_count_imp pl a)"
  unfolding win_count_imp'_def win_count_imp_def winsr_imp_def wc_invar_def
  apply (refine_rcg)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply simp_all
  apply (auto simp add: 
     refine_rel_defs)
proof (unfold winsr_imp'_def, simp_all)
  fix x1
  assume range: "x1 < length pl"
  assume mem: "List.member (pl ! x1) a"
  assume fst: "List_Index.index (pl ! x1) a = 0"
  from mem fst show "pl!x1!0 = a"
    by (metis in_set_member nth_index)
next
  fix x1
  assume range: "x1 < length pl"
  assume mem: "List.member (pl ! x1) a"
  assume nfst: "List_Index.index (pl ! x1) a > 0"
  from mem nfst show "pl!x1!0 \<noteq> a"
    by (metis index_eq_iff)
next
  fix x1
  assume range: "x1 < length pl"
  assume nmem: "\<not> List.member (pl ! x1) a"
  from assms range have nonempty_ballot: "(pl!x1) \<noteq> []" unfolding profile_l_def well_formed_pl_def
    by (metis len_greater_imp_nonempty)
  have "l\<noteq>[] \<and> (l!0 = a) \<longrightarrow> List.member l a"
    by (metis length_greater_0_conv member_def nth_mem) 
  from this nonempty_ballot nmem show "pl!x1!0 \<noteq> a"
    by (metis length_greater_0_conv member_def nth_mem)
qed

theorem win_count_imp'_correct:
  assumes "(pl,pr)\<in>build_rel pr1_\<alpha> (profile_l A)"
  shows "win_count_imp' pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using ref_two_step[OF win_count_imp'_refine win_count_imp_correct] assms refine_IdD
  by (metis in_br_conv) 


text \<open> Moving from Lists to Arrays \<close>

definition win_count_imp_array :: "'a Profile_Array \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp_array p a \<equiv> do {
  (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < array_length p) (\<lambda>(i, ac). do {
    ASSERT (i < array_length p);
    let ballot = (p[[i]]);
    let ac = ac + (if (ballot[[0]] = a) then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"


lemma win_count_imp_array_refine:
  assumes "(pa, pl) \<in> br pa_to_pl (profile_a A)"
  shows "win_count_imp_array pa a \<le> \<Down>Id (win_count_imp' pl a)"
  unfolding win_count_imp_array_def win_count_imp'_def winsr_imp'_def
  apply (refine_rcg)
  apply (refine_dref_type)
  apply (simp_all, safe)
proof (simp_all)
  fix x1
  assume ir: "x1 < array_length pa"
  have "array_length pa = length (list_of_array pa)"
    by (simp add: array_length_list)
  from assms ir this show "x1 < length pl" unfolding pa_to_pl_def
    by (simp add: in_br_conv)
next
  fix x1
  assume ir: "x1 < length pl"
  from assms ir show g2: "x1 < array_length pa" unfolding pa_to_pl_def
    by (simp add: array_length_list in_br_conv)
next
  fix x1
  assume ir: "x1 < length pl"
  assume afst: "a = (pa[[x1]])[[0]]"
  from ir have arrayac: "(pa[[x1]])[[0]] = list_of_array((list_of_array pa)!x1)!0"
    by (metis Diff_Array.array.exhaust array_get.simps list_of_array.simps)
  from assms ir arrayac show "pl! x1 ! 0 = (pa[[x1]])[[0]]" 
    unfolding pa_to_pl_def well_formed_pl_def
    by (simp add: in_br_conv)  
next
  fix x1
  assume ir: "x1 < length pl"
  assume neq: "pa[[x1]][[0]] \<noteq> pl ! x1 ! 0"
  from ir have arrayac: "pa[[x1]][[0]] = list_of_array((list_of_array pa)!x1)!0"
    by (metis Diff_Array.array.exhaust array_get.simps list_of_array.simps)
  from assms ir arrayac have "pl! x1 ! 0 = pa[[x1]][[0]]" 
    unfolding pa_to_pl_def well_formed_pl_def
    by (simp add: in_br_conv)  
  from neq this show "False" by simp
qed

lemma a_l_r_step: "(pr1_\<alpha> \<circ> pa_to_pl) = pa_to_pr"
  by (simp add: fun_comp_eq_conv pa_to_pr_def)
  
lemma win_count_imp_array_correct:
  assumes "(pa, pr) \<in> br pa_to_pr (profile_a A)"
  shows "win_count_imp_array pa a \<le> SPEC (\<lambda>ac. ac = win_count pr a)"
  using assms ref_two_step[OF win_count_imp_array_refine win_count_imp'_correct]
  by (metis in_br_conv pa_to_pr_def profile_a_l refine_IdD)

schematic_goal wc_code_refine_aux: "RETURN ?wc_code \<le> win_count_imp_array p a"
  unfolding win_count_imp_array_def
  by (refine_transfer)

concrete_definition win_count_imp_code for p a uses wc_code_refine_aux

lemma win_count_array[simp]:
  assumes lg: "(profile_a A pa)"
  shows "win_count_imp_code pa a = win_count (pa_to_pr pa) a"
  using lg order_trans[OF win_count_imp_code.refine win_count_imp_array_correct,
    of pa "(pa_to_pr pa)"]
  by (auto simp: refine_rel_defs)

lemma win_count_array_code_correct: 
  assumes lg: "(profile_a A pa)"
  shows "win_count (pa_to_pr pa) a = win_count_imp_code pa a"
  by (metis lg win_count_array)


definition  "prefer_count_invariant p x y \<equiv> \<lambda>(r, ac).
      r \<le> length p \<and>
      ac = card {i::nat. i < r \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

definition prefer_count_mon :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "prefer_count_mon p x y \<equiv> do {
   (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let b = (p!i);
    let ac = ac + (if y \<preceq>\<^sub>b x then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma prefer_count_mon_correct:
  shows "prefer_count_mon p a b \<le> SPEC (\<lambda> wc. wc = prefer_count p a b)"
  unfolding prefer_count_mon_def prefer_count.simps
  apply (intro WHILET_rule[where I="(prefer_count_invariant p a b)"
        and R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding prefer_count_invariant_def
  apply (simp_all)
  apply (erule subst)
  apply (simp)
  apply (intro conjI impI)
proof (simp_all)
  fix r
  assume ir: "r < length p"
  assume blpa: "(b, a) \<in> p!r"
  with blpa have prep: 
         "{i. i < Suc r \<and> (b, a) \<in> p ! i} 
        = {i. i < r \<and> (b, a) \<in> p ! i} \<union> {r}"
    by fastforce
  thus "Suc (card {i. i < r \<and> (b, a) \<in> p ! i}) = card {i. i < Suc r \<and> (b, a) \<in> p ! i}"
    by fastforce
next
  fix r
  assume ir: "r < length p"
  assume bnlpa: "(b, a) \<notin> p!r"
  with bnlpa ir show prep: 
         "card {i. i < r \<and> (b, a) \<in> p ! i} 
        = card {i. i < Suc r \<and> (b, a) \<in> p ! i} "
    using less_Suc_eq by metis    
qed  

end