theory Profile_Array
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
  CAVA_Base.CAVA_Base 
begin

notation array_get ("_[[_]]" [900,0] 1000)

type_synonym 'a Preference_Array = "'a array"

type_synonym 'a Profile_Array = "('a Preference_Array) array"

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
  shows "\<And>idx. idx < array_length array \<longleftrightarrow> idx < length (list_of_array array)"
proof (safe)
  fix x1
  assume ir: "x1 < array_length array"
  from ir show "x1 < length (list_of_array array)"
    by (simp add: array_length_list)
next
  fix x1
  assume ir: "x1 < length (list_of_array array)"
  from ir show "x1 < array_length array"
    by (simp add: array_length_list)
qed

lemma array_access[simp]: 
  fixes array:: "'a array" and list:: "'a list"
  assumes  "list = list_of_array array"
  shows "\<forall>i < length list. array[[i]] = list!i"
proof safe
  fix i
  assume "i < length list"
  from assms this show "array[[i]] = list!i"
    by (simp add: a_idx_it.get_correct array_length_list in_br_conv)
qed

lemma array_index_refine : 
  shows "array_index_of_mon ballot_a a \<le> \<Down>Id (index_mon (list_of_array ballot_a) a)"
  unfolding array_index_of_mon_def index_mon_def
  apply (refine_rcg)
   apply (refine_dref_type)
  by auto

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

lemma lparray_correct : 
  assumes "(barray, r) \<in> br (pa_to_pr) (well_formed_prefa)"
  shows "is_less_pref_array x barray y \<le> SPEC (\<lambda> lp. lp = x \<preceq>\<^sub>r y)"
  unfolding is_less_pref_array_def
  oops




text \<open> Profile Array abstraction functions \<close>

definition pa_to_pl :: "'a Profile_Array \<Rightarrow> 'a Profile_List" where
  "pa_to_pl pa = map (list_of_array) (list_of_array pa)"

definition pa_to_pr :: "'a Profile_Array \<Rightarrow> 'a Profile" where
  "pa_to_pr pa = pl_to_pr_\<alpha> (pa_to_pl pa)"

definition pl_to_pa :: "'a Profile_List \<Rightarrow> 'a Profile_Array" where
  "pl_to_pa pa = array_of_list (map (array_of_list) (pa))"

text \<open> Profile properties and refinement \<close>

definition profile_a :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> bool" where
  "profile_a A pa = profile_l A (pa_to_pl pa)"

abbreviation finite_profile_a :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> bool" where
  "finite_profile_a A pa \<equiv> finite A \<and> profile_a A pa"

lemma profile_data_refine: 
  assumes "(pl,pr)\<in>build_rel pl_to_pr_\<alpha> (profile_l A)"
  shows "profile A pr"
proof -
  from assms have prof: "profile_l A pl"
    using in_br_conv by metis
  from assms have "pr = pl_to_pr_\<alpha> pl"
    using in_br_conv by metis
  with prof show ?thesis 
    using profile_prop_refine by metis
qed

lemma profile_a_l: assumes "profile_a A pa"
  shows "profile_l A (pa_to_pl pa)"
  using assms profile_a_def by (metis)

lemma profile_a_rel: assumes "profile_a A pa"
  shows "profile A (pa_to_pr pa)"
  using profile_data_refine
  by (metis assms brI pa_to_pr_def profile_a_def)

lemma array_refine_length[simp]:
  assumes "(pa, pl) \<in> br pa_to_pl (profile_a A)"
  shows "length (list_of_array pa) = length pl"
  using assms in_br_conv array_length_list
     by (metis length_map pa_to_pl_def) 

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

(* This implementation requires the aasumption that ballots are not empty
   For empty ballots, a guard must be added to avoid accessing the first element *)
definition winsr_imp' :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "winsr_imp' l a \<equiv> (if ((length l > 0) \<and> (l!0 = a)) then 1 else 0)"

(* these auxiliary lemmas illustrate the equivalence of checking the the first
  candidate on a non empty ballot. *)
lemma top_above:
  assumes ne: "length pl > 0"
  shows "pl!0 = a \<longleftrightarrow> above_l pl a = [a]"
  unfolding above_l_def
proof (auto)
  assume mem: "List.member pl (pl ! 0)"
  assume "a = pl ! 0"
  have "List_Index.index pl (pl ! 0) = 0"
    by (simp add: index_eqI)
  from mem this show "take (Suc (List_Index.index pl (pl ! 0))) pl = [pl ! 0]"
    by (metis append_Nil in_set_member index_less_size_conv take0 take_Suc_conv_app_nth)
next
  (*assume mem: "List.member pl a"*)
  assume "take (Suc (List_Index.index pl a)) pl = [a]"
  from this show "pl ! 0 = a"
    by (metis append_Cons append_Nil append_take_drop_id hd_conv_nth list.sel(1))
next
  assume nm: "\<not> List.member pl (pl ! 0)"
  from this have pl_empty: "pl = []"
    by (metis length_greater_0_conv member_def nth_mem)
  from ne this pl_empty show "False"
    by simp
qed

lemma top_l_above_r:
  assumes ballot: "ballot_on A pl"
  assumes ne: "length pl > 0"
  shows "pl!0 = a \<longleftrightarrow> above (pl_\<alpha> pl) a = {a}"
proof -
  from ne have listeq: "pl!0 = a \<longleftrightarrow> above_l pl a = [a]"
    by (simp add: top_above)
  from assms have above_abstract: "set (above_l pl a) = above (pl_\<alpha> pl) a" 
    by (auto simp add: aboveeq)
  have list_set: "above_l pl a = [a] \<longleftrightarrow> set (above_l pl a) = {a}"
    by (metis above_l_def append_self_conv2 gr0I hd_take id_take_nth_drop insert_not_empty list.sel(1) list.set(1) list.set_sel(1) list.simps(15) listeq ne singleton_iff take_eq_Nil)
  from above_abstract listeq this show ?thesis
    by (simp)
qed


lemma winsr_imp_refine:
  assumes "(l,r)\<in>build_rel pl_\<alpha> (ballot_on A)"
  shows "winsr_imp l a = (winsr r a)"
  unfolding winsr_imp_def winsr_def
  using rankeq
  by (metis assms in_br_conv)

lemma nmem_empty_l[simp]:
  shows "\<not>List.member [] a"
    by (simp add: member_rec(2))

lemma winsr_imp'_eq:
  assumes "well_formed_pl l" 
(*and "l \<noteq> []"  necessary when not checking for empty ballots *)
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
  assume "\<not> List.member l (l ! 0)" and "l \<noteq> []"
  thus "False"
    by (metis hd_conv_nth hd_in_set in_set_member)
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
  assumes "(pl,pr)\<in>br pl_to_pr_\<alpha> (profile_l A)"
  shows "win_count_imp pl a \<le> \<Down>Id (win_count_mon_outer pr a)"
  using assms unfolding win_count_imp_def win_count_mon_outer_def
  apply (refine_rcg)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply (auto simp add: refine_rel_defs)
  using  winsr_imp_refine
  by (metis (no_types, lifting) brI profile_l_def)
    
theorem win_count_imp_correct:
  assumes "(pl,pr)\<in>build_rel pl_to_pr_\<alpha> (profile_l A)"
  shows "win_count_imp pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using ref_two_step[OF win_count_imp_refine win_count_mon_outer_correct] assms
    profile_data_refine by fastforce
  
  
definition win_count_imp' :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp' p a \<equiv> do {
  (r, ac) \<leftarrow> WHILET (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let ac = ac + (winsr_imp' (p!r) a);
    let r = r + 1;
    RETURN (r, ac)
  })(0,0);
  RETURN ac
}"


lemma win_count_imp'_refine: 
  fixes a:: "'a"
  assumes "profile_l A pl"
  shows "win_count_imp' pl a \<le> \<Down>Id (win_count_imp pl a)"
  unfolding win_count_imp'_def win_count_imp_def wc_invar_def
  apply (refine_rcg)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply clarsimp_all
proof (unfold winsr_imp'_def winsr_imp_def, (simp_all add: index_eqI), safe)
  fix x1
  assume range: "x1 < length pl"
  assume mem: "List.member (pl ! x1) a"
  assume nfst: "(pl!x1!0) \<noteq> a"
  from range mem nfst show "List_Index.index (pl ! x1) a > 0"
    by (metis in_set_member nth_index zero_less_iff_neq_zero)
next
  fix x1
  assume range: "x1 < length pl"
  assume nmem: "\<not> List.member (pl ! x1) (pl ! x1 ! 0)"
  assume "pl ! x1 \<noteq> []"
  from nmem this show "False" by (metis hd_conv_nth hd_in_set in_set_member)
qed


theorem win_count_imp'_correct:
  assumes nempty_cands: "A \<noteq> {}"
  assumes "(pl,pr)\<in>build_rel pl_to_pr_\<alpha> (profile_l A)"
  shows "win_count_imp' pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using ref_two_step[OF win_count_imp'_refine win_count_imp_correct] 
      assms refine_IdD in_br_conv
  by metis


text \<open> Moving from Lists to Arrays \<close>

definition win_count_imp_array :: "'a Profile_Array \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp_array p a \<equiv> do {
  (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < array_length p) (\<lambda>(i, ac). do {
    ASSERT (i < array_length p);
    let ac = ac + (if (((array_length (p[[i]])) > 0) \<and> ((p[[i]])[[0]] = a)) then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma conv_array[simp]:
  assumes "(pa, pl) \<in> br pa_to_pl (profile_a A)"
  shows  "\<And>x1. x1 < length pl \<Longrightarrow> pl ! x1 = list_of_array (list_of_array pa ! x1)"
proof (-)
  fix x1
  assume ir: "x1 < length pl"
  from assms have "length (list_of_array pa) = length pl" 
     using in_br_conv array_length_list
     by (metis length_map pa_to_pl_def) 
  from assms ir this show "pl ! x1 = list_of_array (list_of_array pa ! x1)"
    by (metis in_br_conv nth_map pa_to_pl_def)
qed
    

lemma win_count_imp_array_refine:
  assumes "(pa, pl) \<in> br pa_to_pl (profile_a A)"
  shows "win_count_imp_array pa a \<le> \<Down>Id (win_count_imp' pl a)"
  unfolding win_count_imp_array_def win_count_imp'_def winsr_imp'_def
  apply (refine_rcg)
  apply (refine_dref_type)
  using assms by (safe, simp_all)+
  

lemma a_l_r_step: "(pl_to_pr_\<alpha> \<circ> pa_to_pl) = pa_to_pr"
  by (simp add: fun_comp_eq_conv pa_to_pr_def)
  
lemma win_count_imp_array_correct:
  assumes "A \<noteq> {}"
  assumes "(pa, pr) \<in> br pa_to_pr (profile_a A)"
  shows "win_count_imp_array pa a \<le> SPEC (\<lambda>ac. ac = win_count pr a)"
  using assms ref_two_step[OF win_count_imp_array_refine win_count_imp'_correct]
  by (metis in_br_conv pa_to_pr_def profile_a_l refine_IdD)

schematic_goal wc_code_refine_aux: "RETURN ?wc_code \<le> win_count_imp_array p a"
  unfolding win_count_imp_array_def
  by (refine_transfer)

concrete_definition win_count_imp_code for p a uses wc_code_refine_aux

lemma win_count_array[simp]:
  assumes "A \<noteq> {}"
  assumes lg: "(profile_a A pa)"
  shows "win_count_imp_code pa a = win_count (pa_to_pr pa) a"
  using assms order_trans[OF win_count_imp_code.refine win_count_imp_array_correct,
      of A]
  by (auto simp: refine_rel_defs)


lemma win_count_array_code_correct: 
  assumes "A \<noteq> {}"
  assumes lg: "(profile_a A pa)"
  shows "win_count (pa_to_pr pa) a = win_count_imp_code pa a"
  using assms by (metis lg win_count_array)


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