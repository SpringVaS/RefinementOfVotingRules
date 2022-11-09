theory Profile_Array
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
    Counting_Functions_Code
    Collections.Diff_Array
    Collections.ArrayHashMap
begin

notation array_get ("_[[_]]" [900,0] 1000)

type_synonym 'a Preference_Array = "'a array"

type_synonym 'a Profile_Array = "('a Preference_Array) array"

definition well_formed_prefa :: "'a Preference_Array \<Rightarrow> bool" where
  "well_formed_prefa pa = ((array_length pa > 0) \<and> distinct (list_of_array pa))"

lemma wfa_imp_wfl[simp]: "well_formed_prefa pa \<longrightarrow> well_formed_pl (list_of_array pa)"
  unfolding well_formed_prefa_def well_formed_pl_def
  by (simp add: array_length_list)



definition array_index_of_mon :: "'a Preference_Array \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "array_index_of_mon ballot a \<equiv> do {
   (i, found) \<leftarrow> WHILEIT (index_mon_inv (list_of_array ballot) a) 
  (\<lambda>(i, found). (i < (array_length ballot) \<and> \<not>found)) 
      (\<lambda>(i,_). do {
      ASSERT (i < (array_length ballot));
      let (c) = (ballot[[i]]);
      if (a = c) then
        RETURN (i,True)
      else
        RETURN (i+1,False)
    })(0, False);
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
  apply (refine_rcg index_mon_correct)
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


lemma profile_a_l: assumes "profile_a A pa"
  shows "profile_l A (pa_to_pl pa)"
  using assms profile_a_def by (metis)

lemma profile_a_rel: assumes "profile_a A pa"
  shows "profile A (pa_to_pr pa)"
  using profile_data_refine
  by (metis assms brI pa_to_pr_def profile_a_def)

lemma finite_profile_a_rel:
  shows "\<forall>A pa. finite_profile_a A pa \<longrightarrow> finite_profile A (pa_to_pr pa)"
  using profile_data_refine
  by (metis brI pa_to_pr_def profile_a_def)


lemma array_refine_length[simp]:
  assumes "(pa, pl) \<in> br pa_to_pl (profile_a A)"
  shows "length (list_of_array pa) = length pl"
  using assms in_br_conv array_length_list
     by (metis length_map pa_to_pl_def) 



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
  shows "win_count_imp_array pa a \<le> \<Down>Id (win_count_ pl a)"
  unfolding win_count_imp_array_def win_count_imp'_def winsr_imp'_def
  apply (refine_rcg)
  apply (refine_dref_type)
  using assms by (safe, simp_all)+
  

lemma a_l_r_step: "(pl_to_pr_\<alpha> \<circ> pa_to_pl) = pa_to_pr"
  by (simp add: fun_comp_eq_conv pa_to_pr_def)
  
lemma win_count_imp_array_correct:
  assumes "(pa, pr) \<in> br pa_to_pr (profile_a A)" and aA: "a \<in> A"
  shows "win_count_imp_array pa a \<le> SPEC (\<lambda>ac. ac = win_count pr a)"
  using assms ref_two_step[OF win_count_imp_array_refine win_count_imp'_correct]
  by (metis in_br_conv pa_to_pr_def profile_a_l refine_IdD)

schematic_goal wc_code_refine_aux: "RETURN ?wc_code \<le> win_count_imp_array p a"
  unfolding win_count_imp_array_def
  by (refine_transfer)

concrete_definition win_count_imp_code for p a uses wc_code_refine_aux

thm win_count_imp_code_def

lemma win_count_array:
  assumes lg: "(profile_a A pa)" and aA: "a \<in> A"
  shows "win_count_imp_code pa a = win_count (pa_to_pr pa) a"
  using assms order_trans[OF win_count_imp_code.refine win_count_imp_array_correct,
      of pa "(pa_to_pr pa)"]
  by (auto simp: refine_rel_defs)


lemma win_count_array_code_correct: 
  assumes lg: "(profile_a A pa)" and aA: "a \<in> A"
  shows "win_count (pa_to_pr pa) a = win_count_imp_code pa a"
  using assms by (metis lg win_count_array)

end