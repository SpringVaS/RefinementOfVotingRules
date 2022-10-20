theory Plurality_Module_Ref
  imports 
        "Component_Types/Electoral_Module_Ref"
        "Verified_Voting_Rule_Construction.Plurality_Module"
begin


fun plurality_r :: "'a Electoral_Module_Ref" where
  "plurality_r A p =
    ({a \<in> A. \<forall>x \<in> A. win_count_imp_code p x \<le> win_count_imp_code p a},
     {a \<in> A. \<exists>x \<in> A. win_count_imp_code p x > win_count_imp_code p a},
     {})"

lemma datarefplurality:
  shows "(plurality_r, plurality) \<in> Id \<rightarrow> (br pa_to_pr (profile_a A)) \<rightarrow> 
    Id"
  apply (refine_rcg)
  apply (auto simp add: 
    refine_rel_defs win_count_array) 
  done
  

lemma plurality_r_sound:
  shows "electoral_module_r plurality_r"
  using datarefplurality plurality_sound
  unfolding electoral_module_def electoral_module_r_def
  apply safe
  oops


type_synonym 'a Electoral_Module_Ref_T = "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> 'a Result_Ref nres"

definition initmap :: "'a set \<Rightarrow> 'a \<rightharpoonup> nat" where
  "initmap A = (SOME m. (\<forall>a\<in>A. ((m a) = Some (0::nat))))"

definition "computewcinvar A p \<equiv> \<lambda>(i, wcmap).
  \<forall>a\<in>A. the (wcmap a) = win_count_imp_code (array_shrink p i) a"

definition computewcforcands :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> ('a \<rightharpoonup> nat) nres" where
  "computewcforcands A p \<equiv> do {
    let wcmap = initmap A;               
    (i, wcmap) \<leftarrow> WHILET (\<lambda>(i, _). i < array_length p) (\<lambda>(i, wcmap). do {
      ASSERT (i < array_length p);
      let ballot = (p[[i]]);
      let wcmap = (if (array_length ballot > 0) then (
        wcmap ((ballot[[0]]) \<mapsto> (the (wcmap (ballot[[0]]))) + 1)) else wcmap);
      let i = i + 1;
     RETURN (i, wcmap)
    })(0, Map.empty);
    RETURN wcmap
  }"

lemma wcmap_correc : assumes "profile_a A p"
  shows "computewcforcands A p \<le> SPEC (\<lambda> m. \<forall> a \<in> A. (the (m a)) = win_count_imp_code p a)"
  unfolding computewcforcands_def initmap_def
  apply (intro WHILET_rule[where I="(computewcinvar A p)" 
        and R="measure (\<lambda>(i,_). (array_length p) - i)"] refine_vcg)
  unfolding computewcinvar_def win_count_imp_code_def
  apply auto 
  oops (* ambitious goal *)

end