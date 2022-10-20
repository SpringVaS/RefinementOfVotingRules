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
  assumes "A \<noteq>{}"
  shows "(plurality_r A, plurality A) \<in> (br pa_to_pr (profile_a A)) \<rightarrow> 
    Id"
  apply (refine_rcg)
  using assms apply (auto simp add: 
    refine_rel_defs) 
  done

type_synonym 'a Electoral_Module_Ref_T = "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> 'a Result_Ref nres"

definition initmap :: "'a set \<Rightarrow> 'a \<rightharpoonup> nat" where
  "initmap A = (SOME m. (\<forall>a\<in>A. ((m a) = Some (0::nat))))"



definition computewcforcands :: "'a set \<Rightarrow> 'a Profile_Array \<Rightarrow> ('a \<rightharpoonup> nat) nres" where
  "computewcforcands A p \<equiv> do {               
    (i, wcmap) \<leftarrow> WHILET (\<lambda>(i, _). i < array_length p) (\<lambda>(i, wcmap). do {
      ASSERT (i < array_length p);
      let ballot = (p[[i]]);
      let winner = (ballot[[0]]);
      let wcmap = (if (wcmap winner = None) then wcmap (winner \<mapsto> 0)
           else wcmap (winner \<mapsto> (the (wcmap winner) + 1)));
      let i = i + 1;
     RETURN (i, wcmap)
    })(0, Map.empty);
    RETURN wcmap
  }"

lemma wcmap_correc : assumes "profile_a A p"
  shows "computewcforcands A p \<le> SPEC (\<lambda> m. \<forall> a \<in> A. (the (m a)) = win_count_imp_code p a)"
  unfolding computewcforcands_def initmap_def
  apply (intro WHILET_rule[where R="measure (\<lambda>(i,_). (array_length p) - i)"] refine_vcg)
  apply auto
  oops (* ambitious goal *)

end