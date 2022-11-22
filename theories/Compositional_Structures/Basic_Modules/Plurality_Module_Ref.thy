theory Plurality_Module_Ref
  imports 
        "Verified_Voting_Rule_Construction.Plurality_Module"
        "Component_Types/Social_Choice_Types/Counting_Functions_Code"
        "Component_Types/Electoral_Module_Ref"
begin

sepref_register wc_fold

sepref_definition win_count_imp_sep is
  "uncurry wc_fold" :: "(list_assn (array_assn nat_assn))\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn)"
  unfolding wc_fold_def[abs_def]  short_circuit_conv 
  apply sepref_dbg_keep 
  done

thm win_count_imp_sep.code

definition (*compute_score :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a, nat nres) map" 
  where *)"compute_scores A p \<equiv> do {
  m \<leftarrow> FOREACHc A (\<lambda> _. True) 
    (\<lambda>x l. do {
      scx \<leftarrow> (wc_fold p x);
      RETURN (l(x\<mapsto>scx))
  }) (Map.empty);
  RETURN m
}"


sepref_register compute_scores

sepref_definition compute_score_sep is
  "uncurry (compute_scores)" :: "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k
    \<rightarrow>\<^sub>a (hm.assn (nat_assn) (nat_assn))" 
  unfolding compute_scores_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACHc _ _ _ \<hole>" hm.fold_custom_empty)
  apply (sepref_dbg_keep)
  done

definition plurality_r :: "'a Electoral_Module_Ref" where
  "plurality_r A p \<equiv> do {
    (m) \<leftarrow> compute_scores A p ;
    let alts = dom m;
    RETURN ({}, {}, {})
  } "

sepref_register plurality_r

sepref_definition plurality_sepref is
  "uncurry plurality_r":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_r_def[abs_def] wc_fold_def[abs_def]
  apply sepref_dbg_keep

lemma datarefplurality:
  fixes A :: "'a set"
  shows "(plurality_r A, plurality A) \<in> (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> Id"
  unfolding plurality_r.simps plurality.simps
  apply (refine_vcg wc_fold_refine_spec)
  apply (auto simp only: 
    refine_rel_defs)
  
  done

lemma plurality_ref_eq:
  fixes A :: "'a set" and pa :: "'a Profile_Array"
  assumes "(profile_a A pa)"
  shows "plurality_r A pa = plurality A (pa_to_pr pa)"
  using assms datarefplurality em_onA
  by blast 

lemma plurality_r_sound:
  shows "electoral_module_r plurality_r" 
  unfolding electoral_module_r_def using plurality_sound plurality_ref_eq
  by (metis electoral_module_def profile_a_rel)

lemma plurality_r_electing2: "\<forall> A pa.
                              (A \<noteq> {} \<and> finite_profile_a A pa) \<longrightarrow>
                                elect_r (plurality_r A pa) \<noteq> {}"
using plurality_electing2 plurality_ref_eq profile_a_rel
  by metis

theorem plurality_r_electing[simp]: "electing plurality"
  oops (* Reformulate properties like electing for refined types. Discussion needed*)

(* For further lemmas, Profile definitions have to be transeferred to profile Array

lemma plurality_inv_mono2: "\<forall> A p q a.
                              (a \<in> elect plurality A p \<and> lifted A p q a) \<longrightarrow>
                                (elect plurality A q = elect plurality A p \<or>
                                    elect plurality A q = {a})"*)

(* --------  *)
  section \<open>Further Refinement: Experiments\<close>


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

  oops (* ambitious goal *)

end