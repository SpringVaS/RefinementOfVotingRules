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

lemma nfwcc: "nofail (wc_fold p a)"
  unfolding wc_fold_def 
  apply (induction p rule: rev_induct, simp)
   apply simp
  by (simp add: pw_bind_nofail)
   

definition compute_scores :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a \<rightharpoonup> nat) nres" 
  where "compute_scores A p \<equiv> do {
  (scores) \<leftarrow> FOREACH A 
    (\<lambda>x m. do {
      scx \<leftarrow> (wc_fold p x);
      RETURN (m(x\<mapsto>scx))
  }) (Map.empty);
  RETURN (scores)
}"

lemma 
  fixes pl:: "'a Profile_List" and A:: "'a set"
  assumes "finite A"
  shows "(compute_scores, ((\<lambda> A p. RETURN ([a \<mapsto> (win_count pr a)]))))
    \<in> Id \<rightarrow> br pl_to_pr_\<alpha> (profile_l A) \<rightarrow> \<langle>Id\<rangle>nres_rel "
  oops
  

sepref_register compute_scores

sepref_definition compute_scores_sep is
  "uncurry (compute_scores)" :: "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k
    \<rightarrow>\<^sub>a (hm.assn (nat_assn) (nat_assn))" 
  unfolding compute_scores_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (sepref_dbg_keep)
  done


definition (*compute_threshold :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> nat nres" 
  where*) "compute_threshold A scores \<equiv> do {
    
    RETURN 0  
}"

definition plurality_r :: "'a Electoral_Module_Ref" where
  "plurality_r A p \<equiv> do {
    (scores) \<leftarrow> compute_scores A p; 
    (e,r,d) \<leftarrow> FOREACH A 
    (\<lambda>x (e,r,d). do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      (if (scx = 1) then 
          RETURN (insert x e,r,d) 
      else 
          RETURN(e, insert x r,d))
    }) ({},{},{}); 
    RETURN (e,r,d)
  } "

sepref_register plurality_r

sepref_definition plurality_sepref is
  "uncurry plurality_r":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_r_def[abs_def] 
    compute_scores_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)+
  apply sepref_dbg_keep
  done

lemma datarefplurality:
  shows "\<forall> A. (plurality_r, (\<lambda> A p. SPEC (\<lambda> elecres. elecres = plurality A p))) \<in> 
    Id \<rightarrow> (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding plurality_r_def FOREACH_def
  compute_scores_def[abs_def]
  apply (refine_vcg wc_fold_correct)
  apply (auto simp add: 
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