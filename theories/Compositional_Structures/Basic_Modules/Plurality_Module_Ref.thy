theory Plurality_Module_Ref
  imports 
        "Verified_Voting_Rule_Construction.Plurality_Module"
        "Component_Types/Social_Choice_Types/Counting_Functions_Code"
        "Component_Types/Electoral_Module_Ref"
    HOL.Finite_Set
begin


definition plurality_fe:: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres"
  where
  "plurality_fe A p = do {
    let maxwc = (Finite_Set.fold max (0::nat) ((win_count p)`A)  );
    (e,r,d) \<leftarrow> FOREACH A 
    (\<lambda>x (e,r,d). do {
      let scx = win_count p x;
      (if (scx = maxwc) then 
          RETURN (insert x e,r,d) 
      else 
          RETURN(e, insert x r,d))
    }) ({},{},{}); 
    RETURN (e,r,d)}" 

lemma 
  assumes "finite A"
  shows "plurality_fe A p \<le> SPEC (\<lambda>res. res = plurality A p)"
  unfolding plurality_fe_def 
  apply (refine_vcg assms FOREACH_rule[where I="\<lambda> it (e,r,d). 
              (alt \<in> e \<longrightarrow> (\<forall>x \<in> A. win_count p x \<le> win_count p alt)) \<and>
              (alt \<in> r \<longrightarrow> (\<exists>x \<in> A. win_count p x > win_count p alt)) \<and>
              d = {} \<and>
              (e \<union> r \<union> d) = (A-it)"])
  oops
 
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
  where "compute_scores A p \<equiv>
  FOREACH A 
    (\<lambda>x m. do {
      scx \<leftarrow> (wc_fold p x);
      RETURN (m(x\<mapsto>scx))
  }) (Map.empty)"

term "(range [1::nat\<mapsto>1::nat])"

find_theorems ran

definition "scoremax A scores \<equiv> do {
  FOREACH (A)
    (\<lambda>x max. do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      (if (scx > max) then 
          RETURN (scx) 
      else 
          RETURN(max))
    }) (0::nat)
}"

sepref_register scoremax

sepref_definition tryitmap 
  is "uncurry scoremax" :: "((hs.assn nat_assn)\<^sup>k *\<^sub>a (hm.assn (nat_assn) (nat_assn))\<^sup>k \<rightarrow>\<^sub>a (nat_assn))"
  unfolding scoremax_def[abs_def]
  apply sepref_dbg_keep
apply sepref_dbg_trans_keep
          apply sepref_dbg_trans_step_keep
subgoal premises p
  oops

lemma compute_scores_correct:
  fixes pl:: "'a Profile_List" and A:: "'a set"
  assumes "finite A" and "profile_l A pl" and "(pl, pr) \<in> profile_rel"
  shows "(compute_scores A pl, ((\<lambda>A p. RETURN ((\<lambda>a. Some (win_count p a))|`A)) A pr))
    \<in> \<langle>Id\<rangle>nres_rel"
  unfolding compute_scores_def
  using assms apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it r. r = (\<lambda> e. Some (win_count (pr) e)) |` (A - it))"])
  apply (auto simp del: win_count.simps)
proof -
  fix x:: 'a
  fix it:: "'a set"
  assume xit: "x \<in> it"
  assume itA: "it \<subseteq> A"
  from xit itA have xiA: "x \<in> A" by fastforce
  from xit itA have wcr: "((\<lambda>e. Some (win_count pr e)) |` (A - it))(x \<mapsto> win_count pr x) =
                      (\<lambda>e. Some (win_count pr e)) |` (A - (it - {x}))"
      using it_step_insert_iff restrict_map_insert
      by metis
  from this have mapupdeq: "(\<lambda>scx. ((\<lambda>e. Some (win_count pr e)) |` (A - it))(x \<mapsto> scx) =
                   (\<lambda>e. Some (win_count pr e)) |` (A - (it - {x})))
      = (\<lambda> wc. wc = win_count pr x)"
    by (metis map_upd_eqD1)
  have "wc_fold pl x \<le> SPEC(\<lambda> scx. scx = win_count pr x)"
    using assms(3) assms(2) wc_fold_correct by metis
  from this mapupdeq show " wc_fold pl x
       \<le> SPEC (\<lambda>scx. ((\<lambda>e. Some (win_count pr e)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>e. Some (win_count pr e)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 


lemma scoremax_correct:
  fixes f:: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat"
  assumes "finite A"
  shows "scoremax A ((\<lambda>a. Some (f p a))|`A) \<le> SPEC (\<lambda>max. (\<forall>a \<in> A. f p a \<le> max) \<and> ((\<exists>e \<in> A. max = f p e) \<or> max = 0))"
  unfolding scoremax_def
  apply (intro FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). f p a \<le> max) \<and> ((\<exists>e \<in> (A - it). max = f p e) \<or> max = 0))"] refine_vcg)
  using assms apply auto
  apply (metis Diff_iff leD nle_le order_trans)
   apply (metis DiffI order_less_imp_le)
  by (metis DiffI nat_neq_iff)
  
  

  oops
sepref_register compute_scores

sepref_definition compute_scores_sep is
  "uncurry (compute_scores)" :: "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k
    \<rightarrow>\<^sub>a (hm.assn (nat_assn) (nat_assn))" 
  unfolding compute_scores_def[abs_def] wc_fold_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  by sepref

definition (*compute_threshold :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> nat nres" 
  where*) "compute_threshold A scores \<equiv> do {
    
    RETURN 0  
}"

definition "plurint A scores th \<equiv>  
    FOREACH (A)
    (\<lambda>x (e,r,d). do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      sel <- th;
      (if (scx = sel) then 
          RETURN (insert x e,r,d) 
      else 
          RETURN(e, insert x r,d))
    }) ({},{},{})"

definition plurality_full :: "'a Electoral_Module_Ref" where
  "plurality_full A p \<equiv> do {
    scores \<leftarrow> compute_scores A p;
    max \<leftarrow> scoremax A scores;
    FOREACH (A)
    (\<lambda>x (e,r,d). do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      (if (scx = max) then 
          RETURN (insert x e,r,d) 
      else 
          RETURN(e, insert x r,d))
    }) ({},{},{})
  } "

sepref_register plurality_full

sepref_definition plurality_sepref is
  "uncurry plurality_full":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_full_def[abs_def] 
    compute_scores_def[abs_def] wc_fold_def[abs_def] scoremax_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)+
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)+
  apply sepref_dbg_keep
  done

find_theorems Max

lemma datarefplurality:
  fixes pr:: "'a Profile" and A:: "'a set"
  assumes "finite A" and "A \<noteq> {}"
  shows "(plurint A ((\<lambda>a. Some (win_count pr a))|`A) 
(SPEC (\<lambda>max. (\<forall>a \<in> A. win_count pr a \<le> max) \<and> ((\<exists>e \<in> A. max = win_count pr e) \<or> max = 0))), 
(\<lambda>A p. SPEC (\<lambda> elecres. elecres = plurality A p)) A pr ) \<in>
   \<langle>Id\<rangle>nres_rel"
  unfolding plurint_def
  apply (refine_rcg)
  apply (refine_vcg FOREACH_rule[where I = "
  (\<lambda>it (e,r,d). (\<forall>elem \<in> e.  \<forall>a \<in> A. win_count pr a \<le> win_count pr elem)
  \<and> (\<forall>elem \<in> r.  \<exists>a \<in> A. win_count pr a > win_count pr elem)
  \<and> d = {} \<and>
  e \<union> r = (A - it))"] )
  using assms(1) apply (auto simp add:
    simp del: win_count.simps )
  using nat_less_le apply blast
  apply (rename_tac e r alt)
  using leD apply blast
   apply (metis UnCI leD)+
  done


end