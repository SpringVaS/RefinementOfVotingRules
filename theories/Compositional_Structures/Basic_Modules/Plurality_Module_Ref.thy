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

definition scoremax:: "('a \<rightharpoonup> nat) \<Rightarrow> nat nres" where "scoremax ma \<equiv> do{
 ASSERT(finite (range ma));
 FOREACH (ran ma)
  (\<lambda>x m. do {
      let s = x;
      if (s > m) then RETURN (s) else RETURN (m)
  }) (0::nat)
}"

sepref_register scoremax

sepref_definition tryitmap 
  is " scoremax" :: "((hm.assn (nat_assn) (nat_assn))\<^sup>k \<rightarrow>\<^sub>a (nat_assn))"
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
    \<in> \<langle>Id\<rangle>nres_rel "
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

definition plurality_r :: "'a Electoral_Module_Ref" where
  "plurality_r A p \<equiv> do {
    scores \<leftarrow> compute_scores A p;
    scoremax \<leftarrow> (scoremax (Map.graph scores));
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
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)+
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)+
  apply sepref_dbg_keep
  oops

lemma datarefplurality:
  shows "finite A \<longrightarrow> ((plurality_r A, (\<lambda> p. SPEC (\<lambda> elecres. elecres = plurality A p))) \<in> 
    (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> \<langle>Id\<rangle>nres_rel)"
  unfolding plurality_r_def FOREACH_def
  compute_scores_def[abs_def]
  apply (refine_vcg wc_fold_correct compute_scores_correct)
  apply (auto simp add:  
    refine_rel_defs simp del: win_count.simps )


  
  oops


end