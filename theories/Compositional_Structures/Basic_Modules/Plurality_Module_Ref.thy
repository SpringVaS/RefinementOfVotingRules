theory Plurality_Module_Ref
  imports 
        "Verified_Voting_Rule_Construction.Plurality_Module"
        "Component_Types/Social_Choice_Types/Counting_Functions_Code"
        "Component_Types/Electoral_Module_Ref"
    HOL.Finite_Set
begin


definition compute_scores :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> ('a \<rightharpoonup> nat) nres" 
  where "compute_scores A p \<equiv>
  FOREACH A 
    (\<lambda>x m. do {
      scx \<leftarrow> (wc_fold p x);
      RETURN (m(x\<mapsto>scx))
  }) (Map.empty)"


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




definition "pluralityparam A scores th \<equiv>  
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

definition plurality_init:: "'a Electoral_Module_Ref" where 
"plurality_init A p \<equiv> do {
  scores <- compute_scores A p;
  pluralityparam A scores (scoremax A scores)
}"

context voting_session
begin

definition "max_comp_spec_plurality \<equiv> 
(SPEC (\<lambda>max. (\<forall>a \<in> A. win_count pr a \<le> max) \<and> ((\<exists>e \<in> A. max = win_count pr e) \<or> max = 0)))"

lemma datarefplurality:
  shows "(pluralityparam A ((\<lambda>a. Some (win_count pr a))|`A) (max_comp_spec_plurality), 
(SPEC (\<lambda> elecres. elecres = plurality A pr))) \<in>
   \<langle>Id\<rangle>nres_rel"
  unfolding pluralityparam_def max_comp_spec_plurality_def
  apply (refine_vcg FOREACH_rule[where I = "
  (\<lambda>it (e,r,d). (\<forall>elem \<in> e.  \<forall>a \<in> A. win_count pr a \<le> win_count pr elem)
  \<and> (\<forall>elem \<in> r.  \<exists>a \<in> A. win_count pr a > win_count pr elem)
  \<and> d = {} \<and>
  e \<union> r = (A - it))"] )
  apply (auto simp add: fina
    simp del: win_count.simps )
  using nat_less_le apply blast
  apply (rename_tac e r alt)
  using leD apply blast
   apply (metis UnCI leD)+
  done

definition "precompute_map_spec = SPEC (\<lambda> map. map = (\<lambda>a. Some (win_count pr a))|`A)"

(* TODO: cleanup in locale *)
lemma compute_scores_correct:
  shows "(compute_scores A pl, (precompute_map_spec))
    \<in> \<langle>Id\<rangle>nres_rel"
  unfolding compute_scores_def precompute_map_spec_def
  apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it r. r = (\<lambda> e. Some (win_count (pr) e)) |` (A - it))"])
  apply (auto simp add: fina simp del: win_count.simps)
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
  from profrel have prel: "(pl, pr) \<in> profile_rel" using profile_type_ref by auto
  from profrel have "profile_l A pl" using profile_prop_list by auto 
  from prel this have "wc_fold pl x \<le> SPEC(\<lambda> scx. scx = win_count pr x)"
    using wc_fold_correct by auto
  from this mapupdeq show " wc_fold pl x
       \<le> SPEC (\<lambda>scx. ((\<lambda>e. Some (win_count pr e)) |` (A - it))(x \<mapsto> scx) =
                      (\<lambda>e. Some (win_count pr e)) |` (A - (it - {x})))"
    using SPEC_cons_rule it_step_insert_iff restrict_map_insert
    by presburger 
qed 





theorem plurality_refine:
  shows "(plurality_init, 
((\<lambda> A p. pluralityparam A ((\<lambda>a. Some (win_count p a))|`A) (max_comp_spec_plurality A p))))
     \<in> \<langle>Id\<rangle>set_rel \<rightarrow> ((profile_on_A_rel A) \<rightarrow> \<langle>Id\<rangle>nres_rel)"
  oops

end 

sepref_definition plurality_sepreftest is
  "uncurry plurality_init":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_init_def[abs_def] pluralityparam_def[abs_def] 
    compute_scores_def[abs_def] wc_fold_def[abs_def] scoremax_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)+
  apply sepref_dbg_keep
  done

end
