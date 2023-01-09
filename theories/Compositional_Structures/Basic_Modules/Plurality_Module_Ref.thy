theory Plurality_Module_Ref
  imports 
        "Verified_Voting_Rule_Construction.Plurality_Module"
        "Component_Types/Social_Choice_Types/Profile_List_Monadic"
        "Component_Types/Electoral_Module_Ref"
    
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

definition pluralityparam ::
    "'a set \<Rightarrow> ('a \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> 'a Result nres" where 
"pluralityparam A scores threshold \<equiv>
    FOREACH (A)
    (\<lambda>x (e,r,d). do {
      ASSERT (x \<in> dom scores);
      let scx = the (scores x);
      let sel = threshold;
      (if (scx = sel) then 
          RETURN (insert x e,r,d) 
      else 
          RETURN(e, insert x r,d))
    }) ({},{},{})"

(* TODO: think about creating a locale like Kruskal AFP 
  where the precompute map monad can be an assumption *)
definition plurality_init:: "'a Electoral_Module_Ref" where 
"plurality_init A p \<equiv> do {
  scores <- compute_scores A p;
  threshold <- (scoremax A scores);
  pluralityparam A scores threshold
}"

sepref_definition plurality_sepref is
  "uncurry plurality_init":: 
    "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (array_assn nat_assn))\<^sup>k 
   \<rightarrow>\<^sub>a ((hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn) \<times>\<^sub>a (hs.assn nat_assn))"
  unfolding plurality_init_def[abs_def] pluralityparam_def[abs_def] 
    compute_scores_def[abs_def] wc_fold_def[abs_def] scoremax_def[abs_def] short_circuit_conv
  apply (rewrite in "FOREACH _ _ \<hole>" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ \<hole>" hs.fold_custom_empty)+
  apply sepref_dbg_keep
  done

thm plurality_sepref.refine

export_code plurality_sepref in Scala_imp

context voting_session
begin

definition "precompute_map \<equiv> (\<lambda>a. Some (win_count pr a))|`A"

definition "max_comp_plurality \<equiv> Max {win_count pr x |x. x \<in> A}"

lemma plurality_monadic_correct:
  shows "(pluralityparam A precompute_map max_comp_plurality
           ,(SPEC (\<lambda> elecres. elecres = plurality A pr))) \<in> \<langle>Id\<rangle>nres_rel "
  unfolding pluralityparam_def precompute_map_def max_comp_plurality_def
  apply (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it (e,r,d). (\<forall>elem \<in> e.  \<forall>a \<in> A. win_count pr a \<le> win_count pr elem)
          \<and> (\<forall>elem \<in> r.  \<exists>a \<in> A. win_count pr a > win_count pr elem)
          \<and> d = {} 
          \<and> e \<union> r = (A - it))"] )
  apply (clarsimp_all simp add: fina
    simp del: win_count.simps )
  subgoal by auto
  using fina score_bounded[where A= A and f=win_count]
  using fina nempa max_score_in[where A= A and f=win_count] 
  apply (rename_tac e r alt)
  using leD 
   (*apply (metis UnCI leD)+*)
  sorry


lemma compute_scores_correct:
  shows "(compute_scores A pl, SPEC (\<lambda> map. map = precompute_map)) \<in> \<langle>Id\<rangle>nres_rel"
  unfolding compute_scores_def precompute_map_def
  apply (refine_vcg FOREACH_rule[where I = 
        "(\<lambda>it r. r = (\<lambda> e. Some (win_count (pr) e))|`(A - it))"])
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


lemma scoremax_correct:
  shows "(scoremax A precompute_map, SPEC (\<lambda> th. th =  max_comp_plurality)) \<in> \<langle>nat_rel\<rangle>nres_rel"
  unfolding scoremax_def max_comp_plurality_def precompute_map_def
  apply (refine_vcg FOREACH_rule[where I = "(\<lambda>it max. (\<forall>a \<in> (A - it). win_count pr a \<le> max) 
\<and> ((\<exists>e \<in> (A - it). max = win_count pr e) \<or> max = 0))"] )
  apply (auto simp add: fina simp del: win_count.simps)
  apply (metis Diff_iff leD nle_le order_trans)
    apply (metis DiffI order_less_imp_le)
  using fina score_bounded[where A= A and p = pr and f=win_count]
  nempa nbexmax[where A= A and p = pr and f=win_count]

  sorry
  (*apply (metis antisym linorder_not_le max_comp_plurality_def)
  using fina nempa nbexmax[where A= A and p = pr and f=win_count]
  apply (simp add: finite_nat_set_iff_bounded)
  done*)

lemma parameterized_refinement: 
  "(pluralityparam, pluralityparam) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> Id \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding pluralityparam_def
  apply (refine_vcg)
  apply (auto simp add: refine_rel_defs)[3]
  apply clarsimp_all
  done


(*lemma rewritep: "((RETURN precompute_map) \<bind> 
(\<lambda> map. pluralityparam A map (scoremax A map)), 
pluralityparam A precompute_map max_comp_plurality)
  \<in> \<langle>Id\<rangle>nres_rel"
  apply clarsimp
  apply refine_vcg
proof -
  have refi: "scoremax A precompute_map \<le> \<Down> Id max_comp_spec_plurality"
    using scoremax_correct nres_relD by blast
  have "(A,A) \<in> \<langle>Id\<rangle>set_rel"
    by simp 
  show "pluralityparam A precompute_map (scoremax A precompute_map)
    \<le> \<Down> Id (pluralityparam A precompute_map max_comp_spec_plurality)"
    unfolding pluralityparam_def
    apply refine_vcg
    apply (refine_dref_type)
    apply (auto simp add: refine_rel_defs)
    using refi refine_IdD by blast
qed*)


(*lemma scores_param: "(compute_scores A pl \<bind> (\<lambda> map. pluralityparam A map 
  (scoremax A map)), pluralityparam A precompute_map max_comp_plurality)
  \<in> \<langle>Id\<rangle>nres_rel"
  using rewritep compute_scores_correct in_nres_rel_iff
  by (metis (no_types, lifting) BNF_Greatest_Fixpoint.IdD Collect_cong Id_refine 
SPEC_eq_is_RETURN(2) bind_refine conc_trans_additional(5)) *)

find_theorems bind

lemma plurality_init_refine:
  shows "(plurality_init A pl, (pluralityparam A precompute_map max_comp_plurality))
      \<in> \<langle>Id\<rangle>nres_rel"
  apply (rule nres_relI)
  apply (simp add: Id_refine)
  unfolding plurality_init_def
proof -
  have "SPEC(\<lambda> map. map =precompute_map) \<bind> (\<lambda>scores. scoremax A scores \<bind> pluralityparam A scores)
    \<le> pluralityparam A precompute_map max_comp_plurality"
    using scoremax_correct[THEN nres_relD, THEN refine_IdD]
    by (metis (no_types, lifting) Collect_cong RETURN_SPEC_conv Refine_Basic.bind_mono(1) let_to_bind_conv order_mono_setup.refl) 
  from this show "compute_scores A pl \<bind> (\<lambda>scores. scoremax A scores \<bind> pluralityparam A scores)
    \<le> pluralityparam A precompute_map max_comp_plurality"
    using compute_scores_correct[THEN nres_relD, THEN refine_IdD]
    using Refine_Basic.bind_mono(1) dual_order.trans by blast
qed 
  

(*lemmas plurality_init_refspec = plurality_init_refine[FCOMP plurality_monadic_correct]*)

theorem plurality_init_correct:
  shows "(plurality_init A pl, (SPEC (\<lambda> elecres. elecres = plurality A pr)))
     \<in> \<langle>Id\<rangle>nres_rel"
  apply (rule nres_relI)
  apply (rule refine_IdI)
  using plurality_monadic_correct[THEN nres_relD, THEN refine_IdD]
  using ref_two_step[OF plurality_init_refine[THEN nres_relD] 
plurality_monadic_correct[THEN nres_relD, THEN refine_IdD], THEN refine_IdD]
  by fastforce
  

theorem plurality_init_dataref:
  shows "(plurality_init, (\<lambda> Alts p. SPEC (\<lambda> elec. elec = (plurality) Alts p)))
     \<in> \<langle>Id\<rangle>set_rel \<rightarrow> (profile_rel) \<rightarrow> \<langle>Id\<rangle>nres_rel"

  oops

(*lemmas pluralitysep_correct= "plurality_sepref.refine[FCOMP plurality_init_dataref]"*)

end



  

end
