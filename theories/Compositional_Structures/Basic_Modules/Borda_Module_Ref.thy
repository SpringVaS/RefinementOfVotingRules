(*  File:       Borda_Module_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Borda_Module_Ref
  imports "Verified_Voting_Rule_Construction.Borda_Module"
           "Component_Types/Elimination_Module_Ref"
begin

definition borda_score_mon :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "borda_score_mon x A p =
    sum_impl (prefer_count_monadic_imp p x) A"

fun borda_score_l :: "'a  \<Rightarrow> 'a set \<Rightarrow> 'a Profile_List \<Rightarrow> nat" where
  "borda_score_l x A p = (\<Sum> y \<in> A. (prefer_count_l p x y))"

lemma borda_score_l_eq:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
    and profl: "profile_l A pl"
  shows "borda_score_l x A pl = borda_score x A pr"
  unfolding borda_score_l.simps borda_score.simps
  using profrel 
    prefer_count_l_eq
  by (metis) 

definition borda_score_opt_mon :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "borda_score_opt_mon a A p =
     nfoldli p (\<lambda>_.True) (\<lambda> x ac. 
        do {
         ra \<leftarrow> index_mon x a;
         let bordac = length x - ra;
         RETURN  (ac + bordac) 
    }) (0::nat)"

sepref_definition opt_bsc is "uncurry2 borda_score_opt_mon"
  :: "nat_assn\<^sup>k *\<^sub>a (hs.assn nat_assn)\<^sup>k *\<^sub>a (profile_impl_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding borda_score_opt_mon_def
  by sepref

definition borda_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "borda_ref A pl \<equiv> do {
   scores \<leftarrow> (pre_compute_scores borda_score_mon A pl);
   max_eliminator_ref scores A pl
}"

definition borda_ref_opt :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "borda_ref_opt A pl \<equiv> do {
   scores \<leftarrow> (pre_compute_scores borda_score_opt_mon A pl);
   max_eliminator_ref scores A pl
}"


lemma borda_score_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
  shows "\<forall> a \<in> A. borda_score_mon a A pl \<le> SPEC (\<lambda> sc. sc = (borda_score a A pr))"
  unfolding borda_score_mon_def borda_score.simps
  by (safe, refine_vcg fina sum_impl_correct prefer_count_monadic_imp_correct profrel)

lemma borda_score_opt_refine:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" 
  assumes 
    fina: "finite A"
    and profl: "profile_l A pl"
  shows "\<forall> a \<in> A. borda_score_opt_mon a A pl  \<le> SPEC (\<lambda> sc. sc = (borda_score_l a A pl))"
proof (unfold  borda_score_opt_mon_def, safe)
  fix a :: 'a 
  assume aA: "a \<in> A"
  show "nfoldli pl (\<lambda>_. True)
          (\<lambda>x ac. index_mon x a \<bind> (\<lambda>ra. let bordac = length x - ra in RETURN (ac + bordac))) 0
         \<le> SPEC (\<lambda>sc. sc = borda_score_l a A pl)"
    apply (refine_vcg index_mon_correct nfoldli_rule[where I = "\<lambda> p1 p2 x. 
    (x = borda_score_l a A p1)"])
    subgoal by auto
    unfolding  rank_l.simps profile_l_def 
      well_formed_pl_def losimp  apply (auto simp del: borda_score_l.simps) 
  proof -
    fix x :: "'a Preference_List"
    fix l1 l2 :: "'a Profile_List"
    assume xpl: "pl = l1 @ x # l2"
    from xpl have idxx: "\<exists> i < length pl. x = pl!i"
      apply (rule_tac x="length l1" in exI) by auto
    from idxx have lox: "set x = A"
      using profl unfolding profile_l_def well_formed_pl_def losimp by auto
    from idxx have disx: "distinct x"
      using profl unfolding profile_l_def well_formed_pl_def by auto
    from lox disx fina have lengtheq: "length x = card A"
      using distinct_card by fastforce
    have validc: "(length x - index x a) = borda_score_l a A ([x])"
      using aA disx unfolding lox[symmetric]
    proof (induction "x" arbitrary: a)
      case Nil
      then show ?case by auto
    next
      case ih: (Cons newa x)
      show ?case
      proof (cases "a = newa")
        case aeqna: True
        from aeqna ih(3) have "borda_score_l a (set (newa # x)) [newa # x] = length (newa # x)"
          apply clarsimp
          using distinct_card by blast 
        from this aeqna show ?thesis
          by (simp) 
      next
        case aneqna: False
        then have nseq: "length (newa # x) - index (newa # x) a = length (x) - index (x) a"
          by auto
        from aneqna have "borda_score_l a (set (newa # x)) [newa # x] =
                        borda_score_l a (set (x)) [x]" apply auto
          by (smt (verit, del_insts) List.finite_set ab_semigroup_add_class.add.commute add.right_neutral add_le_cancel_right bot_nat_0.not_eq_extremum distinct.simps(2) ih.prems(2) less_or_eq_imp_le linorder_not_le plus_1_eq_Suc sum.cong sum.insert)
        from this nseq ih.IH ih.prems(1) ih.prems(2) show ?thesis
          by (metis aneqna distinct.simps(2) set_ConsD) 
      qed        
    qed
    have "\<forall> b \<in> A. prefer_count_l (l1 @ [x]) a b = prefer_count_l (l1) a b  + prefer_count_l ([x]) a b"
      by auto
    from this have "borda_score_l a A (l1 @ [x]) = borda_score_l a A (l1) + borda_score_l a A ([x])"
      apply (auto simp del: prefer_count_l.simps)
      using sum.distrib by blast
    from this show " borda_score_l a A l1 + (length x - index x a) = borda_score_l a A (l1 @ [x])"
      unfolding validc by simp
  qed
qed

lemma borda_score_opt_correct:
    fixes A:: "'a::{default, heap, hashable} set"
 fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and profrel: "(pl, pr) \<in> profile_rel"
    and profl: "profile A pr"
  shows "\<forall> a \<in> A. borda_score_opt_mon a A pl  \<le> SPEC (\<lambda> sc. sc = (borda_score a A pr))"
using  borda_score_opt_refine assms borda_score_l_eq profile_ref
  by (metis)


lemma borda_ref_correct:          
  shows "(uncurry borda_ref, uncurry (RETURN oo borda)) \<in> 
  [\<lambda> (A, _). finite A]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (intro frefI nres_relI, clarsimp simp del: max_eliminator.simps, rename_tac A pl pr)
  fix A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  show "borda_ref A pl \<le> RETURN (max_eliminator borda_score A pr)"
    unfolding borda_ref_def RETURN_SPEC_conv
    by (refine_vcg borda_score_correct max_eliminator_ref_correct_default fina prel)
qed

definition pre_compute_borda_scores :: "'a set
   \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Scores_Map nres" 
  where "pre_compute_borda_scores A pl \<equiv> 
  if (op_set_is_empty A) then RETURN Map.empty else
  do {
   zeromap:: 'a Scores_Map  \<leftarrow> init_map A;
  nfoldli pl (\<lambda>_. True) 
    (\<lambda>ballot map. 
       nfoldli ballot (\<lambda>_. True) 
        (\<lambda>a map. do { ASSERT (op_map_contains_key a map);
      let scx = the (op_map_lookup a map);
        RETURN (op_map_update a (scx + (length ballot - index ballot a)) map)}) map)
     (zeromap)}"

lemma borda_ref_opt_correct:          
  shows "(uncurry borda_ref_opt, uncurry (RETURN oo borda)) \<in> 
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
proof (intro frefI nres_relI, clarsimp simp del: max_eliminator.simps, rename_tac A pl pr)
  fix A:: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profp: "profile A pr"
  show "borda_ref_opt A pl \<le> RETURN (max_eliminator borda_score A pr)"  unfolding borda_ref_opt_def RETURN_SPEC_conv
   by (refine_vcg borda_score_opt_correct max_eliminator_ref_correct_default fina profp prel)
qed

sepref_definition borda_elim_sep_opt is
  "uncurry borda_ref_opt":: 
    "(alts_set_impl_assn nat_assn)\<^sup>k *\<^sub>a (profile_impl_assn nat_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn nat_assn)"
  unfolding borda_ref_opt_def  max_eliminator_ref_def borda_score_opt_mon_def sum_impl_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] 
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hm.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "RETURN ({}, {}, rewrite_HOLE)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ({}, rewrite_HOLE, _)" hs.fold_custom_empty) 
  apply (rewrite in "RETURN ( rewrite_HOLE, _, _)" hs.fold_custom_empty) 
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (rewrite_HOLE, _, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, rewrite_HOLE, rej) else RETURN ({}, rej, def))" hs.fold_custom_empty)
  apply (rewrite in "_ \<bind> (\<lambda>(rej, def). if def = {} then RETURN (_, _, rej) else RETURN (rewrite_HOLE, rej, def))" hs.fold_custom_empty)
  apply sepref_dbg_keep
  done

lemma  borda_elim_sep_opt_correct:
  shows "(uncurry borda_elim_sep_opt, uncurry (RETURN \<circ>\<circ> borda))
    \<in> [\<lambda>(a, b).
           finite_profile
            a b]\<^sub>a (alts_set_impl_assn nat_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn nat_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn nat_assn"
  using borda_elim_sep_opt.refine[FCOMP borda_ref_opt_correct, THEN hfrefD] apply (intro hfrefI)
  using set_rel_id hr_comp_Id2 by auto

                      
declare borda_elim_sep_opt_correct [sepref_fr_rules]



end