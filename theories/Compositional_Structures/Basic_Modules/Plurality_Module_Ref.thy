(*  File:       Plurality_Module_Ref.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

theory Plurality_Module_Ref
  imports 
          "Verified_Voting_Rule_Construction.Plurality_Rule"
           "Component_Types/Elimination_Module_Ref"
begin

section \<open>Refined Plurality Module\<close>

subsection \<open>Definition\<close>

definition plur_score_ref :: "'a Evaluation_Function_Ref" where
  "plur_score_ref x A p = (wc_fold p x)"

definition plurality_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "plurality_ref A pl \<equiv> do {
   scores \<leftarrow> (pre_compute_scores plur_score_ref A pl);
   max_eliminator_ref scores A pl
}"

lemma plur_score_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a Profile_List" and pr:: "'a Profile"
  assumes 
    fina: "finite A"
    and prel: "(pl, pr) \<in> profile_rel"
    and profp: "profile A pr"
  shows "\<forall> a \<in> A. plur_score_ref a A pl \<le> SPEC (\<lambda> sc. sc = (plur_score a A pr))"
  unfolding plur_score_ref_def plur_score.simps
proof safe
  fix a :: 'a
  from prel profp have profl: "profile_l A pl" using profile_ref by auto 
  show "wc_fold pl a \<le> SPEC (\<lambda>sc. sc = win_count pr a) "
    by (refine_vcg fina prel profl wc_fold_correct)
qed

text \<open>Optimized Map Compuation\<close>

definition pre_compute_plur_scores :: "'a set
   \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Scores_Map nres" 
  where "pre_compute_plur_scores A pl \<equiv> 
  if (A = {}) then RETURN Map.empty else
  do {
   zeromap:: 'a Scores_Map \<leftarrow> init_map A;
  nfoldli pl (\<lambda>_. True) 
    (\<lambda>ballot map. 
     do{ 
      ASSERT (length ballot > 0);
      let top = ballot!0;
      ASSERT (op_map_contains_key top map);
      let scx = the (op_map_lookup top map);
        RETURN (op_map_update top (scx + 1) map)})
     (zeromap)}"


sepref_definition plurmap_sep is "uncurry pre_compute_plur_scores" ::
  "(alts_set_impl_assn nat_assn)\<^sup>k *\<^sub>a (profile_impl_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a (hm.assn nat_assn nat_assn)"
  unfolding pre_compute_plur_scores_def init_map_def op_set_is_empty_def[symmetric] 
     hm.fold_custom_empty
  apply sepref_dbg_keep
  done

declare plurmap_sep.refine [sepref_fr_rules]

definition plurality_ref_opt :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "plurality_ref_opt A pl \<equiv> do {
   scores \<leftarrow> (pre_compute_plur_scores A pl);
   max_eliminator_ref scores A pl
}"


subsection \<open>Refinement Lemmas\<close>


lemma plurality_map_correct:
  fixes A :: "'a set" and
        pr :: "'a Profile" and
        pl :: "'a Profile_List"
  assumes fina: "finite A" and
        prel : "(pl, pr) \<in> profile_rel" and
        profl: "profile_l A pl"
  shows "(pre_compute_plur_scores A pl) \<le> SPEC (\<lambda> map. map =(scores_map plur_score A pr))"
  unfolding pre_compute_plur_scores_def scores_map_def plur_score.simps
  apply (refine_vcg empty_map fina prel profl
          nfoldli_rule[where I = "\<lambda> p1 p2 si. ( \<forall> a \<in> A. ((si a) = Some (win_count_l p1 a)))
          \<and>  (\<forall> a . (a \<notin> A \<longrightarrow> si a = None))"] )
     apply (auto)
proof -
  fix xa :: "'a Preference_List"
  fix xb :: 'a
  fix l1 l2 :: "'a Profile_List"
  assume "xb \<in> A"
  from this have nempa: "A \<noteq> {}" by auto
  assume "pl = l1 @ [] # l2"
  from this profl show "False"
    unfolding profile_l_def well_formed_pl_def losimp using nempa
    by (metis in_set_conv_decomp in_set_conv_nth list.set(1))
next
  fix xa :: "'a Preference_List"
  fix l1 l2 :: "'a Profile_List"
  fix sigma :: "'a Scores_Map"
  assume nempxa: "xa \<noteq> []"
  assume "pl = l1 @ xa # l2"
  from this have "set xa = A"
    using profl  unfolding profile_l_def well_formed_pl_def losimp
    by (metis in_set_conv_decomp in_set_conv_nth)
  from this nempxa have innit: "xa ! 0 \<in> A" by auto
  assume somev: 
    "\<forall>a\<in>A. sigma a = Some (fold (\<lambda>x ac. if x \<noteq> [] \<and> x ! 0 = a then ac + 1 else ac) l1 0)"
  assume "sigma (xa ! 0) = None"
  from this somev innit show False
    by simp
next
  fix xa :: 'a
  assume "xa \<in> A"
  from this have nempa: "A \<noteq> {}" by auto
  fix sigma ::  "('a \<Rightarrow> nat option)"
  assume valuemap: 
    "\<forall>a\<in>A. sigma a = Some (fold (\<lambda>x ac. if x \<noteq> [] \<and> x ! 0 = a then ac + 1 else ac) pl 0)"
  assume outnone: " \<forall>a. a \<notin> A \<longrightarrow> sigma a = None"
  from valuemap this have wclmap: "(sigma) = (\<lambda>a . Some (win_count_l pl a))|`A"
    unfolding restrict_map_def win_count_l.simps by auto
  from prel profl have "(pl, pr) \<in> profile_on_A_rel A"
    by (simp add: in_br_conv list_rel_eq_listrel listrel_iff_nth profile_l_def relAPP_def
        relcomp.intros)
  from this wclmap have wcmap: "(sigma) = (\<lambda>a . Some (win_count pr a))|`A"
    using  win_count_l_correct[THEN fun_relD,THEN fun_relD, where x1 = pl and x'1 = pr and A2 = A]
    by fastforce    
  assume neg: "sigma \<noteq> (\<lambda>a. Some (card {i. i < length pr \<and> above (pr ! i) a = {a}})) |` A"
  from wcmap this show False by auto
qed
  
lemma plurality_ref_correct:
  shows "(uncurry plurality_ref, uncurry (RETURN oo plurality_mod)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (intro frefI nres_relI,  clarsimp simp del:  plurality_mod.simps plur_score.simps,
     unfold plurality_ref_def plurality_mod.simps
     RETURN_SPEC_conv, rename_tac A pl pr)
  note max_eliminator_ref_correct_default[where A = A and efn_ref = plur_score_ref and
       efn = plur_score]
  fix A :: "'a::{default, heap, hashable} set"
  fix pr :: "'a Profile"
  fix pl :: "'a Profile_List"
  assume fina: "finite A"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume profp: "profile A pr"
  show " pre_compute_scores plur_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> SPEC (\<lambda>x. x = max_eliminator plur_score A pr)"
    using max_eliminator_ref_correct_default plur_score_correct fina prel profp
    by metis   
qed

lemma plurality_ref_opt_correct:
  shows "(uncurry plurality_ref_opt, uncurry (RETURN oo plurality_mod)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (intro frefI nres_relI,  clarsimp simp del:  plurality_mod.simps plur_score.simps,
     unfold plurality_ref_opt_def plurality_mod.simps
     RETURN_SPEC_conv, rename_tac A pl pr)
  fix A :: "'a::{default, heap, hashable} set"
  fix pr :: "'a Profile"
  fix pl :: "'a Profile_List"
  assume fina: "finite A"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume profp: "profile A pr"
  from this have profl: "profile_l A pl" using prel profile_ref by blast
  show "pre_compute_plur_scores A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> SPEC (\<lambda>x. x = max_eliminator plur_score A pr)"
    by (refine_vcg max_eliminator_ref_correct_pc plurality_map_correct fina prel profl)
qed

subsection \<open>Imperative HOL Synthesis Using Sepref\<close>

sepref_definition plurality_elim_sep is
  "uncurry plurality_ref":: 
    "(hs.assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding plurality_ref_def  max_eliminator_ref_def plur_score_ref_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def[abs_def] scoremax_def[abs_def] wc_fold_def[abs_def] 
    short_circuit_conv hm.fold_custom_empty
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "RETURN (_, _, rewrite_HOLE)" hs.fold_custom_empty)+
  apply (rewrite in "RETURN (_, rewrite_HOLE, _)" hs.fold_custom_empty)+
  apply (rewrite in "RETURN (rewrite_HOLE, _, _)" hs.fold_custom_empty)+ 
  apply sepref_dbg_keep
  done

sepref_definition plurality_elim_sep_opt is
  "uncurry plurality_ref_opt":: 
    "(alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding plurality_ref_opt_def  max_eliminator_ref_def plur_score_ref_def
    less_eliminator_ref_def  elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    scoremax_def[abs_def] op_set_is_empty_def[symmetric]
   pre_compute_plur_scores_def init_map_def op_set_is_empty_def[symmetric] 
     hm.fold_custom_empty 
  apply (rewrite in "RETURN (_, _, rewrite_HOLE)" hs.fold_custom_empty)
  apply (rewrite in "RETURN (_, rewrite_HOLE, _)" hs.fold_custom_empty)+
  apply (rewrite in "RETURN (rewrite_HOLE, _, _)" hs.fold_custom_empty)+
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)+
  by sepref

subsection \<open>Overall Correctness Lemma for Imperative HOL function\<close>

lemma plurality_elim_sep_correct:
  shows "(uncurry plurality_elim_sep_opt, uncurry (RETURN \<circ>\<circ> plurality_mod))
        \<in> elec_mod_seprel id_assn"
  unfolding ballot_assn_def
  using plurality_elim_sep_opt.refine[FCOMP plurality_ref_opt_correct]
  set_rel_id hr_comp_Id2 by simp

declare plurality_elim_sep_correct [sepref_fr_rules]

end