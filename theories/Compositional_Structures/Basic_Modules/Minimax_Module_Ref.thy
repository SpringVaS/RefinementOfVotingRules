(*  File:       Minimax_Module_Ref.thy
    Copyright   2023 Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Minimax Module\<close>

theory Minimax_Module_Ref
  imports "Component_Types/Elimination_Module_Ref"
     "Verified_Voting_Rule_Construction.Minimax_Module"
begin

text \<open>
  This is the Minimax module used by the Minimax voting rule. The Minimax rule
  elects the alternatives with the highest Minimax score. The module implemented
  herein only rejects the alternatives not elected by the voting rule, and defers
  the alternatives that would be elected by the full voting rule.
\<close>

subsection \<open>Definition\<close>

definition minimax_score_ref :: "'a::{default, heap, hashable} Evaluation_Function_Ref" where
  "minimax_score_ref x A p = do {
    ASSERT (finite A \<and> card A > 1);
    let Amx = op_set_copy A;
    Amx <- mop_set_delete x Amx;
    pcal <- pre_compute_scores (\<lambda> y A p. prefer_count_monadic_imp p x y) Amx p;
    mms <- scoremin Amx pcal;
    RETURN mms
}"

(* Min {prefer_count_l p x y | y . y \<in> A - {x}}*)
definition minimax_ref :: "'a::{default, heap, hashable} Electoral_Module_Ref" where
  "minimax_ref A p = do {
    ASSERT (finite A);
    if (card A \<le> 1) then do {let Ac = op_set_copy A; RETURN ({},{},Ac)} else do{
    scores \<leftarrow> (pre_compute_scores minimax_score_ref A p);
    max_eliminator_ref scores A p }
  }"

sepref_definition minimax_score_sep is "uncurry2 minimax_score_ref"
  :: "id_assn\<^sup>k *\<^sub>a (hs.assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding minimax_score_ref_def  pre_compute_scores_def scoremin_def
  hm.fold_custom_empty hs.fold_custom_empty  
  apply sepref_dbg_keep
  done

declare minimax_score_sep.refine[sepref_fr_rules]

sepref_definition minimax_sep is "uncurry minimax_ref"
  :: "(hs.assn id_assn)\<^sup>k *\<^sub>a (profile_impl_assn id_assn)\<^sup>k 
   \<rightarrow>\<^sub>a (result_impl_assn id_assn)"
  unfolding minimax_ref_def  max_eliminator_ref_def 
    less_eliminator_ref_def  
    elimination_module_ref_def[abs_def] eliminate_def[abs_def]
    pre_compute_scores_def 
  scoremax_def[abs_def] op_set_is_empty_def[symmetric] hm.fold_custom_empty 
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "FOREACH _ _ rewrite_HOLE" hs.fold_custom_empty)
  apply (rewrite in "RETURN (_, _, rewrite_HOLE)" hs.fold_custom_empty) +
  apply (rewrite in "RETURN (_, rewrite_HOLE, _)" hs.fold_custom_empty) +
  apply (rewrite in "RETURN ( rewrite_HOLE, _, _)" hs.fold_custom_empty)+ 
  apply sepref_dbg_keep
  done



export_code clist convert_list_to_hash_set minimax_sep in Scala_imp


lemma minimax_score_ref_correct:
  fixes A:: "'a::{default, heap, hashable} set"
  fixes pl:: "'a::{default, heap, hashable} Profile_List" and pr:: "'a::{default, heap, hashable} Profile"
  assumes 
    fina: "finite A" and nempa: "card A > 1"
    and profrel: "(pl, pr) \<in> profile_rel"
    and profprop: "profile A pr"
  shows "\<forall> x \<in> A. minimax_score_ref x A pl \<le> SPEC (\<lambda> sc. sc = (minimax_score x A pr))"
  unfolding minimax_score_ref_def minimax_score.simps op_set_copy_def
proof clarify
  fix x :: 'a
  assume xiA: "x \<in> A"
  show " ASSERT (finite A \<and> 1 < card A) \<bind>
         (\<lambda>_. let Amx = A
               in mop_set_delete x Amx \<bind>
                  (\<lambda>Amx. pre_compute_scores (\<lambda>y A p. prefer_count_monadic_imp p x y) Amx pl \<bind>
                          (\<lambda>pcal. scoremin Amx pcal \<bind> RETURN)))
         \<le> SPEC (\<lambda>sc. sc = Min {(prefer_count pr x y)| y. (y \<in> A - {x})})"
  proof (refine_vcg compute_scores_correct[where efn="(\<lambda> y A p. prefer_count p x y)"] 
        prefer_count_monadic_imp_correct assms)
    show "finite (A - {x})" using fina by simp
    next
    show "\<forall>a\<in>A - {x}. prefer_count_monadic_imp pl x a \<le> SPEC (\<lambda>score. score = prefer_count pr x a)"
      using prefer_count_monadic_imp_correct profrel by auto
    next
    show "\<And>xa. finite A \<and> 1 < card A \<Longrightarrow>
          xa = scores_map (\<lambda>y A p. prefer_count p x y) (A - {x}) pr \<Longrightarrow>
          scoremin (A - {x}) xa
          \<le> SPEC (\<lambda>xa. RETURN xa
                        \<le> SPEC (\<lambda>sc. sc =  Min {(prefer_count pr x y)| y. (y \<in> A - {x})}))"
    proof (clarify, rename_tac sm)
      fix sm:: "'a Scores_Map"
      assume op: "1 < card A"
      from op xiA have neq: "\<not> (A \<subseteq> {x})"
        by (metis empty_iff is_singletonI is_singleton_altdef nat_less_le subset_singleton_iff) 
      show "scoremin (A - {x}) (scores_map (\<lambda>y A p. prefer_count p x y) (A - {x}) pr)
          \<le> SPEC (\<lambda>xa. RETURN xa
                        \<le> SPEC (\<lambda>sc. sc =  Min {(prefer_count pr x y)| y. (y \<in> A - {x})}))"
        by (refine_vcg scoremin_correct op, auto simp add: fina neq) 
    qed
  qed
qed

lemma elimset_sub:
  shows "elimination_set e t r A p \<subseteq> A" 
  unfolding elimination_set.simps
  by simp

lemma minimax_ref_correct:          
  shows "(uncurry minimax_ref, uncurry (RETURN oo minimax)) \<in> 
  ([\<lambda> (A, pl). finite_profile A                         
            pl]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>ballot_rel\<rangle>list_rel)
   \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)"
proof (unfold minimax_ref_def, 
    intro frefI nres_relI, auto simp del: max_eliminator.simps, (rename_tac A pl pr) )
  fix A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profp: "profile A pr"
  assume cardm1: " card A \<le> Suc 0"
  from this fina show "({}, {}, A) = max_eliminator minimax_score A pr"
    unfolding max_eliminator.simps elimination_module.simps less_eliminator.simps 
  proof (cases "card A = 0")
    case True
    from this show "({}, {}, A) = (if (elimination_set minimax_score 
      (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr \<noteq> A)
     then ({},
           elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr,
           A -
           elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr)
     else ({}, {}, A))"
      by (simp add: fina)
  next 
    case False
    from this cardm1 fina have c1: "card A = 1"
      by linarith  
    show "({}, {}, A) =
    (if elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr \<noteq> A
     then ({},
           elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr,
           A -
           elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr)
     else ({}, {}, A))" (*using card_1_singletonE[where A = A]*)
    proof (cases "elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr
     = A")
      case True
      then show ?thesis by simp
    next
      case nin: False
      from this c1 have elimsetemp: 
        "elimination_set minimax_score (Max {minimax_score x A pr | x. (x \<in> A)}) (<) A pr = {}"
        using elimset_sub[where A = A]
        using card_1_singletonE by blast
      from nin show ?thesis unfolding elimsetemp by simp
    qed
  qed
next
   fix A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume prel: " (pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profp: "profile A pr"
  assume cardg1: "\<not> card A \<le> Suc 0"
  from this have op: "card A > 1" by simp
  show " pre_compute_scores minimax_score_ref A pl \<bind> (\<lambda>scores. max_eliminator_ref scores A pl)
       \<le> RETURN (max_eliminator minimax_score A pr)" unfolding SPEC_eq_is_RETURN(2)[symmetric]
    by (refine_vcg  compute_scores_correct max_eliminator_ref_correct_pc
         fina op prel profp minimax_score_ref_correct)
qed

lemmas minimax_sep_correct_aux = minimax_sep.refine[FCOMP minimax_ref_correct]
                                             
lemma  minimax_sep_correct[sepref_fr_rules]:
  shows "(uncurry minimax_sep, uncurry (RETURN \<circ>\<circ> minimax))
    \<in> elec_mod_seprel nat_assn"
  using minimax_sep_correct_aux set_rel_id hr_comp_Id2 unfolding ballot_assn_def
  by simp

  

end
