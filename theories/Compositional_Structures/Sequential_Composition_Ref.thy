theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        Verified_Voting_Rule_Construction.Sequential_Composition
        Refine_Imperative_HOL.Sepref
begin

definition seq_opt :: "'a :: {default, heap, hashable} Electoral_Module \<Rightarrow> 
  'a Electoral_Module
  \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 
  'a Result nres" 
  where "seq_opt m n A p \<equiv> do {
  let (e, r, d) = m A p;
  ASSERT (finite d);
  let newA = d;
  ASSERT(newA \<subseteq> A);
  ASSERT (finite_profile A p);
  let newp = limit_profile newA p;
  ASSERT (finite_profile newA newp);
  let (ne, nr, nd) = n newA newp;
   RETURN (e \<union> ne, r \<union> nr, nd) }"

lemma seq_opt_correct: 
  fixes m n :: "'a :: {default, heap, hashable} Electoral_Module"
  assumes em_m: "electoral_module m" and
  em_n: "electoral_module n"
shows "(uncurry (seq_opt m n), uncurry (RETURN oo (sequential_composition' m n))) \<in>
  [\<lambda> (A, p). finite_profile A p]\<^sub>f (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel) \<rightarrow> 
  \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding comp_apply seq_opt_def
  apply (intro frefI) apply clarsimp
  using assms apply (refine_vcg)
    apply auto
  subgoal unfolding electoral_module_def
    by (metis def_presv_fin_prof em_m snd_conv)
  apply (metis defer_in_alts snd_conv subsetD) 
  by (metis def_presv_fin_prof limit_profile.elims snd_conv)

locale Seqcomp_Impl =
  fixes m n :: "'a :: {default, heap, hashable} Electoral_Module"
  fixes m_sep n_sep :: "'a :: {default, heap, hashable} Electoral_Module_Sep"
  assumes em_m: "electoral_module m" and
  em_n: "electoral_module n"
  assumes m_sep_correct: "(uncurry m_sep, uncurry (RETURN oo m)) \<in> elec_mod_seprel id_assn"
  assumes n_sep_correct: "(uncurry n_sep, uncurry (RETURN oo n)) \<in> elec_mod_seprel id_assn"
begin

  lemma this_loc: "Seqcomp_Impl m n m_sep n_sep" by unfold_locales

  sepref_register m
  sepref_register n

  declare m_sep_correct[sepref_fr_rules]
  declare n_sep_correct[sepref_fr_rules]

schematic_goal seqcomp_sepimpl:
  "(uncurry ?f2, uncurry (seq_opt m n)) \<in> elec_mod_seprel id_assn"
  unfolding seq_opt_def
  by sepref

concrete_definition (in -) seqcomp_sep_uc uses Seqcomp_Impl.seqcomp_sepimpl
  prepare_code_thms (in -) seqcomp_sep_uc_def
lemmas  seqcomp_sep_ucp_refine = seqcomp_sep_uc.refine[OF this_loc]

schematic_goal seqcomp_sepcurried:
 "?curried = curry (seqcomp_sep_uc m_sep n_sep)" by auto

concrete_definition (in -) seqcomp_sep uses Seqcomp_Impl.seqcomp_sepcurried


definition "seqcomp_mn \<equiv> (m \<triangleright> n)"
definition "seqcomp_mn_sep \<equiv> (seqcomp_sep m_sep n_sep)"

theorem seqcomp_sep_correct:
  shows "(uncurry (seqcomp_sep m_sep n_sep), uncurry (RETURN oo (m \<triangleright> n))) 
\<in> elec_mod_seprel id_assn"
    using seqcomp_sep_ucp_refine[FCOMP seq_opt_correct, OF em_m em_n]
    unfolding seq_comp_alt_eq seqcomp_sep_def
    by (simp)

end

abbreviation comp4 (infixl "oooo" 55) where "f oooo g \<equiv> \<lambda>x. f ooo (g x)"

abbreviation sequence_opt
     (infix "\<triangleright>sep" 50) where
  "m \<triangleright>sep n \<equiv> seqcomp_sep m n"


end