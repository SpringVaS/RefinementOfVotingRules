theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        Verified_Voting_Rule_Construction.Sequential_Composition
        Refine_Imperative_HOL.Sepref
begin

definition seq_opt :: "'a Electoral_Module \<Rightarrow> 
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
  fixes m n :: "'a Electoral_Module"
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
  

abbreviation sequence_opt
     (infix "\<triangleright>opt" 50) where
  "m \<triangleright>opt n \<equiv> seq_opt m n"

end