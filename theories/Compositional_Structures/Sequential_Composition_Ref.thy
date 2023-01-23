theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        "Verified_Voting_Rule_Construction.Sequential_Composition"
begin

definition custom_mon_set_uniond :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set nres" where
  "custom_mon_set_uniond A B \<equiv> do {
  FOREACH B
     (\<lambda> x (union). RETURN (insert x union)) A
  }"

lemma custom_mon_set_union_correct:
  fixes A :: "'a set"
  assumes fina: "finite A"
   fixes B :: "'a set"
  assumes finb: "finite B"
  shows "custom_mon_set_uniond A B \<le> SPEC (\<lambda> union. union = A \<union> B)"
  unfolding custom_mon_set_uniond_def
  apply (refine_vcg FOREACH_rule[where I = "\<lambda> it u. u = A \<union> (B-it)"])
  by (auto simp add: fina finb)

lemma hs_union_aref: 
  fixes A :: " ('a \<times> 'b) set"
  shows "((\<union>), op_set_union) \<in> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel"
  unfolding op_set_union_def
  apply (refine_vcg)
  by (auto simp add: set_rel_def)
  

sepref_definition hs_uniondf is 
  "uncurry custom_mon_set_uniond" :: "alts_set_impl_assn\<^sup>d *\<^sub>a alts_set_impl_assn\<^sup>k 
  \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding custom_mon_set_uniond_def
  by sepref


definition sequential_composition_mon :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Electoral_Module_Ref" where
"sequential_composition_mon m n A p = do {
      new_A <- (defer_monadic m) A p;
      new_p <- limit_profile_l A p;  

      electmA  <- (elect_monadic m) A p;
      electnA' <- (elect_monadic n) new_A new_p;
      
      rejectmA  <- (reject_monadic m) A p;
      rejectnA' <- (reject_monadic n) new_A new_p;

      defernA'  <- (defer_monadic n) new_A new_p;

      RETURN (electmA \<union> electnA',rejectmA \<union> rejectnA',defernA')}"
                      
(*
    
                  (elect m A p) \<union> (elect n new_A new_p),
                  (reject m A p) \<union> (reject n new_A new_p),
                  defer n new_A new_p))"

*)


definition seqt :: 
   "nat Electoral_Module_Ref \<Rightarrow> nat Electoral_Module_Ref" where
"seqt m A p = do {
     electmA <- (elect_monadic m) A p;
     RETURN(electmA,{},{})
}"

locale seqcomp_impl =
  fixes m :: "nat Electoral_Module_Ref"
  fixes m_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  fixes n :: "nat Electoral_Module_Ref"
  fixes n_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    m_impl: "(uncurry m_impl, uncurry m)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"  
    and
    n_impl: "(uncurry n_impl, uncurry n)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "seqcomp_impl m m_impl n n_impl" by unfold_locales


sepref_register "m" :: "nat Electoral_Module_Ref"
sepref_register "n" :: "nat Electoral_Module_Ref"

declare m_impl [sepref_fr_rules]
declare n_impl [sepref_fr_rules]


sepref_definition seqt_imp is
  "(uncurry (sequential_composition_mon m n))" 
    :: "alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_mon_def elect_monadic_def defer_monadic_def reject_monadic_def
    limit_profile_l.simps limit_monadic_def
  apply (rewrite in "WHILEIT _ _ _ (_,\<hole>)" arl.fold_custom_empty )
  apply (rewrite in "nfoldli _ _ _ \<hole>" HOL_list.fold_custom_empty )
  by sepref

thm seqt_imp_def

end



end