theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        Verified_Voting_Rule_Construction.Sequential_Composition
        Refine_Imperative_HOL.Sepref
begin


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


abbreviation sequence_ref ::
  "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref"
     (infix "\<triangleright>r" 50) where
  "m \<triangleright>r n \<equiv> sequential_composition_mon m n"

lemma sequence_ref_correct:
  shows "(sequence_ref, sequence) \<in> \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>em_rel"
  apply (refine_vcg)
  unfolding em_rel_def sequential_composition_mon_def
  apply (auto)
  apply (refine_vcg)
  using  limitp_correct  elect_monadic_correct reject_monadic_correct defer_monadic_correct

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





schematic_goal seqt_imp:
  "(uncurry ?c, (uncurry (sequential_composition_mon m n))) 
    \<in> alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_mon_def elect_monadic_def defer_monadic_def reject_monadic_def
    limit_profile_l.simps limit_monadic_def
  apply (rewrite in "WHILEIT _ _ _ (_,\<hole>)" arl.fold_custom_empty )
  apply (rewrite in "nfoldli _ _ _ \<hole>" HOL_list.fold_custom_empty )
  by sepref


concrete_definition (in -) seqt_imp uses seqcomp_impl.seqt_imp
  prepare_code_thms (in -) seqt_imp_def
lemmas seqt_imp_refine = seqt_imp.refine[OF this_loc]

term "\<langle>\<langle>A\<rangle>em_rel,\<langle>\<langle>A\<rangle>em_rel, \<langle>A\<rangle>em_rel\<rangle>fun_rel\<rangle>fun_rel"


thm seqt_imp_def


end 

thm "seqt_imp_def"
thm "seqt_imp.refine"

end