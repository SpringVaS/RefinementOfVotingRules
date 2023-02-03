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





locale seqcomp_impl =
  fixes m_ref :: "nat Electoral_Module_Ref"
  fixes m_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  fixes n_ref :: "nat Electoral_Module_Ref"
  fixes n_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    m_impl: "(uncurry m_impl, uncurry m_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"  
    and
    n_impl: "(uncurry n_impl, uncurry n_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "seqcomp_impl m_ref m_impl n_ref n_impl" by unfold_locales

interpretation m_sel: set_select_imp m_ref m_impl 
  using m_impl by (unfold_locales, simp)

interpretation n_sel:  set_select_imp n_ref n_impl 
  using n_impl by (unfold_locales, simp)

(*sepref_register "m_ref" :: "nat Electoral_Module_Ref"
sepref_register "n_ref" :: "nat Electoral_Module_Ref"

declare m_impl [sepref_fr_rules]
declare n_impl [sepref_fr_rules]*)

sepref_register "(elect_monadic m_ref)"

declare local.m_sel.elect_sep.refine [sepref_fr_rules]

schematic_goal seqcomp_imp:
  "(uncurry ?c, (uncurry (sequential_composition_mon m_ref n_ref))) 
    \<in> alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_mon_def  defer_monadic_def reject_monadic_def
  by sepref

concrete_definition (in -) sequential_composition_sep uses seqcomp_impl.seqcomp_imp
  prepare_code_thms (in -) sequential_composition_sep_def
lemmas seqt_imp_refine = sequential_composition_sep.refine[OF this_loc]




thm sequential_composition_sep_def


end 


abbreviation sequence_sep
     (infix "\<triangleright>sep" 50) where
  "m \<triangleright>sep n \<equiv> sequential_composition_sep m n"




end