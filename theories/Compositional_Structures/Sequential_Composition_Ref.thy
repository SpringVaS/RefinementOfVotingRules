theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        Verified_Voting_Rule_Construction.Sequential_Composition
        Refine_Imperative_HOL.Sepref
begin

definition sequential_composition_ref_test :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Electoral_Module_Ref" where
"sequential_composition_ref_test m n A p = do {
      (mel,mrej,mdef) <- m A p;
 
      let newA = mdef;
      new_p <- limit_profile_l newA p;  
    
      (nel,nrej,ndef) <- n newA new_p;
      
      RETURN (mel \<union> nel, mrej \<union> nrej, ndef)
}"

locale seqcomp_impl =
  fixes m_ref :: "nat Electoral_Module_Ref"
  fixes m_sep :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  fixes n_ref :: "nat Electoral_Module_Ref"
  fixes n_sep :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    m_impl: "(uncurry m_sep, uncurry m_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"  
    and
    n_impl: "(uncurry n_sep, uncurry n_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "seqcomp_impl m_ref m_sep n_ref n_sep" by unfold_locales

sepref_register "m_ref" :: "nat Electoral_Module_Ref"
declare m_impl [sepref_fr_rules]

sepref_register "n_ref" :: "nat Electoral_Module_Ref"
declare n_impl [sepref_fr_rules]

schematic_goal sequence_impl: "(uncurry ?seq,  uncurry (sequential_composition_ref_test m_ref n_ref))
  \<in> alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_ref_test_def defer_monadic_def elect_monadic_def reject_monadic_def
  apply sepref_dbg_keep
  done

concrete_definition (in -) sequential_composition_sep uses seqcomp_impl.sequence_impl
  prepare_code_thms (in -) sequential_composition_sep_def
lemmas seqt_imp_refine = sequential_composition_sep.refine[OF this_loc]

end 

locale sequence_refine = seqcomp_impl +
  fixes m :: "nat Electoral_Module"  and
  n :: "nat Electoral_Module"
assumes module_m: "electoral_module m"
  and module_n: "electoral_module n"
assumes m_ref_correct: "(uncurry m_ref, uncurry (RETURN oo m)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel\<rangle>nres_rel)" and
n_ref_correct: "(uncurry n_ref, uncurry (RETURN oo n)) \<in> 
  ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel\<rangle>nres_rel)"

begin

lemma seq_comp_correct:
  shows "(uncurry (sequential_composition_ref_test m_ref n_ref),
  uncurry (RETURN oo (sequential_composition m n)))
  \<in>   ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel\<rangle>nres_rel)"
  unfolding sequential_composition_ref_test_def
proof (intro frefI nres_relI,clarsimp simp del: limit_profile.simps, rename_tac A pl pr)
  fix A :: "nat set"
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profa: "profile A pr"
  note mrc = m_ref_correct[THEN frefD, THEN nres_relD]
  note nrc = n_ref_correct[THEN frefD, THEN nres_relD]
  let ?new_A = "defer m A pr"
  let ?new_p = "limit_profile ?new_A pr"
  have fin_def: "finite ?new_A"
    using def_presv_fin_prof fina profa module_m
    by metis
  have prof_def_lim:
    "profile (defer m A pr) (limit_profile (defer m A pr) pr)"
    using def_presv_fin_prof fina profa module_m
    by metis
  from fina prel profa have limitref: "limit_profile_l ?new_A pl \<le> 
    \<Down> profile_rel (SPEC (\<lambda> lim. lim = limit_profile (defer m A pr) pr))"
    unfolding SPEC_eq_is_RETURN(2) using limitp_correct[THEN frefD, THEN nres_relD, where
         y1 = "((defer m A pr), pr)" and x1 = "((defer m A pr), pl)"]
    unfolding comp_apply
    by (simp add: fin_def) 
  have "sequential_composition m n A pr =
      (let (mel,mrej,mdef) = m A pr in
      
      let newA = (mdef) in
      let new_p = limit_profile newA pr in
    
      let (nel,nrej,ndef) = n newA new_p in
      
      (mel \<union> nel, mrej \<union> nrej, ndef))"
    unfolding sequential_composition.simps apply auto
    by (metis (no_types, lifting) case_prod_beta')
    
  from prel fina profa prof_def_lim fin_def  have  "  m_ref A pl \<bind>
       (\<lambda>(mel, mrej, mdef).
           limit_profile_l mdef pl \<bind>
           (\<lambda>new_p. n_ref mdef new_p \<bind> (\<lambda>(nel, nrej, ndef). RETURN (mel \<union> nel, mrej \<union> nrej, ndef))))
       \<le> RETURN
           (let (mel,mrej,mdef) = m A pr in
      
      let newA = (mdef) in
      let new_p = limit_profile newA pr in
    
      let (nel,nrej,ndef) = n newA new_p in
      
      (mel \<union> nel, mrej \<union> nrej, ndef))"
    apply (refine_vcg prel fina profa prof_def_lim fin_def 
        limitp_correct[THEN frefD, THEN nres_relD] mrc nrc)
   using limitp_correct[THEN frefD, THEN nres_relD] mrc nrc
    sorry
  show "  m_ref A pl \<bind>
       (\<lambda>(mel, mrej, mdef).
           limit_profile_l mdef pl \<bind>
           (\<lambda>new_p. n_ref mdef new_p \<bind> (\<lambda>(nel, nrej, ndef). RETURN (mel \<union> nel, mrej \<union> nrej, ndef))))
       \<le> RETURN
           (let new_A = defer m A pr; new_p = limit_profile new_A pr
            in (elect m A pr \<union> elect n new_A new_p, reject m A pr \<union> reject n new_A new_p,
                defer n new_A new_p))"
    apply (refine_vcg prel fina profa prof_def_lim fin_def 
        limitp_correct[THEN frefD, THEN nres_relD] mrc nrc)
    sorry
qed

lemmas sequence_correct = sequential_composition_sep.refine[FCOMP seq_comp_correct]

end


abbreviation sequence_sep
     (infix "\<triangleright>sep" 50) where
  "m \<triangleright>sep n \<equiv> sequential_composition_sep m n"




end