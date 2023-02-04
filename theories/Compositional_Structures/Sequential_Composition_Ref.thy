theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        Verified_Voting_Rule_Construction.Sequential_Composition
        Refine_Imperative_HOL.Sepref
begin



definition sequential_composition_ref :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Electoral_Module_Ref" where
"sequential_composition_ref m n A p = do {
      new_A <- (defer_monadic m) A p;
      new_p <- limit_profile_l new_A p;  
                        
      electmA  <- (elect_monadic m) A p;
      electnA' <- (elect_monadic n) new_A new_p;
      
      rejectmA  <- (reject_monadic m) A p;
      rejectnA' <- (reject_monadic n) new_A new_p;

      defernA'  <- (defer_monadic n) new_A new_p;

      RETURN (electmA \<union> electnA',rejectmA \<union> rejectnA',defernA')
}"


definition sequential_composition_ref_test :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Electoral_Module_Ref" where
"sequential_composition_ref_test m n A p = do {
      mresulte <- m A p;
      mresultr <- m A p;
      
      m'result <- m A p;
      
      let newA = (defer_r (m'result));
      new_p <- limit_profile_l newA p;  
      
      nresulte <- n newA new_p;
      nresultr <- n newA new_p;
      nresultd <- n newA new_p;
      
      RETURN (elect_r mresulte \<union> elect_r nresulte, reject_r mresultr \<union> reject_r nresultr
      , defer_r nresultd)
}"

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
  shows "(uncurry (sequential_composition_ref m_ref n_ref),
  uncurry (RETURN oo (sequential_composition m n)))
  \<in>   ([\<lambda> (A, pl). finite_profile A
            pl]\<^sub>f (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r profile_rel)
   \<rightarrow> \<langle>\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel\<rangle>nres_rel)"
  unfolding sequential_composition_ref_def
proof (intro frefI nres_relI,clarsimp simp del: limit_profile.simps, rename_tac A pl pr,
    unfold SPEC_eq_is_RETURN(2)[symmetric], refine_vcg)
  fix A :: "nat set"
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume prel: "(pl, pr) \<in> profile_rel"
  assume fina: "finite A"
  assume profa: "profile A pr"
  note mrc = m_ref_correct[THEN frefD, THEN nres_relD]
  note drc = defer_monadic_correct[THEN frefD, THEN nres_relD]
  from fina prel profa have "defer_monadic m_ref A pl \<le> SPEC (\<lambda> dset. dset = defer m A pr)"
    unfolding SPEC_eq_is_RETURN(2) using m_ref_correct drc[where emref2 = m_ref and em2 = m and x1 = "(A, pl)"
        and y1 = "(A, pr)"]
    by auto
  let ?new_A = "defer m A pr"
  let ?new_p = "limit_profile ?new_A pr"
  have fin_def: "finite ?new_A"
    using def_presv_fin_prof fina profa module_m
    by metis
  have prof_def_lim:
    "profile (defer m A pr) (limit_profile (defer m A pr) pr)"
    using def_presv_fin_prof fina profa module_m
    by metis
  from fina prel profa have "limit_profile_l ?new_A pl \<le> 
    \<Down> profile_rel (SPEC (\<lambda> lim. lim = limit_profile (defer m A pr) pr))"
    unfolding SPEC_eq_is_RETURN(2) using limitp_correct[THEN frefD, THEN nres_relD, where  x1 = 
        "(A, pl)"
        and y1 = "(A, pr)"]
    unfolding comp_apply 
  from prel fina profa show "defer_monadic m_ref A pl
       \<le> SPEC (\<lambda>new_A.
                   limit_profile_l new_A pl \<bind>
                   (\<lambda>new_p.
                       elect_monadic m_ref A pl \<bind>
                       (\<lambda>electmA.
                           elect_monadic n_ref new_A new_p \<bind>
                           (\<lambda>electnA'.
                               reject_monadic m_ref A pl \<bind>
                               (\<lambda>rejectmA.
                                   reject_monadic n_ref new_A new_p \<bind>
                                   (\<lambda>rejectnA'.
                                       defer_monadic n_ref new_A new_p \<bind>
                                       (\<lambda>defernA'.
                                           SPEC
                                            (\<lambda>x. x = (electmA \<union> electnA', rejectmA \<union> rejectnA',
  defernA'))))))))
                   \<le> SPEC (\<lambda>x. x = (let new_A = defer m A pr; new_p = limit_profile new_A pr
                                     in (elect m A pr \<union> elect n new_A new_p,
                                         reject m A pr \<union> reject n new_A new_p, defer n new_A new_p))))"
 

end


abbreviation sequence_sep
     (infix "\<triangleright>sep" 50) where
  "m \<triangleright>sep n \<equiv> sequential_composition_sep m n"




end