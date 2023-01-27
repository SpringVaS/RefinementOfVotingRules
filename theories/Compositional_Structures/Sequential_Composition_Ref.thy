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


find_theorems Id


lemma sequence_ref_correct:
  shows "(sequential_composition_mon, sequential_composition) \<in> \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>em_rel \<rightarrow> \<langle>Id\<rangle>em_rel"
  apply (refine_vcg)
  unfolding  sequential_composition_mon_def sequential_composition.simps
  apply (rename_tac m_ref m n_ref n)
proof (-)
  fix m_ref n_ref :: "'a Electoral_Module_Ref"
  fix m n :: "'a Electoral_Module"
  assume m_refine: "(m_ref, m) \<in> \<langle>Id\<rangle>em_rel"
  assume n_refine: "(n_ref, n) \<in> \<langle>Id\<rangle>em_rel"
  show "((\<lambda>A p. defer_monadic m_ref A p \<bind>
               (\<lambda>new_A.
                   limit_profile_l A p \<bind>
                   (\<lambda>new_p.
                       elect_monadic m_ref A p \<bind>
                       (\<lambda>electmA.
                           elect_monadic n_ref new_A new_p \<bind>
                           (\<lambda>electnA'.
                               reject_monadic m_ref A p \<bind>
                               (\<lambda>rejectmA.
                                   reject_monadic n_ref new_A new_p \<bind>
                                   (\<lambda>rejectnA'.
                                       defer_monadic n_ref new_A new_p \<bind>
                                       (\<lambda>defernA'.
                                           RETURN
                                            (electmA \<union> electnA', rejectmA \<union> rejectnA', defernA')))))))),
        \<lambda>A p. let new_A = defer m A p; new_p = limit_profile new_A p
               in (elect m A p \<union> elect n new_A new_p, reject m A p \<union> reject n new_A new_p,
                   defer n new_A new_p))
       \<in> \<langle>Id\<rangle>em_rel)"
  proof (unfold em_rel_def, (clarsimp simp del: limit_profile.simps), refine_vcg, rename_tac A' A pl pr)
     fix A' A :: "'a set"
     fix pl :: "'a Profile_List"
     fix pr :: "'a Profile"
     assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
     assume prel: "(pl, pr) \<in> profile_rel"
     from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
     from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
     from m_refine arel prel  have "defer_monadic m_ref A' pl \<le> SPEC (\<lambda> defset. defset = defer m A pr)"
       using defer_monadic_correct[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD,
           where x3 = m_ref and x'3 = m and x2 = A' and x'2 = A and x1 = pl and x'1 = pr]
               set_rel_id_simp comp_apply SPEC_eq_is_RETURN(2)[symmetric] refine_IdD
       by metis
       
     from arel prel m_refine n_refine show "defer_monadic m_ref A' pl
       \<le> SPEC (\<lambda>new_A.
                   limit_profile_l A' pl \<bind>
                   (\<lambda>new_p.
                       elect_monadic m_ref A' pl \<bind>
                       (\<lambda>electmA.
                           elect_monadic n_ref new_A new_p \<bind>
                           (\<lambda>electnA'.
                               reject_monadic m_ref A' pl \<bind>
                               (\<lambda>rejectmA.
                                   reject_monadic n_ref new_A new_p \<bind>
                                   (\<lambda>rejectnA'.
                                       defer_monadic n_ref new_A new_p \<bind>
                                       (\<lambda>defernA'.
                                           RETURN
                                            (electmA \<union> electnA', rejectmA \<union> rejectnA', defernA')))))))
                   \<le> SPEC (\<lambda>c. (c, let new_A = defer m A pr; new_p = limit_profile new_A pr
                                    in (elect m A pr \<union> elect n new_A new_p,
                                        reject m A pr \<union> reject n new_A new_p, defer n new_A new_p))
                                \<in> Id))"
       using limitp_correct[THEN fun_relD, THEN fun_relD, THEN nres_relD]
         elect_monadic_correct[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD]
         set_rel_id_simp comp_apply SPEC_eq_is_RETURN(2)
         reject_monadic_correct[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD]
         defer_monadic_correct[THEN fun_relD, THEN fun_relD, THEN fun_relD, THEN nres_relD]
        specify_left
       sorry
   qed
 qed

lemma refine_params:
  assumes "(m_ref, m) \<in> \<langle>Id\<rangle>em_rel" and
    "(n_ref, n) \<in> \<langle>Id\<rangle>em_rel"
  shows "(sequential_composition_mon  m_ref n_ref,  RETURN oo (m \<triangleright> n))
\<in> (elec_mod_relb Id)"
proof (refine_vcg, rename_tac A' A pl pr)
  fix A' A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  assume prel: "(pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  have "(sequential_composition_mon m_ref n_ref, m \<triangleright> n)
    \<in> {(emref, em). (emref, RETURN \<circ>\<circ> em) \<in> elec_mod_relb Id}"
    using assms sequence_ref_correct[THEN fun_relD, THEN fun_relD]
    unfolding em_rel_def by simp
  from this have "(sequential_composition_mon m_ref n_ref, RETURN oo (m \<triangleright> n)) \<in> elec_mod_relb Id"
    unfolding em_rel_def
    by simp
  from arel prel this[THEN fun_relD,THEN fun_relD, THEN nres_relD]
  show "  sequential_composition_mon m_ref n_ref A' pl
       \<le> \<Down> (\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel) ((RETURN \<circ>\<circ>\<circ> (\<triangleright>) m) n A pr)"
    by fastforce
qed


locale seqcomp_impl =
  fixes m :: "nat Electoral_Module"
  fixes m_ref :: "nat Electoral_Module_Ref"
  fixes m_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  fixes n :: "nat Electoral_Module"
  fixes n_ref :: "nat Electoral_Module_Ref"
  fixes n_impl :: "(nat, unit) hashtable
      \<Rightarrow> (nat array \<times> nat) list
         \<Rightarrow> ((nat, unit) hashtable \<times> (nat, unit) hashtable \<times> (nat, unit) hashtable) Heap"
  assumes 
    m_refine: "(m_ref, RETURN oo m) \<in> elec_mod_relb nat_rel" and
    m_impl: "(uncurry m_impl, uncurry m_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"  
    and
    n_refine: "(n_ref, RETURN oo n) \<in> elec_mod_relb nat_rel" and
    n_impl: "(uncurry n_impl, uncurry n_ref)
        \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"

begin

  lemma this_loc: "seqcomp_impl m m_ref m_impl n n_ref n_impl" by unfold_locales


sepref_register "m_ref" :: "nat Electoral_Module_Ref"
sepref_register "n_ref" :: "nat Electoral_Module_Ref"

declare m_impl [sepref_fr_rules]
declare n_impl [sepref_fr_rules]


lemmas m_correct[sepref_fr_rules] = m_impl[FCOMP m_refine]
lemmas n_correct[sepref_fr_rules] = m_impl[FCOMP m_refine]

schematic_goal seqcomp_imp:
  "(uncurry ?c, (uncurry (sequential_composition_mon m_ref n_ref))) 
    \<in> alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_mon_def elect_monadic_def defer_monadic_def reject_monadic_def
    limit_profile_l_def limit_monadic_def
  apply (rewrite in "WHILEIT _ _ _ (_,\<hole>)" arl.fold_custom_empty )
  apply (rewrite in "nfoldli _ _ _ \<hole>" HOL_list.fold_custom_empty )
  by sepref

concrete_definition (in -) sequential_composition_sep uses seqcomp_impl.seqcomp_imp
  prepare_code_thms (in -) sequential_composition_sep_def
lemmas seqt_imp_refine = sequential_composition_sep.refine[OF this_loc]

lemma tog:
  shows "(sequential_composition_mon  m_ref n_ref,  RETURN oo (m \<triangleright> n))
\<in> (elec_mod_relb Id)"
proof (refine_vcg, rename_tac A' A pl pr)
  fix A' A :: "nat set"
  fix pl :: "nat Profile_List"
  fix pr :: "nat Profile"
  assume arel: "(A', A) \<in> \<langle>nat_rel\<rangle>alt_set_rel"
  assume prel: "(pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  have "(sequential_composition_mon m_ref n_ref, m \<triangleright> n)
    \<in> {(emref, em). (emref, RETURN \<circ>\<circ> em) \<in> elec_mod_relb Id}"
    using m_refine n_refine sequence_ref_correct[THEN fun_relD, THEN fun_relD]
    unfolding em_rel_def by simp
  from this have "(sequential_composition_mon m_ref n_ref, RETURN oo (m \<triangleright> n)) \<in> elec_mod_relb Id"
    unfolding em_rel_def
    by simp
  from arel prel this[THEN fun_relD,THEN fun_relD, THEN nres_relD]
  show "   sequential_composition_mon m_ref n_ref A' pl
       \<le> \<Down> (\<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>set_rel) ((RETURN \<circ>\<circ>\<circ> (\<triangleright>) m) n A pr)"
    by fastforce
qed


lemmas seqt_imp_correct = sequential_composition_sep.refine[OF this_loc, 
    FCOMP tog]


thm sequential_composition_sep_def


end 


(*abbreviation sequence_sep
     (infix "\<triangleright>sep" 50) where
  "m \<triangleright>sep n \<equiv> sequential_composition_sep m n"*)




end