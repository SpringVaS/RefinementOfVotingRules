theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        "Verified_Voting_Rule_Construction.Sequential_Composition"
begin

definition sequential_composition_mon :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Electoral_Module_Ref" where
"sequential_composition_mon m n A p = do {
      let electm = elect_monadic m;
      let electn = elect_monadic n;
      let rejectm = reject_monadic m;
      let rejectn = reject_monadic n;
      let defm = defer_monadic m;
      let defn = defer_monadic n;
    
      new_A <- defm A p;
      new_p <- limit_profile_l new_A p;
      
      electmA <- electm A p;
      electnA' <- electn new_A new_p;
      rejectmA <- rejectm A p;
      rejectnA' <- rejectn new_A new_p;
      def <- defn new_A new_p;
 
      RETURN (rejectmA,rejectmA,electmA)}"

(*      let elec = electmA \<union> electnA';
      let rej = rejectmA \<union> rejectnA';
*)

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

(*lemma [sepref_import_param]: "(limit_profile_l,limit_profile_l)
 \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel"
  unfolding limit_profile_l.simps limit_monadic_def
  apply (auto)
proof (rename_tac A' A p)
   fix A' A :: "'a set"
  fix p :: "'a Profile_List"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from arel have aeq: "A' = A" by (simp add: alt_set_rel_def in_br_conv)
  show "(nfoldli p (\<lambda>_. True)
         (\<lambda>x np.
             WHILE\<^sub>T\<^bsup>limit_monadic_inv A' x\<^esup> (\<lambda>(i, nbal). i < length x)
              (\<lambda>(i, nbal).
                  ASSERT (i < length x) \<bind>
                  (\<lambda>_. let c = x ! i
                        in RETURN (if c \<in> A' then (i + 1, nbal @ [c]) else (i + 1, nbal))))
              (0, []) \<bind>
             (\<lambda>x. (case x of (i, x) \<Rightarrow> RETURN x) \<bind> (\<lambda>newb. RETURN (np @ [newb]))))
         [],
        nfoldli p (\<lambda>_. True)
         (\<lambda>x np.
             WHILE\<^sub>T\<^bsup>limit_monadic_inv A x\<^esup> (\<lambda>(i, nbal). i < length x)
              (\<lambda>(i, nbal).
                  ASSERT (i < length x) \<bind>
                  (\<lambda>_. let c = x ! i
                        in RETURN (if c \<in> A then (i + 1, nbal @ [c]) else (i + 1, nbal))))
              (0, []) \<bind>
             (\<lambda>x. (case x of (i, x) \<Rightarrow> RETURN x) \<bind> (\<lambda>newb. RETURN (np @ [newb]))))
         [])
       \<in> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg)
   apply refine_dref_type
    by (auto simp add: aeq)
qed

lemma [sepref_import_param]: "(defer_monadic,defer_monadic)
  \<in>   (\<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel 
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)
   \<rightarrow> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding  defer_monadic_def
   apply (auto)
  apply (rename_tac em' em A' A p)
  apply refine_vcg
   apply refine_dref_type
   apply auto
proof -
  fix em' em :: "'a Electoral_Module_Ref"
  fix A' A :: "'a set"
  fix p :: "'a Profile_List"
  assume em_id: "(em', em) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from this have aeq: "A' = A" by (simp add: in_br_conv alt_set_rel_def)
  from em_id[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD] arel
  show "em' A' p \<le> em A p"
    by blast
qed

 lemma [sepref_import_param]: "(elect_monadic,elect_monadic)
  \<in>   (\<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel 
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)
   \<rightarrow> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding  elect_monadic_def
   apply (auto)
  apply (rename_tac em' em A' A p)
  apply refine_vcg
   apply refine_dref_type
   apply auto
proof -
  fix em' em :: "'a Electoral_Module_Ref"
  fix A' A :: "'a set"
  fix p :: "'a Profile_List"
  assume em_id: "(em', em) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from this have aeq: "A' = A" by (simp add: in_br_conv alt_set_rel_def)
  from em_id[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD] arel
  show "em' A' p \<le> em A p"
    by blast
qed

 lemma [sepref_import_param]: "(reject_monadic,reject_monadic)
  \<in>   (\<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel 
  \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel)
   \<rightarrow> \<langle>Id\<rangle>alt_set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  unfolding  reject_monadic_def
   apply (auto)
  apply (rename_tac em' em A' A p)
  apply refine_vcg
   apply refine_dref_type
   apply auto
proof -
  fix em' em :: "'a Electoral_Module_Ref"
  fix A' A :: "'a set"
  fix p :: "'a Profile_List"
  assume em_id: "(em', em) \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  from this have aeq: "A' = A" by (simp add: in_br_conv alt_set_rel_def)
  from em_id[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD] arel
  show "em' A' p \<le> em A p"
    by blast
qed*)
  

sepref_register "m" :: "nat Electoral_Module_Ref"
sepref_register "n" :: "nat Electoral_Module_Ref"

thm n_impl

declare m_impl [sepref_fr_rules]
declare n_impl [sepref_fr_rules]

sepref_definition electm_imp is
  "(uncurry (elect_monadic m))" 
    :: "(alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_monadic_def
  by sepref

schematic_goal electn_imp:
  "(uncurry ?c, uncurry (elect_monadic n)) \<in> (alts_set_impl_assn)\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a alts_set_impl_assn"
  unfolding elect_monadic_def
  by sepref

definition seqt :: 
   "nat Electoral_Module_Ref" where
"seqt A p = do {
     electmA <- (elect_monadic m) A p;
     RETURN(electmA,op_hs_empty,op_hs_empty)
}"

lemma val: shows "sepref_access m m_impl"
  using m_impl by unfold_locales

lemma elecmsep:
  shows" (uncurry
 (\<lambda>ai bi.
     m_impl ai bi \<bind> (\<lambda>x'. return (fst x'))) ,
 uncurry (elect_monadic m))
\<in> (hs.assn nat_assn)\<^sup>k *\<^sub>a
   profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a hs.assn nat_assn"
  using val elect_sep_def elect_sep.refine
  by auto

declare elecmsep [sepref_fr_rules]

sepref_definition seqt_imp is
  "(uncurry (seqt))" 
    :: "alts_set_impl_assn\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k \<rightarrow>\<^sub>a result_impl_assn"
  unfolding seqt_def 
  apply sepref_dbg_keep


end



end