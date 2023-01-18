theory Sequential_Composition_Ref
  imports "Basic_Modules/Component_Types/Electoral_Module_Ref"
        "Verified_Voting_Rule_Construction.Sequential_Composition"
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

      RETURN (op_set_union,rejectnA',defernA')}"
                      
(*
    
      new_A <- defm A p;
      new_p <- limit_profile_l new_A p;
      

      let elec = electmA \<union> electnA';
      let rej = rejectmA \<union> rejectnA';
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

declare m_impl [sepref_fr_rules]
declare n_impl [sepref_fr_rules]


sepref_definition seqt_imp is
  "(uncurry (sequential_composition_mon m n))" 
    :: "alts_set_impl_assn\<^sup>k *\<^sub>a (profile_impl_assn)\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn)"
  unfolding sequential_composition_mon_def elect_monadic_def defer_monadic_def reject_monadic_def
    limit_profile_l.simps limit_monadic_def
  apply (rewrite in "WHILEIT _ _ _ (_,\<hole>)" arl.fold_custom_empty )
   apply (rewrite in "nfoldli _ _ _ \<hole>" HOL_list.fold_custom_empty )
  apply sepref_dbg_keep
apply sepref_dbg_trans_keep
  oops

end



end