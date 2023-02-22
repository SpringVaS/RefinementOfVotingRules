theory Sepref_Bindings
  imports "Basic_Modules/Borda_Module_Ref"
    "Basic_Modules/Condorcet_Module_Ref"  
    "Basic_Modules/Component_Types/Defer_Equal_Condition_Ref"
    Sequential_Composition_Ref
    "../Borda_Rule_Ref"
    "../Pairwise_Majority_Rule_Ref"

begin

lemma borda_aux:
  shows "(uncurry (RETURN \<circ>\<circ> borda), uncurry (RETURN \<circ>\<circ> borda))
    \<in> \<langle>Id\<rangle>set_rel \<times>\<^sub>r
       \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  apply standard
  apply (rule nres_relI)
  apply simp
  done

lemma condorcet_aux:
  shows "(uncurry (RETURN \<circ>\<circ> condorcet), uncurry (RETURN \<circ>\<circ> condorcet))
    \<in> \<langle>Id\<rangle>set_rel \<times>\<^sub>r
       \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel"
  apply standard
  apply (rule nres_relI)
  apply simp
  done


sepref_decl_op (no_def) defer_equal_imp: "(defer_equal_condition)" :: 
  "\<langle>nat_rel, \<langle>(\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel), \<langle>bool_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 
  where "R = Id" .



locale refine_assns =
 notes  
       ballot_assn_def[symmetric,fcomp_norm_unfold]
       alts_ref_assn_def[symmetric,fcomp_norm_unfold] 
       ballot_ref_assn_def[symmetric,fcomp_norm_unfold]
       alts_assn_def[symmetric,fcomp_norm_unfold] 
begin



sepref_definition borda_rule_sep is "uncurry (seq_opt borda elect_module
  )"
  :: "[\<lambda>(x, xa).
       finite
        x]\<^sub>a (hs.assn nat_assn)\<^sup>k *\<^sub>a
             (list_assn (hr_comp (ballot_impl_assn nat_assn) ballot_rel))\<^sup>k \<rightarrow> 
  result_impl_assn  nat_assn"
  unfolding seq_opt_def
  apply sepref_dbg_keep
  done


definition "impls \<equiv> borda_ref {1::nat, 2} ((([] @ [1::nat])@ [2::nat]) # [])"

 sepref_definition first_imple 
    is "uncurry0 (impls)" ::
 "unit_assn\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn nat_assn)"
   unfolding  impls_def comp_def
   apply (rewrite in "borda_ref rewrite_HOLE _" hs.fold_custom_empty)
   apply (rewrite in "[(rewrite_HOLE @ [1::nat])@ [2::nat]]" arl.fold_custom_empty)
   apply (rewrite in "_ # rewrite_HOLE" HOL_list.fold_custom_empty)
   apply sepref_dbg_keep
   done oops



definition "dimpls A p \<equiv> do {
  let (e, r, d) = borda A p;
  ASSERT (finite d);
  let newA = d;
  let newp = limit_profile newA p;
  let (ne, nr, nd) = elect_module newA newp;
   RETURN (e \<union> ne, r \<union> nr, nd) }"

 sepref_definition second_imple 
    is "uncurry (dimpls)" ::
    " [\<lambda>(a, b).
           finite
            a]\<^sub>a (alts_set_impl_assn nat_assn)\<^sup>k *\<^sub>a
                 (list_assn
                   (hr_comp (ballot_impl_assn nat_assn)
                     ballot_rel))\<^sup>k \<rightarrow> result_impl_assn  nat_assn"
   unfolding  dimpls_def aux_set_copy_def hs.fold_custom_empty
   apply sepref_dbg_keep
   done

lemma seqcomp_opt_correct: 
  fixes m n :: "'a::{default,hashable,heap} Electoral_Module" and
        A :: "'a set" and p :: "'a Profile"
  assumes finprofa: "finite_profile A p" and
   em_m: "electoral_module m" and
  em_n: "electoral_module n"
  shows "seq_opt m n A p \<le>
   RETURN (sequential_composition' m n A p)"
  unfolding comp_apply seq_opt_def sequential_composition'.simps
 using assms apply (refine_vcg)
   apply auto
  by (metis def_presv_fin_prof snd_conv)

end


end