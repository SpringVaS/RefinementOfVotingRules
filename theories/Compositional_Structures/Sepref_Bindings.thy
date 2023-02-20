theory Sepref_Bindings
  imports "Basic_Modules/Borda_Module_Ref"
    "Basic_Modules/Condorcet_Module_Ref"  
    "Basic_Modules/Component_Types/Defer_Equal_Condition_Ref"
    Sequential_Composition_Ref
    "../Borda_Rule_Ref"

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


sepref_decl_op  (no_def) borda ::  "elec_mod_rel_orig R" where "R = Id"
    apply standard
  apply (rule nres_relI)
  apply simp done




sepref_decl_op (no_def) defer_equal_imp: "(defer_equal_condition)" :: 
  "\<langle>nat_rel, \<langle>(\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel), \<langle>bool_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 
  where "R = Id" .



                              

definition "alts_ref_assn \<equiv> hr_comp (alts_set_impl_assn id_assn) (\<langle>Id\<rangle>set_rel)"
                                 

definition "ballot_ref_assn \<equiv>  hr_comp (ballot_impl_assn id_assn) (\<langle>Id\<rangle>list_rel)"

definition "alts_assn \<equiv> hr_comp alts_ref_assn (\<langle>Id\<rangle>set_rel)"
                                           
definition "result_set_one_step \<equiv> hr_comp (alts_set_impl_assn id_assn) (\<langle>Id\<rangle>set_rel)"

definition "result_set_assn \<equiv> hr_comp(result_set_one_step) (\<langle>Id\<rangle>set_rel)"

definition "ballot_assn \<equiv> hr_comp (hr_comp (ballot_impl_assn id_assn) ballot_rel) (\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel)"


locale refine_assns =
 notes  
       ballot_assn_def[symmetric,fcomp_norm_unfold]
       alts_ref_assn_def[symmetric,fcomp_norm_unfold] 
       ballot_ref_assn_def[symmetric,fcomp_norm_unfold]
       alts_assn_def[symmetric,fcomp_norm_unfold] 
      
begin


sepref_decl_impl borda : borda_elim_sep.refine[FCOMP borda_ref_correct] 
  by simp                                                              



end


definition "impls \<equiv> borda_ref {1::nat, 2} ((([] @ [1::nat])@ [2::nat]) # [])"

 sepref_definition first_imple 
    is "uncurry0 (impls)" ::
 "unit_assn\<^sup>k \<rightarrow>\<^sub>a (result_impl_assn nat_assn)"
   unfolding  impls_def comp_def
   apply (rewrite in "borda_ref rewrite_HOLE _" hs.fold_custom_empty)
   apply (rewrite in "[(rewrite_HOLE @ [1::nat])@ [2::nat]]" arl.fold_custom_empty)
   apply (rewrite in "_ # rewrite_HOLE" HOL_list.fold_custom_empty)
   apply sepref_dbg_keep
   done



definition "dimpls \<equiv> borda {1::nat, 2} [{(1::nat, 2)}]"

 sepref_definition second_imple 
    is "uncurry0 (RETURN dimpls)" ::
 "unit_assn\<^sup>k \<rightarrow>\<^sub>a ( hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel) \<times>\<^sub>a
                   hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel) \<times>\<^sub>a
                   hr_comp (hs.assn id_assn) (\<langle>Id\<rangle>set_rel) )"
   unfolding  dimpls_def comp_def
   apply sepref_dbg_keep
apply sepref_dbg_trans_keep
   done



end