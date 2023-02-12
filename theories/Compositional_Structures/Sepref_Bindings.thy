theory Sepref_Bindings
  imports "Basic_Modules/Borda_Module_Ref"
    "Basic_Modules/Condorcet_Module_Ref"  
    "Basic_Modules/Component_Types/Defer_Equal_Condition_Ref"
    Sequential_Composition_Ref

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


sepref_decl_op (no_def) "borda :: 'a Electoral_Module" :: "elec_mod_rel_orig Id" 
  using borda_aux .


sepref_decl_op (no_def) defer_equal_imp: "(defer_equal_condition)" :: 
  "\<langle>nat_rel, \<langle>(\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel), \<langle>bool_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 
  where "R = Id" .



                              

definition "alts_ref_assn \<equiv> hr_comp alts_set_impl_assn (\<langle>Id\<rangle>set_rel)"
                                 

definition "ballot_ref_assn \<equiv>  hr_comp (ballot_impl_assn) (\<langle>Id\<rangle>list_rel)"

definition "alts_assn \<equiv> hr_comp alts_ref_assn (\<langle>Id\<rangle>set_rel)"

definition "result_set_one_step \<equiv> hr_comp alts_set_impl_assn (\<langle>Id\<rangle>set_rel)"

definition "result_set_assn \<equiv> hr_comp(result_set_one_step) (\<langle>Id\<rangle>set_rel)"

definition "ballot_assn \<equiv> hr_comp (hr_comp (ballot_impl_assn) ballot_rel) (\<langle>Id \<times>\<^sub>r Id\<rangle>set_rel)"


locale refine_assns =
 notes  
       ballot_assn_def[symmetric,fcomp_norm_unfold]
       result_set_assn_def[symmetric,fcomp_norm_unfold]
       alts_ref_assn_def[symmetric,fcomp_norm_unfold] 
       ballot_ref_assn_def[symmetric,fcomp_norm_unfold]
       alts_assn_def[symmetric,fcomp_norm_unfold] 
       result_set_one_step_def[symmetric,fcomp_norm_unfold]
      
begin


sepref_decl_impl borda_impl: borda_elim_sep.refine[FCOMP borda_ref_correct] 
  by simp                                       

         

sepref_decl_impl defer_eqal_condition_impl: defer_equal_condition_sep.refine .

 definition "funsc A p \<equiv> RETURN (borda A p)"

 sepref_definition first_imple 
    is "uncurry funsc" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a  (alts_assn \<times>\<^sub>a alts_assn \<times>\<^sub>a alts_assn) "
   unfolding funsc_def id_def comp_def
   apply sepref_dbg_keep


end



end