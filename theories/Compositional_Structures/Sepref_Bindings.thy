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


sepref_decl_op (no_def) "borda :: nat Electoral_Module" :: "elec_mod_rel_orig_nres nat_rel" 
  using borda_aux .



sepref_decl_op (no_def) defer_equal_imp: "(defer_equal_condition)" :: 
  "\<langle>nat_rel, \<langle>(\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel), \<langle>bool_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 
  where "R = Id" .


context fixed_alts
begin

sepref_decl_op (no_def) "condorcet :: nat Electoral_Module" :: 
  "elec_mod_rel_orig_nres nat_rel" 

end


locale refine_assns =
 notes  
       ballot_assn_def[symmetric,fcomp_norm_unfold]
       result_set_assn_def[symmetric,fcomp_norm_unfold]
       alts_ref_assn_def[symmetric,fcomp_norm_unfold] ballot_ref_assn_def[symmetric,fcomp_norm_unfold]
       alts_assn_def[symmetric,fcomp_norm_unfold] 
       result_set_one_step_def[symmetric,fcomp_norm_unfold]
      
begin

thm borda_elim_sepref.refine[FCOMP borda_ref_correct]

sepref_decl_impl borda_impl: borda_elim_sepref.refine[FCOMP borda_ref_correct]  .



sepref_decl_impl defer_eqal_condition_impl: defer_equal_condition_sep.refine .

end


locale seq_binding = seqcomp_impl + refine_assns
begin

sepref_decl_op  seq_comb: "sequential_composition  ::
  'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a Electoral_Module" :: 
  "\<langle>(elec_mod_rel_orig A), \<langle>(elec_mod_rel_orig A), (elec_mod_rel_orig_nres A)\<rangle>fun_rel\<rangle>fun_rel" 
  sorry

  

end