theory Sepref_Bindings
  imports "Basic_Modules/Borda_Module_Ref"
    "Basic_Modules/Condorcet_Module_Ref"
    Sequential_Composition_Ref

begin



sepref_decl_op (no_def) borda_mod: "borda_ref :: 'a Electoral_Module_Ref" :: "elec_mod_rel_ref Id"
  apply standard
  apply (rule nres_relI)
  apply simp
  done

sepref_decl_op (no_def) borda_doit: "borda :: 'a Electoral_Module" :: "elec_mod_rel_orig Id"
  apply standard
  apply (rule nres_relI)
  apply simp
  done
  

  context 
    notes alts_assn_def[symmetric,fcomp_norm_unfold] 
       profile_assn_def[symmetric,fcomp_norm_unfold]
       result_set_assn_def[symmetric,fcomp_norm_unfold]
 alts_ref_assn_def[symmetric,fcomp_norm_unfold] ballot_ref_assn_def[symmetric,fcomp_norm_unfold]
      
begin


sepref_decl_impl borda_impl: borda_elim_sepref.refine[FCOMP borda_ref_correct] 
  unfolding alts_ref_assn_def .



                                                
end