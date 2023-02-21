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


sepref_decl_op  (no_def) "borda :: 'a::{default, heap, hashable} Electoral_Module" 
  ::  "elec_mod_rel_orig R" where "R = Id"
    apply standard
  apply (rule nres_relI)
  apply simp done

sepref_decl_op  (no_def) "elect_module :: 'a::{default, heap, hashable} Electoral_Module" 
  ::  "elec_mod_rel_orig R" where "R = Id"
  .

(*sepref_decl_op  (no_def) condorcet ::  "elec_mod_rel_orig R" where "R = Id"
    apply standard
  apply (rule nres_relI)
  apply simp done*)




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





end

locale sequence_sepref_direct = refine_assns +
 fixes m :: "'a::{default, heap, hashable} Electoral_Module"  and
  n :: "'a::{default, heap, hashable} Electoral_Module"
  fixes m_sep :: "'a::{default, heap, hashable} Electoral_Module_Sep" 
  and n_sep :: "'a::{default, heap, hashable} Electoral_Module_Sep" 
  assumes module_m: "electoral_module m"
  and module_n: "electoral_module n"
  and m_sep_correct: "(uncurry m_sep, uncurry ( RETURN oo m)) \<in> elec_mod_sep_rel id_assn"
  and n_sep_correct: "(uncurry n_sep, uncurry ( RETURN oo n)) \<in> elec_mod_sep_rel id_assn"
begin

                                                              
fun sequential_composition'' :: "'a::{default, heap, hashable} Electoral_Module \<Rightarrow> 
      'a::{default, heap, hashable} Electoral_Module \<Rightarrow>
        'a::{default, heap, hashable} set \<Rightarrow> 'a::{default, heap, hashable} Profile 
\<Rightarrow> 'a::{default, heap, hashable} Result nres" where
  "sequential_composition'' ma na A pr = do {
      (mel,mrej,mdef) <- mop_borda A pr;
      
      let newA = mdef;
      new_p <- mop_limit_profile newA pr;
    
      (nel,nrej,ndef) <- mop_elect_module newA new_p;
      
      RETURN (mel \<union> nel, mrej \<union> nrej, ndef)
}"

sepref_decl_impl borda_elim_sep.refine[FCOMP borda_ref_correct, sepref_fr_rules] 
  by simp        

sepref_decl_impl elect_elect_module_sep_correct [sepref_fr_rules]
  by simp           


sepref_definition seqcompd is "uncurry (RETURN oo (sequential_composition'
  elect_module borda))"
  :: "[\<lambda>(a, b).
           finite a ]\<^sub>a (alts_set_impl_assn id_assn)\<^sup>k *\<^sub>a 
    (list_assn (hr_comp (ballot_impl_assn id_assn) ballot_rel))\<^sup>k 
        \<rightarrow> (result_impl_assn id_assn)"
  unfolding sequential_composition'.simps 
  apply sepref_dbg_keep
 apply sepref_dbg_trans_keep
  oops
  

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