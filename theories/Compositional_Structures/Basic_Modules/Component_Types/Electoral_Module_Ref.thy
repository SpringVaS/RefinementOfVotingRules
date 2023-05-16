(*  File:       Electoral_Module_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Refined Component Types\<close>

theory Electoral_Module_Ref
  imports "Social_Choice_Types/Profile_List_Monadic"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
         
begin                            

section \<open>Refined Electoral Module Type\<close>

subsection \<open>Definition\<close>

type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"


type_synonym 'a Electoral_Module_Sep = "('a, unit) hashtable
      \<Rightarrow> ('a array \<times> nat) list
         \<Rightarrow> (('a, unit) hashtable \<times> ('a, unit) hashtable \<times> ('a, unit) hashtable) Heap"

definition aux_set_copy :: "'a set \<Rightarrow> 'a set nres" where
  "aux_set_copy A \<equiv>  FOREACH A 
     (\<lambda> x cp. RETURN (insert x cp)) {}"

 \<comment> \<open>The elect module should not return just the reference to all alternatives
  but a deep copy.\<close>


lemma aux_set_copy_correct:
  shows "(aux_set_copy, (RETURN o op_set_copy)) 
    \<in> [\<lambda> s. finite s]\<^sub>f \<langle>Id\<rangle>set_rel \<rightarrow> \<langle>\<langle>Id\<rangle>set_rel\<rangle>nres_rel"  
  unfolding aux_set_copy_def comp_apply
  apply (intro frefI nres_relI, clarsimp)
proof (rename_tac A)
  fix A :: "'a set"
  assume fina: "finite A"
  show "FOREACH A (\<lambda>x cp. RETURN (insert x cp)) {} \<le> RETURN A"
    apply (refine_vcg FOREACH_rule[where I = "\<lambda> it x. 
      x = A -it"])
    by (auto simp add: fina)
qed

sepref_definition hs_copy_sep is "aux_set_copy" :: 
  " (hs.assn id_assn)\<^sup>k
 \<rightarrow>\<^sub>a (hs.assn id_assn)"
  unfolding aux_set_copy_def hs.fold_custom_empty
  by sepref

lemma hs_copy_hnr_aux[sepref_fr_rules]: "(hs_copy_sep, RETURN o op_set_copy) 
  \<in> [\<lambda> s. finite s]\<^sub>a (hs.assn id_assn)\<^sup>k \<rightarrow> hs.assn id_assn"
  using hs_copy_sep.refine[FCOMP aux_set_copy_correct] by auto



subsection \<open>Refinement Relations\<close>

definition elec_mod_rel_orig :: "('b \<times> 'b) set \<Rightarrow> 
  ('b Electoral_Module \<times> 'b Electoral_Module) set" where
  "elec_mod_rel_orig R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_rel_orig_nres :: "('a \<times> 'a) set \<Rightarrow> 
  (('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres) \<times> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result nres))
   set" where
  "elec_mod_rel_orig_nres R \<equiv> \<langle>\<langle>R\<rangle>set_rel , \<langle>\<langle>\<langle>R \<times>\<^sub>r R\<rangle>set_rel\<rangle>list_rel , 
  \<langle>\<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel \<times>\<^sub>r \<langle>R\<rangle>set_rel\<rangle>nres_rel\<rangle>fun_rel\<rangle>fun_rel" 

abbreviation elec_mod_seprel where 
  "elec_mod_seprel R \<equiv> [\<lambda>(a, b). finite_profile a b]\<^sub>a 
  (alts_set_impl_assn R)\<^sup>k *\<^sub>a (list_assn (ballot_assn R))\<^sup>k \<rightarrow> (result_impl_assn R)"


subsection \<open>Experimental defintion for Separation Logic Assertion\<close>

definition elec_mod_assn_atom:: 
  "('a  \<Rightarrow> 'a  \<Rightarrow> assn)
     \<Rightarrow> 'a::{default, hashable, heap} Electoral_Module \<Rightarrow> 'a::{default, hashable, heap}  Electoral_Module_Sep \<Rightarrow> assn" where
  "elec_mod_assn_atom R em em_sep \<equiv> emp * \<up>((uncurry em_sep, uncurry (RETURN oo em))
  \<in> elec_mod_seprel R)"
  


end