(*  File:       Electoral_Module_Ref.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>


theory Electoral_Module_Ref
  imports "Social_Choice_Types/Profile_List_Monadic"
          "Social_Choice_Types/Ballot_Refinement"
          "Verified_Voting_Rule_Construction.Electoral_Module"
         
begin                            


type_synonym 'a Electoral_Module_Ref = "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Result nres"

type_synonym 'a Electoral_Module_Sep = "('a, unit) hashtable
      \<Rightarrow> ('a array \<times> nat) list
         \<Rightarrow> (('a, unit) hashtable \<times> ('a, unit) hashtable \<times> ('a, unit) hashtable) Heap"


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
  "elec_mod_seprel R \<equiv> [\<lambda>(a, b).
           finite_profile a b]\<^sub>a (alts_set_impl_assn R)\<^sup>k *\<^sub>a 
    (list_assn (ballot_assn R))\<^sup>k 
        \<rightarrow> (result_impl_assn R)"

definition "is_arrayd_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> length l'>0)"

find_theorems name:"assn"

definition elec_mod_assn_atom:: 
  "('a  \<Rightarrow> 'a  \<Rightarrow> assn)
     \<Rightarrow> 'a::{default, hashable, heap} Electoral_Module \<Rightarrow> 'a::{default, hashable, heap}  Electoral_Module_Sep \<Rightarrow> assn" where
  "elec_mod_assn_atom R em em_sep \<equiv> emp * \<up>((uncurry em_sep, uncurry (RETURN oo em))
  \<in> elec_mod_seprel R)"
  


end