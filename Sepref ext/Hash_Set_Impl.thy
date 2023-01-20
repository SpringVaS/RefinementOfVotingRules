section "Hash-Sets"
theory Hash_Set_Impl
imports Imp_Set_Spec Hash_Map_Impl
begin

subsection \<open>Auxiliary Definitions\<close>
definition map_of_set:: "'a set \<Rightarrow> 'a\<rightharpoonup>unit" 
  where "map_of_set S x \<equiv> if x\<in>S then Some () else None"

lemma ne_some_unit_eq: "x\<noteq>Some () \<longleftrightarrow> x=None" 
  by (cases x) auto

lemma map_of_set_simps[simp]:
  "dom (map_of_set s) = s"
  "map_of_set (dom m) = m"
  "map_of_set {} = Map.empty"
  "map_of_set s x = None \<longleftrightarrow> x\<notin>s"
  "map_of_set s x = Some u \<longleftrightarrow> x\<in>s"
  "map_of_set s (x\<mapsto>()) = map_of_set (insert x s)"
  "(map_of_set s) |` (-{x}) = map_of_set (s -{x})"
  apply (auto simp: map_of_set_def 
    dom_def ne_some_unit_eq restrict_map_def 
    intro!: ext)
  done

lemma map_of_set_eq':
  "map_of_set a = map_of_set b \<longleftrightarrow> a=b"
  apply (auto simp: map_of_set_def[abs_def])
  apply (metis option.simps(3))+
  done

lemma map_of_set_eq[simp]:
  "map_of_set s = m \<longleftrightarrow> dom m=s"
  apply (auto 
    simp: dom_def map_of_set_def[abs_def] ne_some_unit_eq 
    intro!: ext)
  apply (metis option.simps(3))
  done

subsection \<open>Main Definitions\<close>
type_synonym 'a hashset = "('a,unit) hashtable"
definition "is_hashset s ht \<equiv> is_hashmap (map_of_set s) ht"

lemma hs_set_impl: "imp_set is_hashset"
  apply unfold_locales
  apply rule
  unfolding is_hashset_def
  apply (subst map_of_set_eq'[symmetric])
  by (metis preciseD[OF is_hashmap_prec])
interpretation hs: imp_set is_hashset by (rule hs_set_impl)

definition hs_new :: "'a::{heap,hashable} hashset Heap" 
  where "hs_new = hm_new"

lemma hs_new_impl: "imp_set_empty is_hashset hs_new"
  apply unfold_locales
  apply (sep_auto heap: hm_new_rule simp: is_hashset_def hs_new_def)
  done
interpretation hs: imp_set_empty is_hashset hs_new by (rule hs_new_impl)

definition hs_memb:: "'a::{heap,hashable} \<Rightarrow> 'a hashset \<Rightarrow> bool Heap" 
  where "hs_memb x s \<equiv> do { 
  r\<leftarrow>hm_lookup x s; 
  return (case r of Some _ \<Rightarrow> True | None \<Rightarrow> False)  
}"

lemma hs_memb_impl: "imp_set_memb is_hashset hs_memb"
  apply unfold_locales
  unfolding hs_memb_def
  apply (sep_auto 
    heap: hm_lookup_rule 
    simp: is_hashset_def split: option.split)
  done
interpretation hs: imp_set_memb is_hashset hs_memb by (rule hs_memb_impl)
             
definition hs_ins:: "'a::{heap,hashable} \<Rightarrow> 'a hashset \<Rightarrow> 'a hashset Heap"
  where "hs_ins x ht \<equiv> hm_update x () ht"

lemma hs_ins_impl: "imp_set_ins is_hashset hs_ins"
  apply unfold_locales      
  apply (sep_auto heap: hm_update_rule simp: hs_ins_def is_hashset_def)
  done
interpretation hs: imp_set_ins is_hashset hs_ins by (rule hs_ins_impl)


definition hs_delete
  :: "'a::{heap,hashable} \<Rightarrow> 'a hashset \<Rightarrow> 'a hashset Heap"
  where "hs_delete x ht \<equiv> hm_delete x ht"

lemma hs_delete_impl: "imp_set_delete is_hashset hs_delete"
  apply unfold_locales
  apply (sep_auto heap: hm_delete_rule simp: is_hashset_def hs_delete_def)
  done
interpretation hs: imp_set_delete is_hashset hs_delete
  by (rule hs_delete_impl)

definition "hs_isEmpty == hm_isEmpty"

lemma hs_is_empty_impl: "imp_set_is_empty is_hashset hs_isEmpty"
  apply unfold_locales
  apply (sep_auto heap: hm_isEmpty_rule simp: is_hashset_def hs_isEmpty_def)
  done
interpretation hs: imp_set_is_empty is_hashset hs_isEmpty
  by (rule hs_is_empty_impl)

definition "hs_size == hm_size"

lemma hs_size_impl: "imp_set_size is_hashset hs_size"
  apply unfold_locales
  apply (sep_auto heap: hm_size_rule simp: is_hashset_def hs_size_def)
  done
interpretation hs: imp_set_size is_hashset hs_size by (rule hs_size_impl)

type_synonym ('a) hs_it = "('a,unit) hm_it"

definition "hs_is_it s hs its it 
  \<equiv> hm_is_it (map_of_set s) hs (map_of_set its) it"

definition hs_it_init :: "('a::{heap,hashable}) hashset \<Rightarrow> 'a hs_it Heap"
  where "hs_it_init \<equiv> hm_it_init"

definition hs_it_has_next :: "('a::{heap,hashable}) hs_it \<Rightarrow> bool Heap"
  where "hs_it_has_next \<equiv> hm_it_has_next"

definition hs_it_next 
  :: "('a::{heap,hashable}) hs_it \<Rightarrow> ('a\<times>'a hs_it) Heap"
  where 
  "hs_it_next it \<equiv> do {
    ((x,_),it) \<leftarrow> hm_it_next it;
    return (x,it)
  }"

lemma hs_iterate_impl: "imp_set_iterate 
  is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next"
  apply unfold_locales
  unfolding hs_it_init_def hs_it_next_def hs_it_has_next_def 
    hs_is_it_def is_hashset_def
  apply sep_auto
  apply sep_auto
  apply sep_auto
  apply (sep_auto eintros: hm.quit_iteration)
  done

interpretation hs: imp_set_iterate 
  is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next
  by (rule hs_iterate_impl)



partial_function (heap) hs_un_it
  where [code]: "hs_un_it 
    it_has_next it_next set_ins it a = do {
      co \<leftarrow> it_has_next it;
      if co then do {
        (x,it') \<leftarrow> it_next it;
        insx <- set_ins x a;
        hs_un_it it_has_next it_next set_ins it' (insx) 
      } else return a
    }"



lemma hs_un_it_rule:
    assumes "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes "imp_set_ins is_set set_ins"
    assumes FIN: "finite it"
    shows "
    < is_it b q it iti * is_set a p> 
      hs_un_it it_has_next it_next set_ins iti p 
    < \<lambda>r. is_set (a \<union> it) r >\<^sub>t"
  proof -
    interpret imp_set_iterate is_set is_it it_init it_has_next it_next
        + imp_set_ins is_set set_ins
      by fact+

    from FIN show ?thesis
    proof (induction  arbitrary: a p iti rule: finite_psubset_induct)
      case (psubset it)
      show ?case
        apply (subst hs_un_it.simps)
        apply (sep_auto heap: psubset.IH)
        unfolding entails_def apply safe
        apply (metis Un_insert_right insert_Diff)
        apply (metis (no_types, lifting) assn_times_comm ent_refl_true ent_true_drop(1) return_cons_rule sup_bot_right)
        done   
    qed
  qed


 

definition union_loop_ins  where 
"union_loop_ins it_init it_has_next it_next set_ins a b \<equiv> do { 
    it <- (it_init b);
    hs_un_it it_has_next it_next set_ins it a
    }"



lemma set_union_rule:
    assumes IT: "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes INS: "imp_set_ins is_set set_ins"
    assumes finb: "finite b"
    shows "
    <is_set a p * is_set b q>
   union_loop_ins it_init  it_has_next it_next set_ins p q
    <\<lambda>r. is_set (a \<union> b) r * true>"
  proof -
    interpret 
      imp_set_iterate is_set is_it it_init it_has_next it_next
        + imp_set_ins is_set set_ins
      by fact+

    note it_aux[sep_heap_rules] = hs_un_it_rule[OF IT INS finb]
    show ?thesis
      unfolding union_loop_ins_def
       apply (sep_auto)
      done
  qed

 definition "hs_union 
    \<equiv> union_loop_ins hs_it_init hs_it_has_next hs_it_next hs_ins"

lemmas hs_union_rule[sep_heap_rules] =
    set_union_rule[OF hs_iterate_impl hs_ins_impl,
    folded hs_union_def] 


export_code hs_union checking SML_imp
  



end
