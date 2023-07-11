section \<open>Set Interface\<close>
theory IICF_Set
imports "../../Sepref"
begin

subsection \<open>Operations\<close>
definition [simp]: "op_set_is_empty s \<equiv> s={}"
lemma op_set_is_empty_param[param]: "(op_set_is_empty,op_set_is_empty)\<in>\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" by auto

context 
  notes [simp] = IS_LEFT_UNIQUE_def (* Argh, the set parametricity lemmas use single_valued (K\<inverse>) here. *)
begin

find_theorems card
definition op_set_copy :: "'a set \<Rightarrow> 'a set" where [simp]:  "op_set_copy s \<equiv> s"
sepref_decl_op (no_def) set_copy: "op_set_copy" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "A = Id" .
sepref_decl_op set_empty: "{}" :: "\<langle>A\<rangle>set_rel" .
sepref_decl_op (no_def) set_is_empty: op_set_is_empty :: "\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" .
sepref_decl_op set_member: "(\<in>)" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_insert: Set.insert :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_delete: "\<lambda>x s. s - {x}" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" 
  where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_union: "(\<union>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" .
sepref_decl_op set_inter: "(\<inter>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_diff: "(-) ::_ set \<Rightarrow> _" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subseteq: "(\<subseteq>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subset: "(\<subset>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_size: "(card)" :: "\<langle>A\<rangle>set_rel \<rightarrow> nat_rel"  where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" 
proof (standard, rename_tac X Y)
  fix X :: "'a set"
  fix Y :: "'b set"
  assume xy_rel: "(X, Y) \<in> \<langle>A\<rangle>set_rel"
  assume luA: "IS_LEFT_UNIQUE A"
  assume svA: "single_valued A"
  show "((RETURN \<circ> card) X, (RETURN \<circ> card) Y) \<in> \<langle>nat_rel\<rangle>nres_rel"
  proof (refine_vcg, clarsimp_all, cases "finite X")
    case cc: True
    from cc have finx: "finite X" by simp
    from cc svA luA xy_rel have finy: "finite Y"
    using finite_set_rel_transfer by blast 
    from finx xy_rel show "card X = card Y"
    proof (induction arbitrary: Y rule: finite_psubset_induct)
      case cps: (psubset Aa)
      then show ?case
      proof (cases "Aa \<noteq> {}")
        case nempAa: True
        assume xarel: "(Aa, Y) \<in> \<langle>A\<rangle>set_rel"
        from nempAa obtain elemx where xmemb: "elemx \<in> Aa" by auto
        from this obtain subx where stepx: "subx = Aa - {elemx}" by auto
        from this xmemb have subp: "subx \<subset> Aa" by blast 
        from cps.prems nempAa have nempy : "Y \<noteq> {}" by force
        from nempy xarel obtain elemy where ymemb: "elemy \<in> Y \<and> (elemx, elemy) \<in> A"
          using xmemb set_relD1 by force
        from ymemb obtain suby where stepy: "suby = Y - {elemy}"
          by auto
        from stepx stepy  xarel ymemb luA svA  have subrel: "(subx, suby) \<in> \<langle>A\<rangle>set_rel"
          unfolding set_rel_def apply simp
          by (metis Diff_iff converseI insert_Diff insert_iff single_valued_def)
        from stepx stepy  have cardincx: "card Aa = card subx + 1"
          by (metis One_nat_def add.right_neutral add_Suc_right card_Suc_Diff1 cps.hyps xmemb)
        from stepy svA xarel ymemb have cardincy: "card Y = card suby + 1"
          by (metis Suc_eq_plus1 card.remove cps.hyps finite_set_rel_transfer)
          show "card Aa = card Y"
            using cardincx cardincy cps.IH subp subrel by presburger 
      next
        assume xarel: "(Aa, Y) \<in> \<langle>A\<rangle>set_rel"
        case False
        thus ?thesis
          using cps.prems by fastforce 
      qed
    qed
  next
    case infx: False
    from this have cardx0: "card X = 0" by simp
    from xy_rel luA svA infx have "infinite Y" unfolding set_rel_def  
      by (auto, metis finite_set_rel_transfer_back xy_rel)
    from this have cardy0: "card Y = 0" by simp
    from cardx0 cardy0 show "card X = card Y" by simp 
  qed
qed   
    

(* TODO: We may want different operations here: pick with predicate returning option,
  pick with remove, ... *)    
sepref_decl_op set_pick: "RES" :: "[\<lambda>s. s\<noteq>{}]\<^sub>f \<langle>K\<rangle>set_rel \<rightarrow> K" by auto

end

(* TODO: Set-pick. Move from where it is already defined! *)

subsection \<open>Patterns\<close>
lemma pat_set[def_pat_rules]:
  "{} \<equiv> op_set_empty"
  "(\<in>) \<equiv> op_set_member"    
  "Set.insert \<equiv> op_set_insert"
  "(\<union>) \<equiv> op_set_union"
  "(\<inter>) \<equiv> op_set_inter"
  "(-) \<equiv> op_set_diff"
  "(\<subseteq>) \<equiv> op_set_subseteq"
  "(\<subset>) \<equiv> op_set_subset"
  "card \<equiv> op_set_size"
  by (auto intro!: eq_reflection)
  
lemma pat_set2[pat_rules]: 
  "(=) $s${} \<equiv> op_set_is_empty$s"
  "(=) ${}$s \<equiv> op_set_is_empty$s"

  "(-) $s$(Set.insert$x${}) \<equiv> op_set_delete$x$s"
  "SPEC$(\<lambda>\<^sub>2x. (\<in>) $x$s) \<equiv> op_set_pick s"
  "RES$s \<equiv> op_set_pick s"
  by (auto intro!: eq_reflection)


locale set_custom_empty = 
  fixes empty and op_custom_empty :: "'a set"
  assumes op_custom_empty_def: "op_custom_empty = op_set_empty"
begin
  sepref_register op_custom_empty :: "'ax set"

  lemma fold_custom_empty:
    "{} = op_custom_empty"
    "op_set_empty = op_custom_empty"
    "mop_set_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end

end

