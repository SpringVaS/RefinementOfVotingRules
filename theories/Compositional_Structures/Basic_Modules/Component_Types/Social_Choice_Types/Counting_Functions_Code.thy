theory Counting_Functions_Code
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
  Refine_Imperative_HOL.IICF
begin

text \<open>Profile List refines Profile\<close>

lemma profile_data_refine:
  assumes "(pl,pr)\<in>build_rel pl_to_pr_\<alpha> (profile_l A)"
  shows "profile A pr"
proof -
  from assms have prof: "profile_l A pl"
    using in_br_conv by metis
  from assms have "pr = pl_to_pr_\<alpha> pl"
    using in_br_conv by metis
  with prof show ?thesis 
    using profile_prop_refine by metis
qed

text \<open> Monadic definition of ballot properties \<close>

definition "index_mon_inv ballot a \<equiv> (\<lambda> (i, found).
    (i \<le> List_Index.index ballot a)
  \<and> (found \<longrightarrow> (i = List_Index.index ballot a)))"
(*  \<and> (\<not>found \<longrightarrow> (i \<le> List_Index.index ballot a)))"*)

(* low level optimization for pref count *)
definition index_mon :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "index_mon ballot a \<equiv> do {
    (i, found) \<leftarrow> WHILEIT ((index_mon_inv ballot a)) 
  (\<lambda>(i, found). (i < (length ballot) \<and> \<not>found)) 
      (\<lambda>(i,_). do {
      ASSERT (i < (length ballot));
      let (c) = (ballot!i);
      if (a = c) then
        RETURN (i,True)
      else
        RETURN (i+1,False)
    })(0, False);
    RETURN (i)
  }"                          

lemma isl1_measure: "wf (measure (\<lambda>(i, found). length ballot - i - (if found then 1 else 0)))" by simp

lemma index_sound:
  fixes a:: 'a and l :: "'a list" and i::nat
  assumes  "i \<le> index l a"
  shows "(a = l ! i) \<longrightarrow> (i = index l a)"
  by (metis assms(1) index_first le_eq_less_or_eq)

  

lemma index_mon_correct:
  shows "index_mon ballot a \<le> SPEC (\<lambda> r. r = List_Index.index ballot a)"
  unfolding index_mon_def index_mon_inv_def
  apply (intro WHILEIT_rule[where  R="measure (\<lambda>(i, found). length ballot - i - (if found then 1 else 0))"] refine_vcg)
proof (safe, simp_all)
  fix aa::nat
  assume bound: "aa \<le> index ballot (ballot ! aa)"
  (*assume range : "aa < length ballot"*)
  thus "aa = index ballot (ballot ! aa)" by (simp add: index_sound)
next
  fix i
  assume notnow: "a \<noteq> ballot ! i"
  assume notyet: "i \<le> List_Index.index ballot a"
  assume ir: "i < length ballot"
  from notnow have "i \<noteq> List_Index.index ballot a"
    by (metis index_eq_iff ir)
  from notyet this show "Suc i \<le> List_Index.index ballot a"
    by fastforce
next
  assume "index ballot a < length ballot"
  and "a \<noteq> ballot ! index ballot a"
  thus "False"
    by (metis index_eq_iff)
next
  fix aa
  assume "aa \<le> index ballot a"
    and "aa \<noteq> index ballot a"
  thus "aa < length ballot"
    by (metis antisym index_le_size le_neq_implies_less order_trans)
qed

lemma index_mon_refine:
  shows "(index_mon, (\<lambda> ballot a. (RETURN (List_Index.index ballot a))))\<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg index_mon_correct)
  apply simp
  done


definition rank_mon :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "rank_mon ballot a \<equiv> do {
    i \<leftarrow> (index_mon ballot a);
    if (i = length ballot) then RETURN 0 else RETURN (i + 1)
  }"       


lemma rank_mon_correct: "rank_mon ballot a \<le> SPEC (\<lambda> r. r = rank_l ballot a)"
  unfolding rank_mon_def
proof (refine_vcg, (simp_all add: rankdef), safe)
  assume mem: "List.member ballot a"
  from this have "index ballot a \<noteq> length ballot"
    by (simp add: in_set_member index_size_conv)
  from this show "index_mon ballot a \<le> SPEC (\<lambda>i. i = index ballot a \<and> i \<noteq> length ballot)"
    using index_mon_correct
    by (metis (mono_tags, lifting) SPEC_cons_rule)
next
  assume nmem: "\<not> List.member ballot a"
  from this have "index ballot a = length ballot"
    by (simp add: in_set_member)
  from this show "index_mon ballot a \<le> RES {length ballot}"
    using index_mon_correct
    by (metis singleton_conv)
qed


lemma rank_mon_refine:
  shows "(rank_mon, (\<lambda> ballot a. RETURN (rank_l ballot a)))\<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg rank_mon_correct)
  apply simp
  done

sepref_register rank_mon


section \<open>Monadic implementation of counting functions \<close>

text \<open>
  win-count, multiple refinement steps
\<close>

definition "wc_invar p0 a \<equiv> \<lambda>(i,ac).
  i \<le> length p0 
  \<and> ac = card{idx::nat. idx < i\<and> above (p0!idx) a = {a}}"

definition win_count_mon :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_mon p a \<equiv> do {
  (r, ac) \<leftarrow> WHILEIT (wc_invar p a) (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let wc = (if (above (p!r) a = {a}) then (ac + 1) else ac);
    let r = r + 1;
    RETURN (r, wc)
  })(0,0);
  RETURN ac
}"

definition win_count_mon_r :: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_mon_r p a \<equiv> do {
  (r, ac) \<leftarrow> WHILEIT (wc_invar p a) (\<lambda>(r, _). r < length p) (\<lambda>(r, ac). do {
    ASSERT (r < length p);
    let wc = (if (rank (p!r) a = 1) then (ac + 1) else ac);
    let r = r + 1;
    RETURN (r, wc)
  })(0,0);
  RETURN ac
}"

definition "win_count_fold p a =
   foldl
    (\<lambda>(ac::nat) x. 
     if (above x a = {a}) then (ac+1) else (ac)) 
    0 p"


lemma "win_count_fold p a = win_count p a"
  unfolding win_count_fold_def
  apply (induction p)
   apply (clarsimp_all, safe)

  oops

(* The lemma is implicitly proven
in the win_count_mon_correct lemma *)
(* lemma wc_invar_step:
  shows "\<forall> r < length p. wc_invar p a (r, ac) \<longrightarrow> wc_invar p a (r + 1, ac + (if (above (p!r) a = {a}) then 1 else 0))"
  unfolding wc_invar_def *)

lemma win_count_mon_correct:
  shows "win_count_mon p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  unfolding win_count_mon_def win_count.simps
  apply (intro WHILEIT_rule[where R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding wc_invar_def
  apply (simp_all)
  apply (erule subst)
  apply (simp)
  apply (intro conjI impI)
proof (simp_all)
  fix r :: nat
  assume le: "r < length p"
  assume atop: "above (p ! r) a = {a}"
  with atop have prep: 
         "{i. i < Suc r \<and> above (p ! i) a = {a}} 
        = {i. i < r \<and> above (p ! i) a = {a}} \<union> {r}"
    by fastforce
  then show   
         "Suc (card {i. i < r \<and> above (p ! i) a = {a}}) =
          card {i. i < Suc r \<and> above (p ! i) a = {a}}"
    by fastforce
next
  fix r :: nat
  assume "r < length p"
  assume atop: "above (p ! r) a \<noteq> {a}"
  then show "
       card {i. i < r \<and> above (p ! i) a = {a}} =
       card {i. i < Suc r \<and> above (p ! i) a = {a}}"
    by (metis less_Suc_eq)
qed

schematic_goal wc_code_aux: "RETURN ?wc_code \<le> win_count_mon p a"
  unfolding win_count_mon_def
  by (refine_transfer)

concrete_definition win_count_code for p a uses wc_code_aux

thm win_count_code_def


lemma win_count_equiv: 
  shows "win_count p a = win_count_code p a"
proof -
  from order_trans[OF win_count_code.refine win_count_mon_correct] 
    have "win_count_code p a = win_count p a"
      by fastforce
  thus ?thesis by simp
qed


lemma carde: assumes prof: "profile A p"
  shows "\<forall> ballot \<in> set p. (rank ballot a  = 1) = (above ballot a = {a})" 
  using prof
  by (metis above_rank profile_set)
  

lemma isp1_measure: "wf (measure (\<lambda>(i, _).(length p) - i))" by simp

lemma win_count_mon_r_correct:
  assumes prof: "profile A p"
  shows "win_count_mon_r p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  unfolding win_count_mon_r_def win_count.simps
  apply (intro WHILEIT_rule[where R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding wc_invar_def
  apply (simp_all)
  apply (erule subst)
  apply (simp)
proof (safe, simp_all)
  fix aa
  assume aail: "aa < length p"
  assume rank1: "card (above (p ! aa) a) = Suc 0"
  from aail prof rank1 have "above (p ! aa) a = {a}"
    by (metis One_nat_def profile_def rank.simps rankone2)
  from this have prep: 
         "{i. i < Suc aa \<and> above (p ! i) a = {a}} 
        = {i. i < aa \<and> above (p ! i) a = {a}} \<union> {aa}"
    by fastforce
  then show 
         "Suc (card {i. i < aa \<and> above (p ! i) a = {a}}) =
          card {i. i < Suc aa \<and> above (p ! i) a = {a}}"
    by simp
next
  fix aa
  assume aail: "aa < length p"
  assume rank1: "card (above (p ! aa) a) \<noteq> Suc 0"
  from aail rank1 have neq: "above (p ! aa) a \<noteq> {a}"
    by fastforce
  have seteq:
      "{i. i < Suc aa \<and> above (p ! i) a = {a}}
      ={i. i < aa \<and> above (p ! i) a = {a}} \<union> {i. i = aa \<and> above (p ! i) a = {a}}"
    by fastforce
  from neq have emp: "{i. i = aa \<and> above (p ! i) a = {a}} = {}" by blast
    from seteq emp have
    "{i. i < Suc aa \<and> above (p ! i) a = {a}} = {i. i < aa \<and> above (p ! i) a = {a}}"
    by simp
  then show "
      card {i. i < aa \<and> above (p ! i) a = {a}} =
      card {i. i < Suc aa \<and> above (p ! i) a = {a}}"
    by simp
qed

lemma win_count_mon_r_refine_spec:
  shows "(win_count_mon_r, (\<lambda> p a. (RETURN (win_count p a)))) 
    \<in> (br (\<lambda>x. x) (profile A)) \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg win_count_mon_r_correct) 
  apply (auto simp add: refine_rel_defs)
  done




text \<open> Data refinement \<close>

(* these auxiliary lemmas illustrate the equivalence of checking the the first
  candidate on a non empty ballot. *)
lemma top_above:
  assumes ne: "length pl > 0"
  shows "pl!0 = a \<longleftrightarrow> above_l pl a = [a]"
  unfolding above_l_def
proof (simp add: rankdef, safe)
  assume mem: "List.member pl (pl ! 0)"
  assume "a = pl ! 0"
  have "List_Index.index pl (pl ! 0) = 0"
    by (simp add: index_eqI)
  from mem this show "take (Suc (List_Index.index pl (pl ! 0))) pl = [pl ! 0]"
    by (metis append_Nil in_set_member index_less_size_conv take0 take_Suc_conv_app_nth)
next
  (*assume mem: "List.member pl a"*)
  assume "take (Suc (List_Index.index pl a)) pl = [a]"
  from this show "pl ! 0 = a"
    by (metis append_Cons append_Nil append_take_drop_id hd_conv_nth list.sel(1))
next
  assume nm: "\<not> List.member pl (pl ! 0)"
  from this have pl_empty: "pl = []"
    by (metis length_greater_0_conv member_def nth_mem)
  from ne this pl_empty show "False"
    by simp
qed

lemma top_l_above_r:
  assumes ballot: "ballot_on A pl"
  assumes aA: "a \<in> A" and ne: "length pl > 0"
  shows "pl!0 = a \<longleftrightarrow> above (pl_\<alpha> pl) a = {a}"
proof -
  from ne have listeq: "pl!0 = a \<longleftrightarrow> above_l pl a = [a]"
    by (simp add: top_above)
  from assms have above_abstract: "set (above_l pl a) = above (pl_\<alpha> pl) a" 
    by (auto simp add: aboveeq)
  have list_set: "above_l pl a = [a] \<longleftrightarrow> set (above_l pl a) = {a}"
    by (metis above_l_def append_self_conv2 gr0I hd_take id_take_nth_drop insert_not_empty list.sel(1) list.set(1) list.set_sel(1) list.simps(15) listeq ne singleton_iff take_eq_Nil)
  from above_abstract listeq this show ?thesis
    by (simp)
qed

definition "wc_list_invar p0 a \<equiv> \<lambda>(i,ac).
  0 \<le> i \<and> i \<le> length p0"


definition win_count_list_r :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_list_r p a \<equiv> do {
  (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let ac = ac + (if (rank_l (p!i) a = 1) then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma rankeq_refine: 
  fixes A :: "'a set" and l :: "'a Preference_List" and a :: 'a
  assumes "(pl, pr) \<in> (br pl_\<alpha> (ballot_on A))"
  shows "rank_l pl a = Preference_Relation.rank pr a"
proof -
  from assms have ballot: "ballot_on A pl" using in_br_conv
    by metis
  from assms have "pr = pl_\<alpha> pl"
    by (simp add: in_br_conv)
  from ballot this show ?thesis using rankeq
    by metis
qed


lemma win_count_list_r_refine: 
  fixes A:: "'a set"
  shows "(win_count_list_r, win_count_mon_r) \<in> 
  (br pl_to_pr_\<alpha> (profile_l A)) \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding win_count_list_r_def win_count_mon_r_def pl_to_pr_\<alpha>_def profile_l_def wc_list_invar_def
    wc_invar_def
  apply (refine_vcg rankeq_refine)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply (auto simp add:  rankeq_refine  refine_rel_defs)
proof (-)
  fix pl:: "'a Profile_List"
  fix idx::nat
  fix alt::'a
  assume prof: "\<forall>i<length pl. ballot_on A (pl ! i)"
  assume ir: "idx < length pl"
  assume mem: "List.member (pl ! idx) alt"
  from prof ir have bal: "ballot_on A (pl!idx)"
    by blast 
  from bal have "rank_l (pl ! idx) alt = rank (pl_\<alpha> (pl ! idx)) alt" 
    using rankeq
    by metis
  from mem this show "Suc (index (pl ! idx) alt) = card (above (pl_\<alpha> (pl ! idx)) alt)"
    by (metis Suc_eq_plus1 rank.simps rank_alt.elims rankdef)
next
    fix pl:: "'a Profile_List"
  fix idx::nat
  fix alt::'a
  assume prof: "\<forall>i<length pl. ballot_on A (pl ! i)"
  assume ir: "idx < length pl"
  assume nmem: "\<not> List.member (pl ! idx) alt"
   from prof ir have bal: "ballot_on A (pl!idx)"
    by blast 
  from bal have "rank_l (pl ! idx) alt = rank (pl_\<alpha> (pl ! idx)) alt" 
    using rankeq
    by metis
  from nmem this show "card (above (pl_\<alpha> (pl ! idx)) alt) = 0"
    by (simp add: rankdef)
qed

lemma win_count_list_r_refine_spec:
  shows "(win_count_list_r, (\<lambda> pr a. RETURN (win_count pr a))) \<in>
    br pl_to_pr_\<alpha> (profile_l A) \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg win_count_list_r_refine win_count_mon_r_refine_spec)
proof auto
  fix pl:: "'a Profile_List"
  fix pr:: "'a Profile"
  fix alt:: 'a
  assume rel: "(pl, pr) \<in> br pl_to_pr_\<alpha> (profile_l A)"
  from this have "profile_l A pl" using in_br_conv by metis
  from rel this have "profile A pr"
    using profile_data_refine by blast
  from this have "win_count_mon_r pr alt \<le> SPEC (\<lambda>c. (c, win_count pr alt) \<in> nat_rel)"
    using win_count_mon_r_correct by (metis (mono_tags, lifting) SPEC_cons_rule pair_in_Id_conv)
  from this 
    rel have "win_count_list_r pl alt \<le> SPEC (\<lambda>c. (c, win_count pr alt) \<in> nat_rel)" using win_count_list_r_refine
    by (metis conc_trans_additional(5) nres_relD pair_in_Id_conv relAPP_def tagged_fun_relD_both)
  from this show "win_count_list_r pl alt \<le> RES {card {i. i < length pr \<and> above (pr ! i) alt = {alt}}}"
    by fastforce
qed
  


definition win_count_imp_array :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp_array p a \<equiv> do {
  (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let ac = ac + (if (((length (p!i)) > 0) \<and> ((p!i!0) = a)) then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma win_count_imp_array_refine:
  shows "win_count_imp_array pl a \<le> \<Down>Id (win_count_imp' pl a)"
  unfolding win_count_imp_array_def win_count_imp'_def winsr_imp'_def
  apply (refine_rcg)
  apply (refine_dref_type)
  using assms by (safe, simp_all)+
  

lemma a_l_r_step: "(pl_to_pr_\<alpha> \<circ> pa_to_pl) = pa_to_pr"
  by (simp add: fun_comp_eq_conv pa_to_pr_def)
  
lemma win_count_imp_array_correct:
  assumes "(pa, pr) \<in> br pa_to_pr (profile_a A)" and aA: "a \<in> A"
  shows "win_count_imp_array pa a \<le> SPEC (\<lambda>ac. ac = win_count pr a)"
  using assms ref_two_step[OF win_count_imp_array_refine win_count_imp'_correct]
  by (metis in_br_conv pa_to_pr_def profile_a_l refine_IdD)



(* TODO correctness proof *)

definition "wc_fold l a \<equiv> do {
  (ac,a) \<leftarrow> nfoldli l (\<lambda>_. True) 
    (\<lambda>x (ac, a). do {
     if ((length x > 0) \<and> (x!0 = a))then RETURN (ac+1,a) else RETURN (ac,a)
    }) 
    (0,a);
  RETURN ac
}"


sepref_register wc_fold

sepref_definition win_count_imp_sep is
  "uncurry wc_fold" :: "(list_assn (array_assn nat_assn))\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn)"
  unfolding wc_fold_def[abs_def]  short_circuit_conv 
  apply sepref_dbg_keep 
  done


definition win_count_list_top_mon :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_list_top_mon p a \<equiv> do {
  (i, ac) \<leftarrow> WHILEIT (wc_list_invar p a) (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let ballot = (p!i);
    winadd \<leftarrow>
       (if (0 < length ballot)
        then do {
        ASSERT (0 < (length ballot));
        let top = ballot!0;
        if (top = a) then 
         RETURN (ac + 1) 
         else 
         RETURN ac
        }
       else 
         RETURN ac);
    let i = i + 1;
    RETURN (i, winadd)
  })(0,0);
  RETURN ac
}"

sepref_register win_count_list_top_mon

sepref_definition win_count_imp_sep_alt is
  "uncurry win_count_list_top_mon" :: "(list_assn (list_assn nat_assn))\<^sup>k *\<^sub>a (nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn)"
  unfolding win_count_list_top_mon_def[abs_def] wc_list_invar_def[abs_def]  
  apply sepref_dbg_keep
  done

lemma win_count_list_top_refine_sep: 
  shows "(win_count_list_top_mon, win_count_list_r) \<in>
      Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding win_count_list_top_mon_def win_count_list_r_def wc_list_invar_def
  apply (refine_vcg)
        apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
        apply (auto simp add: rank_mon_correct index_eqI refine_rel_defs)
proof (-)
  fix p::"'a Profile_List"
  fix idx::nat
  fix alt::'a
  assume ir: "idx < length p"
  assume mem: "alt \<in> set(p!idx)"
  assume nfst: "p ! idx ! 0 \<noteq> alt"
  from nfst mem show "0 < index (p ! idx) alt"
    by (metis gr0I nth_index)
next  
  fix p::"'a Profile_List"
  fix idx::nat
  fix alt::'a
  assume ir: "idx < length p"
  assume "p ! idx ! 0 \<notin> set (p ! idx)"
  from this show "(p ! idx)= []"
    by (metis hd_conv_nth list.set_sel(1))
qed


definition win_count_imp_array :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"win_count_imp_array p a \<equiv> do {
  (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let ac = ac + (if (((length (p!i)) > 0) \<and> ((p!i!0) = a)) then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"


text \<open>
  pref count
\<close>

definition  "prefer_count_invariant p x y \<equiv> \<lambda>(r, ac).
      r \<le> length p \<and>
      ac = card {i::nat. i < r \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

definition prefer_count_mon :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "prefer_count_mon p x y \<equiv> do {
   (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let b = (p!i);
    let ac = ac + (if y \<preceq>\<^sub>b x then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma prefer_count_mon_correct:
  shows "prefer_count_mon p a b \<le> SPEC (\<lambda> wc. wc = prefer_count p a b)"
  unfolding prefer_count_mon_def prefer_count.simps
  apply (intro WHILET_rule[where I="(prefer_count_invariant p a b)"
        and R="measure (\<lambda>(r,_). (length p) - r)"] refine_vcg)
  unfolding prefer_count_invariant_def
      apply (simp_all)
   apply refine_vcg
  apply (erule subst)
  apply (simp)
proof (simp_all)
  fix r
  assume ir: "r < length p"
  assume blpa: "(b, a) \<in> p!r"
  with blpa have prep: 
         "{i. i < Suc r \<and> (b, a) \<in> p ! i} 
        = {i. i < r \<and> (b, a) \<in> p ! i} \<union> {r}"
    by fastforce
  thus "Suc (card {i. i < r \<and> (b, a) \<in> p ! i}) = card {i. i < Suc r \<and> (b, a) \<in> p ! i}"
    by fastforce
next
  fix r
  assume ir: "r < length p"
  assume bnlpa: "(b, a) \<notin> p!r"
  with bnlpa ir show prep: 
         "card {i. i < r \<and> (b, a) \<in> p ! i} 
        = card {i. i < Suc r \<and> (b, a) \<in> p ! i} "
    using less_Suc_eq by metis    
qed  


definition prefer_count_mon_list :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where
  "prefer_count_mon_list p x y \<equiv> do {
   (i, ac) \<leftarrow> WHILET (\<lambda>(i, _). i < length p) (\<lambda>(i, ac). do {
    ASSERT (i < length p);
    let b = (p!i);
    let ac = ac + (if y \<lesssim>\<^sub>b x then 1 else 0);
    let i = i + 1;
    RETURN (i, ac)
  })(0,0);
  RETURN ac
}"

lemma prefer_count_mon_list_refine:
  assumes "(pl,pr)\<in>br pl_to_pr_\<alpha> (profile_l A)"
  shows "prefer_count_mon_list pl a b \<le> \<Down>Id (prefer_count_mon pr a b)"
    using assms unfolding prefer_count_mon_list_def prefer_count_mon_def pl_to_pr_\<alpha>_def
  apply (refine_rcg)
  apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
  apply (auto simp add: refine_rel_defs) unfolding pl_\<alpha>_def is_less_preferred_than.simps
  by auto

end