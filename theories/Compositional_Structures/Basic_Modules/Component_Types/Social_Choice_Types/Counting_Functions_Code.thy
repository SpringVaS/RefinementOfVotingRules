theory Counting_Functions_Code
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
  Refine_Imperative_HOL.IICF
  RefinementList
begin

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
  by (refine_vcg rank_mon_correct, simp)

sepref_definition rank_imp_sep
  is "uncurry rank_mon" :: "((array_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn)"
  unfolding rank_mon_def[abs_def] index_mon_def[abs_def]
  by sepref


section \<open>Monadic implementation of counting functions \<close>

text \<open>
  win-count, multiple refinement steps
\<close>

definition "wc_invar_fe p0 a \<equiv> \<lambda>(xs,ac).
  xs = drop (length p0 - length xs) p0 \<and>
  ac = card {i. i < (length p0 - length xs) \<and> above (p0!i) a = {a}}"

definition wc_foreach:: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"wc_foreach p a \<equiv> do {
  (xs,ac) \<leftarrow> WHILEIT (wc_invar_fe p a) (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body (\<lambda>x (ac).
     if (above x a = {a}) then RETURN (ac+1) else RETURN (ac)
    )) (p,0);
  RETURN ac
}"

lemma wc_foreach_correct:
  shows "wc_foreach p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  unfolding wc_foreach_def wc_invar_fe_def
  FOREACH_cond_def FOREACH_body_def
  apply (intro WHILEIT_rule[where R="measure (\<lambda>(xs,_). length xs)"]  refine_vcg)
  apply (safe, simp_all)
  apply (metis append_Nil diff_le_self drop_Suc drop_all drop_append length_drop tl_drop)
proof (-)
  fix xs:: "'a Profile"
  assume headr: "xs = drop (length p - length xs) p"
  assume pnemp: "xs \<noteq> []"
  from pnemp headr have hdidx: "hd xs = (p!(length p - length xs))"
    by (metis drop_eq_Nil hd_drop_conv_nth linorder_not_le)
  assume atop: "above (hd xs) a = {a}"
  from hdidx this have aba: "above (p!(length p - length xs)) a = {a}" by simp
  from this aba have comp: "{i. i \<le> (length p) - length xs \<and> above (p ! i) a = {a}} 
        = ({i. i < length p - length xs \<and> above (p ! i) a = {a}} \<union> 
          {(length p - length xs)})"
    by fastforce
  from headr have "{i. i \<le> (length p) - length xs \<and> above (p ! i) a = {a}} 
        = {i. i < Suc (length p) - length xs \<and> above (p ! i) a = {a}}"
    by (metis Suc_diff_le diff_le_self length_drop less_Suc_eq_le)
  from this comp have "{i. i < Suc (length p) - length xs \<and> above (p ! i) a = {a}} 
        = ({i. i < length p - length xs \<and> above (p ! i) a = {a}} \<union> 
          {(length p - length xs)})" by simp
  from this show   
         "Suc (card {i. i < (length p) - length xs \<and> above (p ! i) a = {a}}) =
        card {i. i < Suc (length p) - length xs \<and> above (p ! i) a = {a}}"
    by fastforce
next
  fix xs:: "'a Profile"
  fix alt:: "'a"
  assume headr: "xs = drop (length p - length xs) p"
  show "tl xs = drop (Suc (length p) - length xs) p"
    by (metis Suc_diff_le diff_le_self drop_Suc headr length_drop tl_drop)
next
  fix xs:: "'a Profile"
  fix alt:: "'a"
  assume headr: "xs = drop (length p - length xs) p"
  assume pnemp: "xs \<noteq> []"
  from pnemp headr have hdidx: "hd xs = (p!(length p - length xs))"
    by (metis drop_eq_Nil hd_drop_conv_nth linorder_not_le)
  assume xtop: "alt \<in>  above (hd xs) a"
  assume xna: "alt \<noteq> a"
  from hdidx headr xna xtop show   
         "card {i. i < (length p) - length xs \<and> above (p ! i) a = {a}} =
        card {i. i < Suc (length p) - length xs \<and> above (p ! i) a = {a}}"
  by (metis  Suc_diff_le diff_le_self insert_absorb insert_iff insert_not_empty length_drop less_Suc_eq )
next
    fix xs:: "'a Profile"
  fix alt:: "'a"
  assume headr: "xs = drop (length p - length xs) p"
  from headr show "tl xs = drop (Suc (length p) - length xs) p"
    by (metis Suc_diff_le diff_le_self drop_Suc length_drop tl_drop)
next
    fix xs:: "'a Profile"
  fix alt:: "'a"
  assume headr: "xs = drop (length p - length xs) p"
  assume pnemp: "xs \<noteq> []"
  from pnemp headr have hdidx: "hd xs = (p!(length p - length xs))"
    by (metis drop_eq_Nil hd_drop_conv_nth linorder_not_le)
  assume xtop: "a \<notin>  above (hd xs) a"
  from hdidx this have aba: "above (p!(length p - length xs)) a \<noteq> {a}"
    by fastforce
  from this show   
         "card {i. i < (length p) - length xs \<and> above (p ! i) a = {a}} =
        card {i. i < Suc (length p) - length xs \<and> above (p ! i) a = {a}}"
    by (metis Suc_diff_le diff_le_self headr length_drop less_Suc_eq)
qed
  

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


schematic_goal wc_code_aux: "RETURN ?wc_code \<le> wc_foreach p a"
  unfolding wc_foreach_def FOREACH_body_def FOREACH_cond_def
  by (refine_transfer)

concrete_definition win_count_code for p a uses wc_code_aux

thm win_count_code_def


lemma win_count_equiv: 
  shows "win_count p a = win_count_code p a"
proof -
  from order_trans[OF win_count_code.refine wc_foreach_correct] 
    have "win_count_code p a = win_count p a"
      by fastforce
  thus ?thesis by simp
qed



lemma carde: assumes prof: "profile A p"
  shows "\<forall>ballot \<in> set p. (rank ballot a = 1) = (above ballot a = {a})" 
  using prof
  by (metis above_rank profile_set)

lemma cardei: assumes prof: "profile A p"
  shows "\<forall>i < length p. let ballot=(p!i) in ((rank ballot a = 1) = (above ballot a = {a}))" 
  using prof
  by (metis carde nth_mem)

definition "f_inner_rel a \<equiv> (\<lambda>(x::'a Preference_Relation) (ac::nat).
     (if (rank x a = 1) then RETURN (ac+1) else RETURN (ac)
    ))"

definition wc_foreach_rank:: "'a Profile \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"wc_foreach_rank p a \<equiv> do {
  (xs,ac) \<leftarrow> WHILET (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body (f_inner_rel a)) (p,0::nat);
  RETURN ac
}"


lemma wc_foreach_rank_refine:
  assumes prof: "profile A p"
  shows "wc_foreach_rank p a \<le> \<Down> nat_rel (wc_foreach p a)"
  unfolding wc_foreach_rank_def wc_foreach_def wc_invar_fe_def FOREACH_body_def FOREACH_cond_def 
    f_inner_rel_def
  apply (refine_vcg)
    apply (refine_dref_type) \<comment> \<open>Type-based heuristics to instantiate data 
    refinement goals\<close>
proof (clarsimp_all simp del: rank.simps)
  fix x1:: "'a Profile"
  assume x1ne: "x1 \<noteq> []"
  assume rest: "x1 = drop (length p - length x1) p"
  from x1ne rest show "(rank (hd x1) a = Suc 0) = (above (hd x1) a = {a})" using carde
    by (metis One_nat_def in_set_dropD list.set_sel(1) prof rank.simps)
qed

lemma rank_refaux:
  assumes prof: "profile A p"
  shows "wc_foreach_rank p a \<le> (wc_foreach p a)"
  using prof wc_foreach_rank_refine
  by (metis refine_IdD) 

theorem wc_foreach_rank_correct:
  assumes prof: "profile A p"
  shows "wc_foreach_rank p a \<le> SPEC (\<lambda> wc. wc = win_count p a)"
  using assms ref_two_step[OF wc_foreach_rank_refine wc_foreach_correct]
  by fastforce


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
  and ne: "length pl > 0"
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





definition "f_inner_list a \<equiv> (\<lambda>x ac::nat.
     (if (rank_l x a = 1) then RETURN (ac+1) else RETURN (ac)))"


definition "wc_list_invar p0 a \<equiv> \<lambda>(i,ac::nat).
  0 \<le> i \<and> i \<le> length p0"

definition "wc_list_invar' p0 a \<equiv> \<lambda>(xs,ac).
  xs = drop (length p0 - length xs) p0"


lemma innerf_eq:
  fixes A:: "'a set"  and l :: "'a Preference_List" and a :: 'a
  assumes "(l,r) \<in> ballot_rel"
  shows "f_inner_list a l n \<le> \<Down> nat_rel (f_inner_rel a r n)"
  unfolding f_inner_list_def f_inner_rel_def
  apply (refine_vcg)
  using assms rankeq
  by (metis in_br_conv)

lemma foreachrel:
  assumes "(pl, pr) \<in> profile_rel" and "pl \<noteq> []"
  shows "(hd pl, hd pr) \<in> (ballot_rel) \<and> 
  (tl pl, tl pr) \<in> (profile_rel)"
  using assms
  by (metis list.collapse list_rel_simp(2) list_rel_simp(4))


     
definition wc_foreach_list_rank :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where
"wc_foreach_list_rank pl a \<equiv> do {
  (xs,ac) \<leftarrow> WHILET (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body (f_inner_list a)) (pl,0::nat);
  RETURN ac
}"

lemma initrel: 
  fixes A:: "'a set"
  assumes "(pl, pr) \<in> profile_rel"
  shows "((pl,0::nat), pr , 0::nat) \<in> ((profile_rel \<times>\<^sub>r nat_rel))"
  using assms
  by simp 


lemma wc_foreach_list_rank_refine: 
  fixes A:: "'a set"
  shows "(wc_foreach_list_rank, wc_foreach_rank) \<in> 
  profile_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding wc_foreach_list_rank_def wc_foreach_rank_def 
  FOREACH_cond_def FOREACH_body_def
  apply (refine_vcg initrel)
     apply (simp add: initrel)
  apply refine_dref_type
     apply (simp add: refine_rel_defs)
     apply blast
  apply clarsimp_all
  using innerf_eq
  apply (metis param_hd refine_IdD)
  using foreachrel by (metis)

lemma win_count_list_r_refine_os: 
  fixes A:: "'a set"
  assumes "(pl, pr) \<in> (profile_rel)"
  shows "wc_foreach_list_rank pl a \<le> \<Down> Id (wc_foreach_rank pr a)"
  unfolding wc_foreach_list_rank_def wc_foreach_rank_def 
  FOREACH_cond_def FOREACH_body_def
  using assms apply (refine_vcg wc_foreach_list_rank_refine initrel)
  apply (simp_all only: refine_rel_defs pl_to_pr_\<alpha>_def)
  apply refine_dref_type
     apply (clarsimp_all, safe)
  using innerf_eq
   apply (metis (mono_tags, lifting) brI list.rel_sel refine_IdD)
  using foreachrel
  using list.rel_sel by blast
  

lemma wc_foreach_list_rank_correct:
  assumes "(pl, pr) \<in> profile_rel" and "profile_l A pl"
  shows "wc_foreach_list_rank pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
proof (-)
  from assms have "profile A pr" using profileref
    by (metis (mono_tags, opaque_lifting) fun_relD1 pair_in_Id_conv set_rel_id_simp) 
  from assms(1) this 
  show "wc_foreach_list_rank pl a \<le> (SPEC (\<lambda>wc. wc = win_count pr a))"
  using ref_two_step[OF win_count_list_r_refine_os wc_foreach_rank_correct] refine_IdD
  by (metis)
qed

lemma top_rank1:
  assumes ballot: "ballot_on A ballot" and "length ballot > 0"
  shows "ballot!0 = a \<longleftrightarrow> rank_l ballot a = 1"
  using assms 
  apply clarsimp
  apply safe
    apply (simp add: index_eq_iff)
   apply (metis nth_index)
  by simp 
  

definition wc_foreach_top:: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"wc_foreach_top p  a \<equiv> do {
  (xs::'a Profile_List,ac) \<leftarrow> WHILET (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body (\<lambda>x (ac).
     if ((length x > 0) \<and> (x!0 = a)) then RETURN (ac+1) else RETURN (ac)
    )) (p,0);
  RETURN ac
}"

lemma wc_foreach_top_refine_os: 
  fixes A:: "'a set"
  assumes "profile_l A pl"
  shows "wc_foreach_top pl a \<le> \<Down> Id (wc_foreach_list_rank pl a)"
  unfolding wc_foreach_list_rank_def f_inner_list_def wc_foreach_top_def 
  FOREACH_cond_def FOREACH_body_def
  using assms apply (refine_vcg wc_foreach_list_rank_refine initrel)
  apply (simp_all only: refine_rel_defs pl_to_pr_\<alpha>_def)
  apply refine_dref_type
  apply auto
   apply (metis gr0I index_first)
  by (metis index_eq_iff length_pos_if_in_set)

lemma wc_foreach_top_correct:
  assumes "(pl, pr) \<in> profile_rel" and "profile_l A pl"
  shows "wc_foreach_top pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using assms ref_two_step[OF wc_foreach_top_refine_os wc_foreach_list_rank_correct] refine_IdD 
  by (metis) 

definition wc_fold:: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat nres" 
  where "wc_fold l a \<equiv> 
   nfoldli l (\<lambda>_. True) 
    (\<lambda>x (ac). 
     if ((length x > 0) \<and> (x!0 = a))then RETURN (ac+1) else RETURN (ac)
    ) 
    (0)"

lemma wc_fold_refine:
  shows "wc_fold pl a \<le> \<Down> Id (wc_foreach_top pl a)"
  unfolding wc_fold_def wc_foreach_top_def
  by (simp add: nfoldli_while while.WHILET_def)

theorem wc_fold_correct:
  assumes "(pl, pr) \<in> profile_rel" and "profile_l A pl"
  shows "wc_fold pl a \<le> SPEC (\<lambda> wc. wc = win_count pr a)"
  using assms ref_two_step[OF wc_fold_refine wc_foreach_top_correct] refine_IdD 
  by (metis) 

lemma nfwcc: "nofail (wc_fold p a)"
  unfolding wc_fold_def 
  apply (induction p rule: rev_induct, simp)
   apply simp
  by (simp add: pw_bind_nofail)

text \<open>
  pref count
\<close>

definition  "prefer_count_invariant p x y \<equiv> \<lambda>(r, ac).
      r \<le> length p \<and>
      ac = card {i::nat. i < r \<and> (let r = (p!i) in (y \<preceq>\<^sub>r x))}"

definition "pc_invar_fe p0 a b \<equiv> \<lambda>(xs,ac).
  xs = drop (length p0 - length xs) p0 \<and>
  ac = card {i::nat. i < (length p0 - length xs) \<and> (let r = (p0!i) in (b \<preceq>\<^sub>r a))}"

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


definition pc_foreach:: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"pc_foreach p a b \<equiv> do {
  (xs,ac) \<leftarrow> WHILEIT (pc_invar_fe p a b) (FOREACH_cond (\<lambda>_.True)) 
    (FOREACH_body (\<lambda>x (ac).
     if (b \<preceq>\<^sub>x a) then RETURN (ac+1) else RETURN (ac)
    )) (p,0);
  RETURN ac
}"


definition pc_foldli:: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"pc_foldli p a b \<equiv>
 nfoldli p (\<lambda>_.True)  
     (\<lambda>x (ac).
     if (b \<preceq>\<^sub>x a) then RETURN (ac+1) else RETURN (ac)
    ) (0::nat)"

lemma pc_foldli_correct:
  shows "pc_foldli p a b \<le> SPEC (\<lambda> wc. wc = prefer_count p a b)"
  unfolding pc_foldli_def
  apply (intro nfoldli_rule[where I="\<lambda> proc xs ac. 
    ac = card {i::nat. i < length proc \<and> (let r = (p!i) in (b \<preceq>\<^sub>r a))}"]  refine_vcg)
  apply (auto)
proof (-)
  fix l1:: "'a Profile"
  fix l2:: "'a Profile"
  fix x:: "'a Preference_Relation"
  assume "p = l1 @ x # l2"
  assume blpa: "(b, a) \<in> x" 
  have pnemp: "l1 @ x # l2 \<noteq> []" by simp
  have xatl1: "(l1 @ x # l2) ! (length l1) = x"
    by simp
  from xatl1 blpa have stone: "{i. i \<le>(length l1) \<and> (b, a) \<in> (l1 @ x # l2) ! i} 
        = {i. i < length l1 \<and> (b, a) \<in> (l1 @ x # l2) ! i} \<union> 
        {length l1}"
    by fastforce
  from this have "{i. i < Suc (length l1) \<and> (b, a) \<in> (l1 @ x # l2) ! i} =
  ({i. i < length l1 \<and> (b, a) \<in> (l1 @ x # l2) ! i} \<union> {length l1})"
    using less_Suc_eq_le
    by blast 
  from this show "Suc(card {i. i < length l1 \<and> (b, a) \<in> (l1 @ x # l2) ! i}) =
      card {i. i < Suc (length l1) \<and> (b, a) \<in> (l1 @ x # l2) ! i}"
    by fastforce
next
  fix l1:: "'a Profile"
  fix l2:: "'a Profile"
  fix x:: "'a Preference_Relation"
  assume "p = l1 @ x # l2"
  assume blpa: "(b, a) \<notin> x" 
  have pnemp: "l1 @ x # l2 \<noteq> []" by simp
  have xatl1: "(l1 @ x # l2) ! (length l1) = x"
    by simp
  from xatl1 blpa have stone: "{i. i < Suc (length l1) \<and> (b, a) \<in> (l1 @ x # l2) ! i} 
        = {i. i < length l1 \<and> (b, a) \<in> (l1 @ x # l2) ! i}"
    using less_Suc_eq_le order_le_less by blast
  thus "card {i. i < length l1 \<and> (b, a) \<in> (l1 @ x # l2) ! i} =
       card {i. i < Suc (length l1) \<and> (b, a) \<in> (l1 @ x # l2) ! i}"
    by fastforce
qed

lemma pc_foreach_correct:
  shows "pc_foreach p a b \<le> SPEC (\<lambda> wc. wc = prefer_count p a b)"
  unfolding pc_foreach_def pc_invar_fe_def
  FOREACH_cond_def FOREACH_body_def
  apply (intro WHILEIT_rule[where R="measure (\<lambda>(xs,_). length xs)"] FOREACHoi_rule refine_vcg)
  apply (auto)
     apply (metis Suc_diff_le diff_le_self drop_Suc length_drop tl_drop)
  proof (-)
    fix aa:: "'a Profile"
    assume last: "aa = drop (length p - length aa) p"
  assume pnemp: "aa \<noteq> []"
  assume hdr: "(b, a) \<in> hd aa"
  from last pnemp have hdidx: "hd aa = (p!(length p - length aa))"
    by (metis drop_eq_Nil hd_drop_conv_nth linorder_not_less)
  from hdidx hdr have aba: "(b, a) \<in> (p!(length p - length aa))" by simp
  from pnemp aba have prep: 
         "{i. i \<le> (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = {i. i < length p - length aa \<and> (b, a) \<in> p ! i} \<union> {(length p) - length aa}"
    by fastforce
  from last have "{i. i \<le> (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = {i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i}"
    by (metis Suc_diff_le diff_le_self length_drop less_Suc_eq_le)
  from this prep have "{i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = ({i. i < length p - length aa \<and> (b, a) \<in> p ! i} \<union> 
          {(length p - length aa)})" by simp
  from pnemp this show "Suc (card {i. i < length p - length aa \<and> (b, a) \<in> p ! i}) =
          card {i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i}"
    by fastforce
next
  fix xs:: "'a Profile"
  fix alt:: "'a"
  assume headr: "xs = drop (length p - length xs) p"
  show "tl xs = drop (Suc (length p) - length xs) p"
    by (metis Suc_diff_le diff_le_self drop_Suc headr length_drop tl_drop)
next
  fix aa:: "'a Profile"
  assume last: "aa = drop (length p - length aa) p"
  assume pnemp: "aa \<noteq> []"
  assume hdr: "(b, a) \<notin> hd aa"
  from last pnemp have hdidx: "hd aa = (p!(length p - length aa))"
    by (metis drop_eq_Nil hd_drop_conv_nth linorder_not_less)
  from hdidx hdr have aba: "(b, a) \<notin> (p!(length p - length aa))" by simp
  from pnemp aba have prep: 
         "{i. i \<le> (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = {i. i < length p - length aa \<and> (b, a) \<in> p ! i}"
    using order_le_less by blast   
  from last have "{i. i \<le> (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = {i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i}"
    by (metis Suc_diff_le diff_le_self length_drop less_Suc_eq_le)
  from this prep have "{i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i} 
        = ({i. i < length p - length aa \<and> (b, a) \<in> p ! i})" by simp
  from this show " card {i. i < length p - length aa \<and> (b, a) \<in> p ! i} =
          card {i. i < Suc (length p) - length aa \<and> (b, a) \<in> p ! i}" 
    by simp
qed

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

text \<open> Data refinement \<close>



definition pc_foldli_list:: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"pc_foldli_list p a b \<equiv> 
  nfoldli p (\<lambda>_.True)  
     (\<lambda>x (ac).
     if (b \<lesssim>\<^sub>x a) then RETURN (ac+1) else RETURN (ac)
    ) (0::nat)"


lemma pc_foreach_list_list_refine:
  shows "(pc_foldli_list, pc_foldli)
    \<in> profile_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  apply (auto simp del : is_less_preferred_than.simps)
  apply (rename_tac pl pr a b)
  unfolding pc_foldli_list_def pc_foldli_def
  apply (refine_vcg nfoldli_rule)
  apply (auto simp del : is_less_preferred_than_l.simps is_less_preferred_than.simps)
  apply (rename_tac l r)
  apply (metis in_br_conv less_preffered_l_rel_eq)+
  done

end