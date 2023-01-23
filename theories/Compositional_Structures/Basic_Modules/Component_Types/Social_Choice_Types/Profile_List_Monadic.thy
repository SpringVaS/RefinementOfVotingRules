theory Profile_List_Monadic
  imports "Verified_Voting_Rule_Construction.Profile"
    "Verified_Voting_Rule_Construction.Profile_List"
    Ballot_Refinement
    Refine_Imperative_HOL.IICF
  
begin


fun win_count_l :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "win_count_l p a = fold (\<lambda>x ac. 
     if (0 < length x \<and> x!0 = a) then (ac+1) else (ac)) p 0"


text \<open> Monadic definition of profile functions \<close>

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
  shows "(rank_mon, (\<lambda> ballot a. RETURN (rank_l ballot a)))\<in> Id \<rightarrow> Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  by (refine_vcg rank_mon_correct, simp)

sepref_definition rank_imp_sep
  is "uncurry rank_mon" :: "((arl_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn)"
  unfolding rank_mon_def[abs_def] index_mon_def[abs_def]
  by sepref


definition is_less_preferred_than_mon :: "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool nres" where
"is_less_preferred_than_mon a pl b \<equiv> do {
  ra <- rank_mon pl a;
  rb <- rank_mon pl b;
  RETURN ((ra > 0) \<and> (rb > 0) \<and> (ra \<ge> rb))
}"

lemma ilpm_list_correct:
  shows "is_less_preferred_than_mon a pl b \<le> 
      SPEC (\<lambda> lp. lp =  is_less_preferred_than_l a pl b)" 
  unfolding is_less_preferred_than_mon_def is_less_preferred_than_l.simps 
  apply (refine_vcg rank_mon_correct)
  by (auto simp add: in_set_member)

sepref_definition ilp_sep
  is "uncurry2 is_less_preferred_than_mon" :: 
    "(nat_assn\<^sup>k *\<^sub>a (array_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
  unfolding is_less_preferred_than_mon_def rank_mon_def[abs_def] index_mon_def[abs_def]
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
     RETURN (if ((length x > 0) \<and> (x!0 = a))then (ac+1) else  (ac))
    ) 
    (0)"

lemma wc_fold_refine:
  shows "wc_fold pl a \<le> \<Down> Id (wc_foreach_top pl a)"
  unfolding wc_fold_def wc_foreach_top_def
  by (simp add: nfoldli_mono(1) while_eq_nfoldli)

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

lemma win_count_l_correct:
  shows "(win_count_l, win_count)
    \<in> (profile_on_A_rel A) \<rightarrow> Id \<rightarrow> nat_rel"
  apply (auto simp del: win_count_l.simps win_count.simps)
  apply (rename_tac pl pr)
proof (standard, rename_tac a)
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a:: 'a
  assume prel: "(pl, pr) \<in> (profile_on_A_rel A)"
  from prel have profrel: "(pl, pr) \<in> profile_rel" using profile_type_ref by fastforce
  from prel have profprop: "profile_l A pl" using profile_prop_list by fastforce
  have  "RETURN (win_count_l pl a) = (wc_fold pl a)"
  unfolding  wc_fold_def win_count_l.simps
  using fold_eq_nfoldli[where l = pl and f = "(\<lambda>x ac. if (0 < length x \<and> x ! 0 = a)
       then ac + 1 else ac)" and s = 0]
  by fastforce
  from this profrel profprop have meq: "RETURN (win_count_l pl a) = RETURN (win_count pr a)"
  using wc_fold_correct[where pl=pl and pr = pr and A = A and a = a]
    by (metis mem_Collect_eq nres_order_simps(21))
  from meq show "win_count_l pl a = win_count pr a"
    by simp
qed
  

text \<open>
  pref count
\<close>


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
proof (clarsimp_all)
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

text \<open> Data refinement \<close>

find_theorems "fold"

fun prefer_count_l :: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_l p a b = fold (\<lambda> x ac. (if (b \<lesssim>\<^sub>x a) then (ac+1) else (ac))) p 0"

fun wins_l :: "'a \<Rightarrow> 'a Profile_List \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins_l x p y =
    (prefer_count_l p x y > prefer_count_l p y x)"



fun condorcet_winner_l :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner_l A p w =
      (finite A \<and> profile_l A p \<and>  w \<in> A \<and> (\<forall> x \<in> A - {w} . wins_l w p x))"

definition pc_foldli_list:: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"pc_foldli_list p a b \<equiv> 
  nfoldli p (\<lambda>_.True)  
      (\<lambda> x ac. RETURN  (if (b \<lesssim>\<^sub>x a) then (ac+1) else (ac)))
     (0::nat)"

lemma pc_fold_monad_eq: 
  shows "RETURN (prefer_count_l p a b) = pc_foldli_list p a b"
  unfolding  pc_foldli_list_def
  using fold_eq_nfoldli
  by fastforce


lemma pc_foldli_list_refine:
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

lemma pc_foldli_list_correct:
  shows "(pc_foldli_list, (\<lambda> p a b. SPEC (\<lambda> wc. wc = prefer_count p a b)))
    \<in> profile_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  apply(refine_vcg) 
  apply (clarsimp_all simp del: prefer_count.simps)
  apply (rename_tac pl pr a b)
proof -
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a :: 'a
  fix b :: 'a
  assume profr: "(pl, pr) \<in> profile_rel"
  note ref_two_step[OF pc_foldli_list_refine[THEN fun_relD, THEN fun_relD,
          THEN fun_relD, THEN nres_relD]
            pc_foldli_correct, where x5 = pl and p1=pr and x4 = a and a1 = a
             and x3 = b and b1 = b] 
refine_IdD
  from profr this show "pc_foldli_list pl a b \<le> RES {prefer_count pr a b}"
    by fastforce
qed

definition prefer_count_monadic_imp:: "'a Profile_List \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat nres" where 
"prefer_count_monadic_imp p a b \<equiv> 
  nfoldli p (\<lambda>_.True) (\<lambda> x ac. 
  do {
    b_less_a <- is_less_preferred_than_mon b x a;
    RETURN  (if b_less_a then (ac+1) else (ac)) 
  }) (0::nat)"

lemma prefer_count_monadic_imp_refine:
  shows "(prefer_count_monadic_imp, pc_foldli_list) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  unfolding prefer_count_monadic_imp_def pc_foldli_list_def
  apply (refine_vcg ilpm_list_correct)
  apply (refine_dref_type)
  by auto

theorem prefer_count_monadic_imp_correct:
  assumes "(pl, pr) \<in> profile_rel"
  shows "prefer_count_monadic_imp pl a b \<le> SPEC (\<lambda> pc. pc = prefer_count pr a b)"
  using assms(1) ref_two_step[OF prefer_count_monadic_imp_refine [THEN fun_relD,THEN fun_relD,THEN fun_relD,THEN nres_relD] 
      pc_foldli_list_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD,THEN nres_relD,THEN refine_IdD],
      where x10 = pl and x5 = pl and x'5 = pr] refine_IdD
  by (metis IdI)

lemma prefer_count_monadic_correct_rel:
  shows "(prefer_count_monadic_imp, RETURN ooo prefer_count)
    \<in> profile_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (refine_vcg)
  apply clarify
  using  prefer_count_monadic_imp_correct SPEC_eq_is_RETURN(2) comp_apply refine_IdI
  by (metis)
  
  

definition wins_monadic :: "'a \<Rightarrow> 'a Profile_List \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "wins_monadic x p y \<equiv> do {
    pxy <- prefer_count_monadic_imp p x y;
    pyx <- prefer_count_monadic_imp p y x;
    RETURN (pxy > pyx)
}"


lemma prefer_count_l_correct:
  shows "(prefer_count_l, prefer_count)
    \<in> profile_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> nat_rel"
  apply (auto simp del: prefer_count_l.simps prefer_count.simps)
  apply (rename_tac pl pr)
proof (standard, standard, rename_tac a b)
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a:: 'a and b:: 'a
  assume "(pl, pr) \<in> profile_rel"
  from this have meq: "RETURN (prefer_count_l pl a b) = RETURN (prefer_count pr a b)"
    using pc_fold_monad_eq[where p = pl and a=a and b=b]
        pc_foldli_list_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD,THEN nres_relD, 
        where x3 = pl and x'3=pr and x2 = a and x'2 = a
             and x1 = b and x'1 = b]
    by (metis (full_types) RETURN_ref_SPECD pair_in_Id_conv)
  from meq show "prefer_count_l pl a b = prefer_count pr a b"
    by simp
qed

lemma wins_monadic_correct:
  shows "(wins_monadic, RETURN ooo wins) \<in> Id \<rightarrow> profile_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding wins_monadic_def wins.simps
  apply (clarsimp simp del: prefer_count.simps)
  apply (refine_vcg prefer_count_monadic_imp_correct)
  by (auto)  

sepref_definition wins_imp is "uncurry2 wins_monadic" ::
  "(nat_assn\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn )"
  unfolding wins_monadic_def prefer_count_monadic_imp_def is_less_preferred_than_mon_def
  rank_mon_def index_mon_def
  apply sepref_dbg_keep
  done

lemma wins_l_correct:
  shows "(wins_l, wins)
    \<in> Id \<rightarrow> profile_rel \<rightarrow> Id \<rightarrow> bool_rel"
  apply(refine_vcg)
proof (clarsimp simp del: prefer_count_l.simps prefer_count.simps, rename_tac a pl pr b, safe)
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a:: 'a and b:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "prefer_count_l pl b a < prefer_count_l pl a b"
  note eq = prefer_count_l_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD, 
        where x2= pl and x'2=pr]
  from eq a1 have "\<forall> alt1 alt2. prefer_count_l pl alt1 alt2 = prefer_count pr alt1 alt2 "
    by blast   
  from a2 this show  "prefer_count pr b a < prefer_count pr a b"
    by fastforce
next 
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix a:: 'a and b:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "prefer_count pr b a < prefer_count pr a b"
  note eq = prefer_count_l_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD, 
        where x2= pl and x'2=pr]
  from eq a1 have "\<forall> alt1 alt2. prefer_count_l pl alt1 alt2 = prefer_count pr alt1 alt2 "
    by blast   
  from a2 this show  "prefer_count_l pl b a < prefer_count_l pl a b"
    by fastforce
qed

lemma condorcet_winner_l_correct:
  shows "(condorcet_winner_l, condorcet_winner)
    \<in> \<langle>Id\<rangle>set_rel \<rightarrow> profile_rel \<rightarrow> Id \<rightarrow> bool_rel"
  apply (refine_vcg)
  apply (clarsimp simp del : wins_l.simps wins.simps)
proof (rename_tac A pl pr alt, safe)
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix A:: "'a set" and alt:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "profile_l A pl"
  note winc = wins_l_correct[unfolded fref_def, THEN fun_relD, THEN fun_relD,THEN fun_relD,
      where x2 = alt and x'2 = alt and x1 = pl and x'1 = pr]
  note profr = profileref[THEN fun_relD, THEN fun_relD,
      where x1 = A and x'1 = A and x = pl and x' = pr]
  from a1 a2 profr show "(profile A pr)"
    by simp
next
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix A:: "'a set" and alt:: 'a
  fix con:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "con \<in> A"
  assume a3: "\<not> wins alt pr con"
  assume altwins: "\<forall>x\<in>A - {alt}. wins_l alt pl x"
  note winc = wins_l_correct[unfolded fref_def, THEN fun_relD, THEN fun_relD,THEN fun_relD,
      where x2 = alt and x'2 = alt and x1 = pl and x'1 = pr]
  from a1 a3 winc have "\<not> wins_l alt pl con" by blast
  from altwins a2 this show "con = alt" by blast
next
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix A:: "'a set" and alt:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "profile A pr"
  note winc = wins_l_correct[unfolded fref_def, THEN fun_relD, THEN fun_relD,THEN fun_relD,
      where x2 = alt and x'2 = alt and x1 = pl and x'1 = pr]
  note profr = profileref[THEN fun_relD, THEN fun_relD,
      where x1 = A and x'1 = A and x = pl and x' = pr]
  from a1 a2 profr show "(profile_l A pl)"
    by simp
next
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"
  fix A:: "'a set" and alt:: 'a
  fix con:: 'a
  assume a1: "(pl, pr) \<in> profile_rel"
  assume a2: "con \<in> A"
  assume a3: "\<not> wins_l alt pl con"
  assume altwins: "\<forall>x\<in>A - {alt}. wins alt pr x"
  note winc = wins_l_correct[THEN fun_relD, THEN fun_relD,THEN fun_relD,
      where x2 = alt and x'2 = alt and x1 = pl and x'1 = pr]
  from a1 a3 winc have "\<not> wins alt pr con" by blast
  from altwins a2 this show "con = alt" by blast
qed

definition condorcet_winner_monadic :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "condorcet_winner_monadic A p w \<equiv>
    FOREACH A
        (\<lambda> x b. do {
         winswx <- wins_monadic w p x;
         RETURN (b \<and> ((x = w) \<or> winswx))
        }) True"

sepref_definition cond_imp is "uncurry2 condorcet_winner_monadic" 
  :: "(alts_set_impl_assn\<^sup>k *\<^sub>a profile_impl_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
  unfolding condorcet_winner_monadic_def wins_monadic_def prefer_count_monadic_imp_def 
    is_less_preferred_than_mon_def
  rank_mon_def index_mon_def 
  apply sepref_dbg_keep
  done

lemma condorcet_winner_monadic_correct:
  shows "(condorcet_winner_monadic, RETURN ooo condorcet_winner) 
  \<in> \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  unfolding condorcet_winner_monadic_def
  apply (refine_vcg FOREACHc_rule[where I = "\<lambda> it b. b = condorcet_winner (A - it) p w"])
proof (clarsimp simp del: wins.simps, rename_tac A' A pl pr winner)
  fix A' A :: "'a set"
  fix pl :: "'a Profile_List"
  fix pr :: "'a Profile"  
  fix winner :: 'a
  assume arel: "(A', A) \<in> \<langle>Id\<rangle>alt_set_rel"
  assume prel: "(pl, pr) \<in> profile_rel"
  from arel have aeq: "A' = A" by (auto simp add: alt_set_rel_def in_br_conv)
  from arel have fina: "finite A'" by (auto simp add: alt_set_rel_def in_br_conv)
  show "FOREACH A'  (\<lambda>x b. wins_monadic winner pl x \<bind> (\<lambda>winswx. RETURN (b \<and> (x = winner \<or> winswx)))) True
       \<le> RETURN (finite A \<and> profile A pr \<and> winner \<in> A \<and> (\<forall>x\<in>A - {winner}. wins winner pr x))"
    apply (refine_vcg FOREACH_rule[where I = "\<lambda> it b. b = condorcet_winner (A - it) pr winner"])
        apply (simp add: fina)
      apply (auto simp add: aeq fina)[1]
    oops
    
lemma cond_winner_l_unique:
  fixes A:: "'a set" 
  fixes pl :: "'a Profile_List"
  fixes pr :: "'a Profile"
  fixes c :: 'a and w :: 'a
  assumes
    prel:     "(pl, pr) \<in> profile_rel"    and
    winner_c: "condorcet_winner_l A pl c" and
    winner_w: "condorcet_winner_l A pl w"
  shows "w = c"
  using condorcet_winner_l_correct[THEN fun_relD,THEN fun_relD, THEN fun_relD,
      where x2 = A and x'2 = A and x1 = pl and x'1 = pr] set_rel_id_simp
    cond_winner_unique[where A = A and p = pr and c = c and w = w]
  assms by blast

lemma cond_winner_l_unique2:
  fixes A:: "'a set" 
  fixes pl :: "'a Profile_List"
  fixes pr :: "'a Profile"
  fixes x :: 'a and w :: 'a
  assumes
    prel:     "(pl, pr) \<in> profile_rel"    and
    winner: "condorcet_winner_l A pl w" and
    not_w:  "x \<noteq> w"
  shows "\<not> condorcet_winner_l A pl x"
  using condorcet_winner_l_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD,
      where x2 = A and x'2 = A and x1 = pl and x'1 = pr]  set_rel_id_simp
    cond_winner_unique2[where A = A and p = pr and x = x and w = w]
  assms by blast

lemma cond_winner_unique3_l:
  fixes A:: "'a set" 
  fixes pl :: "'a Profile_List"
  fixes pr :: "'a Profile"
  fixes w :: 'a
  assumes
    prel:     "(pl, pr) \<in> profile_rel"    and
    wcond:    "condorcet_winner_l A pl w"
  shows "{a \<in> A. condorcet_winner_l A pl a} = {w}"
  using condorcet_winner_l_correct[THEN fun_relD,THEN fun_relD,THEN fun_relD,
      where x2 = A and x'2 = A and x1 = pl and x'1 = pr]  set_rel_id_simp
    cond_winner_unique3[where A = A and p = pr and w = w]
  assms by blast

find_theorems nfoldli

fun limit_profile_l :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Profile_List nres" where
  "limit_profile_l A p = 
    nfoldli p (\<lambda>_. True)
      (\<lambda> x np. do {
         newb <- (limit_monadic A x);
        RETURN (op_list_append np newb)}) []"

(*definition limit_monadic :: "'a set \<Rightarrow> 'a Profile_List \<Rightarrow> 'a Profile_List nres" where
 "limit_monadic A p \<equiv> 
 nfoldli p (\<lambda>_.True) (\<lambda> x new_p.
    RETURN (new_p)) [] "*)

sepref_definition limit_sep is "uncurry (limit_profile_l)" :: 
  "(hs.assn nat_assn)\<^sup>k *\<^sub>a (list_assn (arl_assn nat_assn))\<^sup>k \<rightarrow>\<^sub>a (list_assn (arl_assn nat_assn))"
  unfolding limit_profile_l.simps limit_monadic_def
  apply (rewrite in "nfoldli _ _ _ \<hole>" HOL_list.fold_custom_empty)
  apply (rewrite in "WHILEIT _ _ _ \<hole>" arl.fold_custom_empty)
  by sepref

lemma "limitp_refine":
  shows "(limit_profile_l, RETURN oo limit_profile) \<in> 
      \<langle>Id\<rangle>alt_set_rel \<rightarrow> profile_rel \<rightarrow> \<langle>profile_rel\<rangle>nres_rel"
  sorry

end