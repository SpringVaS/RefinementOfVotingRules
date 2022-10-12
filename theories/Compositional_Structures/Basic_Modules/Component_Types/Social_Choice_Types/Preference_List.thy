theory Preference_List
  imports 
    "Verified_Voting_Rule_Construction.Preference_Relation"
    "List-Index.List_Index"
begin

text \<open>                          
  ordered from most to least preferred candidate
\<close>

type_synonym 'a Preference_List = "'a list"

definition well_formed_pl :: "'a Preference_List \<Rightarrow> bool" where
  "well_formed_pl pl \<equiv> length pl > 0 \<and> distinct pl"

text \<open>
  rank 1 is top prefernce, rank 0 is not in list
\<close>
fun rank_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> nat" where
  "rank_l cs x = (if (List.member cs x) then index cs x + 1 else 0)"

fun is_less_preferred_than ::
  "'a \<Rightarrow> 'a Preference_List \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lesssim>\<^sub>_ _" [50, 1000, 51] 50) where
    "x \<lesssim>\<^sub>r y = ((List.member r x) \<and> (List.member r y) \<and> (rank_l r x \<ge> rank_l r y))"

definition limited :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "limited A r \<equiv> (\<forall> x. (List.member r x) \<longrightarrow>  x \<in> A)"

fun limit_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> 'a Preference_List" where
  "limit_l A pl =  List.filter (\<lambda> a. a \<in> A) pl"
  
lemma rank_gt_zero:
  assumes
    wf : "well_formed_pl r" and
    refl: "x \<lesssim>\<^sub>r x"
  shows "rank_l r x \<ge> 1"
proof auto
  from refl show "List.member r x" by auto
qed


definition total_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "total_on_l A pl \<equiv> (\<forall> x \<in> A. (List.member pl x))"

definition refl_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where 
  "refl_on_l A r \<equiv> \<forall>x \<in> A. x \<lesssim>\<^sub>r x"

definition trans :: "'a Preference_List \<Rightarrow> bool" where 
  "trans r \<equiv> \<forall>(x, y, z) \<in> ((set r) \<times> (set r) \<times> (set r)).
       x \<lesssim>\<^sub>r y \<and> y \<lesssim>\<^sub>r z \<longrightarrow> x \<lesssim>\<^sub>r z"

definition preorder_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "preorder_on_l A pl \<equiv> limited A pl \<and> refl_on_l A pl \<and> trans pl"

definition linear_order_on_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "linear_order_on_l A pl \<equiv> preorder_on_l A pl \<and> total_on_l A pl"

definition connex_l :: "'a set \<Rightarrow> 'a Preference_List \<Rightarrow> bool" where
  "connex_l A r \<equiv> limited A r \<and> (\<forall> x \<in> A. \<forall> y \<in> A. x \<lesssim>\<^sub>r y \<or> y \<lesssim>\<^sub>r x)"

lemma lin_ord_imp_connex_l:
  assumes "linear_order_on_l A r"
  shows "connex_l A r"
  by (metis Preference_List.connex_l_def Preference_List.is_less_preferred_than.simps 
          linear_order_on_l_def preorder_on_l_def 
          total_on_l_def assms nle_le)


lemma limitedI:
  "(\<And> x y. \<lbrakk> x \<lesssim>\<^sub>r y \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A) \<Longrightarrow> limited A r"
  unfolding limited_def
  by auto

lemma limited_dest: 
  shows "(\<And> x y. \<lbrakk> is_less_preferred_than x r y; limited A r \<rbrakk> \<Longrightarrow>  x \<in> A \<and> y \<in> A)"
  unfolding limited_def by (simp)  
  
definition above_l :: "'a Preference_List \<Rightarrow> 'a \<Rightarrow> 'a Preference_List" where
  "above_l r c \<equiv> take (rank_l r c) r"

lemma above_trans:
  assumes
    trans: "trans r" and
    less: "a \<lesssim>\<^sub>r b"
  shows "set (above_l r b) \<subseteq> set (above_l r a)"
  by (metis Preference_List.above_l_def Preference_List.is_less_preferred_than.elims(2) less set_take_subset_set_take)


definition pl_\<alpha> :: "'a Preference_List \<Rightarrow> 'a Preference_Relation" where
  "pl_\<alpha> l = {(a, b). a \<lesssim>\<^sub>l b}"


lemma less_preffered_l_rel_eq:
  shows "a \<lesssim>\<^sub>l b \<longleftrightarrow>  Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) b"
  by (simp add: pl_\<alpha>_def)

theorem aboveeq: assumes wf: "well_formed_pl l" and lo: "linear_order_on_l A l"
  shows "set (above_l l a) = Order_Relation.above (pl_\<alpha> l) a"
proof
  show "set (above_l l a) \<subseteq> above (pl_\<alpha> l) a"
  proof clarify
    fix x
    assume "x \<in> set (Preference_List.above_l l a)"
    have "length (above_l l a) = rank_l l a" unfolding above_l_def
      by (simp add: Suc_le_eq in_set_member)
    from wf lo this have "index l x \<le> index l a" unfolding rank_l.simps
      by (metis Preference_List.above_l_def Preference_List.rank_l.simps Suc_eq_plus1 Suc_le_eq \<open>x \<in> set (Preference_List.above_l l a)\<close> bot_nat_0.extremum_strict index_take linorder_not_less)
    from this have "a \<lesssim>\<^sub>l x"
      by (metis One_nat_def Preference_List.above_l_def Preference_List.is_less_preferred_than.elims(3) Preference_List.rank_l.simps Suc_le_mono \<open>x \<in> set (Preference_List.above_l l a)\<close> add.commute add_0 add_Suc empty_iff find_index_le_size in_set_member index_def le_antisym list.set(1) size_index_conv take_0)
    from this have "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) x"
      using less_preffered_l_rel_eq by (metis)
    from this show "x \<in> Order_Relation.above (pl_\<alpha> l) a"
      using pref_imp_in_above by (metis)
  qed
next
  show "above (pl_\<alpha> l) a \<subseteq> set (above_l l a)"
  proof clarify
    fix x
    assume "x \<in> Order_Relation.above (pl_\<alpha> l) a"
    from this have "Preference_Relation.is_less_preferred_than a (pl_\<alpha> l) x"
      using pref_imp_in_above by (metis)
    from this have alpx: "a \<lesssim>\<^sub>l x"
      using less_preffered_l_rel_eq by (metis)
    from this have "rank_l l x \<le> rank_l l a"
      by auto
    from this alpx show "x \<in> set (Preference_List.above_l l a)"
      using Preference_List.above_l_def Preference_List.is_less_preferred_than.simps Preference_List.rank_l.simps
      by (metis Suc_eq_plus1 Suc_le_eq in_set_member index_less_size_conv set_take_if_index)
  qed
qed
  
theorem rankeq: assumes wf: "well_formed_pl l" and lo: "linear_order_on_l A l"
  shows "rank_l l a = Preference_Relation.rank (pl_\<alpha> l) a"
proof (simp, safe)
  assume air: "List.member l a"
  from assms have abe: "Order_Relation.above (pl_\<alpha> l) a = set (above_l l a)" 
    using aboveeq
    by metis 
  from wf have dl: "distinct (above_l l a)" unfolding well_formed_pl_def above_l_def
    using distinct_take by blast
  from dl have ce: "card (set (above_l l a)) = length (above_l l a)" unfolding well_formed_pl_def
    using distinct_card
    by blast
  have "length (above_l l a) = rank_l l a" unfolding above_l_def
    by (simp add: Suc_le_eq in_set_member)
  from air abe dl ce this show "Suc (index l a) = card (Order_Relation.above (pl_\<alpha> l) a)"
    by simp
next
  assume anr: "\<not> List.member l a"
  from anr have "a \<notin> (set l)" unfolding pl_\<alpha>_def
    by (simp add: in_set_member) 
  from this have "a \<notin> Order_Relation.above (pl_\<alpha> l) a" 
      unfolding Order_Relation.above_def pl_\<alpha>_def
      by (simp add: anr)
  from this have "Order_Relation.above (pl_\<alpha> l) a = {}" 
      unfolding Order_Relation.above_def
      using anr less_preffered_l_rel_eq by fastforce
  from this show "card (Order_Relation.above (pl_\<alpha> l) a) = 0" by fastforce
qed

theorem linorder_l_imp_rel:
  assumes wf: "well_formed_pl l" and lo: "linear_order_on_l A l"
  shows "Order_Relation.linear_order_on A (pl_\<alpha> l)"
proof (unfold Order_Relation.linear_order_on_def partial_order_on_def 
    Order_Relation.preorder_on_def, clarsimp, safe)
  from wf have "l \<noteq> []" using well_formed_pl_def
    by auto
  from lo have "refl_on_l A l" 
    by (unfold linear_order_on_l_def preorder_on_l_def, simp)
  from this show "refl_on A (pl_\<alpha> l)" 
  proof (unfold refl_on_l_def pl_\<alpha>_def refl_on_def, clarsimp)
    fix a and b
    assume ni: "\<forall>x\<in>A. List.member l x"
    assume aA: "List.member l a" and bA: "List.member l b"
    from ni aA bA show "a \<in> A \<and> b \<in> A"
      using lo linear_order_on_l_def preorder_on_l_def Preference_List.limited_def by (metis)
  qed
next
  show "Relation.trans (pl_\<alpha> l)"
    by (unfold Preference_List.trans_def pl_\<alpha>_def Relation.trans_def, simp)
next
  show "antisym (pl_\<alpha> l)"
  proof (unfold antisym_def pl_\<alpha>_def is_less_preferred_than.simps, clarsimp)
    fix x and y 
    assume xm: "List.member l x" and ym: "List.member l y"
    assume si: "index l x = index l y"
    from xm ym si show "x = y"
      by (simp add: member_def)
  qed
next
  show "total_on A (pl_\<alpha> l)"
    using connex_l_def lin_ord_imp_connex_l lo pl_\<alpha>_def total_on_def by fastforce
qed

lemma linorder_rel_imp_l: 
  assumes "Order_Relation.linear_order_on A (pl_\<alpha> l)"
  shows "linear_order_on_l A l"
  unfolding linear_order_on_l_def preorder_on_l_def
proof (clarsimp, safe)
  show "Preference_List.limited A l" unfolding pl_\<alpha>_def linear_order_on_def 
    using assms linear_order_on_def less_preffered_l_rel_eq partial_order_onD(1) refl_on_def'
    by (metis Preference_List.limitedI Preference_Relation.is_less_preferred_than.elims(2) case_prodD)
next
  show "refl_on_l A l" unfolding pl_\<alpha>_def 
    using assms refl_on_l_def Preference_Relation.lin_ord_imp_connex less_preffered_l_rel_eq
    by (metis Preference_Relation.connex_def)
next
  show "Preference_List.trans l" unfolding pl_\<alpha>_def
    using Preference_List.trans_def by fastforce
next
  show "total_on_l A l" unfolding pl_\<alpha>_def 
    using Preference_Relation.connex_def Preference_Relation.lin_ord_imp_connex assms 
      total_on_l_def less_preffered_l_rel_eq
    by (metis Preference_List.is_less_preferred_than.elims(2))   
qed

lemma rel_trans:
  shows "Relation.trans (pl_\<alpha> pl)"
  unfolding Relation.trans_def pl_\<alpha>_def
  by auto

lemma connex_imp_refl:
  assumes "connex_l A pl"
  shows "refl_on_l A pl"
  unfolding connex_l_def refl_on_l_def
proof clarsimp
  fix x
  assume "x \<in> A"
  from this assms show "List.member pl x"
    by (metis Preference_List.connex_l_def Preference_List.is_less_preferred_than.elims(1))
qed  

lemma aconnex:
  assumes "well_formed_pl pl" and lo: "linear_order_on_l A pl"
  shows "connex_l A pl"
  using  Preference_List.connex_l_def Preference_List.is_less_preferred_than.simps 
    linear_order_on_l_def preorder_on_l_def refl_on_l_def lo
  by (metis nle_le)
  
end