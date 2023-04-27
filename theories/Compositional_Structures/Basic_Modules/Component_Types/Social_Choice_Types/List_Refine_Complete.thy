theory List_Refine_Complete
  imports Ballot_Refinement

begin

lemma fintarg:
  assumes fina: "finite A" and
          lobar: "linear_order_on A bar"
  shows "finite {b . (x, b) \<in> bar}"
  proof -
    from fina have finbound: "finite (A \<times> A)"
      by blast   
    from lobar fina have barbound: " bar \<subseteq> (A \<times> A)"
      unfolding  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by simp
    from barbound have conssub: "{b . (x, b) \<in> bar} \<subseteq> (A)"
    by blast
    from lobar fina have finbar: "finite bar"
      unfolding  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by (metis finite_SigmaI finite_subset)
    from conssub fina show ?thesis
      using finite_subset by fastforce
  qed

lemma ref_imp_ranksame:
  fixes A :: "'a set" and
        l :: "'a Preference_List" and
        r :: "'a Preference_Relation"
  assumes fina : "finite A"
  assumes wf: "well_formed_pl l"
  assumes lol: "linear_order_on_l A l"
  assumes ref: "r = pl_\<alpha> l"
  shows "\<forall> a \<in> A. rank_l l a = rank r a" 
using assms rankeq
  by metis 

lemma rankeq_imp_ref:
  fixes A :: "'a set" and
        l :: "'a Preference_List" and
        r :: "'a Preference_Relation"
  assumes fina : "finite A"
  assumes wf: "well_formed_pl l"
  assumes lol: "linear_order_on_l A l" and
          lor: "linear_order_on A r"
  assumes ranksame: "\<forall> a \<in> A. rank_l l a = rank r a"
  shows "r = pl_\<alpha> l"
proof (unfold pl_\<alpha>_def, safe, clarsimp_all, safe)
  fix a b :: 'a
  assume tupler: "(a, b) \<in> r"
  from tupler lor have aA: "a \<in> A"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by blast
  from lol have "set l = A" unfolding losimp by simp
  from aA this show "a \<in> set l" by simp
next
  fix a b :: 'a
  assume tupler: "(a, b) \<in> r"
  from tupler lor have aA: "b \<in> A"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by blast
  from lol have "set l = A" unfolding losimp by simp
  from aA this show "b \<in> set l" by simp
next
  fix a b :: 'a
  assume tupler: "(a, b) \<in> r"
  from lol have Al: "set l = A" unfolding losimp by simp
  from tupler lor have aA: "a \<in> A"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by blast
  from tupler lor have bA: "b \<in> A"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by blast
  from fina lor have "finite r"
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    using finite_subset
    by blast
  have finbs: "finite {b. (a, b) \<in> r}" using fina lor fintarg
    by fastforce
  from tupler lor have "{ba. (b, ba) \<in> r} \<subseteq> {b. (a, b) \<in> r}"
    unfolding rank.simps above_def
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
              trans_def antisym_def total_on_def
    by blast
  from this have rc: "rank r b \<le> rank r a"
    unfolding rank.simps above_def using card_mono finbs
    by blast
  from ranksame aA have rsa: "rank r a = rank_l l a"
    by simp
  from ranksame bA have rsb: "rank r b = rank_l l b"
    by simp
  from rc aA bA show "index l b \<le> index l a" unfolding rsa rsb
    rank_l.simps Al by auto
next
  fix a b :: 'a
  assume al: "a \<in> set l"
  assume bl: "b \<in> set l"
  assume icmp: "index l b \<le> index l a"
  from lol have Al: "set l = A" unfolding losimp by simp
  from al bl have eitheror: "(a,b) \<in> r \<or> (b,a) \<in> r"
    using lor
    unfolding Al linear_order_on_def total_on_def
    by (metis partial_order_onD(1) refl_onD)
  from al bl icmp have "rank_l l b \<le> rank_l l a"
    unfolding rank_l.simps by auto
  from this al bl ranksame have rankcomp: "rank r b \<le> rank r a"
    unfolding Al by auto
  from this show "(a,b) \<in> r"
  proof (unfold rank.simps above_def)
    assume cardcomp: "card {ba. (b, ba) \<in> r} \<le> card {b. (a, b) \<in> r}"
    have fin1: "finite {ba. (b, ba) \<in> r}" using fintarg
        lor fina
      by metis
    have fin2: "finite {b. (a, b) \<in> r}" using fintarg
        lor fina
      by metis
    from fin1 fin2 cardcomp eitheror show ?thesis
    using lor unfolding linear_order_on_def partial_order_on_def antisym_def
    preorder_on_def trans_def
    by (smt (verit, del_insts) Collect_mono card_seteq mem_Collect_eq refl_onD refl_on_domain)
  qed
qed


lemma ballot_refinement_complete:
  fixes A :: "'a set"
  and bar:: "'a Preference_Relation"
assumes fina: "finite A"
  and lo: "linear_order_on A bar"
  shows "\<exists> bal :: 'a Preference_List. (bal, bar) \<in> ballot_rel"
  unfolding in_br_conv well_formed_pl_def pl_\<alpha>_def 
  using assms
proof (induction arbitrary: bar)
  case empty
  then have "bar = {}"
    using lin_ord_not_empty by blast
  then show ?case
    apply (rule_tac x = "[]" in exI)
    by simp
next
  case ih: (insert x F)
  obtain baro where defbaro: "baro = limit F bar"
    by auto
  from ih(4) have lobaro: "linear_order_on F baro"
    unfolding defbaro using limit_presv_lin_ord  by blast 
  from this ih(3)[where bar = baro] obtain balo where balrel: "(balo, baro) \<in> ballot_rel"
    unfolding in_br_conv well_formed_pl_def pl_\<alpha>_def
    by blast
  from this have diso: "distinct balo"
    unfolding in_br_conv well_formed_pl_def by simp
  from balrel have absto: "baro = pl_\<alpha> balo"
    unfolding in_br_conv by simp
  from lobaro have lobalo: "linear_order_on_l F balo"
    using balrel linearorder_ref[THEN fun_relD, THEN fun_relD]
    by auto
  then have seteqo: "set balo = F" unfolding losimp by simp
  from ih(1) have finxF: "finite (insert x F)"
    by simp
  from ih.prems have nempcons: "{b. (x, b) \<in> bar} \<noteq> {}"
      unfolding  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by (metis empty_iff insertI1  mem_Collect_eq)
  from ih.prems have barbound: "bar \<subseteq>  ((insert x F) \<times> (insert x F))"
      unfolding  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by simp
  from barbound have conssub: "{b . (x, b) \<in> bar} \<subseteq> (insert x F)"
    by blast
  have  finitecons: "finite {b . (x, b) \<in> bar}"
  proof -
    from finxF have finbound: "finite ((insert x F) \<times> (insert x F))"
      by blast   
    from ih.prems finxF have finbar: "finite bar"
      unfolding  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by (metis finite_SigmaI finite_subset)
    from conssub finxF show ?thesis
      using finite_subset by fastforce
  qed
  have rankxgt0: "(rank bar x) > 0"
  proof (unfold rank.simps above_def)
    from nempcons finitecons show "0 < card {b. (x, b) \<in> bar}"
      using card_gt_0_iff by blast
  qed

  obtain constabs where ca: "constabs = baro \<union> {(a, b) \<in> bar. b = x} \<union> {(x,x)} \<union> {(a, b) \<in> bar. a = x}"
    by auto

  have "constabs = bar" unfolding ca defbaro limit.simps using ih(4) 
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
    by auto


  obtain newbal where defnb: "newbal = take ((rank bar x) - 1) balo @ [x] @ drop ((rank bar x) - 1) balo"
    by auto
  from seteqo diso ih(2) have disnb: "distinct newbal"
    unfolding defnb
    by (metis distinct_insert_nth insert_nth_take_drop)
  have insx: "set newbal = set balo \<union> {x}"
    unfolding defnb
    by (metis inf_sup_aci(5) insert_is_Un insert_nth_take_drop set_insert_nth)
  then have seteqnb: "set newbal = insert x F"
    using seteqo
    by blast
  from this ih(2) have fdx: "filter (\<lambda>x. x \<in> F) (take ((rank bar x) - 1) balo @ [x] @ drop ((rank bar x) - 1) balo)
      = filter (\<lambda>x. x \<in> F) (take ((rank bar x) - 1) balo @ drop ((rank bar x) - 1) balo)"
    by (metis append_Nil filter.simps(2) filter_append)
  from seteqo have balolim: "balo = limit_l F newbal"
    unfolding limit_l.simps defnb fdx append_take_drop_id
    by simp
  have lonb: "linear_order_on (insert x F) (pl_\<alpha> newbal)"
    using seteqnb[symmetric] unfolding losimp[symmetric] 
   linord_eq . 
  have barolim: "baro = limit F (pl_\<alpha> newbal)"
    using limit_eq[where bal=newbal and A = F] disnb
    unfolding well_formed_pl_def balolim[symmetric] absto[symmetric] by simp
  from ih(1) ih(2) have cardxinc: "card F = card (insert x F) - 1"
    by simp
  have rankib: "(rank bar x) - 1 \<le> length balo"
  proof -
    have ranklt: "(rank bar x) \<le> card (insert x F)"
      unfolding rank.simps above_def
      using conssub finxF card_mono by blast 
    from this cardxinc rankxgt0 have "(rank bar x) - 1 \<le> card (F)"
      by linarith
    from this seteqo show ?thesis
      using card_length order_trans by blast
  qed      
  have onFeq: "limit F (pl_\<alpha> newbal) = limit F (bar)"
    using barolim defbaro by fastforce
  from this have fprefs: "\<forall> a \<in> F. \<forall> b \<in> F. (a \<preceq>\<^sub>(pl_\<alpha> newbal) b) = (a \<preceq>\<^sub>(bar) b)"
    using limit_presv_prefs2
    by auto
  (* TODO: assert that x is inserted at the right position *)
  from rankxgt0 rankib have "((take ((rank bar x) - 1) (balo)) @ [x])!((rank bar x)-1) = x"
    by (metis add_diff_cancel_right' append_take_drop_id diff_diff_cancel length_append length_drop nth_append_length)
  from this have "newbal!((rank bar x)-1) = x"
    unfolding defnb
    by (metis add_diff_cancel_right' append_Cons append_take_drop_id diff_diff_cancel length_append length_drop nth_append_length rankib)
  from ih this rankib rankxgt0 seteqnb seteqo disnb diso 
  have posxl: "rank_l newbal x = (rank bar x)"
    unfolding rank_l.simps
    by (metis One_nat_def Suc_eq_plus1 Suc_pred card.insert distinct_card index_nth_id insertCI 
              less_Suc_eq_le )
  from fprefs this have rankxabs: "rank (pl_\<alpha> newbal) x = (rank bar x)" 
    using rankeq disnb unfolding well_formed_pl_def 
    by metis  
  from onFeq[symmetric] ih(4) finxF this have "bar = (pl_\<alpha> newbal)"
  unfolding rank.simps above_def pl_\<alpha>_def
  using finitecons unfolding is_less_preferred_than.simps
  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def antisym_def trans_def
total_on_def seteqnb insert_def defnb is_less_preferred_than_l.simps limit.simps index_def
    apply safe subgoal
    by (metis SigmaE2 barbound defnb in_mono seteqnb)subgoal
    by (metis SigmaE2 barbound defnb seteqnb subset_iff) unfolding card_def 
  
   unfolding  limit.simps defnb
    sorry
  from this show ?case
    apply (rule_tac x = newbal in exI)
    unfolding ballot_rel_def well_formed_pl_def in_br_conv using disnb by auto
qed

end