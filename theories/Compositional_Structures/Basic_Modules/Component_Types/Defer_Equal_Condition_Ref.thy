(*  File:       Defer_Equal_Condition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Defer Equal Condition\<close>

theory Defer_Equal_Condition_Ref
  imports Verified_Voting_Rule_Construction.Defer_Equal_Condition
  Electoral_Module_Ref
begin

text \<open>
  This is a family of termination conditions. For a natural number n,
  the according defer-equal condition is true if and only if the given
  result's defer-set contains exactly n elements.
\<close>

subsection \<open>Definition\<close>

lemma op_repl: "card = op_set_size"
  by auto


sepref_definition defer_equal_condition_sep is "uncurry (RETURN oo defer_equal_condition)" ::
"nat_assn\<^sup>k *\<^sub>a result_impl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding defer_equal_condition.simps
  apply (rewrite in "_ \<hole>" op_repl)
  apply sepref_dbg_keep
  done

end
