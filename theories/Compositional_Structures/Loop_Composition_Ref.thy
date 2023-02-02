theory Loop_Composition_Ref
  imports "Verified_Voting_Rule_Construction.Loop_Composition"
      "Basic_Modules/Component_Types/Electoral_Module_Ref"

begin

function loop_comp_helper ::
    "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module" where
  "t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p) \<Longrightarrow>
      loop_comp_helper acc m t A p = acc A p" |
  "\<not>(t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"

definition loop_composition_ref :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module_Ref \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module"
  where   "loop_composition_ref \<equiv> do {
    RETURN ({},{},{})
}"

end