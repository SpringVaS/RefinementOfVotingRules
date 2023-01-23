theory Elect_Composition_Ref
  imports "Basic_Modules/Elect_Module_Ref"
          Sequential_Composition_Ref
begin

fun elector_ref :: "'a Electoral_Module_Ref \<Rightarrow> 'a Electoral_Module_Ref" where
  "elector_ref m = (m \<triangleright>r elect_module_ref)"

end