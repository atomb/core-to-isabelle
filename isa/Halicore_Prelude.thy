header {* Definitions for Prelude Types and Functions *}

theory Halicore_Prelude
imports Halicore_Commands
begin

subsection {* List datatype *}

halicore_data List a = Nil | Cons "a" "List a"

subsubsection {* Type syntax *}

syntax
  "_htlist0" :: "htyp" ("[]")
  "_htlist1" :: "htyp \<Rightarrow> htyp" ("[_]")

translations
  "_htlist0" => "CONST List"
  "_htlist0" <= "_hunquote (CONST List)"
  "_htlist1 a" == "_htapp _htlist0 a"

end
