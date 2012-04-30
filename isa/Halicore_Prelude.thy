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

subsubsection {* Term syntax *}

nonterminal hexps

syntax
  "" :: "hexp => hexps" ("_")
  "_hexps" :: "[hexp, hexps] => hexps" ("_,/ _")
  "_hlist" :: "[hexps, htyp] => hexp" ("[_]{_}")
  "_hNil" :: "hexp" ("[]")
  "_hCons" :: "[hexp, htyp, hexp] => hexp" ("_ :{_}/ _" [6, 0, 5] 5)

translations -- "input"
  "_hlist (_hexps x xs) t" => "_hCons x t (_hlist xs t)"
  "_hlist x t" => "_hCons x t (_hvtapp (CONST Nil) t)"
  "_hNil" => "CONST Nil"
  "_hCons x t xs" => "_happ (_happ (_hvtapp (CONST Cons) t) x) xs"

term "\<guillemotleft>x :{a} y :{a} z :{a} []{a}\<guillemotright>"
term "\<guillemotleft>[x, y, z]{a}\<guillemotright>"

text {* TODO: output syntax for lists *}

subsection {* Hiding duplicate constant names from the HOL library *}

hide_const (open) HOL.undefined
hide_const (open) List.Nil List.Cons

end
