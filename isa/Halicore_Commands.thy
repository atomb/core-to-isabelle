header {* Definition packages for Halicore datatypes and functions *}

theory Halicore_Commands
imports Halicore_Syntax
uses ("datatype.ML")
begin

subsection {* Defining datatypes *}

text {*
Right now, the @{text halicore_data} command parses its input, and
defines datatypes, but it doesn't define constructor functions yet.
*}

use "datatype.ML"

(*
Usage examples:

halicore_data List a = Nil | Cons "a" "List a"

halicore_data Tree a = Node "Forest a"
and Forest a = Empty | Trees "Tree a" "Forest a"

halicore_data Tree2 (m :: "\<star> \<rightarrow> \<star>") = Tip | Branch "m (Tree2 m)"

*)

subsection {* Defining functions *}

text {*
Right now, the @{text halicore_fun} command parses its input,
but doesn't do anything yet.
*}

ML {*

(*** Outer syntax parsers ***)

val parse_htype : string parser =
  Parse.group "Halicore type" Parse.term_group

val parse_halicore_fun_decl : ((binding * string) * string) list parser =
  Parse.and_list
    (Parse.binding --| Parse.$$$ "::" -- parse_htype --
      (Parse.$$$ "=" |-- Parse.term_group))

val _ =
  Outer_Syntax.local_theory
    "halicore_fun"
    "define functions (Halicore)"
    Keyword.thy_decl
    (parse_halicore_fun_decl >> K I)

*}

(*
Usage examples:

halicore_fun
  ident :: "forall a. a \<rightarrow> a"
    = "\<lambda>@a (x::a). x"
and
  const :: "forall a b. a \<rightarrow> b \<rightarrow> a"
  = "\<lambda>@a @b (x::a) (y::b). x"
*)

end
