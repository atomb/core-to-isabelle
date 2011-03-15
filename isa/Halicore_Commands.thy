header {* Definition packages for Halicore datatypes and functions *}

theory Halicore_Commands
imports Halicore_Syntax
begin

subsection {* Defining datatypes *}

text {*
Right now, the @{text halicore_data} command parses its input, but
doesn't do anything with it. Eventually, it will internally call
@{text fixrec} to actually define a datatype, @{text definition} to
define constructor functions, etc.
*}

ML {*

val parse_tbind : (string * string option) parser =
  (Parse.short_ident >> rpair NONE) ||
  (Parse.$$$ "(" |-- Parse.short_ident --| Parse.$$$ "::" --
    (Parse.typ >> SOME) --| Parse.$$$ ")")

val parse_halicore_data_decl :
    ((binding * (string * string option) list) *
     (binding * string list) list) list parser =
  Parse.and_list
    (Parse.binding -- Scan.repeat parse_tbind --
      (Parse.$$$ "=" |-- Parse.enum1 "|"
        (Parse.binding -- Scan.repeat Parse.term)))
*}

ML {*

val _ =
  Outer_Syntax.command
    "halicore_data"
    "define datatypes (Halicore)"
    Keyword.thy_decl
    (parse_halicore_data_decl >> K (Toplevel.theory I))

*}


(*
Usage examples:

halicore_data List a = Nil | Cons "a" "List a"

halicore_data Tree a = Node "Forest a"
and Forest a = Empty | Trees "Tree a" "Forest a"

halicore_data Tree2 (m :: "\<star> \<rightarrow> \<star>") = Tip | Branch "m (Tree2 m)"

*)

end
