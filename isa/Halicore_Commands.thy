theory Halicore_Commands
imports Halicore_Syntax
begin

(*
Right now, the "halicore_data" command parses its input, but doesn't
do anything with it. Eventually, it will internally call "fixrec" to
actually define a datatype, "definition" to define constructor
functions, etc.
*)

ML {*

val parse_halicore_data_decl :
    ((binding * string list) * (binding * string list) list) list parser =
  Parse.and_list
    (Parse.binding -- Scan.repeat Parse.short_ident --
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

halicore_data Tree2 m = Tip | Branch "m (Tree2 m)"

*)

end
