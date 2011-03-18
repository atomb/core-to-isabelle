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

end
