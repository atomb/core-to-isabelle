header {* Definition packages for Halicore datatypes and functions *}

theory Halicore_Commands
imports Halicore_Syntax
uses ("datatype.ML")
begin

subsection {* Defining datatypes *}

text {*
Right now, the @{text halicore_data} command parses its input, but
doesn't do anything with it. Eventually, it will internally call
@{text fixrec} to actually define a datatype, @{text definition} to
define constructor functions, etc.
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
