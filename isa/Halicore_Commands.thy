header {* Definition packages for Halicore datatypes and functions *}

theory Halicore_Commands
imports Halicore_Syntax
uses ("datatype.ML") ("function.ML")
begin

subsection {* Defining datatypes *}

text {* So far, the @{text halicore_data} command parses its input,
and defines constants for datatypes and their constructors. But it
doesn't prove many theorems about them yet. *}

subsubsection {* Lemmas used with internal proofs *}

lemma T_apply_eqI: "t = (\<Lambda> a. f a) \<Longrightarrow> cont f \<Longrightarrow> \<langle>t a\<rangle> = f a"
unfolding T_apply_def by simp

subsection {* Loading the datatype package *}

use "datatype.ML"

(*
Usage examples:

halicore_data List a = Nil | Cons "a" "List a"

halicore_data Tree a = Node "Forest a"
and Forest a = Empty | Trees "Tree a" "Forest a"

halicore_data Tree2 (m :: "\<star> \<rightarrow> \<star>") = Tip | Branch "m (Tree2 m)"

halicore_data BinTree a b = Leaf "a" | Node "b" "BinTree a b" "BinTree a b"
*)


subsection {* Defining functions *}

text {* Right now, the @{text halicore_fun} command parses its input,
defines the constants, and proves unfolding rules. It doesn't generate
typing rules or any other theorems yet. *}

use "function.ML"

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
