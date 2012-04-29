header {* Definition packages for Halicore datatypes and functions *}

theory Halicore_Commands
imports Halicore_Syntax Halicore_Typecheck Halicore_Simprocs
uses ("datatype.ML") ("function.ML")
begin

subsection {* Prelude constants used by commands *}

subsubsection {* Undefined *}

definition undefined :: "V"
  where "undefined = Vtlam (\<lambda>a::T. \<bottom>)"

lemma has_type_undefined [type_rule]:
  "has_type undefined (Tforall (\<lambda>a. a))"
unfolding undefined_def
by (rule has_type_Vtlam, simp, simp, rule has_type_bottom)

lemma Vcase_undefined [simp]:
  "Vcase t (Vtapp undefined (a::T)) m = Vtapp undefined t"
unfolding undefined_def Vcase_def by simp


subsection {* Defining datatypes *}

text {* The @{text halicore_data} command parses its input, and
defines constants for datatypes and their constructors. So far, it
proves the following theorems:

\begin{itemize}
\item A definition for each type constructor (@{text Tycon_def})
\item An unfolding rule for each unapplied tycon (@{text Tycon_unfold_raw})
\item An unfolding rule for each fully-applied tycon (@{text Tycon_unfold})
\item A definition for each data constructor (@{text Cons_def})
\item A set of @{text has_constructor} rules for each type constructor
  (@{text Tycon_has_constructor}), declared with the @{text
  "[constructor_rule]"} attribute
\item A typing rule for each data constructor (@{text has_type_Cons}),
  declared with the @{text "[type_rule]"} attribute
\end{itemize}
*}

subsubsection {* Lemmas used with internal proofs *}

lemma Tapp_eqI: "t = (\<Lambda> a. f a) \<Longrightarrow> cont f \<Longrightarrow> \<langle>t a\<rangle> = f a"
unfolding Tapp_def by simp

lemmas has_constructor_simps =
  lookup_defls.simps fst_conv snd_conv refl if_True if_False
  list.simps(1-3) char.inject nibble.simps(1-240)

lemmas has_type_constr_intros =
  has_type_Vtlam has_type_Vlam
  cont_id cont_const cont2cont_fst cont2cont_snd
  cont2cont_APP cont2cont_Cons
  cont_Tapp cont_Tforall cont_Vlam cont_Vtlam

subsubsection {* Loading the datatype package *}

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

lemma adm_has_type: "cont f \<Longrightarrow> adm (\<lambda>x. f x ::: t)"
unfolding has_type_def by simp

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
