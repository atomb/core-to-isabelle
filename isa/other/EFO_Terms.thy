theory EFO_Terms
imports Nominal
begin

text {* An attempt to use Nominal-HOL to formalize a semantic
meaning function for a simple lambda-calculus language of
"essentially first order" terms over natural numbers. By
restricting functions to be essentially first order, we can
give a denotational s whose denotational semantics can be given
directly in HOL. The semantics of essentially first order
functions are given by the @{term V} datatype: *}

datatype V
  = Val nat
  | VFun "(nat \<Rightarrow> V)"
  | Wrong             -- "runtime error"

text {* We also include a special value @{term Wrong} that
represents a runtime error. *}

text {* Syntax for essentially first order functions. *}

atom_decl name

nominal_datatype Term
  = Const nat
  | Var name
  | App Term Term
  | Lam "\<guillemotleft>name\<guillemotright>Term"

text {* Type V represents "pure values" without syntactic names,
so permutation on V is a no-op. *}
text {* NOTE: perm has two free type variables, which defeat's Isabelle's
        overloading-uniqueness checker. Thus we need to use (unchecked). *}
overloading
  perm_V \<equiv> "perm :: 'x prm \<Rightarrow> V \<Rightarrow> V" (unchecked)
begin

definition
   perm_V :: "'x prm \<Rightarrow> V \<Rightarrow> V" where 
  "perm_V p (x::V) = x"

end

declare perm_V_def[simp]

lemma supp_V_empty[simp]:
  "supp (x::V) = {}"
by (auto simp add: supp_def)

instance V :: pt_name
by intro_classes auto

instance V :: fs_name
by intro_classes simp


text {* Define a semantic meaning function
from syntax to essentially first order values. Syntax
that doesn't correspond to an essentially first order
value is mapped to @{term Wrong}. *}

types env = "(name \<times> V) list"

fun
  lookup :: "env \<Rightarrow> name \<Rightarrow> V"   
where
  "lookup [] x        = Wrong"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  and   \<theta>::env
  and   X::name
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>) (auto simp add: perm_bij)

text {* REVIIST: Nominal-HOL (Isabelle2009-2) doesn't
accept the following definition, because the @{term env}
parameter varies in recursive calls. How to define this
function such that it passes nominal\_primrec? *} 
nominal_primrec eval :: "Term \<Rightarrow> env \<Rightarrow> V" where
  "eval (Const n) env = Val n"
| "eval (Var v) env   = lookup env v"
| "eval (App f x) env = (case eval f env of
                           VFun f \<Rightarrow> (case eval x env of
                                        Val n \<Rightarrow> f n
                                      | _ \<Rightarrow> Wrong)
                         | _ \<Rightarrow> Wrong)"
| "v\<sharp>env \<Longrightarrow> eval (Lam v x) env = VFun (\<lambda>z. eval x ((v, Val z) # env))"

end