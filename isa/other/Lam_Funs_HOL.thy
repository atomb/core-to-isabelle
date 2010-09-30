theory Lam_Funs_HOL
imports HOLCF
begin

default_sort type

text {* 
  Provides a denotational semantics for the "lam" syntax. The syntax is
  defined below as a HOL datatype, thus the suffix on this theory name.
*}

text {* REVISIT: Shouldn't this be enabled in Tr.thy? *}
declare If_and_if[simp]

types name = nat

datatype lam = 
    Var name
  | App lam lam
  | Lam name lam ("Lam [_]._" [100,100] 100)


text {* A universal domain of lambda-calculus values *}
new_domain V
  = lam (lazy from_lam :: "V \<rightarrow> V");


(******

Idea from Brian for representing F_c coercions:
  Define (a ~ b) to be (forall f. f a \<rightarrow> f b), or maybe ((forall f. f a \<rightarrow> f b), (forall f. f b \<rightarrow> f a)).

  Could use this interpretation both in deflation and PER models.

******)

new_domain env
 = empty
 | entry "(name lift)" (lazy V) env

definition
   equal :: "'a lift \<rightarrow> 'a lift \<rightarrow> tr" where
  "equal = (\<Lambda> x. \<Lambda> y. (FLIFT a b. Def(a=b))\<cdot>x\<cdot>y)"

lemma equal_bot_left[simp]:
  "equal\<cdot>\<bottom> = \<bottom>"
by (auto simp add: equal_def expand_cfun_eq)

lemma equal_bot_right[simp]:
  "equal\<cdot>x\<cdot>\<bottom> = \<bottom>"
apply (case_tac x)
by (auto simp add: equal_def expand_cfun_eq)

lemma equal_def_def[simp]:
  "equal\<cdot>(Def x)\<cdot>(Def y) = Def (x=y)"
by (auto simp add: equal_def)

fixrec
  lookup :: "env \<rightarrow> name lift \<rightarrow> V"   
where
  lookup_empty:  "lookup\<cdot>empty\<cdot>x         = \<bottom>"
| lookup_entry: "\<lbrakk>y \<noteq> \<bottom>; env \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> lookup\<cdot>(entry\<cdot>y\<cdot>e\<cdot>env)\<cdot>x = (If equal\<cdot>x\<cdot>y then e else lookup\<cdot>env\<cdot>x fi)"

primrec eval :: "lam \<Rightarrow> env \<Rightarrow> V" where
  "eval (Var v) env = lookup\<cdot>env\<cdot>(Def v)"
| "eval (App x y) env = from_lam\<cdot>(eval x env)\<cdot>(eval y env)"
| "eval (Lam [v].x) env = lam\<cdot>(\<Lambda> (y::V). eval x (entry\<cdot>(Def v)\<cdot>y\<cdot>env))"

lemma cont_eval[simp]:
  "cont (eval x)"
apply (induct x, auto)
apply (intro cont2cont)
by (rule_tac f="(\<lambda>c. eval x)" in cont2cont_app, auto)

lemmas cont2cont_eval = cont_compose[OF cont_eval, simp]


text {* Testing\<dots> *}

lemma "env \<noteq> \<bottom> \<Longrightarrow> eval (Lam [v]. Var v) env = lam\<cdot>(\<Lambda> v. v)"
by simp

lemma "\<lbrakk>env \<noteq> \<bottom>; f \<noteq> x\<rbrakk> \<Longrightarrow> eval (Lam [f]. Lam [x]. App (Var f) (Var x)) env = lam\<cdot>(\<Lambda> f. lam\<cdot>(\<Lambda> x. from_lam\<cdot>f\<cdot>x))"
by simp

end
