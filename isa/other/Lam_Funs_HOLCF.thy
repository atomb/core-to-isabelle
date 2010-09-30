theory Lam_Funs_HOLCF
imports HOLCF "~~/src/HOL/Nominal/Nominal" "~~/src/HOL/Nominal/Examples/Lam_Funs"
begin

default_sort type

text {* 
  Provides a denotational semantics for the "lam" syntax defined in theory Lam_Funs
*}

text {* A universal domain of lambda-calculus values *}
new_domain V
  = lam (lazy from_lam :: "V \<rightarrow> V");

text {* Permutation over continuous functions that only work over V*}
overloading
  perm_cfun_V \<equiv> "perm :: 'x prm \<Rightarrow> (V \<rightarrow> V) \<Rightarrow> (V \<rightarrow> V)" (unchecked)
begin

definition
   perm_cfun_V :: "'x prm \<Rightarrow> (V \<rightarrow> V) \<Rightarrow> (V \<rightarrow> V)" where 
  "perm_cfun_V p f = f"

end

declare perm_cfun_V_def[simp]

(********
lemma cont_perm_cfun[simp,cont2cont]:
  "cont f \<Longrightarrow> cont (\<lambda>x. p \<bullet> f x)"

lemma perm_cfun_eqvt[eqvt]:
  "p \<bullet> (f\<cdot>x) = (p \<bullet> f) \<cdot> (p \<bullet> x)"
apply (auto simp: perm_cfun_def)

********)



 (**********
Brian sez:
  Define instance of pt_name for continuous function space (they should work just like full function space)
  Prove equivariance of continuous function application
  Register lemma with [eqvt] attribute.
  

REVISIT: Need to define an abstract type of environments as finite maps, so we can prove that it has finite
         support provided each value in the environment has finite support. Then we
         can define "env" in terms of the finite map.
*************)

(******

Idea from Brian for representing F_c coercions:
  Define (a ~ b) to be (forall f. f a \<rightarrow> f b), or maybe ((forall f. f a \<rightarrow> f b), (forall f. f b \<rightarrow> f a)).

  Could use this interpretation both in deflation and PER models.

******)

types env = "name \<Rightarrow> V"


text {* Type V doesn't contain any name values, so permutation is a no-op. *}
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

text {* The nominal_primrec package requres V to be an instance of classes pt_name and fs_name
        (these classes were dynamically generated from the atom_decl in theory Lam_Funs)
     *}

instance V :: pt_name
by intro_classes auto

instance V :: fs_name
by intro_classes simp

lemma from_lam_eqvt[eqvt]:
  "p \<bullet> (from_lam\<cdot>f\<cdot>x) = from_lam\<cdot>(p \<bullet> f)\<cdot>(p \<bullet> x)"
by simp

lemma lam_eqvt[eqvt]:
  "p \<bullet> (lam\<cdot>f) = lam\<cdot>(p \<bullet> f)"
by simp

lemma Abs_CFun_eqvt[eqvt]:
  "p \<bullet> (Abs_CFun (f::V \<Rightarrow> V)) = Abs_CFun (p \<bullet> f)"
by (simp add: perm_fun_def)

lemma fun_upd_eqvt[eqvt]:
  "p \<bullet> (f(x := v)) = (p \<bullet> f)((p \<bullet> x) := (p \<bullet> v))"
apply (subst perm_fun_def)
apply (simp add: fun_upd_def eqvts)
sorry

lemma fresh_V[simp]:
  "x \<sharp> (v::V)"
by (simp add: fresh_def)

nominal_primrec eval :: "lam \<Rightarrow> env \<Rightarrow> V" where
  "eval (Var v) env = env v"
| "eval (App x y) env = from_lam\<cdot>(eval x env)\<cdot>(eval y env)"
| "v\<sharp>env \<Longrightarrow> eval (Lam [v].x) env = lam\<cdot>(\<Lambda> (y::V). eval x (env(v := y)))"
apply(finite_guess)
prefer 3
apply(finite_guess)
apply(finite_guess)
apply(finite_guess)
apply(rule TrueI)+
defer
apply fresh_guess
apply fresh_guess
apply fresh_guess
apply fresh_guess


apply(simp add: fresh_nat)
apply(fresh_guess)+
done

; REVISIT: Check-in to github (even if it doesn't compile), so others on the team can contribute.


apply auto

lemma [simp]: "cont (\<lambda>f. f x)"
by (rule cont2cont_fun [OF cont_id])

lemma [simp]: "cont (%f. f x y)"
by (rule cont2cont_fun [OF cont2cont_fun [OF cont_id]])

lemma cont2cont_fun_upd [cont2cont]: "\<lbrakk>cont f; cont b\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (f x)(a := b x))"
unfolding fun_upd_def
apply (rule cont2cont_lambda)
apply (erule cont_if)
apply (erule cont2cont_fun)
done

lemma cont_eval:
  "cont (eval x)"
proof (induct x, auto)
  fix v x
  assume H: "cont (\<lambda>env. eval x env)"
  show "cont (\<lambda>env. lam\<cdot>(\<Lambda> y. eval x (env(v := y))))"
    by (intro cont2cont cont_compose[OF H])
qed

lemmas cont2cont_eval = cont_compose[OF cont_eval, simp]



end
