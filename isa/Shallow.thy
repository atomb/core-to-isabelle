theory Shallow
imports HOLCF List_Cpo
begin

section "CPO instantiations for HOL types"

instantiation bool :: discrete_cpo
begin

definition
  "(x::bool) \<sqsubseteq> y \<equiv> x = y"

instance
apply (intro_classes)
by (simp add: below_bool_def)

end

lemma cont_if'[simp, cont2cont]:
  assumes b: "cont b"
      and f: "cont f"
      and g: "cont g"
  shows "cont (\<lambda>x. if b x then f x else g x)"
apply (rule cont_apply [OF b])
apply (rule cont_discrete_cpo)
by (case_tac y, auto simp add: f g)

lemma cont_equal[simp,cont2cont]:
  fixes f g :: "'a::cpo \<Rightarrow> 'b::discrete_cpo"
  assumes f: "cont f"
      and g: "cont g"
  shows "cont (\<lambda>x. f x = g x)"
apply (rule cont_apply [OF f])
apply (rule cont_discrete_cpo)
apply (rule cont_apply [OF g])
apply (rule cont_discrete_cpo)
apply (rule cont_const)
done

 
instantiation char :: discrete_cpo
begin

definition
  "(x::char) \<sqsubseteq> y \<equiv> x = y"

instance
apply (intro_classes)
by (simp add: below_char_def)

end

instance list :: (discrete_cpo)discrete_cpo
proof
  fix x y :: "'a list"
  show "(x \<sqsubseteq> y) = (x = y)"
    apply (induct x arbitrary: y)
    by (case_tac[!] y, simp_all)
qed

types Id = "char list"
types ID = "Id lift"

default_sort rep

new_domain 'a finlist =
    Snil                   ("<>")
  | Scons (lazy 'a) "('a finlist)"  (infixl "##" 70)

fixrec snoc :: "'a finlist \<rightarrow> 'a \<rightarrow> 'a finlist" where
  "snoc\<cdot><>\<cdot>y = y ## <>"
| "xs \<noteq> \<bottom> \<Longrightarrow> snoc\<cdot>(x ## xs)\<cdot>y = x ## (snoc\<cdot>xs\<cdot>y)"

new_domain V =
    VInt "(int lift)"
  | Vcon ID "(V finlist)"
  | Vfun (lazy "(V \<rightarrow> V)")
  | Wrong                  -- "Don't go here" (* Oops, sorry *)

fixrec (permissive) V_apply :: "V \<rightarrow> V \<rightarrow> V" where
"V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x" | 
"V_apply\<cdot>f\<cdot>x = Wrong"

lemma V_apply_Vfun[simp]:
  "V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x"
by fixrec_simp

definition V_app :: "V \<Rightarrow> V \<Rightarrow> V"  (infixl "\<bullet>" 99) where
  "f\<bullet>x = V_apply\<cdot>f\<cdot>x"

lemma cont2cont_V_app[simp, cont2cont]:
  "\<lbrakk>cont f; cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. f x \<bullet> g x)"
by (simp add: V_app_def)

lemma V_app_Vfun[simp]:
  "(Vfun\<cdot>f)\<bullet>x = f\<cdot>x"
by (simp add: V_app_def)

pcpodef (open) T = "UNIV :: (V \<rightarrow> V) set"
by simp_all

lemmas cont2cont_Rep_T = cont_Rep_T[THEN cont_compose, simp, cont2cont]
lemmas cont2cont_Abs_T = cont_Abs_T[simplified, simp, cont2cont]

definition
  from_T :: "T \<Rightarrow> V" where
 "from_T T = Vfun\<cdot>(Rep_T T)"

definition
  to_T :: "V \<Rightarrow> T" where
 "to_T x = Abs_T (\<Lambda> y. x\<bullet>y)"

lemma cont2cont_from_T[THEN cont_compose, simp, cont2cont]:
  "cont from_T"
by (simp add: from_T_def[THEN ext])

lemma cont2cont_to_T[simp, cont2cont]:
  "cont f \<Longrightarrow> cont (\<lambda>x. to_T (f x))"
apply (auto simp add: to_T_def intro!: cont_Abs_T)
apply (intro cont2cont)
by (rule cont_apply[OF cont_fst], auto)

typedecl C

definition T_app :: "V \<Rightarrow> T \<Rightarrow> V"  (infixl "\<bullet>\<bullet>" 99) where
  "f\<bullet>\<bullet>t = f\<bullet>(Vfun\<cdot>(Rep_T t))"

lemma V_apply_bot[simp]:
  "\<bottom>\<bullet>x = \<bottom>"
by (auto simp add: V_app_def V_apply.unfold)

definition V_lam :: "T \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" where
"V_lam t f = Vfun\<cdot>(Abs_CFun f)"

lemma cont_V_lam[simp]:
  assumes "cont a"
      and "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. V_lam (a x) (\<lambda>y. f x y))"
using prems
by (auto simp add: V_lam_def)

lemma V_lam_apply[simp]:
  "cont f \<Longrightarrow> V_lam T f \<bullet> x = f x"
by (auto simp add: V_lam_def)

definition T_lam :: "(T \<Rightarrow> V) \<Rightarrow> V" where
"T_lam f = (Vfun\<cdot>(\<Lambda> (Vfun\<cdot>d). f (Abs_T d)))"

-- "REVISIT: f is duplicated three times in the premeses."
lemma cont2cont_T_lam[simp, cont2cont]:
  "\<lbrakk>cont f; \<And>y. cont (f y); \<And>y. cont (\<lambda>x. f x y)\<rbrakk>
  \<Longrightarrow> cont (\<lambda>x. T_lam (f x))"
apply (simp add: T_lam_def)
apply (intro cont2cont)
apply (rule cont_apply[OF cont_fst], auto)
by (rule cont_apply[OF cont2cont_Abs_T], auto)

lemma app_T_lam[simp]:
  assumes A: "cont f"
  shows "T_lam f \<bullet>\<bullet> A = f A"
by (auto simp add: T_lam_def T_app_def cont_compose[OF A] Rep_T_inverse)

definition
  T_forall :: "(T \<Rightarrow> T) \<Rightarrow> T" where
 "T_forall F = Abs_T (\<Lambda> f. T_lam (\<lambda>A. from_T (F A)\<bullet>(f\<bullet>\<bullet>A)))"

definition
  T_fun :: "T \<Rightarrow> T \<Rightarrow> T" where
  "T_fun A B =
     Abs_T (\<Lambda>(Vfun\<cdot>f). Vfun\<cdot>(Rep_T B oo f oo Rep_T A))"

lemma cont2cont_T_fun[simp, cont2cont]:
  assumes f: "cont f"
      and g: "cont g"
  shows "cont (\<lambda>x. T_fun (f x) (g x))"
apply (simp add: T_fun_def)
apply (intro cont2cont)
apply (rule cont_compose[OF g], simp)
by (rule cont_compose[OF f], simp)

(*******
REVISIT: Finish this sanity-check lemma.

lemma "from_T (T_forall (\<lambda>A. T_fun A A))\<bullet>(T_lam (\<lambda>A. V_lam A (\<lambda>x. x))) =
       (T_lam (\<lambda>A. V_lam A (\<lambda>x. x)))"
apply (simp add: T_forall_def from_T_def)
apply (subst Abs_T_inverse, auto)
apply (subst beta_cfun)
apply (intro cont2cont)
apply simp_all
********)

consts coerce :: "V \<Rightarrow> C \<Rightarrow> V"

fixrec match' :: "Id \<rightarrow> (V finlist \<rightarrow> V) 
                    \<rightarrow> (V \<rightarrow> V) 
                    \<rightarrow> V \<rightarrow> V" where
"n2\<noteq>\<bottom> \<and> ls \<noteq> \<bottom> \<Longrightarrow> match'\<cdot>n1\<cdot>f\<cdot>con\<cdot>(Vcon\<cdot>n2\<cdot>ls) = 
   (FLIFT n2'. (if n1=n2' then f\<cdot>ls else con\<cdot>(Vcon\<cdot>n2\<cdot>ls)))\<cdot>n2" 

definition match :: "Id \<Rightarrow> (V finlist \<rightarrow> V)
                        \<Rightarrow> (V \<Rightarrow> V)
                        \<Rightarrow> V \<Rightarrow> V" where
"match nm branch else_branch
   = (\<lambda>x. match'\<cdot>nm\<cdot>branch\<cdot>(\<Lambda> x. else_branch x)\<cdot>x)"

lemma cont2cont_match[THEN cont_compose, simp, cont2cont]:
  "cont else_branch \<Longrightarrow>
   cont (match nm branch else_branch)"
by (auto simp add: match_def)

-- "flsplit is used inside match-branches to pattern match on non-empty finlists."
-- "REVISIT: Replace occurrences of flsplit with (\<Lambda> (x ## <>). ...) patterns."
fixrec flsplit :: "('a \<rightarrow> 'a finlist \<rightarrow> 'b) \<rightarrow> 'a finlist \<rightarrow> 'b" where
  "xs \<noteq> \<bottom> \<Longrightarrow> flsplit\<cdot>f\<cdot>(x ## xs) = f\<cdot>x\<cdot>xs"


section "Datatypes"

definition bot_ty :: T where
  "bot_ty = Abs_T (\<Lambda> v. \<bottom>)"

types constr_spec = "Id \<times> T list"

-- "Auxiliary function used to produce a curried constructor."
fun constr_aux :: "Id \<Rightarrow> T list \<Rightarrow> V finlist \<rightarrow> V" where
   "constr_aux nm [] = (\<Lambda> args.
      Vcon\<cdot>(Def nm)\<cdot>args)"
|  "constr_aux nm (ty # tys) = (\<Lambda> x.
      Vfun\<cdot>(\<Lambda> y. constr_aux nm tys\<cdot>(snoc\<cdot>x\<cdot>y)))"

-- "Builds a curried constructor."
definition
  constr :: "Id \<Rightarrow> T list \<Rightarrow> V" where
 "constr nm tys = constr_aux nm tys\<cdot><>"

fun app_tys :: "T list \<Rightarrow> V finlist \<rightarrow> V finlist" where
  "app_tys [] = (\<Lambda> <>. <>)"
| "app_tys (ty#tys) = (\<Lambda> (x##xs).
     Rep_T ty\<cdot>x ## app_tys tys\<cdot>xs)"

fun data_type :: "(Id \<times> T list) list \<Rightarrow> T" where
  "data_type [] = bot_ty"
| "data_type (p # rest) =
     (case p of
        (cn,tys) \<Rightarrow> Abs_T (\<Lambda> (Vcon\<cdot>nm\<cdot>xs).
          (FLIFT nm'.
             if nm' = cn 
             then Vcon\<cdot>nm\<cdot>(app_tys tys\<cdot>xs)
             else (Rep_T (data_type rest))\<cdot>(Vcon\<cdot>nm\<cdot>xs))\<cdot>nm))"

declare cont_Abs_T[simp, cont2cont]

lemma cont_app_tys[THEN cont_compose, simp]:
  "cont app_tys"
apply (rule list_contI)
   apply (rule app_tys.simps)
by simp_all

lemma cont_data_type[THEN cont_compose, simp, cont2cont]:
  "cont data_type"
apply (rule list_contI)
   apply (rule data_type.simps)
by (simp_all add: prod_case_beta)

end