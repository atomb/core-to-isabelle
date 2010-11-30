theory Shallow
imports HOLCF List_Cpo
begin

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

(*******
    typedef T = "{f :: V \<rightarrow> V. deflation f}"
    apply (rule_tac x="ID" in exI, simp)
    apply (rule deflation_ID)
    done
*******)

pcpodef (open) T = "UNIV :: (V \<rightarrow> V) set"
by simp_all

typedecl C

fixrec (permissive) V_apply :: "V \<rightarrow> V \<rightarrow> V" where
"V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x" | 
"V_apply\<cdot>f\<cdot>x = Wrong"

lemma V_apply_Vfun[simp]:
  "V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x"
by fixrec_simp

definition V_app :: "V \<Rightarrow> V \<Rightarrow> V"  (infixl "\<bullet>" 99) where
  "f\<bullet>x = V_apply\<cdot>f\<cdot>x"

lemma V_app_Vfun[simp]:
  "(Vfun\<cdot>f)\<bullet>x = f\<cdot>x"
by (simp add: V_app_def)

definition T_app :: "V \<Rightarrow> T \<Rightarrow> V"  (infixl "\<bullet>\<bullet>" 99) where
  "f\<bullet>\<bullet>t = f\<bullet>(Vfun\<cdot>(Rep_T t))"

lemma V_apply_bot[simp]:
  "\<bottom>\<bullet>x = \<bottom>"
by (auto simp add: V_app_def V_apply.unfold)

definition V_lam :: "T \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" where
"V_lam t f = Vfun\<cdot>(Abs_CFun f)"

definition T_lam :: "(T \<Rightarrow> V) \<Rightarrow> V" where
"T_lam f = (Vfun\<cdot>(\<Lambda> (Vfun\<cdot>d). f (Abs_T d)))"

definition
  T_fun :: "T \<Rightarrow> T \<Rightarrow> T" where
  "T_fun A B =
     Abs_T (\<Lambda>(Vfun\<cdot>f). Vfun\<cdot>(Rep_T B oo f oo Rep_T A))"

lemma app_T_lam[simp]:
  assumes A: "cont f"
  shows "T_lam f \<bullet>\<bullet> A = f A"
by (auto simp add: T_lam_def T_app_def cont_compose[OF A] cont_Abs_T Rep_T_inverse)

lemma cont_V_lam[simp]:
  assumes "cont a"
      and "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. V_lam (a x) (\<lambda>y. f x y))"
using prems
by (auto simp add: V_lam_def)

lemma V_lam_apply[simp]:
  "cont f \<Longrightarrow> V_lam T f \<bullet> x = f x"
by (auto simp add: V_lam_def)

consts coerce :: "V \<Rightarrow> C \<Rightarrow> V"

fixrec match' :: "ID \<rightarrow> (V finlist \<rightarrow> V) 
                    \<rightarrow> (V \<rightarrow> V) 
                    \<rightarrow> V \<rightarrow> V" where
"n2\<noteq>\<bottom> \<and> ls \<noteq> \<bottom> \<Longrightarrow> match'\<cdot>n1\<cdot>f\<cdot>con\<cdot>(Vcon\<cdot>n2\<cdot>ls) = 
   (FLIFT n1'. 
     (FLIFT n2'. (if n1'=n2' then f\<cdot>ls else con\<cdot>(Vcon\<cdot>n2\<cdot>ls)))\<cdot>n2)\<cdot>n1" 

definition match :: "Id \<Rightarrow> (V finlist \<Rightarrow> V)
                        \<Rightarrow> (V \<Rightarrow> V)
                        \<Rightarrow> V \<Rightarrow> V" where
"match = undefined"


section "Datatypes"

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

lemmas cont2cont_Rep_T[simp, cont2cont] = cont_Rep_T[THEN cont_compose]

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