header {* Halicore term combinators, with typing rules *}

theory Halicore_Terms
imports Halicore_Type_Meaning Halicore_Kind
begin

subsection {* Typing relation *}

definition kstar_denote :: "kstar \<Rightarrow> V defl"
  where "kstar_denote t = unUdefl\<cdot>(ty_denote \<bottom> (to_ty t))"

definition has_type :: "V \<Rightarrow> kstar \<Rightarrow> bool"
  where "has_type x t \<longleftrightarrow> cast\<cdot>(kstar_denote t)\<cdot>x = x"

lemma has_type_bottom: "has_type \<bottom> t"
  unfolding has_type_def by simp

lemma has_type_elim:
  assumes "has_type x t" obtains y where "x = cast\<cdot>(kstar_denote t)\<cdot>y"
using assms unfolding has_type_def by metis


subsection {* Application and abstraction of terms *}

definition Vapp :: "V \<Rightarrow> V \<Rightarrow> V"
  where "Vapp v x = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>s\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> f\<cdot>x | Vtfun\<cdot>f \<Rightarrow> Wrong | Wrong \<Rightarrow> Wrong)"

definition Vlam :: "kstar \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "Vlam t f = Vfun\<cdot>(\<Lambda> x. f (cast\<cdot>(kstar_denote t)\<cdot>x))"

lemma cont_Vapp [simp, cont2cont]:
  assumes u: "cont (\<lambda>x. u x)" and v: "cont (\<lambda>x. v x)"
  shows "cont (\<lambda>x. Vapp (u x) (v x))"
unfolding Vapp_def
by (simp add: cont_compose [OF u] cont_compose [OF v])

lemma cont_Vlam [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Vlam t (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vlam_def
    by (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

lemma cast_Tfun:
  "cast\<cdot>(kstar_denote (Tapp (Tapp Tfun a) b)) = fup\<cdot>Vfun oo
    u_map\<cdot>(cfun_map\<cdot>(cast\<cdot>(kstar_denote a))\<cdot>(cast\<cdot>(kstar_denote b))) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>\<cdot>\<bottom>"
unfolding kstar_denote_def
apply (simp add: to_ty_Tapp to_ty_Tfun)
apply (simp add: TyFun_denote_def)
apply (subst cast_defl_fun2)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (simp add: finite_deflation_u_map finite_deflation_cfun_map)
apply (simp add: eta_cfun)
done

lemma has_type_Vlam:
  assumes 1: "cont f"
  assumes 2: "\<And>x. has_type x a \<Longrightarrow> has_type (f x) b"
  shows "has_type (Vlam a (\<lambda>x. f x)) (Tapp (Tapp Tfun a) b)"
apply (simp add: has_type_def cast_Tfun)
apply (simp add: Vlam_def)
apply (rule cfun_eqI, simp add: cont_compose [OF 1])
apply (rule has_type_def [THEN iffD1])
apply (rule 2)
apply (rule has_type_def [THEN iffD2])
apply simp
done

lemma has_type_Vapp:
  assumes f: "has_type f (Tapp (Tapp Tfun a) b)"
  assumes x: "has_type x a"
  shows "has_type (Vapp f x) b"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_elim [OF x], rename_tac x')
apply (rule has_type_def [THEN iffD2])
apply (simp add: Vapp_def)
apply (simp add: cast_Tfun)
apply (case_tac f', simp_all)
done

lemma Vapp_Vlam:
  assumes f: "cont f"
  assumes x: "has_type y t"
  shows "Vapp (Vlam t f) y = f y"
unfolding Vapp_def Vlam_def
apply (simp add: cont_compose [OF f])
apply (rule has_type_elim [OF x], simp)
done


subsection {* Application and abstraction of types *}

definition Vtapp :: "V \<Rightarrow> 'k::kind \<Rightarrow> V"
  where "Vtapp v t = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>n\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> Wrong | Vtfun\<cdot>f \<Rightarrow> f\<cdot>(Discr (to_ty t)) | Wrong \<Rightarrow> Wrong)"

definition Vtlam :: "('k::kind \<Rightarrow> V) \<Rightarrow> V"
  where "Vtlam f = Vtfun\<cdot>(\<Lambda> u. if has_kind [] (undiscr u) (the_kind TYPE('k))
    then f (of_ty (undiscr u)) else \<bottom>)"

lemma cont_Vtapp [simp, cont2cont]:
  assumes v: "cont (\<lambda>x. v x)"
  shows "cont (\<lambda>x. Vtapp (v x) t)"
unfolding Vtapp_def by (simp add: v)

lemma cont_Vtlam [simp, cont2cont]:
  assumes f: "\<And>t. cont (\<lambda>x. f x t)"
  shows "cont (\<lambda>x. Vtlam (\<lambda>t. f x t))"
unfolding Vtlam_def by (simp add: f)

lemma Vtapp_Vtlam:
  shows "Vtapp (Vtlam (\<lambda>a. h a)) t = h t"
unfolding Vtapp_def Vtlam_def
by (simp add: has_kind_to_ty to_ty_inverse)

lemma cast_kstar_denote_Tforall:
  assumes h: "kcont (h::'k::kind \<Rightarrow> kstar)"
  shows "cast\<cdot>(kstar_denote (Tforall h)) = fup\<cdot>Vtfun oo
    u_map\<cdot>(\<Lambda> f x. if has_kind [] (undiscr x) (the_kind TYPE('k::kind))
      then cast\<cdot>(kstar_denote (h (of_ty (undiscr x))))\<cdot>(f\<cdot>x) else \<bottom>) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>"
unfolding kstar_denote_def
using ty_of_fun_correct [OF h]
apply (clarsimp simp add: fun_has_ty_def)
apply (subst to_ty_Tforall [OF h])
apply (simp add: cast_Uforall)
apply (intro cfun_arg_cong cfun_fun_cong LAM_eqI)
apply (simp add: ty_denote_ty_subst substVar_0 of_ty_inverse)
done

lemma has_type_Vtlam:
  assumes h: "kcont h"
  assumes f: "\<And>a. has_type (f a) (h a)"
  shows "has_type (Vtlam f) (Tforall (\<lambda>a. h a))"
apply (simp add: Vtlam_def has_type_def)
apply (subst cast_kstar_denote_Tforall [OF h])
apply (simp add: cfun_eq_iff)
apply (rule allI, rule impI)
apply (rule has_type_def [THEN iffD1])
apply (rule f)
done

lemma has_type_Vtapp:
  assumes f: "has_type f (Tforall h)"
  assumes h: "kcont h"
  shows "has_type (Vtapp f a) (h a)"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_def [THEN iffD2])
apply (simp add: Vtapp_def)
apply (simp add: cast_kstar_denote_Tforall [OF h])
apply (case_tac f', simp_all add: to_ty_inverse)
done


subsection {* Algebraic datatypes *}

inductive have_types :: "V list \<Rightarrow> kstar list \<Rightarrow> bool"
  where "have_types [] []"
  | "\<lbrakk>has_type x t; have_types xs ts\<rbrakk> \<Longrightarrow> have_types (x # xs) (t # ts)"

inductive_cases have_types_elims:
  "have_types vs []"
  "have_types vs (t # ts)"

lemma have_types_simps [simp]:
  "have_types [] []"
  "\<not> have_types [] (t # ts)"
  "\<not> have_types (x # xs) []"
  "have_types (x # xs) (t # ts) \<longleftrightarrow> has_type x t \<and> have_types xs ts"
by (auto intro: have_types.intros elim: have_types.cases)

lemma have_types_iff:
  "have_types xs ts \<longleftrightarrow> cast\<cdot>(defls\<cdot>(map kstar_denote ts))\<cdot>(up\<cdot>xs) = up\<cdot>xs"
apply (induct ts arbitrary: xs)
apply (simp add: cast_Nil_defl)
apply (case_tac xs, simp, simp)
apply (simp add: cast_Cons_defl)
apply (simp add: cast_defl_fun1 ep_pair.intro finite_deflation_u_map)
apply (case_tac xs, simp, simp)
apply (case_tac "cast\<cdot>(defls\<cdot>(map kstar_denote ts))\<cdot>(up\<cdot>list)", simp, simp)
apply (simp add: has_type_def)
done

lemma has_type_Tdata_elim:
  assumes "has_type x (Tdata tss)"
  obtains "x = \<bottom>" | n xs ts where "x = Vcon\<cdot>n\<cdot>xs"
  and "mapsto tss n ts" and "have_types xs ts"
using assms
unfolding has_type_def kstar_denote_def
apply (simp add: to_ty_Tdata cast_datadefl)
apply (cases x, simp_all add: o_def)
apply (simp only: kstar_denote_def [symmetric])
apply (case_tac "cast\<cdot>(nth_defls\<cdot>(map (map kstar_denote) tss)\<cdot>nat)\<cdot>(up\<cdot>list)", simp_all)
apply (simp add: nth_defls_eq split: split_if_asm)
apply (simp add: have_types_iff [symmetric])
apply (simp add: mapsto_iff)
apply fast
done

lemma mapsto_Nil_elim: "mapsto [] n y \<Longrightarrow> P"
by simp

lemma mapsto_Cons_elim:
  assumes "mapsto (x # xs) n y"
  obtains "n = 0" and "y = x"
  | n' where "n = Suc n'" and "mapsto xs n' y"
using assms by (cases n, simp_all)

lemmas mapsto_elims = mapsto_Nil_elim mapsto_Cons_elim

lemmas has_type_Tdata_elims =
  has_type_Tdata_elim
  mapsto_elims
  have_types_elims

definition has_constructor :: "kstar \<Rightarrow> nat \<Rightarrow> kstar list \<Rightarrow> bool"
  where "has_constructor t n ts \<longleftrightarrow>
    (\<exists>tss. ty_denote \<bottom> (to_ty t) = ty_denote \<bottom> (TyData tss) \<and>
      mapsto tss n (map to_ty ts))"

lemma mapsto_nth_defls:
  "mapsto dss n ds \<Longrightarrow> nth_defls\<cdot>dss\<cdot>n = defls\<cdot>ds"
by (induct dss arbitrary: n, simp, case_tac n, simp_all)

lemma mapsto_map: "mapsto xs n y \<Longrightarrow> mapsto (map f xs) n (f y)"
by (simp add: mapsto_iff)

lemma has_type_Vcon:
  assumes t: "has_constructor t n ts"
  assumes xs: "have_types xs ts"
  shows "has_type (Vcon\<cdot>n\<cdot>xs) t"
using assms unfolding has_constructor_def
apply clarsimp
apply (drule_tac f="map (\<lambda>t. unUdefl\<cdot>(ty_denote \<bottom> t))" in mapsto_map)
apply (drule mapsto_nth_defls)
apply (simp add: has_type_def kstar_denote_def)
apply (simp add: cast_datadefl o_def)
apply (simp add: kstar_denote_def [symmetric])
apply (simp add: have_types_iff)
done


subsection {* Case expressions *}

subsubsection {* Single case branches *}

text {* In a case expression like @{text "case t of Node l r \<rightarrow> e"}, a
value of type @{text B} represents the part @{text "l r \<rightarrow> e"}. It
binds a list of variables, and returns the right-hand side. *}

domain_isomorphism B = "V list \<rightarrow> V"

definition B_type :: "B \<Rightarrow> kstar list \<Rightarrow> kstar \<Rightarrow> bool"
  where "B_type b ts u \<longleftrightarrow> (\<forall>xs. have_types xs ts \<longrightarrow> has_type (B_rep\<cdot>b\<cdot>xs) u)"

definition Bnone :: "V \<Rightarrow> B"
  where "Bnone v = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> Wrong)"

definition Bval :: "kstar \<Rightarrow> (V \<Rightarrow> B) \<Rightarrow> B"
  where "Bval t f = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> Wrong |
    y # ys \<Rightarrow> B_rep\<cdot>(f (cast\<cdot>(kstar_denote t)\<cdot>y))\<cdot>ys)"

text {* Both branch combinators satisfy rewrite rules. *}

lemma B_rep_Bnone: "B_rep\<cdot>(Bnone v)\<cdot>[] = v"
by (simp add: Bnone_def B.abs_iso)

lemma B_rep_Bval:
  assumes f: "cont f" and x: "has_type x t"
  shows "B_rep\<cdot>(Bval t f)\<cdot>(x # xs) = B_rep\<cdot>(f x)\<cdot>xs"
unfolding Bval_def B.abs_iso
by (simp add: cont_compose [OF f] x [unfolded has_type_def])

text {* Both branch combinators are continuous. *}

theorem cont_Bnone [simp, cont2cont]:
  assumes "cont f" shows "cont (\<lambda>x. Bnone (f x))"
using assms unfolding Bnone_def
by (simp add: cont2cont_LAM)

theorem cont_Bval [simp, cont2cont]:
  assumes "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Bval t (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Bval_def
    by (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

text {* Both branch combinators obey typing rules. *}

lemma B_type_Bnone: "has_type y u \<Longrightarrow> B_type (Bnone y) [] u"
unfolding B_type_def
apply (clarify elim!: have_types_elims)
apply (simp add: B_rep_Bnone)
done

lemma B_type_Bval:
  assumes "cont (\<lambda>x. b x)"
  assumes "\<And>x. has_type x t \<Longrightarrow> B_type (b x) ts u"
  shows "B_type (Bval t (\<lambda>x. b x)) (t # ts) u"
using assms unfolding B_type_def
apply (clarify elim!: have_types_elims)
apply (simp add: B_rep_Bval)
done

subsubsection {* Blocks of case branches *}

text {* In a case expression like @{text "case m of {Just x \<rightarrow> a;
Nothing \<rightarrow> b}"}, a value of type @{text M} represents the part @{text
"{Just x \<rightarrow> a; Nothing \<rightarrow> b}"}. Type @{text M} is modeled using a strict
function space because case expressions in GHC-Core are always strict.
The argument type is @{typ V} rather than @{typ "string \<times> V list"}
because case expressions can also force evaluation of non-datatypes,
such as functions. *}

domain_isomorphism M = "V \<rightarrow>! V"

definition M_type :: "M \<Rightarrow> kstar \<Rightarrow> kstar \<Rightarrow> bool"
  where "M_type m t u \<longleftrightarrow>
    (\<forall>x. has_type x t \<longrightarrow> has_type (sfun_rep\<cdot>(M_rep\<cdot>m)\<cdot>x) u)"

definition Mwild :: "V \<Rightarrow> M"
  where "Mwild v = M_abs\<cdot>(sfun_abs\<cdot>(\<Lambda> x. v))"

text {* Defining this to return @{text Wrong} would more accurately
reflect the run-time behavior, but using @{text "\<bottom>"} makes it easier
to prove typing rules. *}

definition Mnone :: "M"
  where "Mnone = Mwild \<bottom>"

definition Mbranch :: "nat \<Rightarrow> B \<Rightarrow> M \<Rightarrow> M"
  where "Mbranch s b m = M_abs\<cdot>(sfun_abs\<cdot>(\<Lambda> x. case x of
    Vint\<cdot>n \<Rightarrow> Wrong |
    Vcon\<cdot>s'\<cdot>xs \<Rightarrow> if s = s' then B_rep\<cdot>b\<cdot>xs else sfun_rep\<cdot>(M_rep\<cdot>m)\<cdot>x |
    Vfun\<cdot>f \<Rightarrow> Wrong | Vtfun\<cdot>f \<Rightarrow> Wrong | Wrong \<Rightarrow> Wrong))"

text {* All match combinators are continuous. *}

lemma cont_Mwild [simp, cont2cont]:
  assumes "cont f" shows "cont (\<lambda>x. Mwild (f x))"
unfolding Mwild_def by (simp add: cont_compose [OF assms])

lemma cont_Mbranch [simp, cont2cont]:
  assumes "cont b" and "cont m"
  shows "cont (\<lambda>x. Mbranch s (b x) (m x))"
unfolding Mbranch_def
by (intro cont2cont assms [THEN cont_compose])

text {* All match combinators obey typing rules *}

(*lemma has_constructor_intro:
  "\<lbrakk>t = datadefl ds; lookup_defls\<cdot>ds\<cdot>s = defls\<cdot>ts\<rbrakk> \<Longrightarrow> has_constructor t s ts"
unfolding has_constructor_def by auto*)

lemma M_type_Mbranch:
  assumes 1: "has_constructor t s ts"
  assumes 2: "B_type b ts u"
  assumes 3: "M_type m t u"
  shows "M_type (Mbranch s b m) t u"
using assms
apply -
apply (clarsimp simp add: M_type_def)
apply (drule spec, drule (1) mp)
apply (simp add: Mbranch_def M.abs_iso strictify_cancel)
apply (clarsimp simp add: has_constructor_def)
apply (simp only: has_type_def)
apply (simp only: has_type_def [where t=u, symmetric])
apply (simp add: kstar_denote_def)
apply (simp add: cast_datadefl)
apply (case_tac x, simp_all)
apply clarsimp
apply (simp add: B_type_def)
apply (drule spec, erule mp)
apply (drule_tac f="map (\<lambda>t. unUdefl\<cdot>(ty_denote \<bottom> t))" in mapsto_map)
apply (simp add: mapsto_nth_defls o_def)
apply (simp add: kstar_denote_def [symmetric])
apply (case_tac "cast\<cdot>(defls\<cdot>(map kstar_denote ts))\<cdot>(up\<cdot>list)")
apply simp
apply (simp add: have_types_iff)
done

lemma M_type_Mwild:
  assumes "has_type x u"
  shows "M_type (Mwild x) t u"
using assms unfolding M_type_def Mwild_def
by (simp add: M.abs_iso strictify_conv_if has_type_bottom)

lemma M_type_Mnone:
  shows "M_type Mnone t u"
unfolding Mnone_def
by (intro M_type_Mwild has_type_bottom)

subsubsection {* Full case expressions *}

definition Vcase :: "kstar \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> M) \<Rightarrow> V"
  where "Vcase t v m = sfun_rep\<cdot>(M_rep\<cdot>(m v))\<cdot>v"

text {* The case expression combinator is continuous. *}

lemma cont_Vcase [simp, cont2cont]:
  assumes "cont v" and "cont (\<lambda>p. m (fst p) (snd p))"
  shows "cont (\<lambda>x. Vcase (t x) (v x) (\<lambda>w. m x w))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. m x y)" and 2: "\<And>x. cont (\<lambda>y. m x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vcase_def
    apply (rule cont_apply [OF assms(1)])
    apply (simp_all add: cont_compose [OF 1] cont_compose [OF 2])
    done
qed

text {* The case expression combinator obeys a typing rule. *}

lemma has_type_Vcase:
  assumes x: "has_type x t"
  assumes m: "\<And>w. has_type w t \<Longrightarrow> M_type (m w) t u"
  shows "has_type (Vcase u x (\<lambda>w. m w)) u"
using assms unfolding Vcase_def M_type_def by simp

text {* Case expressions satisfy some basic rewrite rules. *}

theorem Vcase_Mwild:
  assumes f: "cont f" and x: "x \<noteq> \<bottom>"
  shows "Vcase t x (\<lambda>w. Mwild (f w)) = f x"
by (simp add: Vcase_def Mwild_def M.abs_iso x)

theorem Vcase_Vcon_Mwild:
  assumes "cont f"
  shows "Vcase t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. Mwild (f w)) = f (Vcon\<cdot>s\<cdot>xs)"
using assms by (rule Vcase_Mwild) simp

theorem Vcase_Vlam_Mwild:
  assumes "cont f"
  shows "Vcase t' (Vlam t g) (\<lambda>w. Mwild (f w)) = f (Vlam t g)"
using assms by (rule Vcase_Mwild, simp add: Vlam_def)

theorem Vcase_Mbranch_neq:
  "s \<noteq> s' \<Longrightarrow> Vcase t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. Mbranch s' (b w) (m w)) =
    Vcase t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. m w)"
by (simp add: Vcase_def Mbranch_def M.abs_iso)

lemma Vcase_Mbranch_eq:
  "Vcase t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. Mbranch s (b w) (m w)) = B_rep\<cdot>(b (Vcon\<cdot>s\<cdot>xs))\<cdot>xs"
by (simp add: Vcase_def Mbranch_def M.abs_iso)


subsection {* Let expressions *}

subsubsection {* Non-recursive let expressions *}

definition Vlet :: "kstar \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "Vlet t e f = f (cast\<cdot>(kstar_denote t)\<cdot>e)"

lemma cont_Vlet [simp, cont2cont]:
  assumes e: "cont (\<lambda>x. e x)"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Vlet t (e x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vlet_def
    apply (rule cont_apply [OF e _ 1])
    apply (simp add: cont_compose [OF 2])
    done
qed

lemma has_type_Vlet:
  assumes e: "has_type e t"
  assumes f: "\<And>x. has_type x t \<Longrightarrow> has_type (f x) t'"
  shows "has_type (Vlet t e (\<lambda>x. f x)) t'"
using e f by (simp add: Vlet_def has_type_def)

lemma Vlet_cong:
  assumes e: "e = e'"
  assumes f: "\<And>x. has_type x t \<Longrightarrow> f x = f' x"
  shows "Vlet t e (\<lambda>x. f x) = Vlet t e' (\<lambda>x. f' x)"
using e f by (simp add: Vlet_def has_type_def)

lemma Vlet_unfold:
  assumes "has_type e t"
  shows "Vlet t e f = f e"
using assms by (simp add: Vlet_def has_type_def)

end
