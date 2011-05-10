header {* Definitions of combinators and typing relations *}

theory Halicore_Defs
imports
  HOLCF
  "~~/src/HOL/HOLCF/Library/HOL_Cpo"
  Defl_Lib
begin

subsection {* Domain definitions for Core values and types *}

domain V
  = Vint (lazy "int")
  | Vcon (lazy "string") (lazy "V list")
  | Vfun (lazy "V \<rightarrow> V")
  | Vtfun (lazy "U \<rightarrow> V")
  | Wrong
and U
  = Udefl "T"
  | Ufun "U \<rightarrow> U"
and T ("\<star>")
  = MkT "V defl"


subsection {* Class of kinds *}

text "Core types of all kinds should be embeddable into type U."

class kind = "domain" +
  fixes to_U :: "'a \<rightarrow> U"
  fixes of_U :: "U \<rightarrow> 'a"
  assumes kind: "ep_pair to_U of_U"

interpretation kind: pcpo_ep_pair to_U of_U
unfolding pcpo_ep_pair_def by (rule kind)

instantiation T :: kind
begin

definition "to_U = Udefl"

definition "of_U = (\<Lambda>(Udefl\<cdot>d). d)"

instance proof
  show "ep_pair (to_U :: T \<rightarrow> U) (of_U :: U \<rightarrow> T)"
    unfolding to_U_T_def of_U_T_def
    apply (rule ep_pair.intro)
    apply (case_tac "x = \<bottom>", simp, simp)
    apply (case_tac "y", simp_all)
    done
qed

end

instantiation cfun :: (kind, kind) kind
begin

definition "to_U = Ufun oo cfun_map\<cdot>of_U\<cdot>to_U"

definition "of_U = cfun_map\<cdot>to_U\<cdot>of_U oo (\<Lambda>(Ufun\<cdot>f). f)"

instance proof
  show "ep_pair (to_U :: ('a \<rightarrow> 'b) \<rightarrow> U) (of_U :: U \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding to_U_cfun_def of_U_cfun_def
    apply (intro ep_pair_comp ep_pair_cfun_map kind)
    apply (rule ep_pair.intro)
    apply (case_tac "x = \<bottom>", simp, simp)
    apply (case_tac y, simp_all)
    done
qed

end

text "Application of types to types:"

definition Tapp :: "('a::kind \<rightarrow> 'b::kind) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "Tapp = Rep_cfun"

lemma cont_Tapp [simp, cont2cont]:
  assumes "cont (\<lambda>x. t x)" and "cont (\<lambda>x. u x)"
  shows "cont (\<lambda>x. Tapp (t x) (u x))"
using assms unfolding Tapp_def by (rule cont2cont_APP)


subsection {* Lambda calculus *}

subsubsection {* Typing relation *}

definition has_type :: "V \<Rightarrow> T \<Rightarrow> bool" (infix ":::" 50)
  where "x ::: t \<longleftrightarrow> cast\<cdot>(T_rep\<cdot>t)\<cdot>x = x"

lemma has_type_bottom: "\<bottom> ::: t"
  unfolding has_type_def by simp

lemma has_type_elim:
  assumes "x ::: t" obtains y where "x = cast\<cdot>(T_rep\<cdot>t)\<cdot>y"
using assms unfolding has_type_def by metis


subsubsection {* Function types and value application *}

definition Tfun :: "T \<rightarrow> T \<rightarrow> T"
  where "Tfun = (\<Lambda> a b. T_abs\<cdot>(defl_fun2 (\<Lambda>(up\<cdot>f). Vfun\<cdot>f) (\<Lambda>(Vfun\<cdot>f). up\<cdot>f)
    (\<Lambda> d e. u_map\<cdot>(cfun_map\<cdot>d\<cdot>e))\<cdot>(T_rep\<cdot>a)\<cdot>(T_rep\<cdot>b)))"

lemma cast_T_rep_Tfun:
  "cast\<cdot>(T_rep\<cdot>(Tapp (Tapp Tfun a) b)) = fup\<cdot>Vfun oo
    u_map\<cdot>(cfun_map\<cdot>(cast\<cdot>(T_rep\<cdot>a))\<cdot>(cast\<cdot>(T_rep\<cdot>b))) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>\<cdot>\<bottom>"
apply (simp add: Tfun_def Tapp_def)
apply (subst cast_defl_fun2)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (simp add: finite_deflation_u_map finite_deflation_cfun_map)
apply (simp add: eta_cfun)
done

definition Vapp :: "V \<Rightarrow> V \<Rightarrow> V"
  where "Vapp v x = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>s\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> f\<cdot>x | Vtfun\<cdot>f \<Rightarrow> Wrong | Wrong \<Rightarrow> Wrong)"

definition Vlam :: "T \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "Vlam t f = Vfun\<cdot>(\<Lambda> x. f (cast\<cdot>(T_rep\<cdot>t)\<cdot>x))"

lemma cont_Vapp [simp, cont2cont]:
  assumes u: "cont (\<lambda>x. u x)" and v: "cont (\<lambda>x. v x)"
  shows "cont (\<lambda>x. Vapp (u x) (v x))"
unfolding Vapp_def
by (simp add: cont_compose [OF u] cont_compose [OF v])

lemma cont_Vlam [simp, cont2cont]:
  assumes t: "cont (\<lambda>x. t x)"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Vlam (t x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vlam_def
    apply (rule cont_apply [OF t])
    apply (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
    done
qed

lemma has_type_Vlam:
  assumes 1: "cont f"
  assumes 2: "\<And>x. x ::: a \<Longrightarrow> f x ::: b"
  shows "Vlam a (\<lambda>x. f x) ::: Tapp (Tapp Tfun a) b"
apply (simp add: has_type_def cast_T_rep_Tfun)
apply (simp add: Vlam_def)
apply (rule cfun_eqI, simp add: cont_compose [OF 1])
apply (rule has_type_def [THEN iffD1])
apply (rule 2)
apply (rule has_type_def [THEN iffD2])
apply simp
done

lemma has_type_Vapp:
  assumes f: "f ::: Tapp (Tapp Tfun a) b"
  assumes x: "x ::: a"
  shows "Vapp f x ::: b"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_elim [OF x], rename_tac x')
apply (rule has_type_def [THEN iffD2])
apply (simp add: Vapp_def)
apply (simp add: cast_T_rep_Tfun)
apply (case_tac f', simp_all)
done

lemma Vapp_Vlam:
  assumes f: "cont f"
  assumes x: "y ::: t"
  shows "Vapp (Vlam t f) y = f y"
unfolding Vapp_def Vlam_def
apply (simp add: cont_compose [OF f])
apply (rule has_type_elim [OF x], simp)
done


subsection {* Forall-types and type application *}

definition Vtlam :: "('k::kind \<Rightarrow> V) \<Rightarrow> V"
  where "Vtlam f = Vtfun\<cdot>(\<Lambda> u. f (of_U\<cdot>u))"

definition Vtapp :: "V \<Rightarrow> 'k::kind \<Rightarrow> V"
  where "Vtapp v t = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>s\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> Wrong | Vtfun\<cdot>f \<Rightarrow> f\<cdot>(to_U\<cdot>t) | Wrong \<Rightarrow> Wrong)"

lemma cont_Vtapp [simp, cont2cont]:
  assumes v: "cont (\<lambda>x. v x)"
  assumes t: "cont (\<lambda>x. t x)"
  shows "cont (\<lambda>x. Vtapp (v x) (t x))"
unfolding Vtapp_def by (simp add: v cont_compose [OF t])

lemma cont_Vtlam [simp, cont2cont]:
  assumes "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Vtlam (\<lambda>a. f x a))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vtlam_def
    by (simp add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

definition Tforall :: "('k::kind \<Rightarrow> T) \<Rightarrow> T"
  where "Tforall h = T_abs\<cdot>(defl_fun1 (fup\<cdot>Vtfun) (V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>) u_map\<cdot>
    (pi_defl\<cdot>ID_defl\<cdot>(\<Lambda> u. T_rep\<cdot>(h (of_U\<cdot>u)))))"

lemma cont_Tforall [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Tforall (\<lambda>a. f x a))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Tforall_def
    by (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

lemma cast_T_rep_Tforall:
  assumes h: "cont (h::'k::kind \<Rightarrow> T)"
  shows "cast\<cdot>(T_rep\<cdot>(Tforall h)) = fup\<cdot>Vtfun oo
    u_map\<cdot>(\<Lambda> f x. cast\<cdot>(T_rep\<cdot>(h (of_U\<cdot>x)))\<cdot>(f\<cdot>x)) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>"
unfolding Tforall_def T.abs_iso
apply (subst cast_defl_fun1)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (erule finite_deflation_u_map)
apply (intro cfun_cong refl)
apply (subst cast_pi_defl)
apply (simp add: h [THEN cont_compose])
done

lemma has_type_Vtlam:
  assumes 1: "cont f"
  assumes 2: "cont h"
  assumes 3: "\<And>a. f a ::: h a"
  shows "Vtlam f ::: Tforall (\<lambda>a. h a)"
apply (simp add: has_type_def cast_T_rep_Tforall [OF 2])
apply (simp add: Vtlam_def)
apply (rule cfun_eqI, simp add: cont_compose [OF 1] cont_compose [OF 2])
apply (rule has_type_def [THEN iffD1])
apply (rule 3)
done

lemma has_type_Vtapp:
  assumes f: "f ::: Tforall h"
  assumes h: "cont h"
  shows "Vtapp f a ::: h a"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_def [THEN iffD2])
apply (simp add: Vtapp_def)
apply (simp add: cast_T_rep_Tforall [OF h])
apply (case_tac f', simp_all add: cont_compose [OF h])
done

lemma Vtapp_Vtlam:
  assumes h: "cont (\<lambda>a. h a)"
  shows "Vtapp (Vtlam (\<lambda>a. h a)) t = h t"
unfolding Vtapp_def Vtlam_def
by (simp add: cont_compose [OF h])


subsection {* Datatypes *}

definition Nil_defl :: "'a list u defl"
  where "Nil_defl = defl_principal (Abs_fin_defl
    (\<Lambda>(up\<cdot>xs). case xs of [] \<Rightarrow> up\<cdot>[] | y # ys \<Rightarrow> \<bottom>))"

lemma cast_Nil_defl:
  "cast\<cdot>Nil_defl = (\<Lambda>(up\<cdot>xs). case xs of [] \<Rightarrow> up\<cdot>[] | y # ys \<Rightarrow> \<bottom>)"
unfolding Nil_defl_def
apply (subst cast_defl_principal)
apply (rule Abs_fin_defl_inverse, simp)
apply default
apply (case_tac x, simp, rename_tac xs, case_tac xs, simp, simp)
apply (case_tac x, simp, rename_tac xs, case_tac xs, simp, simp)
apply (rule finite_range_imp_finite_fixes)
apply (rule rev_finite_subset [where B="{\<bottom>, up\<cdot>[]}"], simp)
apply (clarsimp, rename_tac y, case_tac y, simp, case_tac x, simp, simp)
done

definition Cons_defl :: "'a u defl \<rightarrow> 'a list u defl \<rightarrow> 'a list u defl"
  where "Cons_defl = defl_fun2
    (\<Lambda>(:up\<cdot>x, up\<cdot>xs:). up\<cdot>(x # xs))
    (\<Lambda>(up\<cdot>ys). case ys of [] \<Rightarrow> \<bottom> | x # xs \<Rightarrow> (:up\<cdot>x, up\<cdot>xs:))
    sprod_map"

lemma cast_Cons_defl:
  "cast\<cdot>(Cons_defl\<cdot>a\<cdot>b) = (\<Lambda>(:up\<cdot>x, up\<cdot>xs:). up\<cdot>(x # xs))
    oo sprod_map\<cdot>(cast\<cdot>a)\<cdot>(cast\<cdot>b) oo
    (\<Lambda>(up\<cdot>ys). case ys of [] \<Rightarrow> \<bottom> | x # xs \<Rightarrow> (:up\<cdot>x, up\<cdot>xs:))"
unfolding Cons_defl_def
apply (rule cast_defl_fun2)
apply (rule ep_pair.intro)
apply (rename_tac p, case_tac p, simp)
apply (case_tac x, simp, case_tac y, simp, simp)
apply (case_tac y, simp, case_tac x, simp, simp)
apply (erule (1) finite_deflation_sprod_map)
done

fixrec defls :: "T list \<rightarrow> V list u defl"
  where "defls\<cdot>[] = Nil_defl"
  | "defls\<cdot>(d # ds) = Cons_defl\<cdot>(defl_fun1 ID ID u_map\<cdot>(T_rep\<cdot>d))\<cdot>(defls\<cdot>ds)"

fixrec lookup_defls :: "(string \<times> T list) list \<rightarrow> string \<rightarrow> V list u defl"
  where "lookup_defls\<cdot>(x # xs)\<cdot>s =
    (if fst x = s then defls\<cdot>(snd x) else lookup_defls\<cdot>xs\<cdot>s)"

lemma lookup_defls_Nil: "lookup_defls\<cdot>[]\<cdot>s = \<bottom>"
by fixrec_simp

definition "datatype" :: "(string \<times> T list) list \<Rightarrow> T"
  where "datatype xs =
  T_abs\<cdot>
  (defl_fun1 (\<Lambda>(:up\<cdot>s, up\<cdot>vs:). Vcon\<cdot>s\<cdot>vs) (\<Lambda>(Vcon\<cdot>s\<cdot>vs). (:up\<cdot>s, up\<cdot>vs:)) ID\<cdot>
  (sprod_of_prod_defl\<cdot>
  (sig_defl\<cdot>ID_defl\<cdot>(\<Lambda>(up\<cdot>s). lookup_defls\<cdot>xs\<cdot>s))))"

lemma cont_datatype [THEN cont_compose, simp, cont2cont]:
  "cont (\<lambda>xs. datatype xs)"
unfolding datatype_def by simp

lemma cast_datatype:
  "cast\<cdot>(T_rep\<cdot>(datatype xs)) = (\<Lambda>(Vcon\<cdot>s\<cdot>vs). ssplit\<cdot>(\<Lambda> (up\<cdot>s).
    fup\<cdot>(Vcon\<cdot>s))\<cdot>(:up\<cdot>s, cast\<cdot>(lookup_defls\<cdot>xs\<cdot>s)\<cdot>(up\<cdot>vs):))"
unfolding datatype_def T.abs_iso
apply (subst cast_defl_fun1)
apply (rule ep_pair.intro)
apply (case_tac x, simp, rename_tac a b)
apply (case_tac a, simp, case_tac b, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply simp
apply (simp add: cast_sprod_of_prod_defl cast_sig_defl)
apply (rule cfun_eqI, simp)
apply (case_tac x, simp_all add: eta_cfun)
done

inductive have_types :: "V list \<Rightarrow> T list \<Rightarrow> bool"
  where "have_types [] []"
  | "\<lbrakk>has_type x t; have_types xs ts\<rbrakk> \<Longrightarrow> have_types (x # xs) (t # ts)"

lemma have_types_simps [simp]:
  "have_types [] []"
  "\<not> have_types [] (t # ts)"
  "\<not> have_types (x # xs) []"
  "have_types (x # xs) (t # ts) \<longleftrightarrow> x ::: t \<and> have_types xs ts"
by (auto intro: have_types.intros elim: have_types.cases)

lemma have_types_iff: "have_types xs ts \<longleftrightarrow> cast\<cdot>(defls\<cdot>ts)\<cdot>(up\<cdot>xs) = up\<cdot>xs"
apply (induct ts arbitrary: xs)
apply (simp add: cast_Nil_defl)
apply (case_tac xs, simp, simp)
apply (simp add: cast_Cons_defl)
apply (simp add: cast_defl_fun1 ep_pair.intro finite_deflation_u_map)
apply (case_tac xs, simp, simp)
apply (case_tac "cast\<cdot>(defls\<cdot>ts)\<cdot>(up\<cdot>list)", simp, simp)
apply (simp add: has_type_def)
done

lemma has_type_datatype_Nil_elim:
  assumes "x ::: datatype []" obtains "x = \<bottom>"
using assms unfolding has_type_def cast_datatype
by (cases x, simp_all add: lookup_defls_Nil)

lemma has_type_datatype_Cons_elim:
  assumes "x ::: datatype ((s, ts) # ds)"
  obtains vs where "x = Vcon\<cdot>s\<cdot>vs" and "have_types vs ts"
  | "x ::: datatype ds"
using assms unfolding has_type_def cast_datatype
apply (cases x, simp_all, rename_tac s' xs)
apply (case_tac "s = s'", simp_all)
apply (case_tac "cast\<cdot>(defls\<cdot>ts)\<cdot>(up\<cdot>xs)", simp, simp)
apply (simp add: have_types_iff)
done

inductive_cases have_types_elims:
  "have_types vs []"
  "have_types vs (t # ts)"

lemmas has_type_datatype_elims =
  have_types_elims
  has_type_datatype_Cons_elim
  has_type_datatype_Nil_elim

definition has_constructor :: "T \<Rightarrow> string \<Rightarrow> T list \<Rightarrow> bool"
  where "has_constructor t s ts \<longleftrightarrow>
    (\<exists>ds. t = datatype ds \<and> lookup_defls\<cdot>ds\<cdot>s = defls\<cdot>ts)"

lemma has_type_Vcon:
  assumes t: "has_constructor t s ts"
  assumes xs: "have_types xs ts"
  shows "Vcon\<cdot>s\<cdot>xs ::: t"
using assms unfolding has_constructor_def
by (auto simp add: has_type_def cast_datatype have_types_iff)


subsection {* Case expressions *}

subsubsection {* Single case branches *}

text {* In a case expression like @{text "case t of Node l r \<rightarrow> e"}, a
value of type @{text B} represents the part @{text "l r \<rightarrow> e"}. It
binds a list of variables, and returns the right-hand side. *}

domain_isomorphism B = "V list \<rightarrow> V"

definition B_type :: "B \<Rightarrow> T list \<Rightarrow> T \<Rightarrow> bool"
  where "B_type b ts u \<longleftrightarrow> (\<forall>xs. have_types xs ts \<longrightarrow> B_rep\<cdot>b\<cdot>xs ::: u)"

definition Bnone :: "V \<Rightarrow> B"
  where "Bnone v = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> Wrong)"

definition Bval :: "T \<Rightarrow> (V \<Rightarrow> B) \<Rightarrow> B"
  where "Bval t f = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> Wrong |
    y # ys \<Rightarrow> B_rep\<cdot>(f (cast\<cdot>(T_rep\<cdot>t)\<cdot>y))\<cdot>ys)"

text {* Both branch combinators satisfy rewrite rules. *}

lemma B_rep_Bnone: "B_rep\<cdot>(Bnone v)\<cdot>[] = v"
by (simp add: Bnone_def B.abs_iso)

lemma B_rep_Bval:
  assumes f: "cont f" and x: "x ::: t"
  shows "B_rep\<cdot>(Bval t f)\<cdot>(x # xs) = B_rep\<cdot>(f x)\<cdot>xs"
unfolding Bval_def B.abs_iso
by (simp add: cont_compose [OF f] x [unfolded has_type_def])

text {* Both branch combinators are continuous. *}

theorem cont_Bnone [simp, cont2cont]:
  assumes "cont f" shows "cont (\<lambda>x. Bnone (f x))"
using assms unfolding Bnone_def
by (simp add: cont2cont_LAM)

theorem cont_Bval [simp, cont2cont]:
  assumes "cont t" and "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Bval (t x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Bval_def
    apply (rule cont_apply [OF assms(1)])
    apply (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
    done
qed

text {* Both branch combinators obey typing rules. *}

lemma B_type_Bnone: "y ::: u \<Longrightarrow> B_type (Bnone y) [] u"
unfolding B_type_def
apply (clarify elim!: have_types_elims)
apply (simp add: B_rep_Bnone)
done

lemma B_type_Bval:
  assumes "cont (\<lambda>x. b x)"
  assumes "\<And>x. x ::: t \<Longrightarrow> B_type (b x) ts u"
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

definition M_type :: "M \<Rightarrow> T \<Rightarrow> T \<Rightarrow> bool"
  where "M_type m t u \<longleftrightarrow> (\<forall>x. x ::: t \<longrightarrow> sfun_rep\<cdot>(M_rep\<cdot>m)\<cdot>x ::: u)"

definition Mwild :: "V \<Rightarrow> M"
  where "Mwild v = M_abs\<cdot>(sfun_abs\<cdot>(\<Lambda> x. v))"

text {* Defining this to return @{text Wrong} would more accurately
reflect the run-time behavior, but using @{text "\<bottom>"} makes it easier
to prove typing rules. *}

definition Mnone :: "M"
  where "Mnone = Mwild \<bottom>"

definition Mbranch :: "string \<Rightarrow> B \<Rightarrow> M \<Rightarrow> M"
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

lemma has_constructor_intro:
  "\<lbrakk>t = datatype ds; lookup_defls\<cdot>ds\<cdot>s = defls\<cdot>ts\<rbrakk> \<Longrightarrow> has_constructor t s ts"
unfolding has_constructor_def by auto

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
apply (simp add: cast_datatype)
apply (case_tac x, simp_all)
apply clarsimp
apply (simp add: B_type_def)
apply (drule spec, erule mp)
apply (case_tac "cast\<cdot>(defls\<cdot>ts)\<cdot>(up\<cdot>list2)", simp_all)
apply (simp add: have_types_iff)
done

lemma M_type_Mwild:
  assumes "x ::: u"
  shows "M_type (Mwild x) t u"
using assms unfolding M_type_def Mwild_def
by (simp add: M.abs_iso strictify_conv_if has_type_bottom)

lemma M_type_Mnone:
  shows "M_type Mnone t u"
unfolding Mnone_def
by (intro M_type_Mwild has_type_bottom)

subsubsection {* Full case expressions *}

definition Vcase :: "T \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> M) \<Rightarrow> V"
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
  assumes x: "x ::: t"
  assumes m: "\<And>w. w ::: t \<Longrightarrow> M_type (m w) t u"
  shows "Vcase u x (\<lambda>w. m w) ::: u"
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

subsection {* Non-recursive let expressions *}

definition Vlet :: "T \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "Vlet t e f = f (cast\<cdot>(T_rep\<cdot>t)\<cdot>e)"

lemma cont_Vlet [simp, cont2cont]:
  assumes t: "cont (\<lambda>x. t x)"
  assumes e: "cont (\<lambda>x. e x)"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. Vlet (t x) (e x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding Vlet_def
    apply (rule cont_apply [OF t])
    apply (simp add: cont_compose [OF 2])
    apply (rule cont_apply [OF e])
    apply (simp add: cont_compose [OF 2])
    apply (rule 1)
    done
qed

lemma has_type_Vlet:
  assumes e: "has_type e t"
  assumes f: "\<And>x. has_type x t \<Longrightarrow> has_type (f x) t'"
  shows "has_type (Vlet t e (\<lambda>x. f x)) t'"
using e f by (simp add: Vlet_def has_type_def)

lemma Vlet_cong:
  assumes e: "e = e'"
  assumes f: "\<And>x. x ::: t \<Longrightarrow> f x = f' x"
  shows "Vlet t e (\<lambda>x. f x) = Vlet t e' (\<lambda>x. f' x)"
using e f by (simp add: Vlet_def has_type_def)

lemma Vlet_unfold:
  assumes "has_type e t"
  shows "Vlet t e f = f e"
using assms by (simp add: Vlet_def has_type_def)

end
