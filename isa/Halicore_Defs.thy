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

definition T_apply :: "('a::kind \<rightarrow> 'b::kind) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "T_apply = Rep_cfun"

lemma cont_T_apply [simp, cont2cont]:
  assumes "cont (\<lambda>x. t x)" and "cont (\<lambda>x. u x)"
  shows "cont (\<lambda>x. T_apply (t x) (u x))"
using assms unfolding T_apply_def by (rule cont2cont_APP)


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

definition funT :: "T \<rightarrow> T \<rightarrow> T"
  where "funT = (\<Lambda> a b. T_abs\<cdot>(defl_fun2 (\<Lambda>(up\<cdot>f). Vfun\<cdot>f) (\<Lambda>(Vfun\<cdot>f). up\<cdot>f)
    (\<Lambda> d e. u_map\<cdot>(cfun_map\<cdot>d\<cdot>e))\<cdot>(T_rep\<cdot>a)\<cdot>(T_rep\<cdot>b)))"

lemma cast_T_rep_funT:
  "cast\<cdot>(T_rep\<cdot>(T_apply (T_apply funT a) b)) = fup\<cdot>Vfun oo
    u_map\<cdot>(cfun_map\<cdot>(cast\<cdot>(T_rep\<cdot>a))\<cdot>(cast\<cdot>(T_rep\<cdot>b))) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>\<cdot>\<bottom>"
apply (simp add: funT_def T_apply_def)
apply (subst cast_defl_fun2)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (simp add: finite_deflation_u_map finite_deflation_cfun_map)
apply (simp add: eta_cfun)
done

definition V_app :: "V \<Rightarrow> V \<Rightarrow> V"
  where "V_app v x = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>s\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> f\<cdot>x | Vtfun\<cdot>f \<Rightarrow> Wrong | Wrong \<Rightarrow> Wrong)"

definition V_lam :: "T \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "V_lam t f = Vfun\<cdot>(\<Lambda> x. f (cast\<cdot>(T_rep\<cdot>t)\<cdot>x))"

lemma cont_V_app [simp, cont2cont]:
  assumes u: "cont (\<lambda>x. u x)" and v: "cont (\<lambda>x. v x)"
  shows "cont (\<lambda>x. V_app (u x) (v x))"
unfolding V_app_def
by (simp add: cont_compose [OF u] cont_compose [OF v])

lemma cont_V_lam [simp, cont2cont]:
  assumes t: "cont (\<lambda>x. t x)"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. V_lam (t x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding V_lam_def
    apply (rule cont_apply [OF t])
    apply (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
    done
qed

lemma has_type_V_lam:
  assumes 1: "cont f"
  assumes 2: "\<And>x. x ::: a \<Longrightarrow> f x ::: b"
  shows "V_lam a (\<lambda>x. f x) ::: T_apply (T_apply funT a) b"
apply (simp add: has_type_def cast_T_rep_funT)
apply (simp add: V_lam_def)
apply (rule cfun_eqI, simp add: cont_compose [OF 1])
apply (rule has_type_def [THEN iffD1])
apply (rule 2)
apply (rule has_type_def [THEN iffD2])
apply simp
done

lemma has_type_V_app:
  assumes f: "f ::: T_apply (T_apply funT a) b"
  assumes x: "x ::: a"
  shows "V_app f x ::: b"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_elim [OF x], rename_tac x')
apply (rule has_type_def [THEN iffD2])
apply (simp add: V_app_def)
apply (simp add: cast_T_rep_funT)
apply (case_tac f', simp_all)
done

lemma V_beta:
  assumes f: "cont f"
  assumes x: "y ::: t"
  shows "V_app (V_lam t f) y = f y"
unfolding V_app_def V_lam_def
apply (simp add: cont_compose [OF f])
apply (rule has_type_elim [OF x], simp)
done


subsection {* Forall-types and type application *}

definition T_lam :: "('k::kind \<Rightarrow> V) \<Rightarrow> V"
  where "T_lam f = Vtfun\<cdot>(\<Lambda> u. f (of_U\<cdot>u))"

definition T_app :: "V \<Rightarrow> 'k::kind \<Rightarrow> V"
  where "T_app v t = (case v of Vint\<cdot>n \<Rightarrow> Wrong | Vcon\<cdot>s\<cdot>xs \<Rightarrow> Wrong |
    Vfun\<cdot>f \<Rightarrow> Wrong | Vtfun\<cdot>f \<Rightarrow> f\<cdot>(to_U\<cdot>t) | Wrong \<Rightarrow> Wrong)"

lemma cont_T_app [simp, cont2cont]:
  assumes v: "cont (\<lambda>x. v x)"
  assumes t: "cont (\<lambda>x. t x)"
  shows "cont (\<lambda>x. T_app (v x) (t x))"
unfolding T_app_def by (simp add: v cont_compose [OF t])

lemma cont_T_abs [simp, cont2cont]:
  assumes "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. T_lam (\<lambda>a. f x a))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding T_lam_def
    by (simp add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

definition forallT :: "('k::kind \<Rightarrow> T) \<Rightarrow> T"
  where "forallT h = T_abs\<cdot>(defl_fun1 (fup\<cdot>Vtfun) (V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>) u_map\<cdot>
    (pi_defl\<cdot>ID_defl\<cdot>(\<Lambda> u. T_rep\<cdot>(h (of_U\<cdot>u)))))"

lemma cont_forallT [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. forallT (\<lambda>a. f x a))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding forallT_def
    by (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
qed

lemma cast_T_rep_forallT:
  assumes h: "cont (h::'k::kind \<Rightarrow> T)"
  shows "cast\<cdot>(T_rep\<cdot>(forallT h)) = fup\<cdot>Vtfun oo
    u_map\<cdot>(\<Lambda> f x. cast\<cdot>(T_rep\<cdot>(h (of_U\<cdot>x)))\<cdot>(f\<cdot>x)) oo
    V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>"
unfolding forallT_def T.abs_iso
apply (subst cast_defl_fun1)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (erule finite_deflation_u_map)
apply (intro cfun_cong refl)
apply (subst cast_pi_defl)
apply (simp add: h [THEN cont_compose])
done

lemma has_type_T_lam:
  assumes 1: "cont f"
  assumes 2: "cont h"
  assumes 3: "\<And>a. f a ::: h a"
  shows "T_lam f ::: forallT (\<lambda>a. h a)"
apply (simp add: has_type_def cast_T_rep_forallT [OF 2])
apply (simp add: T_lam_def)
apply (rule cfun_eqI, simp add: cont_compose [OF 1] cont_compose [OF 2])
apply (rule has_type_def [THEN iffD1])
apply (rule 3)
done

lemma has_type_T_app:
  assumes f: "f ::: forallT h"
  assumes h: "cont h"
  shows "T_app f a ::: h a"
apply (rule has_type_elim [OF f], rename_tac f')
apply (rule has_type_def [THEN iffD2])
apply (simp add: T_app_def)
apply (simp add: cast_T_rep_forallT [OF h])
apply (case_tac f', simp_all add: cont_compose [OF h])
done

lemma T_beta:
  assumes h: "cont (\<lambda>a. h a)"
  shows "T_app (T_lam (\<lambda>a. h a)) t = h t"
unfolding T_app_def T_lam_def
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

lemma has_type_datatype_intro1:
  assumes "have_types xs ts"
  shows "Vcon\<cdot>s\<cdot>xs ::: datatype ((s, ts) # ds)"
unfolding has_type_def cast_datatype
by (simp add: assms [unfolded have_types_iff])

lemma has_type_datatype_intro2:
  assumes "s \<noteq> s'" and "Vcon\<cdot>s\<cdot>xs ::: datatype ds"
  shows "Vcon\<cdot>s\<cdot>xs ::: datatype ((s', ts) # ds)"
using assms unfolding has_type_def cast_datatype
by simp


subsection {* Case expressions *}

text "Case branches"

domain_isomorphism B = "V list \<rightarrow> V"

definition branch0 :: "V \<Rightarrow> B"
  where "branch0 v = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> Wrong)"

definition branchV :: "T \<Rightarrow> (V \<Rightarrow> B) \<Rightarrow> B"
  where "branchV t f = B_abs\<cdot>(\<Lambda> xs. case xs of [] \<Rightarrow> Wrong |
    y # ys \<Rightarrow> B_rep\<cdot>(f (cast\<cdot>(T_rep\<cdot>t)\<cdot>y))\<cdot>ys)"

lemma B_rep_branch0: "B_rep\<cdot>(branch0 v)\<cdot>[] = v"
by (simp add: branch0_def B.abs_iso)

lemma B_rep_branchV:
  assumes f: "cont f" and x: "x ::: t"
  shows "B_rep\<cdot>(branchV t f)\<cdot>(x # xs) = B_rep\<cdot>(f x)\<cdot>xs"
unfolding branchV_def B.abs_iso
by (simp add: cont_compose [OF f] x [unfolded has_type_def])

theorem cont_branch0 [simp, cont2cont]:
  assumes "cont f" shows "cont (\<lambda>x. branch0 (f x))"
using assms unfolding branch0_def
by (simp add: cont2cont_LAM)

theorem cont_branchV [simp, cont2cont]:
  assumes "cont t" and "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. branchV (t x) (\<lambda>y. f x y))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. f x y)" and 2: "\<And>x. cont (\<lambda>y. f x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding branchV_def
    apply (rule cont_apply [OF assms(1)])
    apply (simp_all add: cont2cont_LAM cont_compose [OF 1] cont_compose [OF 2])
    done
qed

text "Lists of case branches"

domain_isomorphism M = "V \<rightarrow>! V"

definition allmatch :: "V \<Rightarrow> M"
  where "allmatch v = M_abs\<cdot>(sfun_abs\<cdot>(\<Lambda> x. v))"

lemma cont_allmatch [simp, cont2cont]:
  assumes "cont f" shows "cont (\<lambda>x. allmatch (f x))"
unfolding allmatch_def by (simp add: cont_compose [OF assms])

definition endmatch :: "M"
  where "endmatch = allmatch Wrong"

definition endmatch' :: "M"
  where "endmatch' = allmatch \<bottom>"
  -- "less correct, but easier to prove typing rules about"

definition match :: "string \<Rightarrow> B \<Rightarrow> M \<Rightarrow> M"
  where "match s b m = M_abs\<cdot>(sfun_abs\<cdot>(\<Lambda> x. case x of
    Vint\<cdot>n \<Rightarrow> Wrong |
    Vcon\<cdot>s'\<cdot>xs \<Rightarrow> if s = s' then B_rep\<cdot>b\<cdot>xs else sfun_rep\<cdot>(M_rep\<cdot>m)\<cdot>x |
    Vfun\<cdot>f \<Rightarrow> Wrong | Vtfun\<cdot>f \<Rightarrow> Wrong | Wrong \<Rightarrow> Wrong))"

lemma cont_match [simp, cont2cont]:
  assumes "cont b" and "cont m"
  shows "cont (\<lambda>x. match s (b x) (m x))"
unfolding match_def
by (intro cont2cont assms [THEN cont_compose])

text "Case expressions"

definition cases :: "T \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> M) \<Rightarrow> V"
  where "cases t v m = sfun_rep\<cdot>(M_rep\<cdot>(m v))\<cdot>v"

lemma cont_cases [simp, cont2cont]:
  assumes "cont v" and "cont (\<lambda>p. m (fst p) (snd p))"
  shows "cont (\<lambda>x. cases (t x) (v x) (\<lambda>w. m x w))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. m x y)" and 2: "\<And>x. cont (\<lambda>y. m x y)"
    using assms unfolding prod_cont_iff by simp_all
  show ?thesis
    unfolding cases_def
    apply (rule cont_apply [OF assms(1)])
    apply (simp_all add: cont_compose [OF 1] cont_compose [OF 2])
    done
qed

theorem cases_allmatch:
  assumes f: "cont f" and x: "x \<noteq> \<bottom>"
  shows "cases t x (\<lambda>w. allmatch (f w)) = f x"
by (simp add: cases_def allmatch_def M.abs_iso x)

theorem cases_Vcon_allmatch:
  assumes "cont f"
  shows "cases t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. allmatch (f w)) = f (Vcon\<cdot>s\<cdot>xs)"
using assms by (rule cases_allmatch) simp

theorem cases_V_lam_allmatch:
  assumes "cont f"
  shows "cases t' (V_lam t g) (\<lambda>w. allmatch (f w)) = f (V_lam t g)"
using assms by (rule cases_allmatch, simp add: V_lam_def)

theorem cases_match_neq:
  "s \<noteq> s' \<Longrightarrow> cases t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. match s' (b w) (m w)) =
    cases t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. m w)"
by (simp add: cases_def match_def M.abs_iso)

lemma cases_match_eq:
  "cases t (Vcon\<cdot>s\<cdot>xs) (\<lambda>w. match s (b w) (m w)) = B_rep\<cdot>(b (Vcon\<cdot>s\<cdot>xs))\<cdot>xs"
by (simp add: cases_def match_def M.abs_iso)

end
