header {* Meaning function for type expressions *}

theory Halicore_Type_Meaning
imports
  Halicore_Type_Deep
  Defl_Lib
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/HOLCF/Library/HOL_Cpo"
begin

subsection {* Domain definition for Core values *}

text {* We must first show that type @{text ty} is countable. *}

instance kind :: countable
  by countable_datatype

instance base :: countable
  by countable_datatype

instance visibility :: countable
  by countable_datatype

instance ty :: countable
  by countable_datatype

domain V
  = Vint (lazy "int")
  | Vcon (lazy "nat") (lazy "V list")
  | Vfun (lazy "V \<rightarrow> V")
  | Vtfun (lazy "ty discr \<rightarrow> V")
  | Wrong

subsection {* Deflation model of types *}

domain U = Udefl (unUdefl :: "V defl") | Ufun (Uapp :: "U \<rightarrow> U")

definition TyFun_denote :: "U"
  where "TyFun_denote = Ufun\<cdot>(\<Lambda> a. Ufun\<cdot>(\<Lambda> b.
    Udefl\<cdot>(defl_fun2 (\<Lambda>(up\<cdot>f). Vfun\<cdot>f) (\<Lambda>(Vfun\<cdot>f). up\<cdot>f)
      (\<Lambda> d e. u_map\<cdot>(cfun_map\<cdot>d\<cdot>e))\<cdot>(unUdefl\<cdot>a)\<cdot>(unUdefl\<cdot>b))))"

primrec base_denote :: "base \<Rightarrow> U"
  where "base_denote TyFun = TyFun_denote"
  | "base_denote TyInt = \<bottom>"
  | "base_denote TyChar = \<bottom>"

subsubsection {* Datatypes *}

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

fixrec defls :: "'a defl list \<rightarrow> 'a list u defl"
  where "defls\<cdot>[] = Nil_defl"
  | "defls\<cdot>(d # ds) = Cons_defl\<cdot>(defl_fun1 ID ID u_map\<cdot>d)\<cdot>(defls\<cdot>ds)"

lemma cont2cont_nat_case_simple [simp, cont2cont]:
  assumes "cont (\<lambda>x. f1 x)"
  assumes "\<And>n'. cont (\<lambda>x. f2 x n')"
  shows "cont (\<lambda>x. case n of 0 \<Rightarrow> f1 x | Suc n' \<Rightarrow> f2 x n')"
using assms by (cases n) auto -- "TODO: move to library"

fixrec nth_defls :: "V defl list list \<rightarrow> nat \<rightarrow> V list u defl"
  where "nth_defls\<cdot>(ds # dss)\<cdot>n =
    (case n of 0 \<Rightarrow> defls\<cdot>ds | Suc n' \<Rightarrow> nth_defls\<cdot>dss\<cdot>n')"

lemma nth_defls_Nil: "nth_defls\<cdot>[]\<cdot>n = \<bottom>"
by fixrec_simp

lemma nth_defls_eq:
  "nth_defls\<cdot>dss\<cdot>n = (if n < length dss then defls\<cdot>(dss ! n) else \<bottom>)"
by (induct dss arbitrary: n, simp add: nth_defls_Nil, simp split: nat.split)

definition datadefl :: "V defl list list \<rightarrow> V defl"
  where "datadefl = (\<Lambda> xs. defl_fun1
    (\<Lambda>(:up\<cdot>n, up\<cdot>vs:). Vcon\<cdot>n\<cdot>vs) (\<Lambda>(Vcon\<cdot>n\<cdot>vs). (:up\<cdot>n, up\<cdot>vs:)) ID\<cdot>
  (sprod_of_prod_defl\<cdot>(sig_defl\<cdot>ID_defl\<cdot>(\<Lambda>(up\<cdot>n). nth_defls\<cdot>xs\<cdot>n))))"

lemma cast_datadefl:
  "cast\<cdot>(datadefl\<cdot>xs) = (\<Lambda>(Vcon\<cdot>s\<cdot>vs). ssplit\<cdot>(\<Lambda> (up\<cdot>s).
    fup\<cdot>(Vcon\<cdot>s))\<cdot>(:up\<cdot>s, cast\<cdot>(nth_defls\<cdot>xs\<cdot>s)\<cdot>(up\<cdot>vs):))"
apply (simp add: datadefl_def)
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

subsubsection {* Forall-types *}

definition Uforall :: "kind \<Rightarrow> (ty discr \<rightarrow> V defl) \<rightarrow> V defl"
  where "Uforall k = (\<Lambda> h. defl_fun1 (fup\<cdot>Vtfun) (V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>) u_map\<cdot>
    (defl_fun1 decode_cfun encode_cfun ID\<cdot>(strict_pi_defl\<cdot>ID_defl\<cdot>
      (\<Lambda>(up\<cdot>x). if has_kind [] (undiscr x) k then h\<cdot>x else \<bottom>))))"

lemma cast_Uforall:
  "cast\<cdot>(Uforall k\<cdot>h) = fup\<cdot>Vtfun oo u_map\<cdot>(\<Lambda> f x. if has_kind [] (undiscr x) k
    then cast\<cdot>(h\<cdot>x)\<cdot>(f\<cdot>x) else \<bottom>) oo V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>"
unfolding Uforall_def
apply simp
apply (subst cast_defl_fun1)
apply (rule ep_pair.intro)
apply (case_tac x, simp, simp)
apply (case_tac y, simp, simp, simp, simp, simp, simp)
apply (erule finite_deflation_u_map)
apply (intro cfun_arg_cong cfun_fun_cong)
apply (subst cast_defl_fun1, simp add: ep_pair_def, simp)
apply (subst cast_strict_pi_defl)
apply (simp add: decode_cfun_def encode_cfun_def cfun_eq_iff)
done

lemma LAM_eqI: "(\<And>x. f x = g x) \<Longrightarrow> (\<Lambda> x. f x) = (\<Lambda> y. g y)"
by simp (* TODO: put in library *)

lemma cont2cont_nat_case [simp, cont2cont]:
  assumes f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. nat_case (f x) (g x))"
apply (rule cont2cont_lambda, rename_tac n)
apply (case_tac n, simp_all add: f)
apply (rule cont_compose [OF cont_fun g])
done

definition ty_denote' :: "(nat \<Rightarrow> U) \<rightarrow> ty discr \<rightarrow> U"
  where "ty_denote' = (\<mu> ty_denote'. \<Lambda> \<sigma> t.
    case undiscr t of TyVar n \<Rightarrow> \<sigma> n
    | TyBase b \<Rightarrow> base_denote b
    | TyApp t1 t2 \<Rightarrow> Uapp\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t1))\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t2))
    | TyAll k t \<Rightarrow>
      Udefl\<cdot>(Uforall k\<cdot>(\<Lambda> u. unUdefl\<cdot>
        (ty_denote'\<cdot>(nat_case (ty_denote'\<cdot>\<bottom>\<cdot>u) \<sigma>)\<cdot>(Discr t))))
    | TyLam k t \<Rightarrow> Ufun\<cdot>(\<Lambda> x. ty_denote'\<cdot>(nat_case x \<sigma>)\<cdot>(Discr t))
    | TyFix v k t \<Rightarrow> (\<mu> x. ty_denote'\<cdot>(nat_case x \<sigma>)\<cdot>(Discr t))
    | TyData tss \<Rightarrow>
      Udefl\<cdot>(datadefl\<cdot>(map (map (\<lambda>t. unUdefl\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t)))) tss)))"

lemma cont2cont_map_simple [simp, cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::type \<Rightarrow> 'c::cpo"
  assumes f: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. map (\<lambda>y. f x y) xs)"
  by (induct xs, simp_all add: f)

lemma ty_denote'_unfold:
  "ty_denote'\<cdot>\<sigma>\<cdot>t =
    (case undiscr t of TyVar n \<Rightarrow> \<sigma> n
    | TyBase b \<Rightarrow> base_denote b
    | TyApp t1 t2 \<Rightarrow> Uapp\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t1))\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t2))
    | TyAll k t \<Rightarrow>
      Udefl\<cdot>(Uforall k\<cdot>(\<Lambda> u. unUdefl\<cdot>
        (ty_denote'\<cdot>(nat_case (ty_denote'\<cdot>\<bottom>\<cdot>u) \<sigma>)\<cdot>(Discr t))))
    | TyLam k t \<Rightarrow> Ufun\<cdot>(\<Lambda> x. ty_denote'\<cdot>(nat_case x \<sigma>)\<cdot>(Discr t))
    | TyFix v k t \<Rightarrow> (\<mu> x. ty_denote'\<cdot>(nat_case x \<sigma>)\<cdot>(Discr t))
    | TyData tss \<Rightarrow>
      Udefl\<cdot>(datadefl\<cdot>(map (map (\<lambda>t. unUdefl\<cdot>(ty_denote'\<cdot>\<sigma>\<cdot>(Discr t)))) tss)))"
apply (subst def_cont_fix_eq [OF ty_denote'_def [THEN eq_reflection]])
apply (rule cont2cont_LAM')
apply (rule cont2cont_LAM_discrete)
apply (case_tac "undiscr t", simp_all)
apply (simp add: cont2cont_fun)
apply (subst beta_cfun)
apply (rule cont2cont_LAM_discrete)
apply (case_tac "undiscr t", simp_all)
apply (rule cont2cont_fun, rule cont_id)
done

definition ty_denote :: "(nat \<Rightarrow> U) \<Rightarrow> ty \<Rightarrow> U"
  where "ty_denote \<sigma> t = ty_denote'\<cdot>\<sigma>\<cdot>(Discr t)"

lemma ty_denote_simps [simp]:
  "ty_denote \<sigma> (TyVar n) = \<sigma> n"
  "ty_denote \<sigma> (TyBase b) = base_denote b"
  "ty_denote \<sigma> (TyApp t1 t2) = Uapp\<cdot>(ty_denote \<sigma> t1)\<cdot>(ty_denote \<sigma> t2)"
  "ty_denote \<sigma> (TyAll k t) =
      Udefl\<cdot>(Uforall k\<cdot>(\<Lambda> u. unUdefl\<cdot>
        (ty_denote (nat_case (ty_denote \<bottom> (undiscr u)) \<sigma>) t)))"
  "ty_denote \<sigma> (TyLam k t) = Ufun\<cdot>(\<Lambda> x. ty_denote (nat_case x \<sigma>) t)"
  "ty_denote \<sigma> (TyFix v k t) = (\<mu> x. ty_denote (nat_case x \<sigma>) t)"
  "ty_denote \<sigma> (TyData tss) =
      Udefl\<cdot>(datadefl\<cdot>(map (map (\<lambda>t. unUdefl\<cdot>(ty_denote \<sigma> t))) tss))"
unfolding ty_denote_def
by (subst ty_denote'_unfold, simp)+

lemma cont_ty_denote: "cont (\<lambda>\<sigma>. ty_denote \<sigma> t)"
  unfolding ty_denote_def by simp

declare cont_ty_denote [THEN cont_compose, simp, cont2cont]

subsection {* Convertibility relation preserves meaning *}

lemma ty_induct:
  assumes TyVar: "\<And>n. P (TyVar n)"
  assumes TyBase: "\<And>b. P (TyBase b)"
  assumes TyApp: "\<And>t1 t2. \<lbrakk>P t1; P t2\<rbrakk> \<Longrightarrow> P (TyApp t1 t2)"
  assumes TyAll: "\<And>k t. P t \<Longrightarrow> P (TyAll k t)"
  assumes TyLam: "\<And>k t. P t \<Longrightarrow> P (TyLam k t)"
  assumes TyFix: "\<And>v k t. P t \<Longrightarrow> P (TyFix v k t)"
  assumes TyData: "\<And>tss. list_all (list_all P) tss \<Longrightarrow> P (TyData tss)"
  shows "P t"
apply (induct t)
apply (rule TyVar)
apply (rule TyBase)
apply (erule (1) TyApp)
apply (erule TyAll)
apply (erule TyLam)
apply (erule TyFix)
apply (erule TyData)
apply (simp, simp, simp, simp)
done

lemma nat_case_substVar [simp]:
  "nat_case u (substVar \<sigma> i x) = substVar (nat_case u \<sigma>) (Suc i) x"
by (rule ext, rename_tac n, case_tac n, simp_all)

lemma ty_denote_ty_lift:
  "ty_denote (substVar \<sigma> i y) (ty_lift i t) = ty_denote \<sigma> t"
apply (induct t arbitrary: \<sigma> i rule: ty_induct)
apply simp_all
apply (simp add: cons_lift_conv_map args_lift_conv_map o_def)
apply (simp add: list_all_iff cong: map_cong)
done

lemma substVar_0: "substVar \<sigma> 0 x = nat_case x \<sigma>"
by (rule ext, rename_tac n, case_tac n, simp_all)

lemma ty_denote_ty_subst:
  "ty_denote \<sigma> (ty_subst i t x) =
    ty_denote (substVar \<sigma> i (ty_denote \<sigma> x)) t"
apply (induct t arbitrary: \<sigma> i x rule: ty_induct)
apply (simp add: substVar_def) (* TyVar *)
apply simp (* TyBase *)
apply simp (* TyApp *)
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0]) (* TyAll *)
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0]) (* TyLam *)
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0]) (* TyFix *)
apply (simp add: cons_subst_conv_map args_subst_conv_map)
apply (simp add: list_all_iff cong: map_cong)
done

lemma step_ty_denote:
  "step t t' \<Longrightarrow> ty_denote \<sigma> t = ty_denote \<sigma> t'"
apply (induct arbitrary: \<sigma> set: step)
txt "unfold"
apply (simp add: ty_denote_ty_subst substVar_0)
apply (subst fix_eq, simp)
txt "beta"
apply (simp add: ty_denote_ty_subst substVar_0)
apply simp (* TyVar *)
apply simp (* TyBase *)
apply simp (* TyApp *)
apply simp (* TyAll *)
apply simp (* TyLam *)
apply simp (* TyFix *)
txt "TyData"
apply simp
apply (rule cfun_arg_cong)
apply (erule list_all2_induct, simp_all)
apply (erule list_all2_induct, simp_all)
done

lemma steps_ty_denote:
  "steps t t' \<Longrightarrow> ty_denote \<sigma> t = ty_denote \<sigma> t'"
by (induct set: steps, auto dest: step_ty_denote)

lemma conv_imp_ty_denote:
  "conv t1 t2 \<Longrightarrow> ty_denote \<sigma> t1 = ty_denote \<sigma> t2"
by (induct set: conv, simp add: steps_ty_denote)

end
