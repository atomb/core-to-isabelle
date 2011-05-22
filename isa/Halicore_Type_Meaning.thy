header {* Meaning function for type expressions *}

theory Halicore_Type_Meaning
imports Halicore Halicore_Type_Deep
begin

definition Uapp :: "U \<rightarrow> U \<rightarrow> U"
  where "Uapp = (\<Lambda> (Ufun\<cdot>f). f)"

lemma Uapp_Ufun [simp]: "Uapp\<cdot>(Ufun\<cdot>f) = f"
unfolding Uapp_def
by (cases "f = \<bottom>", simp_all)

primrec nat_append :: "'a::type list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "nat_append [] f = f"
  | "nat_append (x # xs) f = nat_case x (nat_append xs f)"

primrec base_denote :: "base \<Rightarrow> U"
  where "base_denote TyFun = to_U\<cdot>Tfun"
  | "base_denote TyInt = \<bottom>"
  | "base_denote TyChar = \<bottom>"

consts Tdata' :: "string \<rightarrow> T list list \<rightarrow> T"

definition Uforall :: "(U \<rightarrow> U) \<rightarrow> U"
  where "Uforall = (\<Lambda> f. Udefl\<cdot>(T_abs\<cdot>(defl_fun1 (fup\<cdot>Vtfun) (V_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>up\<cdot>\<bottom>) u_map\<cdot>(pi_defl\<cdot>ID_defl\<cdot>(\<Lambda> u. T_rep\<cdot>(of_U\<cdot>(f\<cdot>u)))))))"

primrec ty_denote :: "(nat \<Rightarrow> U) \<Rightarrow> ty \<Rightarrow> U"
  and tdef_denote :: "(nat \<Rightarrow> U) \<Rightarrow> tdef \<Rightarrow> U"
  and cons_denote :: "(nat \<Rightarrow> U) \<Rightarrow> ty list list \<Rightarrow> T list list"
  and args_denote :: "(nat \<Rightarrow> U) \<Rightarrow> ty list \<Rightarrow> T list"
where ty_denote_TyVar:
    "ty_denote \<sigma> (TyVar n) = \<sigma> n"
  | ty_denote_TyBase:
    "ty_denote \<sigma> (TyBase b) = base_denote b"
  | ty_denote_TyApp:
    "ty_denote \<sigma> (TyApp t1 t2) =
      Uapp\<cdot>(ty_denote \<sigma> t1)\<cdot>(ty_denote \<sigma> t2)"
  | ty_denote_TyAll:
    "ty_denote \<sigma> (TyAll k t) =
      Uforall\<cdot>(\<Lambda> u. ty_denote (nat_case u \<sigma>) t)"
  | ty_denote_TyRec:
    "ty_denote \<sigma> (TyRec d) = (\<mu> x. tdef_denote (nat_case x \<sigma>) d)"
  | tdef_denote_TyLam:
    "tdef_denote \<sigma> (TyLam k d) =
      Ufun\<cdot>(\<Lambda> x. tdef_denote (nat_case x \<sigma>) d)" (* FIXME: don't ignore k *)
  | tdef_denote_TyNew:
    "tdef_denote \<sigma> (TyNew t) = ty_denote \<sigma> t"
  | tdef_denote_TyData:
    "tdef_denote \<sigma> (TyData s tss) = to_U\<cdot>(Tdata'\<cdot>s\<cdot>(cons_denote \<sigma> tss))"
  | cons_denote_Nil:
    "cons_denote \<sigma> [] = []"
  | cons_denote_Cons:
    "cons_denote \<sigma> (ts # tss) = args_denote \<sigma> ts # cons_denote \<sigma> tss"
  | args_denote_Nil:
    "args_denote \<sigma> [] = []"
  | args_denote_Cons:
    "args_denote \<sigma> (t # ts) = of_U\<cdot>(ty_denote \<sigma> t) # args_denote \<sigma> ts"

lemma cont2cont_nat_case [simp, cont2cont]:
  assumes f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. nat_case (f x) (g x))"
apply (rule cont2cont_lambda, rename_tac n)
apply (case_tac n, simp_all add: f)
apply (rule cont_compose [OF cont_fun g])
done

lemma
  shows cont_ty_denote: "cont (\<lambda>\<sigma>. ty_denote \<sigma> t)"
  and cont_tdef_denote: "cont (\<lambda>\<sigma>. tdef_denote \<sigma> d)"
  and cont_cons_denote: "cont (\<lambda>\<sigma>. cons_denote \<sigma> tss)"
  and cont_args_denote: "cont (\<lambda>\<sigma>. args_denote \<sigma> ts)"
apply (induct t and d and tss and ts)
txt "TyVar"
apply (simp, rule cont_fun)
txt "TyBase"
apply simp
txt "TyApp"
apply simp
txt "TyAll"
apply simp
apply (intro cont2cont)
apply (erule cont_compose, simp)
txt "TyRec"
apply simp
apply (intro cont2cont)
apply (erule cont_compose, simp)
txt "TyLam"
apply simp
apply (intro cont2cont)
apply (erule cont_compose, simp)

apply simp (* TyNew *)
apply simp (* TyData *)
apply simp (* [] *)
apply simp (* ts # tss *)
apply simp (* [] *)
apply simp (* t # ts *)
done

declare cont_ty_denote [THEN cont_compose, simp, cont2cont]
declare cont_tdef_denote [THEN cont_compose, simp, cont2cont]

lemma nat_case_substVar [simp]:
  "nat_case u (substVar \<sigma> i x) = substVar (nat_case u \<sigma>) (Suc i) x"
by (rule ext, rename_tac n, case_tac n, simp_all)

lemma
  shows ty_denote_ty_lift:
    "ty_denote (substVar \<sigma> i y) (ty_lift i t) = ty_denote \<sigma> t"
  and tdef_denote_tdef_lift:
    "tdef_denote (substVar \<sigma> i y) (tdef_lift i d) = tdef_denote \<sigma> d"
  and cons_denote_cons_lift:
    "cons_denote (substVar \<sigma> i y) (cons_lift i tss) = cons_denote \<sigma> tss"
  and args_denote_args_lift:
    "args_denote (substVar \<sigma> i y) (args_lift i ts) = args_denote \<sigma> ts"
by (induct t and d and tss and ts arbitrary: \<sigma> i and \<sigma> i and \<sigma> i and \<sigma> i)
  simp_all

lemma substVar_0: "substVar \<sigma> 0 x = nat_case x \<sigma>"
by (rule ext, rename_tac n, case_tac n, simp_all)

lemma LAM_eqI: "(\<And>x. f x = g x) \<Longrightarrow> (\<Lambda> x. f x) = (\<Lambda> y. g y)"
by simp (* TODO: put in library *)

lemma
  shows ty_denote_ty_subst:
    "ty_denote \<sigma> (ty_subst i t x) =
     ty_denote (substVar \<sigma> i (ty_denote \<sigma> x)) t"
  and tdef_denote_tdef_subst:
    "tdef_denote \<sigma> (tdef_subst i d x) =
     tdef_denote (substVar \<sigma> i (ty_denote \<sigma> x)) d"
  and cons_denote_cons_subst:
    "cons_denote \<sigma> (cons_subst i tss x) =
     cons_denote (substVar \<sigma> i (ty_denote \<sigma> x)) tss"
  and args_denote_args_subst:
    "args_denote \<sigma> (args_subst i ts x) =
     args_denote (substVar \<sigma> i (ty_denote \<sigma> x)) ts"
apply (induct t and d and tss and ts
  arbitrary: \<sigma> i x and \<sigma> i x and \<sigma> i x and \<sigma> i x)
apply (simp add: substVar_def) (* TyVar *)
apply simp (* TyBase *)
apply simp (* TyApp *)
txt "TyAll"
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0])
txt "TyRec"
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0])
txt "TyLam"
apply (simp add: ty_denote_ty_lift [where i=0, unfolded substVar_0])
apply simp (* TyNew *)
apply simp (* TyData *)
apply simp (* [] *)
apply simp (* ts # tss *)
apply simp (* [] *)
apply simp (* t # ts *)
done

lemma ty_ax_ty_denote:
  "ty_ax \<Gamma> t d k \<Longrightarrow> ty_denote \<sigma> t = tdef_denote \<sigma> d"
apply (induct set: ty_ax)
txt "TyRec"
apply (simp add: tdef_denote_tdef_subst substVar_0)
apply (subst fix_eq, simp)
txt "TyApp"
apply (simp add: tdef_denote_tdef_subst substVar_0)
done

lemma ty_eq_ty_denote:
  "ty_eq \<Gamma> t t' k \<Longrightarrow> ty_denote \<sigma> t = ty_denote \<sigma> t'"
apply (induct arbitrary: \<sigma> set: ty_eq)
apply simp (* refl *)
apply simp (* sym *)
apply simp (* trans *)
apply simp (* TyApp *)
apply simp (* TyAll *)
apply (drule ty_ax_ty_denote, simp) (* axiom *)
done

end
