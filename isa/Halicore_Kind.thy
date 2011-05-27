header {* Kinds as Isabelle types *}

theory Halicore_Kind
imports Halicore_Type_Deep
begin

subsection {* Class and type definitions *}

class kind =
  fixes the_kind :: "'a itself \<Rightarrow> kind"
  fixes to_ty :: "'a \<Rightarrow> ty"
  fixes of_ty :: "ty \<Rightarrow> 'a"
  assumes kind_type:
    "type_definition to_ty of_ty {t. has_kind [] t (the_kind TYPE('a))}"
begin

lemma to_ty_inverse: "of_ty (to_ty x) = x"
using type_definition.Rep_inverse [OF kind_type] by simp

lemma of_ty_inverse:
  "has_kind [] t (the_kind TYPE('a)) \<Longrightarrow> to_ty (of_ty t) = t"
using type_definition.Abs_inverse [OF kind_type] by simp

lemma has_kind_to_ty:
  "has_kind [] (to_ty x) (the_kind TYPE('a))"
using type_definition.Rep [OF kind_type] by simp

end

text {* Every kind is inhabited. *}

definition kind_witness :: "kind \<Rightarrow> ty" where
  "kind_witness k = TyRec k (TyVar 0)"

lemma kind_witness: "has_kind \<Delta> (kind_witness k) k"
unfolding kind_witness_def by (intro kind_rules)

typedef (open) kstar = "{t. has_kind [] t KStar}"
  by (fast intro: kind_witness)

instantiation kstar :: kind
begin
  definition "the_kind (i::kstar itself) = KStar"
  definition "to_ty = Rep_kstar"
  definition "of_ty = Abs_kstar"

  instance
  apply default
  apply (unfold the_kind_kstar_def to_ty_kstar_def of_ty_kstar_def)
  apply (rule type_definition_kstar)
  done
end

typedef (open) ('a::kind, 'b::kind) kfun =
  "{t. has_kind [] t (KArrow (the_kind TYPE('a)) (the_kind TYPE('b)))}"
by (fast intro: kind_witness)

instantiation kfun :: (kind, kind) kind
begin
  definition
    "the_kind (i::('a, 'b) kfun itself) =
      KArrow (the_kind TYPE('a)) (the_kind TYPE('b))"
  definition "to_ty = Rep_kfun"
  definition "of_ty = Abs_kfun"

  instance
  apply default
  apply (unfold the_kind_kfun_def to_ty_kfun_def of_ty_kfun_def)
  apply (rule type_definition_kfun)
  done
end

subsection {* Higher order abstract syntax *}

text {* The first conjunct is actually implied by the second, but it
is hard to prove. It is easier to just include it in the definition.
*}

definition fun_has_ty :: "('a::kind \<Rightarrow> 'b::kind) \<Rightarrow> ty \<Rightarrow> bool"
  where "fun_has_ty f t \<longleftrightarrow>
    has_kind [the_kind TYPE('a::kind)] t (the_kind TYPE('b::kind))
    \<and> (\<forall>x. to_ty (f x) = ty_subst 0 t (to_ty x))"

definition ty_of_fun :: "('a::kind \<Rightarrow> 'b::kind) \<Rightarrow> ty"
  where "ty_of_fun f = (THE t. fun_has_ty f t)"

definition kcont :: "('a::kind \<Rightarrow> 'b::kind) \<Rightarrow> bool"
  where "kcont f = (\<exists>t. fun_has_ty f t)"

text {* The well-definedness of the unique choice depends on the
injectivity of substitution. *}

primrec ty_unsubst :: "nat \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  and cons_unsubst :: "nat \<Rightarrow> ty list list \<Rightarrow> ty list list \<Rightarrow> ty list list"
  and args_unsubst :: "nat \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> ty list"
where "ty_unsubst i (TyVar n) t' = TyVar (skip i n)"
| "ty_unsubst i (TyBase b) t' = TyBase b"
| "ty_unsubst i (TyApp t1 t2) t' =
    (case t' of
      TyApp t1' t2' \<Rightarrow> TyApp (ty_unsubst i t1 t1') (ty_unsubst i t2 t2')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyAll k t1) t' =
    (case t' of
      TyAll k' t1' \<Rightarrow> TyAll k (ty_unsubst (Suc i) t1 t1')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyLam k t1) t' =
    (case t' of
      TyLam k' t1' \<Rightarrow> TyLam k (ty_unsubst (Suc i) t1 t1')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyFix k t1) t' =
    (case t' of
      TyFix k' t1' \<Rightarrow> TyFix k (ty_unsubst (Suc i) t1 t1')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyRec k t1) t' =
    (case t' of
      TyRec k' t1' \<Rightarrow> TyRec k (ty_unsubst (Suc i) t1 t1')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyData s tss) d' =
    (case d' of
      TyData s' tss' \<Rightarrow> TyData s (cons_unsubst i tss tss')
    | _ \<Rightarrow> TyVar i)"
| "cons_unsubst i [] tss' = []"
| "cons_unsubst i (ts # tss) tss' =
    args_unsubst i ts (hd tss') # cons_unsubst i tss (tl tss')"
| "args_unsubst i [] ts' = []"
| "args_unsubst i (t # ts) ts' =
    ty_unsubst i t (hd ts') # args_unsubst i ts (tl ts')"

lemma
  assumes x [simp]: "ty_lift 0 x = x"
  assumes y [simp]: "ty_lift 0 y = y"
  assumes x_y [simp]: "\<And>i. ty_unsubst i x y = TyVar i"
  shows ty_unsubst:
    "ty_unsubst i (ty_subst i t x) (ty_subst i t y) = t"
  and cons_unsubst:
    "cons_unsubst i (cons_subst i tss x) (cons_subst i tss y) = tss"
  and args_unsubst:
    "args_unsubst i (args_subst i ts x) (args_subst i ts y) = ts"
apply (induct t and tss and ts arbitrary: i and i and i)
apply (rule_tac x="nat" and i="i" in skip_cases)
apply simp_all
done

lemma mapsto_iff: "mapsto xs i x \<longleftrightarrow> i < length xs \<and> xs ! i = x"
by (induct xs arbitrary: i, simp, case_tac i, simp, simp)

lemma has_kind_implies_ty_lift_eq:
  "\<lbrakk>has_kind \<Delta> t k; length \<Delta> \<le> i\<rbrakk> \<Longrightarrow> ty_lift i t = t"
apply (induct arbitrary: i set: has_kind)
apply (simp add: mapsto_iff skip_def)
apply simp_all
apply (erule rev_mp)
apply (induct_tac tss, simp)
apply (rename_tac ts tss, induct_tac ts, simp_all)
done

lemma ty_lift_kind_witness:
  "ty_lift i (kind_witness k) = kind_witness k"
apply (rule has_kind_implies_ty_lift_eq [where \<Delta>="[]"])
apply (rule kind_witness)
apply simp
done

lemma fun_has_ty_unique:
  fixes f :: "'a::kind \<Rightarrow> 'b::kind"
  assumes "fun_has_ty f t" and "fun_has_ty f t'"
  shows "t = t'"
proof -
  let ?k = "the_kind TYPE('a)"
  let ?x = "kind_witness ?k"
  let ?y = "TyApp (kind_witness (KArrow KStar ?k)) (kind_witness KStar)"
  have has_kind_x: "has_kind [] ?x ?k"
    by (rule kind_witness)
  have ty_lift_x: "ty_lift 0 ?x = ?x"
    by (rule has_kind_implies_ty_lift_eq [OF has_kind_x], simp)
  have has_kind_y: "has_kind [] ?y ?k"
    by (rule has_kind.TyApp [OF kind_witness kind_witness])
  have ty_lift_y: "ty_lift 0 ?y = ?y"
    by (rule has_kind_implies_ty_lift_eq [OF has_kind_y], simp)
  have x_y: "\<And>i. ty_unsubst i ?x ?y = TyVar i"
    by (simp add: kind_witness_def)
  note * = ty_unsubst [OF ty_lift_x ty_lift_y x_y, where i=0]
  show "t = t'"
    apply (rule box_equals [OF _ * *])
    apply (cut_tac assms, clarsimp simp add: fun_has_ty_def)
    apply (frule_tac x="of_ty ?x" in spec)
    apply (drule_tac x="of_ty ?y" in spec)
    apply (frule_tac x="of_ty ?x" in spec)
    apply (drule_tac x="of_ty ?y" in spec)
    apply (simp add: of_ty_inverse has_kind_x has_kind_y)
    done
qed

lemma ty_of_fun_correct:
  fixes f :: "'a::kind \<Rightarrow> 'b::kind"
  shows "kcont f \<Longrightarrow> fun_has_ty f (ty_of_fun f)"
unfolding kcont_def ty_of_fun_def
by (rule theI', erule ex_ex1I, rule fun_has_ty_unique)

lemma kcont_ty_subst:
  assumes "has_kind [the_kind TYPE('a::kind)] t (the_kind TYPE('b::kind))"
  shows "kcont (\<lambda>x::'a::kind. of_ty (ty_subst 0 t (to_ty x))::'b::kind)"
unfolding kcont_def
apply (rule exI)
apply (simp only: fun_has_ty_def, safe)
apply (rule assms)
apply (rule of_ty_inverse)
apply (rule has_kind_ty_subst_0)
apply (rule assms)
apply (rule has_kind_to_ty)
done

subsection {* Operations on types *}

definition Tapp :: "('a::kind, 'b::kind) kfun \<Rightarrow> 'a \<Rightarrow> 'b"
  where "Tapp t u = of_ty (TyApp (to_ty t) (to_ty u))"

lemma to_ty_Tapp: "to_ty (Tapp t u) = TyApp (to_ty t) (to_ty u)"
unfolding Tapp_def
apply (rule of_ty_inverse)
apply (rule has_kind.TyApp)
apply (subst the_kind_kfun_def [symmetric])
apply (rule has_kind_to_ty)
apply (rule has_kind_to_ty)
done

definition Tfun :: "(kstar, (kstar, kstar) kfun) kfun"
  where "Tfun = of_ty (TyBase TyFun)"

lemma to_ty_Tfun: "to_ty Tfun = TyBase TyFun"
unfolding Tfun_def
apply (rule of_ty_inverse)
apply (rule has_kind.TyBase)
apply (simp add: the_kind_kfun_def the_kind_kstar_def)
done

definition Tforall :: "('a::kind \<Rightarrow> kstar) \<Rightarrow> kstar"
  where "Tforall f = of_ty (TyAll (the_kind TYPE('a)) (ty_of_fun f))"

lemma to_ty_Tforall:
  fixes f :: "'a::kind \<Rightarrow> kstar"
  assumes f: "kcont f"
  shows "to_ty (Tforall f) = TyAll (the_kind TYPE('a)) (ty_of_fun f)"
unfolding Tforall_def
apply (rule of_ty_inverse)
apply (simp add: the_kind_kstar_def)
apply (rule has_kind.TyAll)
apply (cut_tac ty_of_fun_correct [OF f])
apply (simp add: fun_has_ty_def the_kind_kstar_def)
done

end
