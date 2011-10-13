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
  "kind_witness k = TyFix Opaque k (TyVar 0)"

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
| "ty_unsubst i (TyFix v k t1) t' =
    (case t' of
      TyFix v' k' t1' \<Rightarrow> TyFix v k (ty_unsubst (Suc i) t1 t1')
    | _ \<Rightarrow> TyVar i)"
| "ty_unsubst i (TyData tss) d' =
    (case d' of
      TyData tss' \<Rightarrow> TyData (cons_unsubst i tss tss')
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

lemma ty_of_fun_unique:
  fixes f :: "'a::kind \<Rightarrow> 'b::kind"
  shows "fun_has_ty f t \<Longrightarrow> ty_of_fun f = t"
unfolding ty_of_fun_def
by (rule the_equality, assumption, erule (1) fun_has_ty_unique)

lemma kcont_intro: "fun_has_ty f t \<Longrightarrow> kcont f"
  unfolding kcont_def by fast

lemma fun_has_ty_intro:
  fixes f :: "'a::kind \<Rightarrow> 'b::kind"
  assumes "has_kind [the_kind TYPE('a)] t (the_kind TYPE('b))"
  assumes "\<And>x. to_ty (f x) = ty_subst 0 t (to_ty x)"
  shows "fun_has_ty f t"
  using assms unfolding fun_has_ty_def by fast

lemma kcont_ty_subst:
  assumes "has_kind [the_kind TYPE('a::kind)] t (the_kind TYPE('b::kind))"
  shows "kcont (\<lambda>x::'a::kind. of_ty (ty_subst 0 t (to_ty x))::'b::kind)"
apply (rule kcont_intro)
apply (rule fun_has_ty_intro)
apply (rule assms)
apply (rule of_ty_inverse)
apply (rule has_kind_ty_subst_0)
apply (rule assms)
apply (rule has_kind_to_ty)
done

lemma kcont_ident: "kcont (\<lambda>x. x)"
apply (rule kcont_intro [where t="TyVar 0"])
apply (rule fun_has_ty_intro)
apply (intro kind_rules)
apply simp
done

lemma kcont_const: "kcont (\<lambda>x. c)"
apply (rule kcont_intro [where t="ty_lift 0 (to_ty c)"])
apply (rule fun_has_ty_intro)
apply (rule has_kind_Cons_ty_lift_0)
apply (rule has_kind_to_ty)
apply (simp add: ty_subst_ty_lift_cancel)
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

lemma kcont_Tapp: "\<lbrakk>kcont f; kcont g\<rbrakk> \<Longrightarrow> kcont (\<lambda>x. Tapp (f x) (g x))"
unfolding kcont_def
apply (clarify, rename_tac t u)
apply (rule_tac x="TyApp t u" in exI)
apply (simp add: fun_has_ty_def the_kind_kfun_def, safe)
apply (erule (1) has_kind.TyApp)
apply (simp add: to_ty_Tapp)
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

definition Tdata :: "kstar list list \<Rightarrow> kstar"
  where "Tdata xss = of_ty (TyData (map (map to_ty) xss))"

lemma to_ty_Tdata: "to_ty (Tdata xss) = TyData (map (map to_ty) xss)"
unfolding Tdata_def
apply (rule of_ty_inverse)
apply (simp add: the_kind_kstar_def)
apply (rule has_kind.TyData)
apply (subst the_kind_kstar_def [where i="TYPE(kstar)", symmetric])
apply (induct xss, simp, rename_tac xs xss)
apply (induct_tac xs, simp_all add: has_kind_to_ty)
done

subsection {* Parallel substitution and simultaneous continuity *}

primrec tlifts :: "nat \<Rightarrow> ty \<Rightarrow> ty" where
  "tlifts 0 t = t"
| "tlifts (Suc i) t = ty_lift i (tlifts i t)"

primrec tsubsts :: "nat \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubsts i [] t = t"
| "tsubsts i (x # xs) t = ty_subst i (tsubsts (Suc i) xs t) (tlifts i x)"

definition kconts :: "kind list \<Rightarrow> ((nat \<Rightarrow> ty) \<Rightarrow> 'b::kind) \<Rightarrow> bool"
  where "kconts ks f \<longleftrightarrow> (\<exists>t. has_kind ks t (the_kind TYPE('b)) \<and>
    (\<forall>ts. list_all2 (has_kind []) ts ks \<longrightarrow>
      tsubsts 0 ts t = to_ty (f (\<lambda>n. ts ! n))))"

lemma tlift_0_tlifts: "ty_lift i (tlifts i t) = ty_lift 0 (tlifts i t)"
by (induct i) (simp_all add: ty_lift_0_ty_lift(1) [symmetric])

lemma ty_substs_tsubsts_Suc_tlifts:
  "ty_subst 0 (tsubsts (Suc 0) xs t) x =
    tsubsts 0 xs (foo xs t x)"
apply (induct xs)
apply simp defer
apply simp
oops

lemma tsubsts_TyApp:
  "tsubsts i xs (TyApp t1 t2) = TyApp (tsubsts i xs t1) (tsubsts i xs t2)"
by (induct xs arbitrary: i) simp_all

lemma tsubsts_TyAll:
  "tsubsts i xs (TyAll k t) = TyAll k (tsubsts (Suc i) xs t)"
by (induct xs arbitrary: i) (simp_all add: tlift_0_tlifts)

lemma kconts_imp_kcont:
  fixes f :: "'a::kind \<Rightarrow> 'b::kind"
  shows "kconts [the_kind TYPE('a)] (\<lambda>s. f (of_ty (s 0))) \<Longrightarrow> kcont f"
unfolding kconts_def kcont_def
apply clarify
apply (rule_tac x=t in exI)
apply (simp only: fun_has_ty_def, safe)
apply (drule_tac x="[to_ty x]" in spec)
apply (simp add: has_kind_to_ty to_ty_inverse)
done

lemma substVar_lt: "n < i \<Longrightarrow> substVar V i x n = V n"
unfolding substVar_def by simp

lemma tsubsts_TyVar_lt: "n < i \<Longrightarrow> tsubsts i xs (TyVar n) = TyVar n"
by (induct xs arbitrary: i) (simp_all add: substVar_lt)

lemma tsubsts_TyVar_nth:
  "\<lbrakk>i \<le> n; n < i + length xs\<rbrakk>
   \<Longrightarrow> tsubsts i xs (TyVar n) = tlifts i (xs ! (n - i))"
apply (induct xs arbitrary: i, simp_all)
apply (case_tac "i = n")
apply (simp add: tsubsts_TyVar_lt)
apply (cases n, simp, simp add: Suc_diff_le ty_subst_ty_lift_cancel)
done

lemma kconts_bound:
  assumes "mapsto ks n (the_kind TYPE('a::kind))"
  shows "kconts ks (\<lambda>s. of_ty (s n)::'a::kind)"
using assms
unfolding kconts_def
apply (rule_tac x="TyVar n" in exI, safe)
apply (rule has_kind.TyVar [OF assms])
apply (subst of_ty_inverse)
apply (clarsimp simp add: list_all2_conv_all_nth mapsto_iff)
apply (drule spec, drule (1) mp, simp)
apply (simp add: mapsto_iff list_all2_conv_all_nth)
apply (simp add: tsubsts_TyVar_nth)
done

lemma kconts_Tapp:
  "\<lbrakk>kconts ks f; kconts ks g\<rbrakk> \<Longrightarrow> kconts ks (\<lambda>s. Tapp (f s) (g s))"
unfolding kconts_def
apply (clarify, rename_tac t u)
apply (simp add: the_kind_kfun_def)
apply (rule_tac x="TyApp t u" in exI, safe)
apply (erule (1) has_kind.TyApp)
apply (simp add: tsubsts_TyApp to_ty_Tapp)
done

lemma Tforall_ty_subst_0:
  assumes "has_kind [the_kind TYPE('a::kind)] t KStar"
  shows "Tforall (\<lambda>x::'a::kind. of_ty (ty_subst 0 t (to_ty x))) =
    of_ty (TyAll (the_kind TYPE('a)) t)"
unfolding Tforall_def
apply (subst ty_of_fun_unique [where t=t])
apply (rule_tac [2] refl)
apply (simp only: fun_has_ty_def, safe)
apply (simp only: the_kind_kstar_def assms)
apply (rule of_ty_inverse)
apply (simp only: the_kind_kstar_def)
apply (rule has_kind_ty_subst_0 [OF assms has_kind_to_ty])
done

lemma shift_eq:
  "\<Gamma>{i:=k} = (if i \<le> length \<Gamma> then take i \<Gamma> @ [k] @ drop i \<Gamma> else \<Gamma>)"
apply (induct i arbitrary: \<Gamma>)
apply (simp add: shift_0)
apply (case_tac \<Gamma>)
apply (simp add: shift_Nil_Suc)
apply (simp add: shift_Cons_Suc)
done

lemma drop_Suc_shift: "drop (Suc i) (\<Gamma>{i:=k}) = drop i \<Gamma>"
by (auto simp add: shift_eq min_def)

lemma take_Suc_shift: "i \<le> length \<Gamma> \<Longrightarrow> take (Suc i) (\<Gamma>{i:=k}) = take i \<Gamma> @ [k]"
by (simp add: shift_eq min_def)

lemma args_lift_conv_map: "args_lift i = map (ty_lift i)"
by (rule ext, induct_tac x, simp_all)

lemma cons_lift_conv_map: "cons_lift i = map (args_lift i)"
by (rule ext, induct_tac x, simp_all)

lemma has_kind_imp_ty_lift_cancel:
  "\<lbrakk>has_kind \<Gamma> t k; length \<Gamma> \<le> i\<rbrakk> \<Longrightarrow> ty_lift i t = t"
apply (induct arbitrary: i set: has_kind)
apply (simp add: mapsto_iff skip_def)
apply simp_all
apply (simp add: cons_lift_conv_map args_lift_conv_map)
apply (rule map_idI, rule map_idI, simp add: list_all_iff)
done

lemma has_kind_tlifts:
  "has_kind (drop i \<Gamma>) t k \<Longrightarrow> has_kind \<Gamma> (tlifts i t) k"
apply (induct i arbitrary: \<Gamma>, simp_all add: tlift_0_tlifts)
apply (case_tac \<Gamma>)
apply (drule_tac x="[]" in meta_spec, simp)
apply (simp add: has_kind_imp_ty_lift_cancel)
apply (simp add: has_kind_Cons_ty_lift_0)
done

lemma has_kind_tsubsts:
  assumes "list_all2 (has_kind (drop i \<Gamma>)) xs ks"
  assumes "has_kind (take i \<Gamma> @ ks @ drop i \<Gamma>) t k"
  shows "i \<le> length \<Gamma> \<Longrightarrow> has_kind \<Gamma> (tsubsts i xs t) k"
using assms
apply (induct xs arbitrary: \<Gamma> ks i)
apply simp
apply (simp add: list_all2_Cons1, clarify)
apply (rule_tac k'="z" in has_kind_ty_subst)
apply (drule_tac x="\<Gamma>{i:=z}" in meta_spec)
apply (drule_tac x="zs" in meta_spec)
apply (drule_tac x="Suc i" in meta_spec)
apply (drule meta_mp)
apply (simp add: shift_eq)
apply (drule meta_mp)
apply (simp only: drop_Suc_shift)
apply (drule meta_mp)
apply (simp only: drop_Suc_shift)
apply (simp add: take_Suc_shift)
apply assumption
apply (erule has_kind_tlifts)
done

lemma kconts_Tforall:
  assumes "kconts (the_kind TYPE('a::kind) # ks)
    (\<lambda>s. f (\<lambda>n. s (Suc n)) (of_ty (s 0)))"
  shows "kconts ks (\<lambda>s. Tforall (\<lambda>x::'a::kind. f s x))"
 using assms unfolding kconts_def the_kind_kstar_def
 apply clarify
 apply (rule_tac x="TyAll (the_kind TYPE('a)) t" in exI, safe)
  apply (erule has_kind.TyAll)
 apply (subgoal_tac "fun_has_ty (f (\<lambda>n. ts ! n)) (tsubsts (Suc 0) ts t)")
  apply (subst to_ty_Tforall)
   apply (simp only: kcont_def, erule exI)
  apply (subst tsubsts_TyAll)
  apply (rule arg_cong [where f="TyAll (the_kind TYPE('a))"])
  apply (rule fun_has_ty_unique, assumption)
  apply (rule ty_of_fun_correct)
  apply (simp only: kcont_def, erule exI)
 apply (simp only: fun_has_ty_def, safe)
  apply (rule has_kind_tsubsts)
    apply simp
   apply (simp add: the_kind_kstar_def)
  apply simp
 apply (drule_tac x="to_ty x # ts" in spec)
 apply (drule mp)
  apply (simp add: has_kind_to_ty)
 apply (simp add: to_ty_inverse)
done

lemma mapsto_weaken: "mapsto xs n x \<Longrightarrow> mapsto (xs @ ys) n x"
by (simp add: mapsto_iff nth_append)

lemma has_kind_weaken: "has_kind \<Gamma> t k \<Longrightarrow> has_kind (\<Gamma> @ \<Gamma>') t k"
apply (induct set: has_kind)
apply (auto intro!: has_kind.intros mapsto_weaken
  elim: list_all_mono [rule_format, COMP swap_prems_rl])
done

lemma has_kind_Nil_implies: "has_kind [] t k \<Longrightarrow> has_kind \<Gamma> t k"
using has_kind_weaken [where \<Gamma> = "[]" and \<Gamma>' = \<Gamma>] by simp

lemma args_subst_conv_map:
  "args_subst i ts t' = map (\<lambda>t. ty_subst i t t') ts"
by (induct ts, simp_all)

lemma cons_subst_conv_map:
  "cons_subst i tss t' = map (\<lambda>ts. args_subst i ts t') tss"
by (induct tss, simp_all)

lemma has_kind_imp_ty_subst_cancel:
  "\<lbrakk>has_kind \<Gamma> t k; length \<Gamma> \<le> i\<rbrakk> \<Longrightarrow> ty_subst i t x = t"
apply (induct arbitrary: i x set: has_kind)
apply (simp add: mapsto_iff substVar_def)
apply simp_all
apply (simp add: cons_subst_conv_map args_subst_conv_map)
apply (rule map_idI, rule map_idI, simp add: list_all_iff)
done

lemma kconts_const: "kconts ks (\<lambda>s. (a::'a::kind))"
unfolding kconts_def
apply (rule_tac x="to_ty a" in exI, safe)
apply (rule has_kind_Nil_implies)
apply (rule has_kind_to_ty)
apply (erule thin_rl)
apply (rule_tac x="0::nat" in spec)
apply (induct_tac ts, simp_all)
apply (rule allI)
apply (rule has_kind_imp_ty_subst_cancel)
apply (rule has_kind_to_ty)
apply simp
done

lemmas kcont_intros =
  kconts_imp_kcont
  kconts_const
  kconts_bound
  mapsto_intros
  kconts_Tapp
  kconts_Tforall

text "Example of proof automation:"

lemma "kcont (\<lambda>t. Tforall (\<lambda>z. Tapp z (Tforall (\<lambda>u. Tapp (Tapp Tfun t) u))))"
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
apply (rule kcont_intros)
done

end
