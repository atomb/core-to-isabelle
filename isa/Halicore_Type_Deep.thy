header {* Deep embedding of Halicore type expressions *}

theory Halicore_Type_Deep
imports Skip ListEnv
begin

subsection {* Type definitions *}

datatype kind = KStar | KArrow kind kind

datatype base = TyFun | TyInt | TyChar

type_synonym tag = string

datatype ty
  = TyVar nat
  | TyBase base
  | TyApp ty ty
  | TyAll kind ty
  | TyLam kind ty
  | TyFix kind ty
  | TyRec kind ty
  | TyData tag "ty list list"


subsection {* Kinding relation *}

primrec base_kind :: "base \<Rightarrow> kind"
  where "base_kind TyFun = KArrow KStar (KArrow KStar KStar)"
  | "base_kind TyInt = KStar"
  | "base_kind TyChar = KStar"

lemma mapsto_intros:
  "mapsto (z # xs) 0 z"
  "mapsto xs n z \<Longrightarrow> mapsto (x # xs) (Suc n) z"
by simp_all

lemma list_all_mono [mono]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> list_all P xs \<longrightarrow> list_all Q xs"
by (induct xs, simp_all)

inductive has_kind :: "kind list \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> bool"
where TyVar: "mapsto \<Gamma> n k \<Longrightarrow> has_kind \<Gamma> (TyVar n) k"
  | TyBase: "base_kind b = k \<Longrightarrow> has_kind \<Gamma> (TyBase b) k"
  | TyApp:
    "\<lbrakk>has_kind \<Gamma> t1 (KArrow k1 k2); has_kind \<Gamma> t2 k1\<rbrakk>
      \<Longrightarrow> has_kind \<Gamma> (TyApp t1 t2) k2"
  | TyAll:
    "has_kind (k # \<Gamma>) t KStar \<Longrightarrow> has_kind \<Gamma> (TyAll k t) KStar"
  | TyLam:
    "has_kind (k1 # \<Gamma>) t k2 \<Longrightarrow> has_kind \<Gamma> (TyLam k1 t) (KArrow k1 k2)"
  | TyFix: "has_kind (k # \<Gamma>) t k \<Longrightarrow> has_kind \<Gamma> (TyFix k t) k"
  | TyRec: "has_kind (k # \<Gamma>) t k \<Longrightarrow> has_kind \<Gamma> (TyRec k t) k"
  | TyData: "list_all (list_all (\<lambda>t. has_kind \<Gamma> t KStar)) tss
      \<Longrightarrow> has_kind \<Gamma> (TyData s tss) KStar"

inductive_cases has_kind_elims:
  "has_kind \<Delta> (TyVar n) k"
  "has_kind \<Delta> (TyBase b) k"
  "has_kind \<Delta> (TyApp t1 t2) k"
  "has_kind \<Delta> (TyAll k1 t) k"
  "has_kind \<Delta> (TyLam k1 t) k"
  "has_kind \<Delta> (TyFix k1 t) k"
  "has_kind \<Delta> (TyRec k1 t) k"
  "has_kind \<Delta> (TyData s tss) k"

lemma list_all_intros:
  "list_all P []"
  "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)"
by simp_all

lemmas kind_rules =
  has_kind.intros
  mapsto_intros
  list_all_intros


subsection {* Substitution *}

primrec ty_lift :: "nat \<Rightarrow> ty \<Rightarrow> ty"
  and cons_lift :: "nat \<Rightarrow> ty list list \<Rightarrow> ty list list"
  and args_lift :: "nat \<Rightarrow> ty list \<Rightarrow> ty list"
  where "ty_lift i (TyVar n) = TyVar (skip i n)"
  | "ty_lift i (TyBase b) = TyBase b"
  | "ty_lift i (TyApp t1 t2) = TyApp (ty_lift i t1) (ty_lift i t2)"
  | "ty_lift i (TyAll k t) = TyAll k (ty_lift (Suc i) t)"
  | "ty_lift i (TyLam k t) = TyLam k (ty_lift (Suc i) t)"
  | "ty_lift i (TyFix k t) = TyFix k (ty_lift (Suc i) t)"
  | ty_lift_TyRec:
    "ty_lift i (TyRec k t) = TyRec k (ty_lift (Suc i) t)"
  | ty_lift_TyData:
    "ty_lift i (TyData s tss) = TyData s (cons_lift i tss)"
  | "cons_lift i [] = []"
  | cons_lift_Cons:
    "cons_lift i (ts # tss) = args_lift i ts # cons_lift i tss"
  | "args_lift i [] = []"
  | "args_lift i (t # ts) = ty_lift i t # args_lift i ts"

primrec ty_subst :: "nat \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  and cons_subst :: "nat \<Rightarrow> ty list list \<Rightarrow> ty \<Rightarrow> ty list list"
  and args_subst :: "nat \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> ty list"
  where "ty_subst i (TyVar n) x = substVar TyVar i x n"
  | "ty_subst i (TyBase b) x = TyBase b"
  | "ty_subst i (TyApp t1 t2) x = TyApp (ty_subst i t1 x) (ty_subst i t2 x)"
  | "ty_subst i (TyAll k t) x = TyAll k (ty_subst (Suc i) t (ty_lift 0 x))"
  | "ty_subst i (TyLam k t) x = TyLam k (ty_subst (Suc i) t (ty_lift 0 x))"
  | "ty_subst i (TyFix k t) x = TyFix k (ty_subst (Suc i) t (ty_lift 0 x))"
  | ty_subst_TyRec:
    "ty_subst i (TyRec k t) x = TyRec k (ty_subst (Suc i) t (ty_lift 0 x))"
  | ty_subst_TyData:
    "ty_subst i (TyData s tss) x = TyData s (cons_subst i tss x)"
  | "cons_subst i [] x = []"
  | "cons_subst i (ts # tss) x = args_subst i ts x # cons_subst i tss x"
  | "args_subst i [] x = []"
  | "args_subst i (t # ts) x = ty_subst i t x # args_subst i ts x"

lemma Cons_shift: "y # shift A i x = shift (y # A) (Suc i) x"
using shift_shift [of A i x y] by (simp add: shift_0)

lemma has_kind_shift_ty_lift:
  "has_kind \<Gamma> t k \<Longrightarrow> has_kind (\<Gamma>{i:=k'}) (ty_lift i t) k"
apply (induct arbitrary: i set: has_kind)
apply (simp add: has_kind.TyVar mapsto_shift_skip)
apply (simp add: has_kind.TyBase)
apply (force intro!: has_kind.TyApp)
apply (simp add: has_kind.TyAll Cons_shift)
apply (simp add: has_kind.TyLam Cons_shift)
apply (simp add: has_kind.TyFix Cons_shift)
apply (simp add: has_kind.TyRec Cons_shift)
apply (simp, rule has_kind.TyData)
apply (erule rev_mp, induct_tac tss, simp, simp)
apply (rename_tac ts tss)
apply (induct_tac ts, simp, simp)
done

lemma has_kind_Cons_ty_lift_0:
  "has_kind \<Gamma> t k \<Longrightarrow> has_kind (k' # \<Gamma>) (ty_lift 0 t) k"
by (rule has_kind_shift_ty_lift [where i=0, unfolded shift_0])

lemma has_kind_ty_subst [OF _ refl]:
  "\<lbrakk>has_kind \<Gamma>' t k; \<Gamma>' = shift \<Gamma> i k'; has_kind \<Gamma> x k'\<rbrakk>
    \<Longrightarrow> has_kind \<Gamma> (ty_subst i t x) k"
apply (induct arbitrary: \<Gamma> i x set: has_kind, simp_all)
txt "TyVar"
apply (rule_tac x=n and i=i in skip_cases)
apply (simp add: mapsto_shift_eq)
apply (simp add: mapsto_shift_skip)
apply (erule has_kind.TyVar)
txt "TyBase"
apply (erule has_kind.TyBase)
txt "TyApp"
apply (rule_tac ?k1.0=k1 in has_kind.TyApp, simp, simp)
txt "TyAll"
apply (rule has_kind.TyAll)
apply (simp add: has_kind_Cons_ty_lift_0 Cons_shift)
txt "TyLam"
apply (rule has_kind.TyLam)
apply (simp add: has_kind_Cons_ty_lift_0 Cons_shift)
txt "TyFix"
apply (rule has_kind.TyFix)
apply (simp add: has_kind_Cons_ty_lift_0 Cons_shift)
txt "TyRec"
apply (rule has_kind.TyRec)
apply (simp add: has_kind_Cons_ty_lift_0 Cons_shift)
txt "TyData"
apply (rule has_kind.TyData)
apply (erule rev_mp)
apply (induct_tac tss, simp, simp, rename_tac ts tss)
apply (induct_tac ts, simp, simp)
done

lemma has_kind_ty_subst_0:
  "\<lbrakk>has_kind (k' # \<Gamma>) t k; has_kind \<Gamma> x k'\<rbrakk>
    \<Longrightarrow> has_kind \<Gamma> (ty_subst 0 t x) k"
by (rule has_kind_ty_subst [where i=0, unfolded shift_0])

lemma ty_lift_0_ty_lift [OF le0]:
  "i \<le> k \<Longrightarrow> ty_lift i (ty_lift k t) = ty_lift (Suc k) (ty_lift i t)"
  "i \<le> k \<Longrightarrow> cons_lift i (cons_lift k cs) = cons_lift (Suc k) (cons_lift i cs)"
  "i \<le> k \<Longrightarrow> args_lift i (args_lift k ts) = args_lift (Suc k) (args_lift i ts)"
by (induct t and cs and ts arbitrary: i k and i k and i k)
   (simp_all add: skip_skip_le)

lemma ty_lift_ty_subst_0 [OF le0]:
  "k \<le> i \<Longrightarrow> ty_lift i (ty_subst k t x) =
    ty_subst k (ty_lift (Suc i) t) (ty_lift i x)"
  "k \<le> i \<Longrightarrow> cons_lift i (cons_subst k cs x) =
    cons_subst k (cons_lift (Suc i) cs) (ty_lift i x)"
  "k \<le> i \<Longrightarrow> args_lift i (args_subst k ts x) =
    args_subst k (args_lift (Suc i) ts) (ty_lift i x)"
apply (induct t and cs and ts arbitrary: i k x and i k x and i k x)
apply (rule_tac x=nat and i=k in skip_cases)
apply (simp add: skip_def)
apply (simp add: skip_Suc_skip)
apply (simp_all add: ty_lift_0_ty_lift)
done

lemma ty_subst_ty_lift_cancel:
  "ty_subst i (ty_lift i t) x = t"
  "cons_subst i (cons_lift i cs) x = cs"
  "args_subst i (args_lift i ts) x = ts"
by (induct t and cs and ts arbitrary: i x and i x and i x, simp_all)

lemma ty_lift_ty_subst_le:
  "i \<le> k \<Longrightarrow> ty_lift i (ty_subst k t x) =
    ty_subst (Suc k) (ty_lift i t) (ty_lift i x)"
  "i \<le> k \<Longrightarrow> cons_lift i (cons_subst k cs x) =
    cons_subst (Suc k) (cons_lift i cs) (ty_lift i x)"
  "i \<le> k \<Longrightarrow> args_lift i (args_subst k ts x) =
    args_subst (Suc k) (args_lift i ts) (ty_lift i x)"
apply (induct t and cs and ts arbitrary: i k x and i k x and i k x)
apply (rule_tac x="nat" and i="k" in skip_cases)
apply (simp add: skip_def)
apply (simp add: skip_skip_le)
apply (simp_all add: ty_lift_0_ty_lift)
done

lemma ty_subst_ty_subst_0 [OF le0]:
  "j \<le> i \<Longrightarrow>
    ty_subst i (ty_subst j t u) v =
    ty_subst j (ty_subst (Suc i) t (ty_lift j v)) (ty_subst i u v)"
  "j \<le> i \<Longrightarrow>
    cons_subst i (cons_subst j cs u) v =
    cons_subst j (cons_subst (Suc i) cs (ty_lift j v)) (ty_subst i u v)"
  "j \<le> i \<Longrightarrow>
    args_subst i (args_subst j ts u) v =
    args_subst j (args_subst (Suc i) ts (ty_lift j v)) (ty_subst i u v)"
apply (induct t and cs and ts arbitrary: i j u v and i j u v and i j u v)
apply (rule_tac x="nat" and i="j" in skip_cases)
apply (rule_tac x="nat" and i="Suc i" in skip_cases)
apply simp
apply (clarsimp, clarsimp simp add: skip_def)
apply (clarsimp, simp add: substVar_def skip_def ty_subst_ty_lift_cancel)
apply (simp_all add: ty_lift_0_ty_lift ty_lift_ty_subst_le [OF le0])
done

subsection {* Coercibility proofs between types *}

text {* Relation @{text step} denotes parallel beta reduction of type
expressions. It also allows unfolding of @{text TyFix} (but not @{text
TyRec}) as a reduction step. *}

lemma list_all2_mono [mono]:
  "(\<And>x y. P x y \<longrightarrow> Q x y) \<Longrightarrow> list_all2 P xs ys \<longrightarrow> list_all2 Q xs ys"
by (induct xs arbitrary: ys, simp, case_tac ys, simp, simp)

inductive step :: "ty \<Rightarrow> ty \<Rightarrow> bool"
  where unfold: "step t t'
      \<Longrightarrow> step (TyFix k t) (ty_subst 0 t' (TyFix k t'))"
  | beta: "\<lbrakk>step t t'; step u u'\<rbrakk>
      \<Longrightarrow> step (TyApp (TyLam k t) u) (ty_subst 0 t' u')"
  | TyVar: "step (TyVar n) (TyVar n)"
  | TyBase: "step (TyBase b) (TyBase b)"
  | TyApp: "\<lbrakk>step t t'; step u u'\<rbrakk>
      \<Longrightarrow> step (TyApp t u) (TyApp t' u')"
  | TyAll: "step t t' \<Longrightarrow> step (TyAll k t) (TyAll k t')"
  | TyLam: "step t t' \<Longrightarrow> step (TyLam k t) (TyLam k t')"
  | TyFix: "step t t' \<Longrightarrow> step (TyFix k t) (TyFix k t')"
  | TyRec: "step t t' \<Longrightarrow> step (TyRec k t) (TyRec k t')"
  | TyData: "list_all2 (list_all2 step) tss tss'
      \<Longrightarrow> step (TyData s tss) (TyData s tss')"

inductive_cases step_elims:
  "step (TyVar n) t'"
  "step (TyBase b) t'"
  "step (TyApp t1 t2) t'"
  "step (TyAll t1 t2) t'"
  "step (TyLam k t) t'"
  "step (TyFix k t) t'"
  "step (TyRec k t) t'"
  "step (TyData s tss) t'"

lemma list_all2_intros:
  "list_all2 P [] []"
  "\<lbrakk>P x y; list_all2 P xs ys\<rbrakk> \<Longrightarrow> list_all2 P (x # xs) (y # ys)"
by simp_all

lemma list_all2_induct
  [consumes 1, case_names Nil Cons, induct set: list_all2]:
  assumes P: "list_all2 P xs ys"
  assumes Nil: "R [] []"
  assumes Cons: "\<And>x xs y ys. \<lbrakk>P x y; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
using P
apply (induct xs arbitrary: ys)
apply (simp add: Nil, case_tac ys, simp, simp add: Cons)
done

lemma step_refl: "step t t"
by (induct t) (rule step.intros list_all2_intros | assumption)+

text {* Each relation preserves kinds. *}

lemma list_all2_list_all_implies_list_all:
  assumes P: "list_all2 P xs ys" and Q: "list_all Q xs"
  assumes R: "\<And>x y. P x y \<Longrightarrow> Q x \<Longrightarrow> R y"
  shows "list_all R ys"
using P Q
apply (induct xs arbitrary: ys, simp)
apply (case_tac ys, simp, auto intro: R)
done

lemma step_has_kind:
  assumes "step t t'" and "has_kind \<Gamma> t k"
  shows "has_kind \<Gamma> t' k"
using assms
apply (induct arbitrary: \<Gamma> k set: step)
apply (auto elim!: has_kind_elims list_all2_list_all_implies_list_all
  intro!: has_kind.intros has_kind_ty_subst_0)
done

text {* The reduction relations are confluent. *}

lemma step_ty_lift:
  assumes "step t t'"
  shows "step (ty_lift i t) (ty_lift i t')"
using assms
apply (induct arbitrary: i set: step)
apply (simp add: ty_lift_ty_subst_0 step.unfold)
apply (simp add: ty_lift_ty_subst_0 step.beta)
apply (simp_all add: step.intros)
apply (rule step.TyData)
apply (erule list_all2_induct, simp, simp)
apply (erule list_all2_induct, simp, simp)
done

lemma step_ty_subst:
  assumes t: "step t t'"
  assumes u: "step u u'"
  shows "step (ty_subst i t u) (ty_subst i t' u')"
using assms
apply (induct arbitrary: i u u' set: step)
apply (simp_all add: ty_subst_ty_subst_0 step.intros step_ty_lift)
apply (rule_tac x=n and i=i in skip_cases, simp, simp add: step.TyVar)
apply (rule step.TyData)
apply (erule list_all2_induct, simp, simp)
apply (erule list_all2_induct, simp, simp)
done

lemma list_all2_list_all2_implies_list_all2:
  assumes P: "list_all2 P xs ys" and Q: "list_all2 Q xs zs"
  assumes R: "\<And>x y z. P x y \<Longrightarrow> Q x z \<Longrightarrow> R y z"
  shows "list_all2 R ys zs"
using P Q
apply (induct xs arbitrary: ys zs, simp)
apply (case_tac ys, simp, case_tac zs, simp, auto elim: R)
done

lemma step_confluent:
  "\<lbrakk>step t x; step t y\<rbrakk> \<Longrightarrow> \<exists>u. step x u \<and> step y u"
apply (induct arbitrary: y set: step)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
apply (blast elim!: step_elims intro!: step.intros step_ty_subst)
 apply (elim step_elims, clarsimp, rename_tac tss'')
 apply (drule (1) list_all2_list_all2_implies_list_all2)
 apply (erule (1) list_all2_list_all2_implies_list_all2)
 apply (erule conjE)
 apply (drule spec, erule (1) mp)
 apply (erule thin_rl)
 apply (erule list_all2_induct)
   apply simp
   apply (rule exI)
   apply (rule step.TyData)
   apply simp
  apply (clarsimp elim!: step_elims)
  apply (erule list_all2_induct)
   apply (rule exI, rule conjI)
    apply (rule step.TyData)
    apply (rule list_all2_Cons [THEN iffD2, OF conjI], simp, assumption)
   apply (rule step.TyData)
   apply (rule list_all2_Cons [THEN iffD2, OF conjI], simp, assumption)
  apply (clarsimp elim!: step_elims)
  apply (case_tac tss'b, simp, clarsimp)
  apply (rule exI, rule conjI)
   apply (rule step.TyData)
   apply (rule list_all2_Cons [THEN iffD2, OF conjI])
    apply (erule (1) list_all2_Cons [THEN iffD2, OF conjI])
   apply assumption
  apply (rule step.TyData)
  apply (rule list_all2_Cons [THEN iffD2, OF conjI])
   apply (erule (1) list_all2_Cons [THEN iffD2, OF conjI])
  apply assumption
done

subsection {* Transitive reducibility relation *}

text {* Relation @{text steps} is the reflexive, transitive closure of
@{text step}. *}

inductive steps :: "ty \<Rightarrow> ty \<Rightarrow> bool"
  for t where steps_refl: "steps t t"
  | steps_step: "\<lbrakk>steps t u; step u u'\<rbrakk> \<Longrightarrow> steps t u'"

lemma steps_trans:
  assumes "steps t u"
  shows "steps u v \<Longrightarrow> steps t v"
by (induct set: steps, fact, erule (1) steps_step)

lemma steps_has_kind:
  assumes "steps t t'" and "has_kind \<Gamma> t k"
  shows "has_kind \<Gamma> t' k"
using assms
apply (induct set: steps)
apply (auto elim: step_has_kind)
done

lemma steps_ty_lift:
  assumes "steps t t'"
  shows "steps (ty_lift i t) (ty_lift i t')"
using assms
apply (induct set: steps)
apply (rule steps_refl)
apply (erule steps_step)
apply (erule step_ty_lift)
done

lemma steps_step_confluent:
  assumes "steps t a" and "step t b"
  shows "\<exists>t'. step a t' \<and> steps b t'"
using assms
apply (induct set: steps)
apply (rule exI, erule conjI [OF _ steps_refl])
apply clarsimp
apply (drule (1) step_confluent, clarsimp)
apply (rule exI, erule conjI)
apply (erule (1) steps_step)
done

lemma steps_confluent:
  assumes "steps t a" and "steps t b"
  shows "\<exists>t'. steps a t' \<and> steps b t'"
using assms
apply (induct set: steps)
apply (rule exI, erule conjI [OF _ steps_refl])
apply clarsimp
apply (drule (1) steps_step_confluent, clarsimp)
apply (rule exI, erule conjI)
apply (erule (1) steps_step)
done

lemma steps_ty_subst:
  assumes "steps t t'" and "steps u u'"
  shows "steps (ty_subst i t u) (ty_subst i t' u')"
using assms(1)
apply (induct set: steps)
using assms(2)
apply (induct set: steps)
apply (rule steps_refl)
apply (erule steps_step)
apply (erule step_ty_subst [OF step_refl])
apply (erule steps_step)
apply (erule step_ty_subst [OF _ step_refl])
done

lemma steps_TyApp:
  assumes "steps t t'" and "steps u u'"
  shows "steps (TyApp t u) (TyApp t' u')"
using assms(1)
apply (induct set: steps)
using assms(2)
apply (induct set: steps)
apply (rule steps_refl)
apply (erule steps_step)
apply (erule step.TyApp [OF step_refl])
apply (erule steps_step)
apply (erule step.TyApp [OF _ step_refl])
done

lemma steps_TyAll_dest:
  assumes "steps (TyAll k t) u"
  shows "\<exists>t'. u = TyAll k t' \<and> steps t t'"
using assms
apply (induct set: steps)
apply (simp add: steps_refl)
apply (clarsimp elim!: step_elims)
apply (erule (1) steps_step)
done


subsection {* Convertibility of type expressions *}

text {* Relation @{text conv} is the symmetric closure of @{text
steps}. *}

inductive conv :: "ty \<Rightarrow> ty \<Rightarrow> bool"
  where steps: "\<lbrakk>steps t1 u; steps t2 u\<rbrakk> \<Longrightarrow> conv t1 t2"

lemma conv_refl: "conv t t"
by (rule conv.steps [OF steps_refl steps_refl])

lemma conv_sym: "conv t u \<Longrightarrow> conv u t"
by (erule conv.induct, erule (1) conv.steps)

lemma conv_trans: "conv t u \<Longrightarrow> conv u v \<Longrightarrow> conv t v"
apply (clarsimp elim!: conv.cases)
apply (drule (1) steps_confluent, clarify)
apply (rule conv.steps)
apply (erule (1) steps_trans)
apply (erule (1) steps_trans)
done

lemma conv_unfold: "conv (TyFix k t) (ty_subst 0 t (TyFix k t))"
apply (rule conv.intros [OF _ steps_refl])
apply (rule steps_step [OF steps_refl])
apply (rule step.unfold [OF step_refl])
done

lemma conv_beta: "conv (TyApp (TyLam k t) u) (ty_subst 0 t u)"
apply (rule conv.intros [OF _ steps_refl])
apply (rule steps_step [OF steps_refl])
apply (rule step.beta [OF step_refl step_refl])
done

lemma conv_subst:
  assumes "conv t t'" and "conv u u'"
  shows "conv (ty_subst i t u) (ty_subst i t' u')"
using assms
by (auto elim!: conv.cases intro: conv.intros steps_ty_subst)

lemma conv_TyApp:
  "\<lbrakk>conv t t'; conv u u'\<rbrakk> \<Longrightarrow> conv (TyApp t u) (TyApp t' u')"
by (auto elim!: conv.cases intro: conv.intros steps_TyApp)

lemma conv_TyAll_dest:
  "conv (TyAll k t) (TyAll k t') \<Longrightarrow> conv t t'"
by (auto elim!: conv.cases dest!: steps_TyAll_dest
  intro: conv.intros)


subsection {* Injective type constructors *}

inductive ty_injective :: "ty \<Rightarrow> bool"
  where TyBase: "ty_injective (TyBase b)"
  | TyApp: "ty_injective t \<Longrightarrow> ty_injective (TyApp t u)"
  | TyRec: "ty_injective (TyRec k t)"

lemma step_ty_injective:
  "\<lbrakk>step t t'; ty_injective t\<rbrakk> \<Longrightarrow> ty_injective t'"
apply (induct set: step)
apply (auto elim: ty_injective.cases intro!: ty_injective.intros)
done

lemma steps_ty_injective:
  "\<lbrakk>steps t t'; ty_injective t\<rbrakk> \<Longrightarrow> ty_injective t'"
apply (induct set: steps, assumption)
apply (auto dest: step_ty_injective)
done

lemma ty_injective_step_dest:
  "\<lbrakk>ty_injective t; step (TyApp t u) ty\<rbrakk>
    \<Longrightarrow> \<exists>t' u'. ty = TyApp t' u' \<and> step t t' \<and> step u u'"
apply (induct arbitrary: u ty set: ty_injective)
apply (auto elim: step_elims)
done

lemma ty_injective_steps_dest:
  "\<lbrakk>steps (TyApp t u) ty; ty_injective t\<rbrakk>
    \<Longrightarrow> \<exists>t' u'. ty = TyApp t' u' \<and> steps t t' \<and> steps u u'"
apply (induct set: steps)
apply (simp add: steps_refl)
apply clarsimp
apply (drule (1) steps_ty_injective [COMP swap_prems_rl])
apply (drule (1) ty_injective_step_dest, clarsimp)
apply (rule conjI)
apply (erule (1) steps_step)
apply (erule (1) steps_step)
done

lemma ty_injective_conv_dest:
  "\<lbrakk>conv (TyApp t a) (TyApp u b); ty_injective t; ty_injective u\<rbrakk>
    \<Longrightarrow> conv t u \<and> conv a b"
apply (clarsimp elim!: conv.cases)
apply (drule (1) ty_injective_steps_dest)
apply (drule (1) ty_injective_steps_dest)
apply clarsimp
apply (rule conjI)
apply (erule (1) conv.intros)
apply (erule (1) conv.intros)
done

lemma ty_injective_conv_iff:
  "\<lbrakk>ty_injective t; ty_injective u\<rbrakk>
    \<Longrightarrow> conv (TyApp t a) (TyApp u b) \<longleftrightarrow> conv t u \<and> conv a b"
by (safe dest!: ty_injective_conv_dest intro!: conv_TyApp)


subsection {* Examples *}

notation Suc ("_\<onesuperior>" [1000] 1000)

text {*
data Tree a = Leaf a | Node (Forest a)
data Forest a = Nil | Cons (Tree a) (Forest a)
*}

definition Tree :: ty
  where "Tree = TyRec (KArrow KStar KStar) (TyLam KStar (TyData ''Tree'' [[TyVar 0], [TyApp (TyRec (KArrow KStar KStar) (TyLam KStar (TyData ''Forest''
  [[], [TyApp (TyVar 0\<onesuperior>) (TyVar 0), TyApp (TyVar 0\<onesuperior>\<onesuperior>\<onesuperior>) (TyVar 0)]]))) (TyVar 0)]]))"

definition Forest :: ty
  where "Forest = TyRec (KArrow KStar KStar) (TyLam KStar (TyData ''Forest''
  [[], [TyApp (TyVar 0\<onesuperior>) (TyVar 0), TyApp Tree (TyVar 0)]]))"

lemma has_kind_Tree: "has_kind \<Gamma> Tree (KArrow KStar KStar)"
unfolding Tree_def
by (rule kind_rules)+

lemma has_kind_Forest: "has_kind \<Gamma> Forest (KArrow KStar KStar)"
unfolding Forest_def Tree_def
by (rule kind_rules)+

lemma ty_injective_Tree: "ty_injective Tree"
unfolding Tree_def by (rule ty_injective.TyRec)

lemma conv_Tree_iff: "conv (TyApp Tree a) (TyApp Tree b) \<longleftrightarrow> conv a b"
by (simp add: ty_injective_conv_iff ty_injective_Tree conv_refl)

text {*
data Either a b = Left a | Right b
data List a = Nil | Cons a (List a)
*}

definition
  "Either = TyRec (KArrow KStar (KArrow KStar KStar))
    (TyLam KStar (TyLam KStar (TyData ''Either'' [[TyVar 0\<onesuperior>], [TyVar 0]])))"

definition
  "List = TyRec (KArrow KStar KStar) (TyLam KStar
    (TyData ''List'' [[], [TyVar 0, TyApp (TyVar 0\<onesuperior>) (TyVar 0)]]))"

lemma has_kind_Either:
  "has_kind \<Gamma> Either (KArrow KStar (KArrow KStar KStar))"
unfolding Either_def by (rule kind_rules)+

lemma has_kind_List:
  "has_kind \<Gamma> List (KArrow KStar KStar)"
unfolding List_def by (rule kind_rules)+

text {*
newtype MyList a = MkMyList (List a)
*}

definition
  "MyList = TyFix (KArrow KStar KStar)
    (TyLam KStar (TyApp List (TyVar 0)))"

lemma has_kind_MyList:
  "has_kind \<Gamma> MyList (KArrow KStar KStar)"
unfolding MyList_def by (rule kind_rules has_kind_List)+

lemma ty_subst_List: "ty_subst i List x = List"
unfolding List_def by simp

lemma conv_MyList:
  shows "conv (TyApp MyList a) (TyApp List a)"
unfolding MyList_def
apply (rule conv_trans)
apply (rule conv_TyApp [OF conv_unfold conv_refl])
apply (simp add: ty_subst_List)
apply (rule conv_trans [OF conv_beta])
apply (simp add: ty_subst_List)
apply (rule conv_refl)
done

text {*
newtype Tree a = MkTree (Either a (Forest a))
newtype Forest a = MkForest (List (Tree a))
*}

definition
  "Tree' = TyFix (KArrow KStar KStar) (TyLam KStar (TyApp (TyApp Either (TyVar 0)) (TyApp (TyFix (KArrow KStar KStar) (TyLam KStar (TyApp List (TyApp (TyVar 0\<onesuperior>\<onesuperior>\<onesuperior>) (TyVar 0))))) (TyVar 0))))"

definition
  "Forest' = TyFix (KArrow KStar KStar)
    (TyLam KStar (TyApp List (TyApp Tree' (TyVar 0))))"

lemma has_kind_Tree':
  "has_kind \<Gamma> Tree' (KArrow KStar KStar)"
unfolding Tree'_def
by (rule kind_rules has_kind_Either has_kind_List)+

lemma has_kind_Forest':
  "has_kind \<Gamma> Forest' (KArrow KStar KStar)"
unfolding Forest'_def
by (rule kind_rules has_kind_List has_kind_Tree')+

lemma conv_Forest':
  "conv (TyApp Forest' a) (TyApp List (TyApp Tree' a))"
unfolding Forest'_def Tree'_def List_def Either_def
apply (rule conv_trans)
apply (rule conv_TyApp [OF conv_unfold conv_refl])
apply simp
apply (rule conv_trans [OF conv_beta])
apply simp
apply (rule conv_refl)
done

lemma conv_Tree':
  "conv (TyApp Tree' a) (TyApp (TyApp Either a) (TyApp Forest' a))"
unfolding Forest'_def Tree'_def List_def Either_def
apply (rule conv_trans)
apply (rule conv_TyApp [OF conv_unfold conv_refl])
apply simp
apply (rule conv_trans [OF conv_beta])
apply simp
apply (rule conv_refl)
done

end
