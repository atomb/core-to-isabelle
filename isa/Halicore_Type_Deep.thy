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
  | TyRec tdef
and tdef
  = TyLam kind tdef
  | TyNew ty
  | TyData tag "ty list list"
(* 7 seconds *)


subsection {* Kinding relation *}

primrec base_kind :: "base \<Rightarrow> kind"
  where "base_kind TyFun = KArrow KStar (KArrow KStar KStar)"
  | "base_kind TyInt = KStar"
  | "base_kind TyChar = KStar"

primrec tdef_kind :: "tdef \<Rightarrow> kind"
  where "tdef_kind (TyLam k t) = KArrow k (tdef_kind t)"
  | "tdef_kind (TyNew t) = KStar"
  | "tdef_kind (TyData s tss) = KStar"

lemma mapsto_intros:
  "mapsto (z # xs) 0 z"
  "mapsto xs n z \<Longrightarrow> mapsto (x # xs) (Suc n) z"
by simp_all

lemma list_all_mono [mono]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> list_all P xs \<longrightarrow> list_all Q xs"
by (induct xs, simp_all)

inductive has_kind :: "kind list \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> bool"
  and tdef_ok :: "kind list \<Rightarrow> tdef \<Rightarrow> kind \<Rightarrow> bool"
where has_kind_TyVar: "mapsto \<Gamma> n k \<Longrightarrow> has_kind \<Gamma> (TyVar n) k"
  | has_kind_TyBase: "has_kind \<Gamma> (TyBase b) (base_kind b)"
  | has_kind_TyAll:
    "has_kind (k # \<Gamma>) t KStar \<Longrightarrow> has_kind \<Gamma> (TyAll k t) KStar"
  | has_kind_TyApp:
    "\<lbrakk>has_kind \<Gamma> t1 (KArrow k1 k2); has_kind \<Gamma> t2 k1\<rbrakk>
      \<Longrightarrow> has_kind \<Gamma> (TyApp t1 t2) k2"
  | has_kind_TyRec:
    "\<lbrakk>tdef_kind d = k; tdef_ok (k # \<Gamma>) d k\<rbrakk>
      \<Longrightarrow> has_kind \<Gamma> (TyRec d) k"
  | tdef_ok_TyLam:
    "tdef_ok (k1 # \<Gamma>) d k2 \<Longrightarrow> tdef_ok \<Gamma> (TyLam k1 d) (KArrow k1 k2)"
  | tdef_ok_TyNew: "has_kind \<Gamma> t k \<Longrightarrow> tdef_ok \<Gamma> (TyNew t) k"
  | tdef_ok_TyData: "list_all (list_all (\<lambda>t. has_kind \<Gamma> t KStar)) tss
      \<Longrightarrow> tdef_ok \<Gamma> (TyData s tss) KStar"

lemma list_all_intros:
  "list_all P []"
  "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)"
by simp_all

lemma tdef_kind_intros:
  "tdef_kind t = k' \<Longrightarrow> tdef_kind (TyLam k t) = KArrow k k'"
  "tdef_kind (TyNew ty) = KStar"
  "tdef_kind (TyData s tss) = KStar"
by simp_all

lemmas kind_rules =
  has_kind_tdef_ok.intros
  mapsto_intros
  list_all_intros
  tdef_kind_intros


subsection {* Substitution *}

primrec ty_lift :: "nat \<Rightarrow> ty \<Rightarrow> ty"
  and tdef_lift :: "nat \<Rightarrow> tdef \<Rightarrow> tdef"
  and cons_lift :: "nat \<Rightarrow> ty list list \<Rightarrow> ty list list"
  and args_lift :: "nat \<Rightarrow> ty list \<Rightarrow> ty list"
  where "ty_lift i (TyVar n) = TyVar (skip i n)"
  | "ty_lift i (TyBase b) = TyBase b"
  | "ty_lift i (TyApp t1 t2) = TyApp (ty_lift i t1) (ty_lift i t2)"
  | "ty_lift i (TyAll k t) = TyAll k (ty_lift (Suc i) t)"
  | ty_lift_TyRec:
    "ty_lift i (TyRec d) = TyRec (tdef_lift (Suc i) d)"
  | "tdef_lift i (TyLam k d) = TyLam k (tdef_lift (Suc i) d)"
  | "tdef_lift i (TyNew t) = TyNew (ty_lift i t)"
  | tdef_lift_TyData:
    "tdef_lift i (TyData s tss) = TyData s (cons_lift i tss)"
  | "cons_lift i [] = []"
  | cons_lift_Cons:
    "cons_lift i (ts # tss) = args_lift i ts # cons_lift i tss"
  | "args_lift i [] = []"
  | "args_lift i (t # ts) = ty_lift i t # args_lift i ts"

primrec ty_subst :: "nat \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  and tdef_subst :: "nat \<Rightarrow> tdef \<Rightarrow> ty \<Rightarrow> tdef"
  and cons_subst :: "nat \<Rightarrow> ty list list \<Rightarrow> ty \<Rightarrow> ty list list"
  and args_subst :: "nat \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> ty list"
  where "ty_subst i (TyVar n) x = substVar TyVar i x n"
  | "ty_subst i (TyBase b) x = TyBase b"
  | "ty_subst i (TyApp t1 t2) x = TyApp (ty_subst i t1 x) (ty_subst i t2 x)"
  | "ty_subst i (TyAll k t) x = TyAll k (ty_subst (Suc i) t (ty_lift 0 x))"
  | ty_subst_TyRec:
    "ty_subst i (TyRec d) x = TyRec (tdef_subst (Suc i) d (ty_lift 0 x))"
  | "tdef_subst i (TyLam k d) x = TyLam k (tdef_subst (Suc i) d (ty_lift 0 x))"
  | "tdef_subst i (TyNew t) x = TyNew (ty_subst i t x)"
  | tdef_subst_TyData:
    "tdef_subst i (TyData s tss) x = TyData s (cons_subst i tss x)"
  | "cons_subst i [] x = []"
  | "cons_subst i (ts # tss) x = args_subst i ts x # cons_subst i tss x"
  | "args_subst i [] x = []"
  | "args_subst i (t # ts) x = ty_subst i t x # args_subst i ts x"

lemma Cons_shift: "y # shift A i x = shift (y # A) (Suc i) x"
using shift_shift [of A i x y] by (simp add: shift_0)

lemma tdef_kind_tdef_lift [simp]:
  "tdef_kind (tdef_lift i d) = tdef_kind d"
by (induct d arbitrary: i, simp_all)

lemma
  shows has_kind_shift_ty_lift:
    "has_kind \<Gamma> t k \<Longrightarrow> has_kind (\<Gamma>{i:=k'}) (ty_lift i t) k"
  and tdef_ok_shift_ty_lift:
    "tdef_ok \<Gamma> d k \<Longrightarrow> tdef_ok (\<Gamma>{i:=k'}) (tdef_lift i d) k"
apply (induct arbitrary: i and i set: has_kind tdef_ok)
apply (simp add: has_kind_TyVar mapsto_shift_skip)
apply (simp add: has_kind_TyBase)
apply (simp add: has_kind_TyAll Cons_shift)
apply (force intro!: has_kind_TyApp)
apply (drule sym, simp)
apply (rule has_kind_TyRec, simp)
apply (simp add: Cons_shift)
apply (simp add: tdef_ok_TyLam Cons_shift)
apply (simp add: tdef_ok_TyNew)
apply simp
apply (rule tdef_ok_TyData)
apply (erule rev_mp, induct_tac tss, simp, simp)
apply (rename_tac ts tss)
apply (induct_tac ts, simp, simp)
done

lemma has_kind_Cons_ty_lift_0:
  "has_kind \<Gamma> t k \<Longrightarrow> has_kind (k' # \<Gamma>) (ty_lift 0 t) k"
by (rule has_kind_shift_ty_lift [where i=0, unfolded shift_0])

lemma tdef_kind_tdef_subst:
  "tdef_kind (tdef_subst i d x) = tdef_kind d"
by (induct d arbitrary: i x, simp_all)

lemma mapsto_unskip:
  "n \<noteq> i \<Longrightarrow> mapsto (shift \<Gamma> i k') n k \<Longrightarrow> mapsto \<Gamma> (unskip i n) k"
apply (induct \<Gamma> arbitrary: i n)
apply (case_tac i)
apply (case_tac n, simp, simp add: shift_0)
apply (simp add: shift_Nil_Suc)
apply (case_tac i)
apply (case_tac n, simp, simp add: shift_0 unskip_0_Suc)
apply (simp add: shift_Cons_Suc)
apply (case_tac n, simp add: unskip_i_0, simp add: unskip_Suc_Suc)
done

lemma
  shows has_kind_ty_subst [OF _ refl]:
    "\<lbrakk>has_kind \<Gamma>' t k; \<Gamma>' = shift \<Gamma> i k'; has_kind \<Gamma> x k'\<rbrakk>
      \<Longrightarrow> has_kind \<Gamma> (ty_subst i t x) k"
  and tdef_ok_tdef_subst [OF _ refl]:
    "\<lbrakk>tdef_ok \<Gamma>' d k; \<Gamma>' = shift \<Gamma> i k'; has_kind \<Gamma> x k'\<rbrakk>
      \<Longrightarrow> tdef_ok \<Gamma> (tdef_subst i d x) k"
apply (induct arbitrary: \<Gamma> i x and \<Gamma> i x set: has_kind tdef_ok, simp_all)
txt "TyVar"
apply (case_tac "n = i")
apply (simp add: mapsto_shift_eq substVar_eq)
apply (simp add: substVar_neq)
apply (rule has_kind_TyVar)
apply (erule (1) mapsto_unskip)
txt "TyBase"
apply (rule has_kind_TyBase)
txt "TyAll"
apply (rule has_kind_TyAll)
apply (simp add: has_kind_Cons_ty_lift_0 shift_Cons_Suc)
txt "TyApp"
apply (rule_tac ?k1.0=k1 in has_kind_TyApp, simp, simp)
txt "TyRec"
apply (rule has_kind_TyRec)
apply (simp add: tdef_kind_tdef_subst)
apply (simp add: has_kind_Cons_ty_lift_0 shift_Cons_Suc)
txt "TyLam"
apply (rule tdef_ok_TyLam)
apply (simp add: has_kind_Cons_ty_lift_0 shift_Cons_Suc)
txt "TyNew"
apply (rule tdef_ok_TyNew)
apply simp
txt "TyData"
apply (rule tdef_ok_TyData)
apply (erule rev_mp)
apply (induct_tac tss, simp, simp, rename_tac ts tss)
apply (induct_tac ts, simp, simp)
done

lemma has_kind_ty_subst_0:
  "\<lbrakk>has_kind (k' # \<Gamma>) t k; has_kind \<Gamma> x k'\<rbrakk>
    \<Longrightarrow> has_kind \<Gamma> (ty_subst 0 t x) k"
by (rule has_kind_ty_subst [where i=0, unfolded shift_0])

lemma tdef_ok_tdef_subst_0:
  "\<lbrakk>tdef_ok (k' # \<Gamma>) d k; has_kind \<Gamma> x k'\<rbrakk>
    \<Longrightarrow> tdef_ok \<Gamma> (tdef_subst 0 d x) k"
by (rule tdef_ok_tdef_subst [where i=0, unfolded shift_0])

subsection {* Coercibility proofs between types *}

inductive ty_ax :: "kind list \<Rightarrow> ty \<Rightarrow> tdef \<Rightarrow> kind \<Rightarrow> bool"
where ty_ax_TyRec:
    "has_kind \<Gamma> (TyRec d) k
      \<Longrightarrow> ty_ax \<Gamma> (TyRec d) (tdef_subst 0 d (TyRec d)) k"
  | ty_ax_TyApp:
    "\<lbrakk>ty_ax \<Gamma> t (TyLam k1 d) (KArrow k1 k2); has_kind \<Gamma> x k1\<rbrakk>
      \<Longrightarrow> ty_ax \<Gamma> (TyApp t x) (tdef_subst 0 d x) k2"

inductive ty_eq :: "kind list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> bool"
where ty_eq_refl:
    "has_kind \<Gamma> a k \<Longrightarrow> ty_eq \<Gamma> a a k"
  | ty_eq_sym:
    "ty_eq \<Gamma> a b k \<Longrightarrow> ty_eq \<Gamma> b a k"
  | ty_eq_trans:
    "\<lbrakk>ty_eq \<Gamma> a b k; ty_eq \<Gamma> b c k\<rbrakk> \<Longrightarrow> ty_eq \<Gamma> a c k"
  | ty_eq_TyApp:
    "\<lbrakk>ty_eq \<Gamma> f g (KArrow k1 k2); ty_eq \<Gamma> a b k1\<rbrakk>
      \<Longrightarrow> ty_eq \<Gamma> (TyApp f a) (TyApp g b) k2"
  | ty_eq_TyAll:
    "ty_eq (k # \<Gamma>) a b KStar \<Longrightarrow> ty_eq \<Gamma> (TyAll k a) (TyAll k b) KStar"
  | ty_eq_axiom:
    "ty_ax \<Gamma> a (TyNew b) KStar \<Longrightarrow> ty_eq \<Gamma> a b KStar"

inductive_cases
  has_kind_TyRec_elim: "has_kind \<Gamma> (TyRec d) k"
and
  tdef_ok_TyLam_elim: "tdef_ok \<Gamma> (TyLam k1 d) (KArrow k1 k2)"
and
  tdef_ok_TyNew_elim: "tdef_ok \<Gamma> (TyNew b) KStar"

lemma ty_ax_has_kind:
  assumes "ty_ax \<Gamma> t d k"
  shows "has_kind \<Gamma> t k \<and> tdef_ok \<Gamma> d k"
using assms
apply (induct set: ty_ax)
txt "TyRec"
apply simp
apply (erule has_kind_TyRec_elim)
apply (rule tdef_ok_tdef_subst_0, assumption)
apply (rule has_kind_TyRec, simp, simp)
txt "TyApp"
apply (rule conjI)
apply (force intro!: has_kind_TyApp)
apply (erule conjE)
apply (erule tdef_ok_TyLam_elim)
apply (erule (1) tdef_ok_tdef_subst_0)
done

lemma ty_eq_has_kind:
  assumes "ty_eq \<Gamma> t t' k"
  shows "has_kind \<Gamma> t k \<and> has_kind \<Gamma> t' k"
using assms
apply (induct set: ty_eq)
apply simp (* refl *)
apply simp (* sym *)
apply simp (* trans *)
apply (force intro!: has_kind_TyApp) (* TyApp *)
apply (simp add: has_kind_TyAll) (* TyAll *)
apply (drule ty_ax_has_kind)
apply clarsimp
apply (erule (1) tdef_ok_TyNew_elim)
done


subsection {* Examples *}

notation Suc ("_\<onesuperior>" [1000] 1000)

text {*
data Tree a = Leaf a | Node (Forest a)
data Forest a = Nil | Cons (Tree a) (Forest a)
*}

definition Tree :: ty
  where "Tree = TyRec (TyLam KStar (TyData ''Tree'' [[TyVar 0], [TyApp (TyRec (TyLam KStar (TyData ''Forest''
  [[], [TyApp (TyVar 0\<onesuperior>) (TyVar 0), TyApp (TyVar 0\<onesuperior>\<onesuperior>\<onesuperior>) (TyVar 0)]]))) (TyVar 0)]]))"

definition Forest :: ty
  where "Forest = TyRec (TyLam KStar (TyData ''Forest''
  [[], [TyApp (TyVar 0\<onesuperior>) (TyVar 0), TyApp Tree (TyVar 0)]]))"

lemma has_kind_Tree: "has_kind \<Gamma> Tree (KArrow KStar KStar)"
unfolding Tree_def
by (rule kind_rules)+

lemma has_kind_Forest: "has_kind \<Gamma> Forest (KArrow KStar KStar)"
unfolding Forest_def Tree_def
by (rule kind_rules)+

text {*
data Either a b = Left a | Right b
data List a = Nil | Cons a (List a)
*}

definition
  "Either = TyRec (TyLam KStar (TyLam KStar
    (TyData ''Either'' [[TyVar 0\<onesuperior>], [TyVar 0]])))"

definition
  "List = TyRec (TyLam KStar
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
  "MyList = TyRec (TyLam KStar (TyNew (TyApp List (TyVar 0))))"

lemma has_kind_MyList:
  "has_kind \<Gamma> MyList (KArrow KStar KStar)"
unfolding MyList_def by (rule kind_rules has_kind_List)+

lemma ty_ax_TyApp':
  "\<lbrakk>has_kind \<Gamma> x k1; ty_ax \<Gamma> t (TyLam k1 d) (KArrow k1 k2);
    d2 = tdef_subst 0 d x\<rbrakk>
    \<Longrightarrow> ty_ax \<Gamma> (TyApp t x) d2 k2"
by (simp add: ty_ax_TyApp)

lemma ty_ax_TyRec':
  "\<lbrakk>has_kind \<Gamma> t k; t = TyRec d; d' = tdef_subst 0 d (TyRec d)\<rbrakk>
    \<Longrightarrow> ty_ax \<Gamma> t d' k"
by (simp add: ty_ax_TyRec)

lemma substVar_Suc_0: "substVar \<sigma> (Suc i) x 0 = \<sigma> 0"
by (simp add: substVar_def unskip_i_0)

lemma substVar_Suc_Suc:
  "substVar \<sigma> (Suc i) x (Suc n) = substVar (\<sigma> \<circ> Suc) i x n"
by (simp add: substVar_def unskip_Suc_Suc)

lemma substVar_0_0: "substVar \<sigma> 0 x 0 = x"
by (simp add: substVar_def)

lemmas subst_simps =
  skip_Suc_0 skip_Suc_Suc
  substVar_0_0
  substVar_Suc_0
  substVar_Suc_Suc

lemma ty_subst_List: "ty_subst i List x = List"
unfolding List_def by (simp add: subst_simps)

lemma ty_eq_MyList:
  assumes "has_kind \<Gamma> a KStar"
  shows "ty_eq \<Gamma> (TyApp MyList a) (TyApp List a) KStar"
apply (rule ty_eq_axiom)
apply (rule ty_ax_TyApp' [OF assms])
apply (rule ty_ax_TyRec' [OF has_kind_MyList MyList_def])
apply simp
apply (simp add: ty_subst_List subst_simps)
done

text {*
newtype Tree a = MkTree (Either a (Forest a))
newtype Forest a = MkForest (List (Tree a))
*}

definition
  "Tree' = TyRec (TyLam KStar (TyNew (TyApp (TyApp Either (TyVar 0)) (TyApp (TyRec (TyLam KStar (TyNew (TyApp List (TyApp (TyVar 0\<onesuperior>\<onesuperior>\<onesuperior>) (TyVar 0)))))) (TyVar 0)))))"

definition
  "Forest' = TyRec (TyLam KStar
    (TyNew (TyApp List (TyApp Tree' (TyVar 0)))))"

lemma has_kind_Tree':
  "has_kind \<Gamma> Tree' (KArrow KStar KStar)"
unfolding Tree'_def
by (rule kind_rules has_kind_Either has_kind_List)+

lemma has_kind_Forest':
  "has_kind \<Gamma> Forest' (KArrow KStar KStar)"
unfolding Forest'_def
by (rule kind_rules has_kind_List has_kind_Tree')+

lemma ty_eq_Forest':
  assumes "has_kind \<Gamma> a KStar"
  shows "ty_eq \<Gamma> (TyApp Forest' a) (TyApp List (TyApp Tree' a)) KStar"
apply (rule ty_eq_axiom)
apply (rule ty_ax_TyApp' [OF assms])
apply (rule ty_ax_TyRec' [OF has_kind_Forest' Forest'_def])
apply simp
apply (simp add: List_def Tree'_def Either_def subst_simps)
done

lemma ty_eq_Tree':
  assumes "has_kind \<Gamma> a KStar"
  shows "ty_eq \<Gamma> (TyApp Tree' a) (TyApp (TyApp Either a) (TyApp Forest' a)) KStar"
apply (rule ty_eq_axiom)
apply (rule ty_ax_TyApp' [OF assms])
apply (rule ty_ax_TyRec' [OF has_kind_Tree' Tree'_def])
apply simp
apply (simp add: List_def Forest'_def Tree'_def Either_def subst_simps)
done

unused_thms

end
