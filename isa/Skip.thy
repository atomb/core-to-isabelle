theory Skip
imports Main
begin

subsection {* skip and unskip *}

definition
  skip :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "skip i n = (if n < i then n else Suc n)"

lemma skip_0: "skip 0 n = Suc n"
unfolding skip_def by simp

lemma skip_Suc_Suc: "skip (Suc i) (Suc n) = Suc (skip i n)"
unfolding skip_def by simp

lemma skip_Suc_0: "skip (Suc i) 0 = 0"
unfolding skip_def by simp

lemma skip_inject: "(skip i m = skip i n) = (m = n)"
unfolding skip_def by simp

lemma skip_skip_le:
  "i \<le> j \<Longrightarrow> skip i (skip j n) = skip (Suc j) (skip i n)"
unfolding skip_def by auto

lemma skip_Suc_skip:
  "i \<le> j \<Longrightarrow> skip (Suc j) (skip i n) = skip i (skip j n)"
unfolding skip_def by auto

lemma skip_neq: "skip i n \<noteq> i"
unfolding skip_def by simp

definition
  unskip :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "unskip i n = (if i < n then (n - 1) else n)"

lemma unskip_i_0: "unskip i 0 = 0"
unfolding unskip_def by simp

lemma unskip_0_Suc: "unskip 0 (Suc n) = n"
unfolding unskip_def by simp

lemma unskip_Suc_Suc: "unskip (Suc i) (Suc n) = Suc (unskip i n)"
unfolding unskip_def by simp

lemma unskip_skip: "unskip i (skip i n) = n"
unfolding unskip_def skip_def by simp

lemma skip_unskip: "n \<noteq> i \<Longrightarrow> skip i (unskip i n) = n"
unfolding skip_def unskip_def by auto

lemma skip_cases:
  assumes 1: "x = i \<Longrightarrow> P"
  assumes 2: "\<And>n. x = skip i n \<Longrightarrow> P"
  shows "P"
apply (case_tac "x = i")
apply (erule 1)
apply (erule 2 [OF skip_unskip [symmetric]])
done

lemma unskip_inject: "\<lbrakk>m \<noteq> i; n \<noteq> i\<rbrakk> \<Longrightarrow> (unskip i m = unskip i n) = (m = n)"
apply safe
apply (drule skip_inject [where i="i", THEN iffD2])
apply (simp add: skip_unskip)
done

subsection {* substVar *}

definition
  substVar :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "substVar V i x n = (if n = i then x else V (unskip i n))"

lemma substVar_eq: "substVar V i x i = x"
unfolding substVar_def by simp

lemma substVar_neq: "n \<noteq> i \<Longrightarrow> substVar V i x n = V (unskip i n)"
unfolding substVar_def by simp

lemma substVar_lt: "n < i \<Longrightarrow> substVar V i x n = V n"
unfolding substVar_def unskip_def by simp

lemma substVar_gt: "i < n \<Longrightarrow> substVar V i x n = V (n - 1)"
unfolding substVar_def unskip_def by simp

lemma substVar_Var:
  "substVar V i (V m) n = V (if n = i then m else unskip i n)"
unfolding substVar_def by simp

lemma substVar_skip: "substVar V i x (skip i n) = V n"
unfolding substVar_def by (simp add: skip_neq unskip_skip)

lemma lift_substVar_le:
  assumes lift_V: "\<And>n. lift i (V n) = V (skip i n)"
  shows "i \<le> j \<Longrightarrow>
       lift i (substVar V j x n) =
       substVar V (Suc j) (lift i x) (skip i n)"
apply (rule_tac x="n" and i="j" in skip_cases)
apply (simp add: skip_def substVar_eq)
apply (simp add: substVar_skip skip_skip_le lift_V)
done

lemma lift_substVar_ge:
  assumes lift_V: "\<And>n. lift i (V n) = V (skip i n)"
  shows "j \<le> i \<Longrightarrow>
       lift i (substVar V j x n) =
       substVar V j (lift i x) (skip (Suc i) n)"
apply (rule_tac x="n" and i="j" in skip_cases)
apply (simp add: skip_def substVar_eq)
apply (simp add: substVar_skip skip_Suc_skip lift_V)
done

lemma subst_substVar_ge:
  assumes subst_lift: "\<And>x. subst j (lift j y) x = y"
  assumes lift_V: "\<And>i n. lift i (V n) = V (skip i n)"
  assumes subst_V: "\<And>i n x. subst i (V n) x = substVar V i x n"
  shows "j \<le> i \<Longrightarrow>
       subst i (substVar V j x n) y =
       subst j (substVar V (Suc i) (lift j y) n) (subst i x y)"
 apply (rule_tac x="n" and i="j" in skip_cases)
  apply (rule_tac x="n" and i="Suc i" in skip_cases)
   apply simp
  apply (clarsimp simp add: subst_V substVar_eq substVar_skip)
  apply (clarsimp simp add: skip_def substVar_eq)
 apply (clarsimp simp add: subst_V substVar_skip)
by (auto simp add: assms substVar_def unskip_def skip_def)

end
