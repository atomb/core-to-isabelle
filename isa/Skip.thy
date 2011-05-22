theory Skip
imports Main
begin

subsection {* skip *}

text {* The function @{text "skip i"} enumerates all naturals except
@{text "i"}. *}

definition
  skip :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "skip i = (\<lambda>n. if n < i then n else Suc n)"

lemma skip_0 [simp]: "skip 0 = Suc"
unfolding skip_def by simp

lemma skip_Suc_Suc [simp]: "skip (Suc i) (Suc n) = Suc (skip i n)"
unfolding skip_def by simp

lemma skip_Suc_0 [simp]: "skip (Suc i) 0 = 0"
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

lemma skip_cases:
  assumes 1: "x = i \<Longrightarrow> P"
  assumes 2: "\<And>n. x = skip i n \<Longrightarrow> P"
  shows "P"
apply (cases "x = i", erule 1)
apply (rule 2 [where n="if i < x then (x - 1) else x"])
apply (auto simp add: skip_def)
done

subsection {* substVar *}

definition substVar :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "substVar V i x n =
    (if n = i then x else V (if i < n then (n - 1) else n))"

lemma substVar_0_0: "substVar V 0 x 0 = x"
unfolding substVar_def by simp

lemma substVar_0_Suc [simp]: "substVar V 0 x (Suc n) = V n"
unfolding substVar_def by simp

lemma substVar_Suc_0 [simp]: "substVar V (Suc i) x 0 = V 0"
unfolding substVar_def by simp

lemma substVar_Suc_Suc [simp]:
  "substVar V (Suc i) x (Suc n) = substVar (\<lambda>n. V (Suc n)) i x n"
unfolding substVar_def by simp

lemma substVar_eq [simp]: "substVar V i x i = x"
unfolding substVar_def by simp

lemma substVar_skip [simp]: "substVar V i x (skip i n) = V n"
unfolding substVar_def skip_def by auto

end
