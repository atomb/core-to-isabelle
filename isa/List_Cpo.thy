(*  Title:      HOLCF/Library/List_Cpo.thy
    Author:     Brian Huffman
    Version:    Isabelle2009-2
*)

header {* Lists as a complete partial order *}

theory List_Cpo
imports HOLCF
begin

subsection {* Lemmas from the development version of HOLCF *}

lemma prod_contI:
  assumes f1: "\<And>y. cont (\<lambda>x. f (x, y))"
  assumes f2: "\<And>x. cont (\<lambda>y. f (x, y))"
  shows "cont f"
proof -
  have "cont (\<lambda>(x, y). f (x, y))"
    by (intro cont2cont_split f1 f2 cont2cont)
  thus "cont f"
    by (simp only: split_eta)
qed

lemma prod_cont_iff:
  "cont f \<longleftrightarrow> (\<forall>y. cont (\<lambda>x. f (x, y))) \<and> (\<forall>x. cont (\<lambda>y. f (x, y)))"
apply safe
apply (erule cont_compose [OF _ cont_pair1])
apply (erule cont_compose [OF _ cont_pair2])
apply (simp only: prod_contI)
done

subsection {* Lists are a partial order *}

instantiation list :: (po) po
begin

definition
  "xs \<sqsubseteq> ys \<longleftrightarrow> list_all2 (op \<sqsubseteq>) xs ys"

instance proof
  fix xs :: "'a list"
  from below_refl show "xs \<sqsubseteq> xs"
    unfolding below_list_def
    by (rule list_all2_refl)
next
  fix xs ys zs :: "'a list"
  assume "xs \<sqsubseteq> ys" and "ys \<sqsubseteq> zs"
  with below_trans show "xs \<sqsubseteq> zs"
    unfolding below_list_def
    by (rule list_all2_trans)
next
  fix xs ys zs :: "'a list"
  assume "xs \<sqsubseteq> ys" and "ys \<sqsubseteq> xs"
  with below_antisym show "xs = ys"
    unfolding below_list_def
    by (rule list_all2_antisym)
qed

end

lemma below_list_simps [simp]:
  "[] \<sqsubseteq> []"
  "x # xs \<sqsubseteq> y # ys \<longleftrightarrow> x \<sqsubseteq> y \<and> xs \<sqsubseteq> ys"
  "\<not> [] \<sqsubseteq> y # ys"
  "\<not> x # xs \<sqsubseteq> []"
by (simp_all add: below_list_def)

lemma Nil_below_iff [simp]: "[] \<sqsubseteq> xs \<longleftrightarrow> xs = []"
by (cases xs, simp_all)

lemma below_Nil_iff [simp]: "xs \<sqsubseteq> [] \<longleftrightarrow> xs = []"
by (cases xs, simp_all)

lemma list_below_induct [consumes 1, case_names Nil Cons]:
  assumes "xs \<sqsubseteq> ys"
  assumes 1: "P [] []"
  assumes 2: "\<And>x y xs ys. \<lbrakk>x \<sqsubseteq> y; xs \<sqsubseteq> ys; P xs ys\<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)"
  shows "P xs ys"
using `xs \<sqsubseteq> ys`
proof (induct xs arbitrary: ys)
  case Nil thus ?case by (simp add: 1)
next
  case (Cons x xs) thus ?case by (cases ys, simp_all add: 2)
qed

lemma list_below_cases:
  assumes "xs \<sqsubseteq> ys"
  obtains "xs = []" and "ys = []" |
    x y xs' ys' where "xs = x # xs'" and "ys = y # ys'"
using assms by (cases xs, simp, cases ys, auto)

text "Thanks to Joachim Breitner"

lemma list_Cons_below:
  assumes "a # as \<sqsubseteq> xs"
  obtains b and bs where "a \<sqsubseteq> b" and "as \<sqsubseteq> bs" and "xs = b # bs"
  using assms by (cases xs, auto)

lemma list_below_Cons:
  assumes "xs \<sqsubseteq> b # bs"
  obtains a and as where "a \<sqsubseteq> b" and "as \<sqsubseteq> bs" and "xs = a # as"
  using assms by (cases xs, auto)

lemma hd_mono: "xs \<sqsubseteq> ys \<Longrightarrow> hd xs \<sqsubseteq> hd ys"
by (cases xs, simp, cases ys, simp, simp)

lemma tl_mono: "xs \<sqsubseteq> ys \<Longrightarrow> tl xs \<sqsubseteq> tl ys"
by (cases xs, simp, cases ys, simp, simp)

lemma ch2ch_hd [simp]: "chain (\<lambda>i. S i) \<Longrightarrow> chain (\<lambda>i. hd (S i))"
by (rule chainI, rule hd_mono, erule chainE)

lemma ch2ch_tl [simp]: "chain (\<lambda>i. S i) \<Longrightarrow> chain (\<lambda>i. tl (S i))"
by (rule chainI, rule tl_mono, erule chainE)

lemma below_same_length: "xs \<sqsubseteq> ys \<Longrightarrow> length xs = length ys"
unfolding below_list_def by (rule list_all2_lengthD)

lemma list_chain_induct [consumes 1, case_names Nil Cons]:
  assumes "chain S"
  assumes 1: "P (\<lambda>i. [])"
  assumes 2: "\<And>A B. chain A \<Longrightarrow> chain B \<Longrightarrow> P B \<Longrightarrow> P (\<lambda>i. A i # B i)"
  shows "P S"
using `chain S`
proof (induct "S 0" arbitrary: S)
  case Nil
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF `chain S`])
  with Nil have "\<forall>i. S i = []" by simp
  thus ?case by (simp add: 1)
next
  case (Cons x xs)
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF `chain S`])
  hence *: "\<forall>i. S i \<noteq> []" by (rule all_forward, insert Cons) auto
  have "chain (\<lambda>i. hd (S i))" and "chain (\<lambda>i. tl (S i))"
    using `chain S` by simp_all
  moreover have "P (\<lambda>i. tl (S i))"
    using `chain S` and `x # xs = S 0` [symmetric]
    by (simp add: Cons(1))
  ultimately have "P (\<lambda>i. hd (S i) # tl (S i))"
    by (rule 2)
  thus "P S" by (simp add: *)
qed

lemma list_chain_cases:
  assumes S: "chain S"
  obtains "S = (\<lambda>i. [])" |
    A B where "chain A" and "chain B" and "S = (\<lambda>i. A i # B i)"
using S by (induct rule: list_chain_induct) simp_all

subsection {* Lists are a complete partial order *}

lemma is_lub_Cons:
  assumes A: "range A <<| x"
  assumes B: "range B <<| xs"
  shows "range (\<lambda>i. A i # B i) <<| x # xs"
using assms
unfolding is_lub_def is_ub_def Ball_def [symmetric]
by (clarsimp, case_tac u, simp_all)

instance list :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a list"
  assume "chain S" thus "\<exists>x. range S <<| x"
  proof (induct rule: list_chain_induct)
    case Nil thus ?case by (auto intro: lub_const)
  next
    case (Cons A B) thus ?case by (auto intro: is_lub_Cons cpo_lubI)
  qed
qed

subsection {* Continuity of list operations *}

lemma cont2cont_Cons [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x # g x)"
apply (rule contI)
apply (rule is_lub_Cons)
apply (erule contE [OF f])
apply (erule contE [OF g])
done

lemma lub_Cons:
  fixes A :: "nat \<Rightarrow> 'a::cpo"
  assumes A: "chain A" and B: "chain B"
  shows "(\<Squnion>i. A i # B i) = (\<Squnion>i. A i) # (\<Squnion>i. B i)"
by (intro thelubI is_lub_Cons cpo_lubI A B)

lemma cont2cont_list_case:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h1: "\<And>y ys. cont (\<lambda>x. h x y ys)"
  assumes h2: "\<And>x ys. cont (\<lambda>y. h x y ys)"
  assumes h3: "\<And>x y. cont (\<lambda>ys. h x y ys)"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
apply (rule cont_apply [OF f])
apply (rule contI)
apply (erule list_chain_cases)
apply (simp add: lub_const)
apply (simp add: lub_Cons)
apply (simp add: cont2contlubE [OF h2])
apply (simp add: cont2contlubE [OF h3])
apply (simp add: diag_lub ch2ch_cont [OF h2] ch2ch_cont [OF h3])
apply (rule cpo_lubI, rule chainI, rule below_trans)
apply (erule cont2monofunE [OF h2 chainE])
apply (erule cont2monofunE [OF h3 chainE])
apply (case_tac y, simp_all add: g h1)
done

lemma cont2cont_list_case' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h: "cont (\<lambda>p. h (fst p) (fst (snd p)) (snd (snd p)))"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
using assms by (simp add: cont2cont_list_case prod_cont_iff)

text {* The simple version (due to Joachim Breitner) is needed if the
  element type of the list is not a cpo. *}

lemma cont2cont_list_case_simple [simp, cont2cont]:
  assumes "cont (\<lambda>x. f1 x)"
  assumes "\<And>y ys. cont (\<lambda>x. f2 x y ys)"
  shows "cont (\<lambda>x. case l of [] \<Rightarrow> f1 x | y # ys \<Rightarrow> f2 x y ys)"
using assms by (cases l) auto

text {* Lemma for proving continuity of recursive list functions: *}

lemma list_contI:
  fixes f :: "'a::cpo list \<Rightarrow> 'b::cpo"
  assumes f: "\<And>x xs. f (x # xs) = g x xs (f xs)"
  assumes g1: "\<And>xs y. cont (\<lambda>x. g x xs y)"
  assumes g2: "\<And>x y. cont (\<lambda>xs. g x xs y)"
  assumes g3: "\<And>x xs. cont (\<lambda>y. g x xs y)"
  shows "cont f"
proof (rule contI2)
  obtain h where h: "\<And>x xs y. g x xs y = h\<cdot>x\<cdot>xs\<cdot>y"
  proof
    fix x xs y show "g x xs y = (\<Lambda> x xs y. g x xs y)\<cdot>x\<cdot>xs\<cdot>y"
    by (simp add: cont2cont_LAM g1 g2 g3)
  qed
  show mono: "monofun f"
    apply (rule monofunI)
    apply (erule list_below_induct)
    apply simp
    apply (simp add: f h monofun_cfun)
    done
  fix Y :: "nat \<Rightarrow> 'a list"
  assume "chain Y" thus "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
    apply (induct rule: list_chain_induct)
    apply simp
    apply (simp add: lub_Cons f h)
    apply (simp add: contlub_cfun [symmetric] ch2ch_monofun [OF mono])
    apply (simp add: monofun_cfun)
    done
qed

text {* There are probably lots of other list operations that also
deserve to have continuity lemmas.  I'll add more as they are
needed. *}

subsection {* Using lists with fixrec *}

definition
  match_Nil :: "'a::cpo list \<rightarrow> 'b match \<rightarrow> 'b match"
where
  "match_Nil = (\<Lambda> xs k. case xs of [] \<Rightarrow> k | y # ys \<Rightarrow> Fixrec.fail)"

definition
  match_Cons :: "'a::cpo list \<rightarrow> ('a \<rightarrow> 'a list \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Cons = (\<Lambda> xs k. case xs of [] \<Rightarrow> Fixrec.fail | y # ys \<Rightarrow> k\<cdot>y\<cdot>ys)"

lemma match_Nil_simps [simp]:
  "match_Nil\<cdot>[]\<cdot>k = k"
  "match_Nil\<cdot>(x # xs)\<cdot>k = Fixrec.fail"
unfolding match_Nil_def by simp_all

lemma match_Cons_simps [simp]:
  "match_Cons\<cdot>[]\<cdot>k = Fixrec.fail"
  "match_Cons\<cdot>(x # xs)\<cdot>k = k\<cdot>x\<cdot>xs"
unfolding match_Cons_def by simp_all

setup {*
  Fixrec.add_matchers
    [ (@{const_name Nil}, @{const_name match_Nil}),
      (@{const_name Cons}, @{const_name match_Cons}) ]
*}

end
