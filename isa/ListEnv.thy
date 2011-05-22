(* Version: Isabelle2011 *)

header {* Environments *}

theory ListEnv imports Skip begin

type_synonym 'a env = "'a list"

subsection {* mapsto *}

primrec mapsto :: "['a env, nat, 'a] \<Rightarrow> bool"
  where mapsto_Nil:
    "mapsto [] n y = False"
  | mapsto_Cons:
    "mapsto (x # xs) n y = (case n of 0 \<Rightarrow> x = y | Suc i \<Rightarrow> mapsto xs i y)"

declare mapsto_Cons [simp del]

lemma mapsto_Cons_0 [simp]: "mapsto (x # xs) 0 y = (x = y)"
by (simp add: mapsto_Cons)

lemma mapsto_Cons_Suc [simp]: "mapsto (x # xs) (Suc n) y = mapsto xs n y"
by (simp add: mapsto_Cons)

lemma mapsto_same:
  "\<lbrakk>mapsto A i x; mapsto A i y\<rbrakk> \<Longrightarrow> x = y"
apply (induct A arbitrary: i)
apply simp
apply (case_tac i, simp, simp)
done

subsection {* shift *}

primrec shift :: "['a env, nat, 'a] \<Rightarrow> 'a env" ("_{_:=_}" [90,0,0] 91)
  where shift_0:
    "shift A 0 y = y # A"
  | shift_Suc:
    "shift A (Suc i) y = (case A of [] \<Rightarrow> [] | x # xs \<Rightarrow> x # shift xs i y)"

declare shift_Suc [simp del]

lemma shift_Nil_Suc [simp]: "shift [] (Suc i) y = []"
by (simp add: shift_Suc)

lemma shift_Cons_Suc [simp]: "shift (x # xs) (Suc i) y = x # shift xs i y"
by (simp add: shift_Suc)

lemma Cons_shift: "x # shift xs i y = shift (x # xs) (Suc i) y"
by (simp add: shift_Suc)

lemma mapsto_shift_eq:
  "mapsto (A{i:=x}) i y = (i \<le> length A \<and> x = y)"
apply (induct A arbitrary: i)
apply (case_tac i, simp, simp)
apply (case_tac i, simp, simp)
done

lemma mapsto_shift_0_0: "mapsto (A{0:=x}) 0 x"
by simp

lemma mapsto_shift_skip: "mapsto (A{i:=x}) (skip i n) y = mapsto A n y"
apply (induct A arbitrary: i n)
apply (case_tac i, simp, simp)
apply (case_tac i, simp)
apply (case_tac n, simp, simp)
done

lemma shift_shift_le:
  "i \<le> j \<Longrightarrow> shift (shift A j x) i y = shift (shift A i y) (Suc j) x"
apply (induct A arbitrary: i j)
apply (case_tac i, simp)
apply (case_tac j, simp, simp)
apply (case_tac i, simp)
apply (case_tac j, simp, simp)
done

lemma shift_shift:
  "A{i:=x}{0:=y} = A{0:=y}{Suc i:=x}"
by simp

subsection {* shifts *}

primrec shifts :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "shifts A i [] = A"
  | "shifts A i (x # xs) = shift (shifts A i xs) i x"

lemma shifts_0_shift:
  "shifts (shift A i x) 0 ys = shift (shifts A 0 ys) (i + length ys) x"
by (induct ys) (simp_all add: shift_shift)


subsection {* unshift *}

primrec unshift :: "'a env \<Rightarrow> nat \<Rightarrow> 'a env"
  where unshift_Nil: "unshift [] i = []"
  | unshift_Cons:
    "unshift (x # xs) i = (case i of 0 \<Rightarrow> xs | Suc j \<Rightarrow> x # unshift xs j)"

declare unshift_Cons [simp del]

lemma unshift_Cons_0 [simp]: "unshift (x # xs) 0 = xs"
by (simp add: unshift_Cons)

lemma unshift_Cons_Suc [simp]: "unshift (x # xs) (Suc i) = x # unshift xs i"
by (simp add: unshift_Cons)

lemma unshift_shift: "unshift (shift A i x) i = A"
apply (induct i arbitrary: A)
apply simp
apply (case_tac A, simp, simp)
done

lemma shift_unshift: "mapsto A i x \<Longrightarrow> shift (unshift A i) i x = A"
apply (induct A arbitrary: i)
apply simp
apply (case_tac i, simp, simp)
done

subsection {* map *}

lemma map_map: "map f (map g xs) = map (\<lambda>x. f (g x)) xs"
by (induct xs) simp_all

lemma mapsto_mapI:
  "mapsto A n x \<Longrightarrow> mapsto (map f A) n (f x)"
apply (induct A arbitrary: n)
apply simp
apply (case_tac n, simp, simp)
done

lemma mapsto_map_iff:
  "mapsto (map f A) n x = (\<exists>y. mapsto A n y \<and> f y = x)"
apply (induct A arbitrary: n)
apply simp
apply (case_tac n, simp, simp)
done

lemma map_shift:
  "map f (A{i:=x}) = (map f A){i:=f x}"
apply (induct A arbitrary: i)
apply (case_tac i, simp, simp)
apply (case_tac i, simp, simp)
done

lemma map_shifts: "map f (shifts A i xs) = shifts (map f A) i (map f xs)"
by (induct xs) (simp_all add: map_shift)

subsection {* Empty environment *}

lemma not_mapsto_Nil: "\<not> mapsto [] n x"
by simp

declare shift_0 [simp del]
declare shift_Nil_Suc [simp del]
declare shift_Cons_Suc [simp del]

end
