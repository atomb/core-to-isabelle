theory IdId
imports "../Shallow"
begin

text {* Example: The identity function applied to itself. *}

text {* In core, there are two possible expressions for "id id == id":

1. (id @ a \<rightarrow> a) (id @ a) = (id @ a)

2. (id @ (forall a. a \<rightarrow> a)) id == id

*}

definition ident :: V where
  "ident = T_lam (\<lambda>a. V_lam a (\<lambda>x. x))"

lemma "ident\<bullet>\<bullet>(T_fun A A)\<bullet>(ident\<bullet>\<bullet>A) = ident\<bullet>\<bullet>A"
by (auto simp add: ident_def)

end