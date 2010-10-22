theory Shallow
imports HOLCF begin

types Id = "char list"
types ID = "Id lift"

default_sort rep

new_domain 'a finlist =
    Snil                   ("<>")
  | Scons (lazy 'a) "('a finlist)"  (infixl "##" 70)

fixrec snoc :: "'a finlist \<rightarrow> 'a \<rightarrow> 'a finlist" where
  "snoc\<cdot><>\<cdot>y = y ## <>"
| "xs \<noteq> \<bottom> \<Longrightarrow> snoc\<cdot>(x ## xs)\<cdot>y = x ## (snoc\<cdot>xs\<cdot>y)"

new_domain V =
    VInt "(int lift)"
  | Vcon ID "(V finlist)"
  | Vfun (lazy "(V \<rightarrow> V)")
  | Wrong                  -- "Don't go here"

typedef T = "{f :: V \<rightarrow> V. deflation f}"
apply (rule_tac x="ID" in exI, simp)
apply (rule deflation_ID)
done

typedecl C

fixrec (permissive) V_apply :: "V \<rightarrow> V \<rightarrow> V" where
"V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x" | 
"V_apply\<cdot>f\<cdot>x = Wrong"

definition V_app :: "V \<Rightarrow> V \<Rightarrow> V"  (infixl "\<bullet>" 99) where
  "f\<bullet>x = V_apply\<cdot>f\<cdot>x"

definition T_app :: "V \<Rightarrow> T \<Rightarrow> V"  (infixl "\<bullet>\<bullet>" 99) where
  "f\<bullet>\<bullet>t = f\<bullet>(Vfun\<cdot>(Rep_T t))"

definition V_lam :: "(V \<Rightarrow> V) \<Rightarrow> V" where
"V_lam f = Vfun\<cdot>(Abs_CFun f)"

definition T_lam :: "(T \<Rightarrow> V) \<Rightarrow> V" where
"T_lam f = (Vfun\<cdot>(\<Lambda> (Vfun\<cdot>d). f (Abs_T d)))"

consts coerce :: "V \<Rightarrow> C \<Rightarrow> V"

fixrec match' :: "ID \<rightarrow> (V finlist \<rightarrow> V) 
                    \<rightarrow> (V \<rightarrow> V) 
                    \<rightarrow> V \<rightarrow> V" where
"n2\<noteq>\<bottom> \<and> ls \<noteq> \<bottom> \<Longrightarrow> match'\<cdot>n1\<cdot>f\<cdot>con\<cdot>(Vcon\<cdot>n2\<cdot>ls) = 
   (FLIFT n1'. 
     (FLIFT n2'. (if n1'=n2' then f\<cdot>ls else con\<cdot>(Vcon\<cdot>n2\<cdot>ls)))\<cdot>n2)\<cdot>n1" 

definition match :: "Id \<Rightarrow> (V finlist \<Rightarrow> V)
                        \<Rightarrow> (V \<Rightarrow> V)
                        \<Rightarrow> V \<Rightarrow> V" where
"match = undefined"