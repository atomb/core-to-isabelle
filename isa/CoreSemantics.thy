theory CoreSemantics
imports HOLCF CoreSyntax
begin

default_sort rep

types ID = "(Id lift)"

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

-- "Model types as deflations"

types Vtype = "V \<rightarrow> V"

types ('a,'b) env = "'a \<rightharpoonup> 'b"

record ty_env =
  tenv :: "(Tvar,Vtype) env"
  tcenv :: REVISIT: How to represent type constructors?

record exp_env =
  tenv :: ty_env
  venv :: "(Var, V) env"
  cenv :: "(Id, V) env"

fixrec (permissive) V_apply :: "V \<rightarrow> V \<rightarrow> V" where
| "V_apply\<cdot>(Vfun\<cdot>f)\<cdot>x = f\<cdot>x"
| "V_apply\<cdot>f\<cdot>x = Wrong"

definition V_app :: "V \<Rightarrow> V \<Rightarrow> V"  (infixl "\<bullet>" 99) where
  "f\<bullet>x = V_apply\<cdot>f\<cdot>x"

definition Vty_app :: "Vtype \<Rightarrow> V \<Rightarrow> V"  (infixl "\<bullet>\<bullet>" 99) where
  "f\<bullet>\<bullet>x = Vfun\<cdot>f\<cdot>x"

fun ty :: "Ty \<Rightarrow> ty_env \<Rightarrow> Vtype" where
  "ty (Tvar v) tenv = the (tenv v)"
| "ty (Tcon

fun exp :: "Exp \<Rightarrow> exp_env \<Rightarrow> V" where
  "exp (Var v) env = (case venv env v of
                              Some x \<Rightarrow> x
                            | None \<Rightarrow> \<bottom>)"
| "exp (Dcon d) env = (case cenv env d of
                         Some x \<Rightarrow> x
                       | None \<Rightarrow> \<bottom>)"
| "exp (App f x) env = (exp f env) \<bullet> (exp x env)"
| "exp (Appt F t) env = (exp F env) \<bullet>\<bullet> (ty t (tenv env))"

