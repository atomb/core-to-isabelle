header {* Simplification procedures *}

theory Halicore_Simprocs
imports Halicore_Defs
begin

definition is_constructor :: "V \<Rightarrow> string \<Rightarrow> V list \<Rightarrow> bool"
  where "is_constructor x s xs \<longleftrightarrow> x = Vcon\<cdot>s\<cdot>xs"

lemma is_constructor_eq:
  "\<lbrakk>is_constructor x s xs; is_constructor y s ys\<rbrakk> \<Longrightarrow> x = y \<equiv> xs = ys"
unfolding is_constructor_def by simp

lemma is_constructor_not_eq:
  "\<lbrakk>is_constructor x s xs; is_constructor y t ys; s \<noteq> t\<rbrakk> \<Longrightarrow> x = y \<equiv> False"
unfolding is_constructor_def by simp

lemma is_constructor_below:
  "\<lbrakk>is_constructor x s xs; is_constructor y s ys\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<equiv> xs \<sqsubseteq> ys"
unfolding is_constructor_def by simp

lemma is_constructor_not_below:
  "\<lbrakk>is_constructor x s xs; is_constructor y t ys; s \<noteq> t\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<equiv> False"
unfolding is_constructor_def by simp

lemma is_constructor_Vcase_eq:
  assumes "is_constructor x s xs"
  shows "Vcase t x (\<lambda>w. Mbranch s (b w) (m w)) \<equiv> B_rep\<cdot>(b x)\<cdot>xs"
using assms unfolding is_constructor_def
by (simp add: Vcase_Mbranch_eq)

lemma is_constructor_Vcase_neq:
  assumes "is_constructor x s xs" and "s \<noteq> s'"
  shows "Vcase t x (\<lambda>w. Mbranch s' (b w) (m w)) \<equiv> Vcase t x (\<lambda>w. m w)"
using assms unfolding is_constructor_def
by (simp add: Vcase_Mbranch_neq)

ML {*
structure Halicore_Simprocs =
struct

fun dest_is_constructor
      (Const (@{const_name is_constructor}, _) $ x $ s $ xs) = (x, s, xs)
  | dest_is_constructor t = raise TERM ("dest_is_constructor", [t])

structure Is_Con_Data = Generic_Data
(
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop
        (single o #1 o dest_is_constructor o HOLogic.dest_Trueprop o concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val get_con_rules =
  Item_Net.content o Is_Con_Data.get o Context.Proof

val add_con_rule =
  Thm.declaration_attribute (Is_Con_Data.map o Item_Net.update)

val del_con_rule =
  Thm.declaration_attribute (Is_Con_Data.map o Item_Net.remove)

fun compare_constructor_proc rule1 rule2 (phi : morphism) ss ct =
  let
    val (_ $ x $ y) = Thm.term_of ct
    val ctxt = Simplifier.the_context ss
    val net = Is_Con_Data.get (Context.Proof ctxt)
    val thmx = hd (Item_Net.retrieve net x)
    val thmy = hd (Item_Net.retrieve net y)
    val s = (#2 o dest_is_constructor o HOLogic.dest_Trueprop o concl_of) thmx
    val t = (#2 o dest_is_constructor o HOLogic.dest_Trueprop o concl_of) thmy
  in
    if s = t
      then SOME (rule1 OF [thmx, thmy])
      else NONE (* TODO: prove that s \<noteq> t and use rule2 *)
  end
  handle Empty => NONE (* due to failed hd function *)

val con_equal_proc = compare_constructor_proc
  @{thm is_constructor_eq} @{thm is_constructor_not_eq}

val con_below_proc = compare_constructor_proc
  @{thm is_constructor_below} @{thm is_constructor_not_below}

fun con_case_proc (phi : morphism) ss ct =
  let
    val rule1 = @{thm is_constructor_Vcase_eq}
    val rule2 = @{thm is_constructor_Vcase_neq}
    val (_ $ _ $ x $ Abs (_, _, _ $ s' $ _ $ _)) = Thm.term_of ct
    val ctxt = Simplifier.the_context ss
    val net = Is_Con_Data.get (Context.Proof ctxt)
    val thmx = hd (Item_Net.retrieve net x)
    val s = (#2 o dest_is_constructor o HOLogic.dest_Trueprop o concl_of) thmx
  in
    if s = s'
      then SOME (rule1 OF [thmx])
      else NONE (* TODO: prove that s \<noteq> s' and use rule2 *)
  end
  handle Empty => NONE (* due to failed hd function *)

val setup =
  Attrib.setup
    (Binding.name "is_constructor")
    (Attrib.add_del add_con_rule del_con_rule)
    "declaration of data constructor (Halicore)"
  #>
  Global_Theory.add_thms_dynamic
    (Binding.name "is_constructor", Item_Net.content o Is_Con_Data.get)

end
*}

setup Halicore_Simprocs.setup

simproc_setup con_equal_proc ("(x::V) = (y::V)") =
  Halicore_Simprocs.con_equal_proc

simproc_setup con_below_proc ("(x::V) \<sqsubseteq> (y::V)") =
  Halicore_Simprocs.con_below_proc

simproc_setup con_case_proc ("Vcase t x (\<lambda>w. Mbranch s (b w) (m w))") =
  Halicore_Simprocs.con_case_proc

end
