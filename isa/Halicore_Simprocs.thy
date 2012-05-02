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

lemma is_constructor_Vcase_Mwild:
  assumes "is_constructor x s xs" and "cont f"
  shows "Vcase t x (\<lambda>w. Mwild (f w)) \<equiv> f x"
using assms unfolding is_constructor_def
by (simp add: Vcase_Mwild)

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

structure Tag_Def_Data = Generic_Data
(
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop
        (single o fst o Logic.dest_equals o concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val get_con_rules =
  Item_Net.content o Is_Con_Data.get o Context.Proof

val add_con_rule =
  Thm.declaration_attribute (Is_Con_Data.map o Item_Net.update)

val del_con_rule =
  Thm.declaration_attribute (Is_Con_Data.map o Item_Net.remove)

val add_tag_def =
  Thm.declaration_attribute (Tag_Def_Data.map o Item_Net.update)

val del_tag_def =
  Thm.declaration_attribute (Tag_Def_Data.map o Item_Net.remove)

fun prove_neq ctxt s t =
  let
    val net = Tag_Def_Data.get (Context.Proof ctxt)
    val s_def = hd (Item_Net.retrieve net s)
    val t_def = hd (Item_Net.retrieve net t)
    val goal = HOLogic.mk_not (HOLogic.mk_eq (s, t))
    val prop = HOLogic.mk_Trueprop goal
    val rules = @{thms list.inject list.distinct char.inject nibble.distinct}
    val tac1 = rewrite_goal_tac [s_def, t_def] 1
    val tac2 = simp_tac (HOL_ss addsimps rules) 1
  in
    Goal.prove ctxt [] [] prop (K (tac1 THEN tac2))
  end

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
      else SOME (rule2 OF [thmx, thmy, prove_neq ctxt s t])
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
    val (_ $ _ $ x $ Abs (_, _, _ $ t $ _ $ _)) = Thm.term_of ct
    val ctxt = Simplifier.the_context ss
    val net = Is_Con_Data.get (Context.Proof ctxt)
    val thmx = hd (Item_Net.retrieve net x)
    val s = (#2 o dest_is_constructor o HOLogic.dest_Trueprop o concl_of) thmx
  in
    if s = t
      then SOME (rule1 OF [thmx])
      else SOME (rule2 OF [thmx, prove_neq ctxt s t])
  end
  handle Empty => NONE (* due to failed hd function *)

fun con_wild_proc (phi : morphism) ss ct =
  let
    val rule1 = @{thm is_constructor_Vcase_Mwild}
    val (_ $ _ $ x $ _) = Thm.term_of ct
    val ctxt = Simplifier.the_context ss
    val net = Is_Con_Data.get (Context.Proof ctxt)
    val thmx = hd (Item_Net.retrieve net x)
  in
    SOME (rule1 OF [thmx])
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
  #>
  Attrib.setup
    (Binding.name "tag_def")
    (Attrib.add_del add_tag_def del_tag_def)
    "declaration of constructor tag definition (Halicore)"

end
*}

setup Halicore_Simprocs.setup

simproc_setup con_equal_proc ("(x::V) = (y::V)") =
  Halicore_Simprocs.con_equal_proc

simproc_setup con_below_proc ("(x::V) \<sqsubseteq> (y::V)") =
  Halicore_Simprocs.con_below_proc

simproc_setup con_case_proc ("Vcase t x (\<lambda>w. Mbranch s (b w) (m w))") =
  Halicore_Simprocs.con_case_proc

simproc_setup con_wild_proc ("Vcase t x (\<lambda>w. Mwild (v w))") =
  Halicore_Simprocs.con_wild_proc

end
