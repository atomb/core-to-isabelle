(* typecheck.ML *)
(* Type checking tactic and simproc for Halicore terms *)

signature HALICORE_TYPECHECK =
sig
  val get_type_rules : Proof.context -> thm list
  val add_type_rule : attribute
  val del_type_rule : attribute

  val get_con_rules : Proof.context -> thm list
  val add_con_rule : attribute
  val del_con_rule : attribute

  val dest_Abs : term -> term * term

  val typecheck_thm : Proof.context -> thm list -> term -> thm
  val typecheck_tac : Proof.context -> thm list -> int -> tactic

  val setup : theory -> theory
end

structure Halicore_Typecheck : HALICORE_TYPECHECK =
struct

fun dest_has_type (Const (@{const_name has_type}, _) $ x $ t) = (x, t)
  | dest_has_type t = raise TERM ("dest_has_type", [t])

fun dest_has_constructor
      (Const (@{const_name has_constructor}, _) $ t $ s $ ts) = (t, s, ts)
  | dest_has_constructor t = raise TERM ("dest_has_constructor", [t])

structure Type_Rule_Data = Generic_Data
(
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop
        (single o fst o dest_has_type o HOLogic.dest_Trueprop o concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val get_type_rules =
  Item_Net.content o Type_Rule_Data.get o Context.Proof

val add_type_rule =
  Thm.declaration_attribute (Type_Rule_Data.map o Item_Net.update)

val del_type_rule =
  Thm.declaration_attribute (Type_Rule_Data.map o Item_Net.remove)

structure Con_Rule_Data = Generic_Data
(
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop
        (single o #2 o dest_has_constructor o HOLogic.dest_Trueprop o concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val get_con_rules =
  Item_Net.content o Con_Rule_Data.get o Context.Proof

val add_con_rule =
  Thm.declaration_attribute (Con_Rule_Data.map o Item_Net.update)

val del_con_rule =
  Thm.declaration_attribute (Con_Rule_Data.map o Item_Net.remove)

(* Transforms theorem "cont f ==> P" into "P" *)
fun solve_cont_prem thm =
  let
    val rules = @{thms term_cont_rules}
    val tac = SOLVED' (REPEAT_ALL_NEW (resolve_tac rules)) 1
  in
    the (SINGLE tac thm)
    (* TODO: better error message than "exception Option" if this fails *)
  end

fun dest_Abs (Abs (x, T, t)) =
      let
        val (y', t') = Term.dest_abs (x, T, t)
      in
        (Free (y', T), t')
      end
  | dest_Abs t =
      let
        val T = Term.domain_type (Term.fastype_of t)
        val x = Free (Name.variant (Term.add_free_names t []) "x", T)
      in
        (x, t $ x)
      end

fun typecheck_thm ctxt rules : term -> thm =
  let
    val con_rules = Con_Rule_Data.get (Context.Proof ctxt)
    val net0 = Type_Rule_Data.get (Context.Proof ctxt)
    val net1 = fold Item_Net.update rules net0
    val thy = ProofContext.theory_of ctxt
    val cert = Thm.cterm_of thy
    val certT = Thm.ctyp_of thy
    (* builds theorem for value of type V *)
    fun check net e =
      case e of
        Const (@{const_name V_app}, _) $ e1 $ e2 =>
          let
            val thm1 = check net e1
            val thm2 = check net e2
          in
            @{thm has_type_V_app} OF [thm1, thm2]
          end
      | Const (@{const_name T_app}, _) $ e $ t =>
          let
            val tinsts = [SOME (certT (fastype_of t))]
            val insts = [NONE, NONE, SOME (cert t)]
            val rule = Drule.instantiate' tinsts insts @{thm has_type_T_app}
            val thm1 = check net e
            val thm2 = rule OF [thm1]
          in
            solve_cont_prem thm2
          end
      | Const (@{const_name V_lam}, _) $ t $ f =>
          let
            val (x, e) = dest_Abs f
            val cprop = cert (HOLogic.mk_Trueprop (@{const has_type} $ x $ t))
            val net' = Item_Net.update (Thm.assume cprop) net
            val thm1 = check net' e
            val thm2 = Thm.implies_intr cprop thm1
            val thm3 = Thm.forall_intr (cert x) thm2
            val thm4 = Drule.compose_single (thm3, 2, @{thm has_type_V_lam})
          in
            solve_cont_prem thm4
          end
      | Const (@{const_name T_lam}, _) $ f =>
          let
            val (a, e) = dest_Abs f
            val thm0 = check net e
            val thm1 = Thm.forall_intr (cert a) thm0
            val thm2 = Drule.compose_single (thm1, 3, @{thm has_type_T_lam})
          in
            solve_cont_prem (solve_cont_prem thm2)
          end
      | Const (@{const_name cases}, _) $ u $ e $ f =>
          let
            val (w, m) = dest_Abs f
            val thm0 = check net e
            val (_, t) = dest_has_type (HOLogic.dest_Trueprop (concl_of thm0))
            val cprop = cert (HOLogic.mk_Trueprop (@{const has_type} $ w $ t))
            val net' = Item_Net.update (Thm.assume cprop) net
            val thm1 = check_m net' m (cert t) (cert u)
            val thm2 = Thm.implies_intr cprop thm1
            val thm3 = Thm.forall_intr (cert w) thm2
            val thm4 = thm0 RS @{thm has_type_cases}
            val thm5 = Drule.compose_single (thm3, 1, thm4)
          in thm5 end
      | e => hd (Item_Net.retrieve net e)
        (* TODO: better error message than exception Empty if this fails *)
    (* builds theorem for value of type M *)
    and check_m net m t u =
      case m of
        Const (@{const_name endmatch'}, _) =>
          Drule.instantiate' [] [SOME t, SOME u] @{thm M_type_endmatch}
      | Const (@{const_name allmatch}, _) $ e =>
          let
            val thm0 = check net e
            val insts = [NONE, SOME u, SOME t]
            val thm1 = Drule.instantiate' [] insts @{thm M_type_allmatch}
          in
            thm0 RS thm1
          end
      | Const (@{const_name match}, _) $ s $ b $ m =>
          let
            val insts = [SOME t, NONE, NONE, NONE, SOME u]
            val rule = Drule.instantiate' [] insts @{thm M_type_match}
            val thm1 = hd (Item_Net.retrieve con_rules s)
            (* TODO: better error message if this fails *)
            val thm2 = check_b net b
            val thm3 = check_m net m t u
          in
            rule OF [thm1, thm2, thm3]
          end
      | m => raise TERM ("check_m", [m])
    (* builds theorem for value of type B *)
    and check_b net b =
      case b of
        Const (@{const_name branch0}, _) $ e =>
          (check net e) RS @{thm B_type_branch0}
      | Const (@{const_name branchV}, _) $ t $ f =>
          let
            val (x, b) = dest_Abs f
            val cprop = cert (HOLogic.mk_Trueprop (@{const has_type} $ x $ t))
            val net' = Item_Net.update (Thm.assume cprop) net
            val thm1 = check_b net' b
            val thm2 = Thm.implies_intr cprop thm1
            val thm3 = Thm.forall_intr (cert x) thm2
            val thm4 = Drule.compose_single (thm3, 2, @{thm B_type_branchV})
          in
            solve_cont_prem thm4
          end
      | b => raise TERM ("check_b", [b])
  in
    check net1
  end

fun dest_alls prop =
  if Logic.is_all prop then
    let
      val ((x, T), prop1) = Logic.dest_all prop
      val (xs, prop2) = dest_alls prop1
    in
      (Free (x, T) :: xs, prop2)
    end
  else ([], prop)

fun typecheck_tac ctxt prems =
  let
    val thy = ProofContext.theory_of ctxt
    val cert = Thm.cterm_of thy
    val dest_has_type_prop = dest_has_type o HOLogic.dest_Trueprop
    val rules = filter (can (dest_has_type_prop o concl_of)) prems
    fun thm_of prop =
      let
        val (vars, prop') = dest_alls prop
        val (assms, concl) = Logic.strip_horn prop'
        val assms' = filter (can dest_has_type_prop) assms
        val rules' = map (Thm.assume o cert) assms'
        val (x, _) = dest_has_type_prop concl
        val thm0 = typecheck_thm ctxt (rules @ rules') x
        val thm1 = fold Thm.implies_intr (map cert assms') thm0
        val thm2 = Drule.forall_intr_list (map cert vars) thm1
        val thm3 = Drule.gen_all thm2
      in thm3 end
  in
    SUBGOAL (fn (prop, i) =>
      solve_tac (the_list (try thm_of prop)) i)
  end

val setup =
  Attrib.setup
    (Binding.name "type_rule")
    (Attrib.add_del add_type_rule del_type_rule)
    "declaration of type rule (Halicore)"
  #>
  Global_Theory.add_thms_dynamic
    (Binding.name "type_rule", Item_Net.content o Type_Rule_Data.get)
  #>
  Attrib.setup
    (Binding.name "constructor_rule")
    (Attrib.add_del add_con_rule del_con_rule)
    "declaration of data constructor (Halicore)"
  #>
  Global_Theory.add_thms_dynamic
    (Binding.name "constructor_rule", Item_Net.content o Con_Rule_Data.get)

end
