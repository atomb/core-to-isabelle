(* datatype.ML *)
(* Implementation of halicore_data command *)

signature HALICORE_DATATYPE =
sig
  type info = unit  (* TODO: replace this with record of theorems *)

  val add_halicore_data :
      ((binding * (string * typ option) list) *
       (binding * term list) list) list
      -> local_theory -> info * local_theory

  val add_halicore_data_cmd :
      ((binding * (string * string option) list) *
       (binding * string list) list) list
      -> local_theory -> info * local_theory
end

structure Halicore_Datatype : HALICORE_DATATYPE =
struct

type info = unit

(*** Building terms and types ***)

val kstar = @{typ T}

fun forall_const k =
  Const (@{const_name forallT}, (k --> kstar) --> kstar)

fun mk_forall (a, t) =
  forall_const (fastype_of a) $ Term.lambda a t

fun T_lam_const k =
  Const (@{const_name T_lam}, (k --> @{typ V}) --> @{typ V})

fun mk_T_lam (a, t) =
  T_lam_const (fastype_of a) $ Term.lambda a t

fun mk_V_lam ((x, t), e) =
  @{const V_lam} $ t $ Term.lambda x e

fun T_apply_const (S, T) =
  Const(@{const_name T_apply}, HOLCF_Library.mk_cfunT (S, T) --> (S --> T))

fun mk_T_apply (t, u) =
  let val (S, T) =
    case fastype_of t of
        Type(@{type_name cfun}, [S, T]) => (S, T)
      | _ => raise TERM ("mk_T_apply", [t, u])
  in T_apply_const (S, T) $ t $ u end

fun dest_big_lambdas (Const (@{const_name Abs_cfun}, _) $ Abs (x, T, t)) =
  let
    val (x', t1) = Term.dest_abs (x, T, t)
    val (vs, t2) = dest_big_lambdas t1
  in
    ((x', T) :: vs, t2)
  end
  | dest_big_lambdas t = ([], t)


(*** Defining Halicore datatypes ***)

fun gen_add_halicore_data
    (prep_typ : local_theory -> 'a -> typ)
    (prep_term : local_theory -> 'b -> term)
    (raw_specs :
      ((binding * (string * 'a option) list) *
       (binding * 'b list) list) list)
    (lthy : local_theory) : info * local_theory =
  let
    val (raw_lhss, raw_rhss) = ListPair.unzip raw_specs
    val (tbinds, raw_targss) = ListPair.unzip raw_lhss

    (* Parse kinds on left-hand sides *)
    fun prep_targ (a, k) =
      (a, the_default @{typ T} (Option.map (prep_typ lthy) k))
    val targss = map (map prep_targ) raw_targss

    (* compute kinds of new type constructors *)
    fun kind_of targs = HOLCF_Library.-->> (map snd targs, @{typ T})
    val kinds = map kind_of targss

    (* declare type constructors in a local context *)
    fun fix_of tbind kind = (tbind, SOME kind, NoSyn)
    val fixes = map2 fix_of tbinds kinds
    val (tycon_names, tycon_ctxt) = ProofContext.add_fixes fixes lthy
    val tycons = map Free (tycon_names ~~ kinds)

    (* Print some stuff for debugging *)
    fun print_tycon t k = writeln (t ^ " :: " ^ Syntax.string_of_typ lthy k)
    val _ = map2 print_tycon tycon_names kinds

    (* Parse constructor types on right-hand sides *)    
    fun prep_rhs targs raw_rhs =
      let
        (* temporarily declare type arguments for parsing *)
        val targs_ctxt =
          fold Variable.declare_constraints (map Free targs) tycon_ctxt
      in
        map (apsnd (map (prep_term targs_ctxt))) raw_rhs
      end
    val rhss : (binding * term list) list list = map2 prep_rhs targss raw_rhss

    (* Define constructor tags *)
    fun define_tag (cbind, ts) =
      let
        val ctag = HOLogic.mk_string (Binding.name_of cbind)
        (* TODO: eventually, we should define constants for these *)
      in
        ((cbind, ctag), ts)
      end
    val rhss' : ((binding * term) * term list) list list =
      map (map define_tag) rhss

    (* Build recursive datatype equations *)
    fun mk_datatype targs constrs =
      let
        fun one_constr ((cbind, ctag), ts) =
          HOLogic.mk_prod (ctag, HOLogic.mk_list @{typ T} ts)
        val body = @{const "datatype"} $
          HOLogic.mk_list @{typ "string * T list"} (map one_constr constrs)
      in
        HOLCF_Library.big_lambdas (map Free targs) body
      end
    val tycon_rhss = map2 mk_datatype targss rhss'

    (* Prove continuity of datatype functional *)
    val functional =
      HOLCF_Library.lambda_tuple tycons (HOLCF_Library.mk_tuple tycon_rhss)
    val cont_thm =
      let
        val prop = HOLogic.mk_Trueprop (HOLCF_Library.mk_cont functional)
        val rules = Cont2ContData.get lthy
        val tac = REPEAT_ALL_NEW (match_tac rules) 1
      in
        Goal.prove lthy [] [] prop (K tac)
      end

    (* Define datatype constants *)
    val fixpoint =
      HOLCF_Library.mk_fix (HOLCF_Library.mk_cabs functional)
    fun one_def tbind rhs =
      ((tbind, NoSyn), ((Binding.suffix_name "_def" tbind, []), rhs))
    fun defs [] _ = []
      | defs (b::[]) t = [one_def b t]
      | defs (b::bs) t =
          one_def b (HOLCF_Library.mk_fst t) ::
            defs bs (HOLCF_Library.mk_snd t)
    val (fixdef_thms : (term * (string * thm)) list, lthy) = lthy
      |> fold_map Local_Theory.define (defs tbinds fixpoint)

    (* Generate datatype unfolding rules *)
    fun pair_equalI (thm1, thm2) = @{thm Pair_equalI} OF [thm1, thm2]
    val tuple_fixdef_thm = foldr1 pair_equalI (map (snd o snd) fixdef_thms)
    val tuple_unfold_thm =
      Local_Defs.unfold lthy @{thms split_conv}
        (@{thm def_cont_fix_eq} OF [tuple_fixdef_thm, cont_thm])
    fun unfolds [] thm = []
      | unfolds (n::[]) thm = [(n, thm)]
      | unfolds (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1}
          val thmR = thm RS @{thm Pair_eqD2}
        in (n, thmL) :: unfolds ns thmR end
    val unfold_thms = unfolds tbinds tuple_unfold_thm
    fun unfold_note (tbind, thm) : Attrib.binding * Thm.thm list =
      ((Binding.suffix_name "_unfold_raw" tbind, []), [thm])
    val (_, lthy) = lthy
      |> fold_map (Local_Theory.note o unfold_note) unfold_thms

    (* Prove applied form of unfold rules *)
    fun prove_applied_unfold thm =
      let
        val concl = concl_of thm
        val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop concl)
        val (vs, rhs') = dest_big_lambdas rhs
        val lhs' = Library.foldl mk_T_apply (lhs, map Free vs)
        val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'))
        val rule = Library.foldl (op RS) (thm, map (K @{thm T_apply_eqI}) vs)
        val rules = Cont2ContData.get lthy
        val tac = rtac rule 1 THEN REPEAT (match_tac rules 1)
      in
        Goal.prove lthy (map fst vs) [] prop (K tac)
      end
    val unfold_thms' = map (apsnd prove_applied_unfold) unfold_thms
    fun unfold_note' (tbind, thm) : Attrib.binding * Thm.thm list =
      ((Binding.suffix_name "_unfold" tbind, []), [thm])
    val (_, lthy) = lthy
      |> fold_map (Local_Theory.note o unfold_note') unfold_thms'

    (* Prove has_constructor theorems *)
    fun prove_has_constrs ((tycon, targs), rhs) (tbind, unfold_thm) =
      let
        val lhs = Library.foldl mk_T_apply (tycon, map Free targs)
        val xs = map fst targs
        fun prove_has_constr ((cbind, ctag), ts) =
          let
            val list = HOLogic.mk_list @{typ T} ts
            val goal = @{const has_constructor} $ lhs $ ctag $ list
            val prop = HOLogic.mk_Trueprop goal
            val rules = @{thms has_constructor_simps}
            val tac1 = rtac @{thm has_constructor_intro} 1
            val tac2 = rtac unfold_thm 1
            val tac3 = simp_tac (HOL_ss addsimps rules) 1
            val tac = tac1 THEN tac2 THEN tac3
          in
            Goal.prove lthy xs [] prop (K tac)
          end
        val thms = map prove_has_constr rhs
        val thm_bind = Binding.suffix_name "_has_constructor" tbind
        val attrib = Attrib.internal (K Halicore_Typecheck.add_con_rule)
      in
        ((thm_bind, [attrib]), thms)
      end
    val has_constr_thms =
      map2 prove_has_constrs (tycons ~~ targss ~~ rhss') unfold_thms'
    val (_, lthy) = lthy
      |> fold_map Local_Theory.note has_constr_thms

    (* Define data constructor constants *)
    fun define_constrs ((tycon, targs), rhs) lthy =
      let
        val used = map fst targs
        fun one_def bind rhs =
          ((bind, NoSyn), ((Binding.suffix_name "_def" bind, []), rhs))
        fun define_constr ((cbind, ctag), ts) lthy =
          let
            val x_names = Name.variant_list used (map (K "x") ts)
            val xs = map (fn x => Free (x, @{typ V})) x_names
            val e1 = HOLCF_Library.mk_capply (@{const Vcon}, ctag)
            val e2 = HOLCF_Library.mk_capply (e1, HOLogic.mk_list @{typ V} xs)
            val e3 = Library.foldr mk_V_lam (xs ~~ ts, e2)
            val e4 = Library.foldr mk_T_lam (map Free targs, e3)
            val ((con, (s, def_thm)), lthy) = lthy
              |> Local_Theory.define (one_def cbind e4)
            (* TODO: prove typing rule *)
          in
            (* eventually we'll have to return some other stuff too *)
            ((), lthy)
          end
      in
        fold_map define_constr rhs lthy
      end
    val (_, lthy) = lthy
      |> fold_map define_constrs ((tycons ~~ targss) ~~ rhss')

    val info = ()
  in
    (info, lthy)
  end

fun halicore_read_term ctxt str =
  Syntax.read_term ctxt ("\<langle>" ^ str ^ "\<rangle>")

val add_halicore_data_cmd =
  gen_add_halicore_data Syntax.read_typ halicore_read_term

val add_halicore_data =
  gen_add_halicore_data Syntax.check_typ Syntax.check_term

(*** Outer syntax parsers ***)

val parse_tbind : (string * string option) parser =
  (Parse.short_ident >> rpair NONE) ||
  (Parse.$$$ "(" |-- Parse.short_ident --| Parse.$$$ "::" --
    (Parse.typ >> SOME) --| Parse.$$$ ")")

val parse_htype : string parser =
  Parse.group "Halicore type" Parse.term_group

val parse_halicore_data_decl :
    ((binding * (string * string option) list) *
     (binding * string list) list) list parser =
  Parse.and_list
    (Parse.binding -- Scan.repeat parse_tbind --
      (Parse.$$$ "=" |-- Parse.enum1 "|"
        (Parse.binding -- Scan.repeat parse_htype)))

val _ =
  Outer_Syntax.local_theory
    "halicore_data"
    "define datatypes (Halicore)"
    Keyword.thy_decl
    (parse_halicore_data_decl >> (snd oo add_halicore_data_cmd))

end
