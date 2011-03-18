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

    (* Build recursive datatype equations *)
    fun mk_datatype targs constrs =
      let
        fun one_constr (cbind, ts) =
          let
            val ctag = HOLogic.mk_string (Binding.name_of cbind)
          in
            HOLogic.mk_prod (ctag, HOLogic.mk_list @{typ T} ts)
          end
        val body = @{const "datatype"} $
          HOLogic.mk_list @{typ "string * T list"} (map one_constr constrs)
      in
        HOLCF_Library.big_lambdas (map Free targs) body
      end
    val tycon_rhss = map2 mk_datatype targss rhss

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
    val (thmss, lthy) = lthy
      |> fold_map (Local_Theory.note o unfold_note) unfold_thms

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
