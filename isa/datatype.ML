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
    val (tycon_names, ctxt) = ProofContext.add_fixes fixes lthy
    val tycons = map Free (tycon_names ~~ kinds)

    (* Print some stuff for debugging *)
    fun print_tycon t k = writeln
      (Syntax.string_of_term ctxt t ^ " :: " ^ Syntax.string_of_typ ctxt k)
    val _ = map2 print_tycon tycons kinds

    (* Parse constructor types on right-hand sides *)    
    fun prep_rhs targs raw_rhs =
      let
        (* temporarily declare type arguments for parsing *)
        val targs_ctxt =
          fold Variable.declare_constraints (map Free targs) ctxt
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
          HOLogic.mk_list @{typ "string * T"} (map one_constr constrs)
      in
        HOLCF_Library.big_lambdas (map Free targs) body
      end
    val datatypes = map2 mk_datatype targss rhss
 
    (* Print some stuff for debugging *)
    val _ = map (writeln o Syntax.string_of_term ctxt) datatypes

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
