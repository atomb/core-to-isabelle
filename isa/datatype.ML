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

    fun prep_targ (a, k) =
      (a, the_default @{typ T} (Option.map (prep_typ lthy) k))
    fun prep_lhs (tbind, targs) =
      let
        val targs' = map prep_targ targs
        val kind = HOLCF_Library.-->> (map snd targs', @{typ T})
        val _ = writeln (Binding.str_of tbind ^ " :: " ^ Syntax.string_of_typ lthy kind)
      in
        (tbind, kind, targs')
      end
    val lhss = map prep_lhs raw_lhss

    fun prep_constr (cbind, ts) = (cbind, map (prep_term lthy) ts)
    fun prep_spec ((tbind, targs), constrs) =
      ((tbind, map prep_targ targs), map prep_constr constrs)

    val specs = map prep_spec raw_specs
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
