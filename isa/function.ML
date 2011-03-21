(* function.ML *)
(* Implementation of halicore_fun command *)

signature HALICORE_FUNCTION =
sig
  type info = unit  (* TODO: replace this with record of theorems *)

  val add_halicore_fun :
      ((binding * term) * term) list
      -> local_theory -> info * local_theory

  val add_halicore_fun_cmd :
      ((binding * string) * string) list
      -> local_theory -> info * local_theory
end

structure Halicore_Function : HALICORE_FUNCTION =
struct

type info = unit

fun gen_add_halicore_fun
    (prep_htype : local_theory -> 'a -> term)
    (prep_hterm : local_theory -> 'b -> term)
    (raw_specs : ((binding * 'a) * 'b) list)
    (lthy : local_theory) : info * local_theory =
  let
    val ((binds, raw_htypes), raw_hterms) =
      apfst ListPair.unzip (ListPair.unzip raw_specs)

    (* parse types on lhs *)
    val htypes = map (prep_htype lthy) raw_htypes

    (* declare type constructors in a local context *)
    val fixes = map (fn bind => (bind, SOME @{typ V}, NoSyn)) binds
    val (const_names, const_ctxt) = ProofContext.add_fixes fixes lthy
    val consts = map (fn n => Free (n, @{typ V})) const_names

    (* Parse right-hand sides *)
    val hterms = map (prep_hterm const_ctxt) raw_hterms

    (* Print some stuff for debugging *)
    fun print_const x e = writeln (x ^ " :: " ^ Syntax.string_of_term lthy e)
    val _ = map2 print_const const_names htypes

    (* Prove continuity of functional *)
    val functional =
      HOLCF_Library.lambda_tuple consts (HOLCF_Library.mk_tuple hterms)
    val cont_thm =
      let
        val prop = HOLogic.mk_Trueprop (HOLCF_Library.mk_cont functional)
        val rules = Cont2ContData.get lthy
        val tac = REPEAT_ALL_NEW (match_tac rules) 1
      in
        Goal.prove lthy [] [] prop (K tac)
      end

    (* Define function constants *)
    val fixpoint =
      HOLCF_Library.mk_fix (HOLCF_Library.mk_cabs functional)
    fun one_def bind rhs =
      ((bind, NoSyn), ((Binding.suffix_name "_def" bind, []), rhs))
    fun defs [] _ = []
      | defs (b::[]) t = [one_def b t]
      | defs (b::bs) t =
          one_def b (HOLCF_Library.mk_fst t) ::
            defs bs (HOLCF_Library.mk_snd t)
    val (fixdef_thms : (term * (string * thm)) list, lthy) = lthy
      |> fold_map Local_Theory.define (defs binds fixpoint)

    (* Generate function unfolding rules *)
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
    val unfold_thms = unfolds binds tuple_unfold_thm
    fun unfold_note (bind, thm) : Attrib.binding * Thm.thm list =
      ((Binding.suffix_name "_unfold" bind, []), [thm])
    val (thmss, lthy) = lthy
      |> fold_map (Local_Theory.note o unfold_note) unfold_thms

    val info = ()
  in
    (info, lthy)
  end

fun read_halicore_type ctxt str =
  Syntax.read_term ctxt ("\<langle>" ^ str ^ "\<rangle>")

fun read_halicore_term ctxt str =
  Syntax.read_term ctxt ("\<guillemotleft>" ^ str ^ "\<guillemotright>")

val add_halicore_fun_cmd =
  gen_add_halicore_fun read_halicore_type read_halicore_term

val add_halicore_fun =
  gen_add_halicore_fun Syntax.check_term Syntax.check_term

(*** Outer syntax parsers ***)

val parse_htype : string parser =
  Parse.group "Halicore type" Parse.term_group

val parse_hterm : string parser =
  Parse.group "Halicore term" Parse.term_group

val parse_halicore_fun_decl : ((binding * string) * string) list parser =
  Parse.and_list
    (Parse.binding --| Parse.$$$ "::" -- parse_htype --
      (Parse.$$$ "=" |-- parse_hterm))

val _ =
  Outer_Syntax.local_theory
    "halicore_fun"
    "define functions (Halicore)"
    Keyword.thy_decl
    (parse_halicore_fun_decl >> (snd oo add_halicore_fun_cmd))

end
