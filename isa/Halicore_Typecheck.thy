header {* Typechecking tactic and solver for Halicore terms *}

theory Halicore_Typecheck
imports Halicore_Defs
uses ("typecheck.ML")
begin

subsection {* Building theorems for type judgments *}

lemmas type_cont_rules =
  cont_id cont_const cont2cont_fst cont2cont_snd
  cont_T_apply cont_forallT

lemmas term_cont_rules =
  type_cont_rules
  cont_V_app cont_V_lam
  cont_T_app cont_T_lam
  cont_cases cont_match cont_allmatch
  cont_branch0 cont_branchV

use "typecheck.ML"

setup Halicore_Typecheck.setup

text {* We declare a new Isar method called @{text typecheck}. *}

method_setup typecheck = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (Halicore_Typecheck.typecheck_tac ctxt []))
*} "typecheck terms (Halicore)"


text {* Next we configure @{text typecheck} as a solver for the simplifier. *}

setup {*
  let
    val solver = mk_solver' "typecheck"
      (fn ss =>
        Halicore_Typecheck.typecheck_tac
          (Simplifier.the_context ss)
          (Simplifier.prems_of_ss ss))
  in
    Simplifier.map_simpset (fn ss => ss addSolver solver)
  end
*}

end
