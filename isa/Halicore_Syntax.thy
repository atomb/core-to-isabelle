header {* Parsing and pretty-printing for Halicore terms and types *}

theory Halicore_Syntax
imports Halicore_Defs
begin

subsection {* ``Halicore brackets'' *}

nonterminal hval
nonterminal htyp

syntax
  "_hquote"   :: "hval => logic"  ("\<guillemotleft>_\<guillemotright>")
  "_htquote"  :: "htyp => logic"  ("\<langle>_\<rangle>")
  "_hunquote" :: "logic => hval"  ("\<lbrace>_\<rbrace>")
  "_hunquote" :: "logic => htyp"  ("\<lbrace>_\<rbrace>")

translations
  "_hquote x" => "x"
  "_hunquote x" => "x"
  "x" <= "_hunquote (_hquote x)"
  "_htquote x" => "x"
  "x" <= "_hunquote (_htquote x)"

text {* The following print translation removes any pair of antiquote
brackets that encloses just a single constant or variable. *}

print_ast_translation {*
  let
    fun ast_tr [x as Appl [Constant @{syntax_const "_free"}, _]] = x
      | ast_tr [x as Appl [Constant @{syntax_const "_bound"}, _]] = x
      | ast_tr [x as Appl [Constant @{syntax_const "_var"}, _]] = x
      | ast_tr [Appl [Constant @{syntax_const "_constrain"},
          x as Appl [Constant @{syntax_const "_free"}, _], _]] = x
      | ast_tr [x as Constant _] = x
      | ast_tr xs = raise Match
      | ast_tr xs = raise Syntax.AST ("_hunquote", xs)
  in
    [(@{syntax_const "_hunquote"}, ast_tr)]
  end
*}

subsection {* Value application *}

syntax
  ""       :: "id => hval"              ("_")
  ""       :: "longid => hval"          ("_")
  ""       :: "hval => hval"            ("'(_')")
  "_happ"  :: "hval => hval => hval"    ("(1_/ _)" [999, 1000] 999)

translations
  "_happ f x" => "CONST V_app f x"
  "_hquote (_happ (_hunquote f) (_hunquote x))" <= "CONST V_app f x"

subsection {* Application of values to types *}

syntax
  "_hvtapp" :: "hval => htyp => hval"  ("(1_/ @_)" [999, 1000] 999)

translations
  "_hvtapp x t" => "CONST T_app x t"
  "_hquote (_hvtapp (_hunquote x) (_hunquote t))" <= "CONST T_app x t"

subsection {* Type application *}

syntax
  ""       :: "id => htyp"              ("_")
  ""       :: "longid => htyp"          ("_")
  ""       :: "htyp => htyp"            ("'(_')")
  "_htapp"  :: "htyp => htyp => htyp"    ("(1_/ _)" [999, 1000] 999)

translations
  "_htapp t u" => "CONST T_apply t u"
  "_htquote (_htapp (_hunquote t) (_hunquote u))" <= "CONST T_apply t u"

subsection {* Function arrow syntax *}

syntax
  "_htfun" :: "htyp => htyp => htyp"    (infixr "\<rightarrow>" 10)

translations
  "_htfun a b" == "_htapp (_htapp (CONST funT) a) b"
  "CONST funT" <= "_hunquote (CONST funT)"

subsection {* Kind syntax *}

nonterminal hkind

setup {*
  Sign.add_modesyntax Syntax.mode_input
    [(@{type_syntax T}, "hkind", Delimfix "\<star>"),
     (@{type_syntax T}, "hkind", Delimfix "*"),
     (@{type_syntax cfun}, "hkind => hkind => hkind", Mixfix ("_ \<rightarrow>/ _", [5, 4], 4)),
     ("", "hkind => hkind", Delimfix "'(_')")]
*}

subsection {* Lambda abstractions *}

nonterminal harg
nonterminal hargs
nonterminal hidt

syntax
  "_habs"  :: "harg => hval => hval"
  "_hlam"  :: "hargs => hval => hval"   ("(3\<lambda>_./ _)" [0, 3] 3)
  "_harg"  :: "harg => hargs"           ("_")
  "_hargs" :: "harg => hargs => hargs"  ("_/ _" [1, 0] 0)
  "_hvarg" :: "id => htyp => harg"      ("'(_::_')")
  "_htarg" :: "hidt => harg"            ("@_")
  ""       :: "id => hidt"              ("_")
  "_hidt"  :: "id => hkind => hidt"     ("'(_::_')")

translations
  "_hlam (_hargs p ps) r" == "_hlam (_harg p) (_hlam ps r)"
  "_hlam (_harg p) r" == "_habs p r"
  "_habs (_hvarg x t) r" => "CONST V_lam t (_abs x r)"
  "_habs (_htarg (_hidt a k)) r" => "CONST T_lam (_abs (_constrain a k) r)"
  "_habs (_htarg a) r" => "CONST T_lam (_abs (a::T) r)"
  "_hquote (_habs (_hvarg x (_hunquote t)) (_hunquote r))" <= "CONST V_lam t (_abs x r)"

text {* This print translation for type-lambdas puts a kind annotation
on the type variable unless it is of kind star (@{text \<star>}). *}

print_translation {*
  [(@{const_syntax T_lam}, fn [Abs (abs as (_, T, _))] =>
    let
      val (x, t) = atomic_abs_tr' abs
      val hidt = Syntax.const @{syntax_const "_hidt"}
      val habs = Syntax.const @{syntax_const "_habs"}
      val htarg = Syntax.const @{syntax_const "_htarg"}
      val hquote = Syntax.const @{syntax_const "_hquote"}
      val hunquote = Syntax.const @{syntax_const "_hunquote"}
      val x' =
        if T = @{typ T} then x else hidt $ x $ Syntax.term_of_typ false T
    in
      hquote $ (habs $ (htarg $ x') $ (hunquote $ t))
    end)]
*}

subsection {* Forall types *}

nonterminal hidts

syntax
  "_hidts"   :: "hidt => hidts => hidts" ("_/ _" [1, 0] 0)
  "_hidt1"   :: "hidt => hidts"          ("_")
  "_hforall" :: "hidts => htyp => htyp"  ("(forall _./ _)" [0, 3] 3)
  "_hall"    :: "hidt => htyp => htyp"

translations
  "_hforall (_hidts t ts) r" == "_hforall (_hidt1 t) (_hforall ts r)"
  "_hforall (_hidt1 t) r" == "_hall t r"
  "_hall (_hidt a k) r" => "CONST forallT (_abs (_constrain a k) r)"
  "_hall a r" => "CONST forallT (_abs (a::T) r)"

text {* This print translation for forall-types puts a kind annotation
on the type variable unless it is of kind star (@{text \<star>}). *}

print_translation {*
  [(@{const_syntax forallT}, fn [Abs (abs as (_, T, _))] =>
    let
      val (x, t) = atomic_abs_tr' abs
      val hidt = Syntax.const @{syntax_const "_hidt"}
      val hall = Syntax.const @{syntax_const "_hall"}
      val htquote = Syntax.const @{syntax_const "_htquote"}
      val hunquote = Syntax.const @{syntax_const "_hunquote"}
      val x' =
        if T = @{typ T} then x else hidt $ x $ Syntax.term_of_typ false T
    in
      htquote $ (hall $ x' $ (hunquote $ t))
    end)]
*}

(* TODO: The two print translations above have a lot of duplication.
It would be better to factor out the common parts. *)

subsection {* Case expressions *}

nonterminal hmatch
nonterminal hpat

syntax
  "_hmquote"  :: "hmatch => logic"  ("\<langle>\<langle>_\<rangle>\<rangle>")
  "_hmunquote" :: "logic => hmatch"  ("\<lbrace>_\<rbrace>")
  "_hcase"     :: "htyp => hval => id => hmatch => hval"
      ("case '(_')/ _/ of _/ {(_)}")
  "_hwild"     :: "hval => hmatch" ("('_ \<rightarrow>/ _)")
  "_hmatch"    :: "hpat => hval => hmatch => hmatch" ("(_ \<rightarrow>/ _);/ _")
  "_hmatch1"   :: "hpat => hval => hmatch" ("(_ \<rightarrow>/ _)")
  "_hpat"      :: "hpat => harg => hpat" ("_/ _")
  "_hcon"      :: "longid => hpat" ("_")
  "_hcon"      :: "id => hpat" ("_")
  "_hbranch"   :: "hpat => any => hmatch"
  "_htag"      :: "any => hpat"

translations
  "_hmquote x" => "x"
  "_hmunquote x" => "x"
  "x" <= "_hmunquote (_hmquote x)"
  "_hcase t v w m" => "CONST cases t v (_abs w m)"
  "_hquote (_hcase (_hunquote t) (_hunquote v) w (_hmunquote m))" <= "CONST cases t v (_abs w m)"
  "_hmatch1 p r" == "_hmatch p r (CONST endmatch')"
  "CONST endmatch'" <= "_hmunquote (CONST endmatch')"
  "_hmatch p r m" => "_hbranch p (CONST branch0 r) m"
  "_hmatch p (_hunquote r) m" <= "_hbranch p (CONST branch0 r) m"
  "_hbranch (_hpat p (_hvarg x t)) b m"
      == "_hbranch p (CONST branchV t (_abs x b)) m"
  "_hbranch s b m" => "CONST match s b m"
  "_hmquote (_hbranch (_htag s) b (_hmunquote m))" <= "CONST match s b m"
  "_hwild r" => "CONST allmatch r"
  "_hmquote (_hwild (_hunquote r))" <= "CONST allmatch r"

subsection {* Examples *}

term "\<langle>forall a. a \<rightarrow> a\<rangle>"
term "\<langle>forall a b c. a \<rightarrow> b \<rightarrow> c \<rightarrow> a\<rangle>"
term "\<guillemotleft>f x (g y)\<guillemotright>"
term "\<guillemotleft>\<lambda>(x::a). f x\<guillemotright>"
term "\<guillemotleft>\<lambda>(x::a) (y::b). f x y\<guillemotright>"
term "\<guillemotleft>\<lambda> (x::m (m a b c d \<rightarrow> b) b c d) (y::b \<rightarrow> c). f (g x y)\<guillemotright>"
term "\<guillemotleft>\<lambda> (f::forall a. a \<rightarrow> a). f @b\<guillemotright>"
term "\<guillemotleft>\<lambda> (x::a). f @a @b x\<guillemotright>"
term "\<guillemotleft>\<lambda> @a (x::a). x\<guillemotright>"
term "\<guillemotleft>\<lambda> @(m::\<star> \<rightarrow> \<star> \<rightarrow> \<star>). x\<guillemotright>"
term "\<guillemotleft>\<lambda> @(m::(\<star> \<rightarrow> \<star>) \<rightarrow> \<star> \<rightarrow> \<star>) @(a::\<star>). f@(m b a) x\<guillemotright>"
term "\<guillemotleft>\<lambda> @a (x::a). f @a x\<guillemotright>"
term "\<guillemotleft>case (t) v of w {_ \<rightarrow> g}\<guillemotright>"

end
