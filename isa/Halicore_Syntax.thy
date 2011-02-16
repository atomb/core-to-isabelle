theory Halicore_Syntax
imports Halicore_Defs
begin

nonterminal hval
nonterminal hvals
nonterminal hpat
nonterminal hpats
nonterminal htyp
nonterminal hidt
nonterminal hkind

text "``Halicore brackets''"

syntax
  "_hquote"   :: "hval => logic"  ("\<guillemotleft>_\<guillemotright>")
  "_hunquote" :: "logic => hval"  ("\<lbrace>_\<rbrace>")
  "_htquote"  :: "htyp => logic"  ("\<langle>_\<rangle>")
  "_hunquote" :: "logic => htyp"  ("\<lbrace>_\<rbrace>")
translations
  "_hquote x" => "x"
  "_hunquote x" => "x"
  "x" <= "_hunquote (_hquote x)"
  "_htquote x" => "x"
(*  "_htunquote x" => "x" *)
  "x" <= "_hunquote (_htquote x)"

ML_val Syntax.string_of_term
ML_val ML_Syntax.print_term
ML_val Syntax.str_of_ast

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

text "Value application"

syntax
  ""       :: "id => hval"              ("_")
  ""       :: "longid => hval"          ("_")
  ""       :: "hval => hval"            ("'(_')")
  "_happ"  :: "hval => hval => hval"    ("(1_/ _)" [999, 1000] 999)
translations
  "_happ f x" => "CONST V_app f x"
  "_hquote (_happ (_hunquote f) (_hunquote x))" <= "CONST V_app f x"

text "Type application"

syntax
  ""       :: "id => htyp"              ("_")
  ""       :: "longid => htyp"          ("_")
  ""       :: "htyp => htyp"            ("'(_')")
  "_htapp"  :: "htyp => htyp => htyp"    ("(1_/ _)" [999, 1000] 999)
translations
  "_htapp t u" => "CONST T_apply t u"
  "_htquote (_htapp (_hunquote t) (_hunquote u))" <= "CONST T_apply t u"

text "Function arrow syntax"

syntax
  "_htfun" :: "htyp => htyp => htyp"    (infixr "\<rightarrow>" 10)
translations
  "_htfun a b" == "_htapp (_htapp (CONST funT) a) b"
  "CONST funT" <= "_hunquote (CONST funT)"

text "Kind syntax"

setup {*
  Sign.add_modesyntax Syntax.mode_input
    [(@{type_syntax T}, "hkind", Delimfix "\<star>"),
     (@{type_syntax T}, "hkind", Delimfix "*"),
     (@{type_syntax cfun}, "hkind => hkind => hkind", Mixfix ("_ \<rightarrow>/ _", [5, 4], 4)),
     ("", "hkind => hkind", Delimfix "'(_')")]
*}

text "Lambda abstractions"

syntax
  "_habs"  :: "hpat => hval => hval"
  "_hlam"  :: "hpats => hval => hval"   ("(3\<lambda>_./ _)" [0, 3] 3)
  "_hpat"  :: "hpat => hpats"           ("_")
  "_hpats" :: "hpat => hpats => hpats"  ("_/ _" [1, 0] 0)
  "_hvpat" :: "id => htyp => hpat"      ("'(_::_')")
  "_htpat" :: "hidt => hpat"            ("@_")
  ""       :: "id => hidt"              ("_")
  "_hidt"  :: "id => hkind => hidt"     ("'(_::_')")
translations
  "_hlam (_hpats p ps) r" == "_hlam (_hpat p) (_hlam ps r)"
  "_hlam (_hpat p) r" == "_habs p r"
  "_habs (_hvpat x t) r" => "CONST V_lam t (_abs x r)"
  "_habs (_htpat (_hidt a k)) r" => "CONST T_lam (_abs (_constrain a k) r)"
  "_habs (_htpat a) r" => "CONST T_lam (_abs a r)"
  "_hquote (_habs (_hvpat x (_hunquote t)) (_hunquote r))" <= "CONST V_lam t (_abs x r)"
  "_hquote (_habs (_htpat a) (_hunquote r))" <= "CONST T_lam (_abs a r)"

text "Application of terms to types"

syntax
  "_hvtapp" :: "hval => htyp => hval"  ("(1_/ @_)" [999, 1000] 999)
translations
  "_hvtapp x t" => "CONST T_app x t"
  "_hquote (_hvtapp (_hunquote x) (_hunquote t))" <= "CONST T_app x t"

text "Forall types"

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
  "_hall a r" => "CONST forallT (_abs a r)"
  "_htquote (_hall a (_hunquote r))" <= "CONST forallT (_abs a r)"
(* TODO: show kind annotations when necessary *)
(* use advanced print_translation for this *)

text "Examples"

term "\<langle>forall a. a \<rightarrow> a\<rangle>"
term "\<langle>forall a b c. a \<rightarrow> b \<rightarrow> c \<rightarrow> a\<rangle>"
term "\<guillemotleft>f x (g y)\<guillemotright>"
term "\<guillemotleft>\<lambda>(x::a). f x\<guillemotright>"
term "\<guillemotleft>\<lambda>(x::a) (y::b). f x y\<guillemotright>"
term "\<guillemotleft>\<lambda> (x::m (m a b c d \<rightarrow> b) b c d) (y::b \<rightarrow> c). f (g x y)\<guillemotright>"
term "\<guillemotleft>\<lambda> (f::forall a. a \<rightarrow> a). f @b\<guillemotright>"
term "\<guillemotleft>\<lambda> (x::a). f @a @b x\<guillemotright>"
term "\<guillemotleft>\<lambda> @a (x::a). x\<guillemotright>"
term "\<guillemotleft>\<lambda> @(m::* \<rightarrow> * \<rightarrow> *). x\<guillemotright>"
term "\<guillemotleft>\<lambda> @(m::(\<star> \<rightarrow> *) \<rightarrow> * \<rightarrow> *) @(a::\<star>). f@(m b a) x\<guillemotright>"
term "\<guillemotleft>\<lambda> @a (x::a). f @a x\<guillemotright>"

end
