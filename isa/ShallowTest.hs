import Language.Core.Syntax
import Language.Core.Parser
-- import Language.Core.ParseGlue
import System.Environment
import Data.List ( intercalate, isSuffixOf )
import System.FilePath ( takeBaseName )
import qualified Data.ByteString.Lazy.Char8 as L

processTdef :: Tdef -> String
processTdef (Data (_, _, name) tbinds cdefs) =
  L.unpack name ++ " " ++
  intercalate " " (map processTbindQuoted tbinds) ++
  " = " ++ intercalate " | " (map processCdef cdefs)
processTdef (Newtype {}) = error "newtype not yet implemented"
  
processTbindQuoted :: Tbind -> String
processTbindQuoted (tvar, Klifted)       = L.unpack tvar
processTbindQuoted (tvar, k@(Karrow {})) = "(" ++ L.unpack tvar ++ " :: " ++
  quote (showKind k) ++ ")"

processTbind :: Tbind -> String
processTbind (tvar, Klifted)       = L.unpack tvar
processTbind (tvar, k@(Karrow {})) = "(" ++ L.unpack tvar ++ " :: " ++ showKind k ++ ")"

showKind :: Kind -> String
showKind Klifted        = "\\<star>"
showKind Kunlifted      = error "unlifted kinds not supported" -- " # "
showKind Kopen          = error "open kinds not supported"     -- " ? "
showKind (Karrow k1 k2) = showKind k1 ++ " \\<rightarrow> " ++ showKind k2
showKind (Keq _ _)      = error "equality kinds not supported"

processCdef :: Cdef -> String
processCdef (Constr (_, _, name) [] [])  = L.unpack name
processCdef (Constr (_, _, name) [] tys) = L.unpack name ++ " " ++
  intercalate " " (map (quote.showTy) tys)

showTy :: Ty -> String
showTy (Tvar v)      = L.unpack v
showTy (Tapp t1 t2)  = "(" ++ showTy t1 ++ " " ++ showTy t2 ++ ")"
showTy (Tarrow t1 t2) = "(" ++ "funT " ++ showTy t1 ++ " " ++ showTy t2 ++ ")"
showTy (Tcon (_, _, t))
  | "ZLzmzgZR" `isSuffixOf` L.unpack t = "funT"
  | otherwise = L.unpack t
showTy (Tforall tbind ty)  = "(forall " ++ processTbind tbind ++
  ". " ++ showTy ty ++ ")"
showTy t             = error $ "Ty not fully implemented: " ++ show t

quote :: String -> String
quote s = "\"" ++ s ++ "\""

processVdef :: Vdef -> String
processVdef (Vdef _ (_, _, name) ty exp) = L.unpack name ++ " :: " ++
  quote (showTy ty) ++ " =\n    " ++ quote (processExp exp)

lambda :: String
lambda = "\\<lambda>"

processExp :: Exp -> String
processExp (Var  (_, _,v))     = L.unpack v
processExp (Dcon (_, _, d))    = L.unpack d
processExp (Lit  {})        = error "Embedding literals not yet supported."
processExp (App  exp1 exp2) = "(" ++ processExp exp1 ++ " " ++ processExp exp2 ++ ")"
processExp (Appt exp ty)    = "(" ++ processExp exp ++ " @" ++ showTy ty ++ ")"
processExp (Lam bind exp)   = lambda ++ " " ++ processVbind bind ++ ".\n     " ++ processExp exp
processExp (Lamt bind exp)  = lambda ++ " @" ++ processTbind bind ++ ".\n     " ++ processExp exp
processExp (Case exp vbind ty alts) =
  "case " ++ "(" ++ showTy ty ++ ") " ++
  processExp exp ++ " of " ++ unVbind vbind ++ "\n      " ++
  " { " ++ intercalate ";\n         " (map processAlt alts) ++ "\n       }"
processExp exp              = error $ "Not implemented: " ++ show exp
-- TODO: Finish this definition

unVbind :: Vbind -> String
unVbind ((_, _, v), _) = L.unpack v

rightArrow :: String
rightArrow = "\\<rightarrow>"

processAlt :: Alt -> String
processAlt (Acon (_, _, dcon) [] vbinds exp) =
  L.unpack dcon ++ " " ++ intercalate " " (map processVbind vbinds) ++ " " ++
  rightArrow ++ " " ++ processExp exp
processAlt (Adefault exp) = "_ " ++ rightArrow ++ " " ++ processExp exp
processAlt alt = error $ "Alt not implemented: " ++ show alt
  

{-

Acon (Qual Dcon) [Tbind] [Vbind] Exp	 
Alit Lit Exp	 
Adefault Exp	 
-}

-- processBind :: Bind -> String
-- processBind (Vb vbind) = "(" ++ processVbind vbind  ++ ")"
-- processBind (Tb tbind) = " @" ++ processTbind tbind

processVbind :: Vbind -> String
processVbind ((_,_,var), ty) = "(" ++ (L.unpack var ++ "::" ++ showTy ty) ++ ")"

{-  The goal is to get something of the form:
  halicore_fun
    map :: "forall a b. (a -> b) -> [a] -> [b]"
         = "rhs"
See Halicore_Syntax.thy for examples
-}

{-
convert :: Exp -> Term
convert (Var (_,v)) = TmVar v
convert (Dcon (_,d)) = VCon d 
-- convert (Lit (Literal (Lint i) _)) = VInt i
convert (Lit _) = undefined {- Rationals, Strings, Chars? -}
convert (App e e') = VApp (convert e) (convert e')
convert (Appt e t') = TApp (convert e) t'
-- convert (Lam (Vb (v, ty)) e) = VLam v ty (convert e)
-- convert (Lam (Tb (v, k)) e) = TLam v (convert e)
convert (Let v e) = undefined
convert (Case e v _ alts) = undefined
convert (Cast e _) = convert e
convert (Note _ e) = convert e
convert (External _ _) = undefined
-}
processVdefg :: Vdefg -> String
processVdefg (Nonrec vdef) = halicore_fun ++ processVdef vdef
processVdefg (Rec vdefs) = halicore_fun ++
  intercalate "\nand\n  " (map processVdef vdefs) ++ "\n"

halicore_fun = "\n\nhalicore_fun\n  "

--processModule :: Module -> IsaDefs
processModule :: Module -> FilePath -> String
processModule (Module _ tdefs vdefgs) name = 
  header name ++ "\n" ++ processTdefs tdefs ++
  concatMap processVdefg vdefgs ++
  "\n\nend"

processTdefs :: [Tdef] -> String
processTdefs [] = []
processTdefs tdefs = "halicore_data\n  " ++
  intercalate "\nand\n  " (map processTdef tdefs) ++ "\n"

{-
data IsaDefs = Defs [TyDecl] [TmDecl]

data TyDecl = TyDecl
data TmDecl = TmDecl IId Term

type IId = String
data ITy = ITyvar IId
-}
header :: FilePath -> String
header name = unlines ["theory " ++ name,
                  "imports Halicore\nbegin"]
{-
embedTy :: Ty -> String
embedTy (Tvar v)            = v
embedTy (Tcon (_, v))       = v -- FIXME: Do not drop the qualifier
embedTy (Tapp t1 t2)        = embedTy t1 ++ " " ++ embedTy t2
embedTy (Tforall tbind ty)  = "(forall " ++ processTbind tbind ++
  ". " ++ embedTy ty ++ ")"
embedTy (TransCoercion  {}) = error "embedTy TransCoercion"
embedTy (SymCoercion    {}) = error "embedTy SymCoercion"
embedTy (UnsafeCoercion {}) = error "UnsafeCoercion"
embedTy (InstCoercion   {}) = error "InstCoercion"
embedTy (LeftCoercion   {}) = error "LeftCoercion"
embedTy (RightCoercion  {}) = error "RightCoercion"
-}
{-
embed :: Term -> String
embed (VInt i) = "VInt (Def "++(show i)++")"
embed (VApp t t') = "V_app "++(embed t)++ " " ++ (embed t')
embed (TApp t ty) = "T_app "++(embed t)++ " " ++ (embedTy ty)
embed (VLam i ty t) = "V_lam " ++ (embedTy ty) ++ " (" ++ "\\<lambda> "++i++". "++(embed t)++")"
embed (TLam i t) = "T_lam (" ++ "\\<lambda> "++i++". "++(embed t)++")"
embed (TmVar i) = i
embed (VCon i) = "Vcon\\<cdot>(Def "++ i++")"

embedM :: IsaDefs -> String
embedM (Defs _ tms) = unlines $ map embedTmDecl tms
-}
nameConv :: String -> String
nameConv = ('h':)
{-
embedTmDecl :: TmDecl -> String
embedTmDecl (TmDecl i t) = 
  unlines ["definition " ++ (nameConv i) ++ " where",
           "\"" ++ (nameConv i) ++ " = " ++ (embed t) ++ "\""]
-}
{-
data Term = TLam IId Term 
          | VLam IId Ty Term
          | VApp Term Term
          | TApp Term Ty
          | VInt Integer
          | VCon IId
          | TmVar IId

valToTmDecl :: Vdefg -> TmDecl
valToTmDecl (Nonrec (Vdef ((_,v), _, e))) 
  = TmDecl v (convert e)
-}
{-
convert :: Exp -> Term
convert (Var (_,v)) = TmVar v
convert (Dcon (_,d)) = VCon d 
convert (Lit (Literal (Lint i) _)) = VInt i
convert (Lit _) = undefined {- Rationals, Strings, Chars? -}
convert (App e e') = VApp (convert e) (convert e')
convert (Appt e t') = TApp (convert e) t'
convert (Lam (Vb (v, ty)) e) = VLam v ty (convert e)
convert (Lam (Tb (v, k)) e) = TLam v (convert e)
convert (Let v e) = undefined
convert (Case e v _ alts) = undefined
convert (Cast e _) = convert e
convert (Note _ e) = convert e
convert (External _ _) = undefined
-}

main = do
  [f] <- getArgs
  c   <- L.readFile f
  let newName = takeBaseName f
  case parseModule newName c of
    Left err -> putStrLn $ "Failed: " ++ show err
    Right  m -> putStrLn $ processModule m newName
{-
  case parse c 0 of
    FailP s -> putStrLn $ "Failed: " ++ s
    OkP m   -> putStrLn $ processModule m newName
-}
    --OkP m   -> putStrLn $ header ++ "\n" ++ (embedM $ processModule m)
