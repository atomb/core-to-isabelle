import Language.Core.Core
import Language.Core.Parser
import Language.Core.ParseGlue
import System.Environment

processModule :: Module -> IsaDefs
processModule (Module _ _ vdefs) 
 = Defs [] (map valToTmDecl vdefs)

data IsaDefs = Defs [TyDecl] [TmDecl]

data TyDecl = TyDecl
data TmDecl = TmDecl IId Term

type IId = String
data ITy = ITyvar IId

header :: String
header = unlines ["theory IsaCore",
                  "imports Shallow HOLCF begin"]

embedTy :: Ty -> String
embedTy (Tvar v) = v

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

nameConv :: String -> String
nameConv = ('h':)

embedTmDecl :: TmDecl -> String
embedTmDecl (TmDecl i t) = 
  unlines ["definition " ++ (nameConv i) ++ " where",
           "\"" ++ (nameConv i) ++ " = " ++ (embed t) ++ "\""]

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

main = do
  [f] <- getArgs
  c   <- readFile f
  case parse c 0 of
    FailP s -> putStrLn $ "Failed: " ++ s
    OkP m   -> putStrLn $ header ++ "\n" ++ (embedM $ processModule m)
