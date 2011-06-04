module Language.Core.Isabelle where

import Language.Core.Syntax
import Data.List ( intercalate, isSuffixOf )

import Text.PrettyPrint.Leijen.Text

import qualified Data.Text.Lazy as T
import Data.Text.Lazy ( toStrict )
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy.Char8 as L

bs2t :: L.ByteString -> T.Text
bs2t = E.decodeUtf8

bs2d :: L.ByteString -> Doc
bs2d = text . bs2t

s2d :: String -> Doc
s2d  = text . T.pack

rightarrow :: Doc
rightarrow = s2d "\\<rightarrow>"

lambda :: Doc
lambda = s2d "\\<lambda>"

caseDoc :: Doc
caseDoc = s2d "case"

ofDoc :: Doc
ofDoc = s2d "of"

rightArrow :: Doc
rightArrow = s2d "\\<rightarrow>"

funT :: Doc
funT = s2d "funT"

forall :: Doc
forall = s2d "forall"

at :: Doc
at = s2d "@"

underscore :: Doc
underscore = s2d "_"

vbar :: Doc
vbar = s2d "|"

dcolon :: Doc
dcolon = colon <> colon

processTdef :: Tdef -> Doc
processTdef (Data (_, _, name) tbinds cdefs) =
  bs2d name </>
  sep (map processTbindQuoted tbinds) </>
  equals <+> cat (punctuate (space <> vbar <> space) (map processCdef cdefs))
processTdef (Newtype {}) = error "newtype not yet implemented"

processTbindQuoted :: Tbind -> Doc
processTbindQuoted (tvar, Klifted)       = bs2d tvar
processTbindQuoted (tvar, k@(Karrow {})) = parens (bs2d tvar </> dcolon <+>
  dquotes (showKind k))

processTbind :: Tbind -> Doc
processTbind (tvar, Klifted)       = bs2d tvar
processTbind (tvar, k@(Karrow {})) =
  parens (bs2d tvar </> dcolon <+> showKind k)

showKind :: Kind -> Doc
showKind Klifted        = s2d "\\<star>"
showKind Kunlifted      = error "unlifted kinds not supported" -- " # "
showKind Kopen          = error "open kinds not supported"     -- " ? "
showKind (Karrow k1 k2) = showKind k1 <+> rightarrow <+> showKind k2
showKind (Keq _ _)      = error "equality kinds not supported"

processCdef :: Cdef -> Doc
processCdef (Constr (_, _, name) [] [])  = bs2d name
processCdef (Constr (_, _, name) [] tys) = bs2d name <+>
  sep (map (dquotes.showTy) tys)

showTy :: Ty -> Doc
showTy (Tvar v)           = bs2d v
showTy (Tapp t1 t2)       = parens (showTy t1 <+> showTy t2)
showTy (Tarrow t1 t2)     = parens (funT <+> showTy t1 <+> showTy t2)
showTy (Tcon (_, _, t))   = bs2d t
showTy (Tforall tbind ty) = parens (forall <+> processTbind tbind <>
  dot <+> showTy ty)
showTy t                  = error $ "Ty not fully implemented: " ++ show t

processVdef :: Vdef -> Doc
processVdef (Vdef _ (_, _, name) ty exp) = bs2d name </> dcolon <+>
  dquotes (showTy ty) <+> equals </> dquotes (processExp exp)

processExp :: Exp -> Doc
processExp (Var  (_, _,v))  = bs2d v
processExp (Dcon (_, _, d)) = bs2d d
processExp (Lit  {})        = error "Embedding literals not yet supported."
processExp (App  exp1 exp2) = parens (processExp exp1 <+> processExp exp2)
processExp (Appt exp ty)    = parens (processExp exp <+> at <> showTy ty)
processExp (Lam bind exp)   = lambda <+> processVbind bind <> dot </> processExp exp
processExp (Lamt bind exp)  = lambda <+> at <> processTbind bind <> dot </> processExp exp
processExp (Case exp vbind ty alts) =
  caseDoc <+> parens (showTy ty) </>
  processExp exp <+> ofDoc <+> unVbind vbind </>
  braces (cat (punctuate semi (map processAlt alts)))
processExp exp              = error $ "Not implemented: " ++ show exp
-- TODO: Finish this definition


unVbind :: Vbind -> Doc
unVbind ((_, _, v), _) = bs2d v

processAlt :: Alt -> Doc
processAlt (Acon (_, _, dcon) [] vbinds exp) =
  bs2d dcon <+> sep (map processVbind vbinds) <+>
  rightArrow <+> processExp exp
processAlt (Adefault exp) = underscore <+> rightArrow <+> processExp exp
processAlt alt = error $ "Alt not implemented: " ++ show alt

processVbind :: Vbind -> Doc
processVbind ((_,_,var), ty) = parens (bs2d var <+> dcolon <+> showTy ty)

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
processVdefg :: Vdefg -> Doc
processVdefg (Nonrec vdef) = halicore_fun </> processVdef vdef
processVdefg (Rec vdefs) = halicore_fun </>
  cat (punctuate (s2d " and ") (map processVdef vdefs)) <> line

halicore_fun = line <> line <> (s2d "halicore_fun") <> line

--processModule :: Module -> IsaDefs
processModule :: Module -> FilePath -> Doc
processModule (Module _ tdefs vdefgs) name =
  header name <$> processTdefs tdefs <+>
  cat (map processVdefg vdefgs) <>
  line <> line <> s2d "end"

processTdefs :: [Tdef] -> Doc
processTdefs [] = empty
processTdefs tdefs = s2d "halicore_data" <$>
  cat (punctuate (s2d " and ") (map processTdef tdefs)) <> line

header :: FilePath -> Doc
header name =
  s2d "theory" <+> s2d name <$>
  s2d "imports Halicore" <$>
  s2d "begin"

