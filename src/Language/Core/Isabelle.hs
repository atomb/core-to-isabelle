{-# LANGUAGE OverloadedStrings #-}
module Language.Core.Isabelle where

import Prelude hiding ( exp )
import Language.Core.Core
import Language.Core.CoreUtils ( freeVarss )
import Language.Core.Printer () -- for show instances

import Text.PrettyPrint.Leijen.Text

import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Text.Encoding.Z as Z
import Data.List ( isSuffixOf )

-- * Conversion Functions
bs2t :: L.ByteString -> T.Text
bs2t = E.decodeUtf8

bs2d :: L.ByteString -> Doc
bs2d = text . bs2t

s2d :: String -> Doc
s2d  = text . T.pack

z2d :: String -> Doc
z2d = s2d . Z.zDecodeString

isaDcon :: Dcon -> Doc
isaDcon "ZMZN" = text "Nil"
isaDcon "ZC"   = text "Cons"
isaDcon dcon   = z2d dcon

-- * Utility functions
spacePunctuate :: Doc -> [Doc] -> [Doc]
spacePunctuate p = punctuate (space <> p <> space)

header :: FilePath -> Doc
header name =
  s2d "theory" <+> s2d name <$>
  s2d "imports Halicore" <$>
  s2d "begin" <> line

unVbind :: Vbind -> Doc
unVbind (v, _) = z2d v

altToExp :: Alt -> Exp
altToExp (Acon _ _ _ r) = r
altToExp (Alit _ r    ) = r
altToExp (Adefault r  ) = r

-- * Literals
rightArrow :: Doc
rightArrow = s2d "\\<rightarrow>"

lambda :: Doc
lambda = s2d "\\<lambda>"

star :: Doc
star = s2d "\\<star>"

caseDoc :: Doc
caseDoc = s2d "case"

ofDoc :: Doc
ofDoc = s2d "of"

funT :: Doc
funT = s2d "funT"

forall :: Doc
forall = s2d "forall"

andDoc :: Doc
andDoc = s2d "and"

end :: Doc
end = s2d "end"

at :: Doc
at = s2d "@"

halicore_fun :: Doc
halicore_fun = s2d "halicore_fun"

halicore_data :: Doc
halicore_data = s2d "halicore_data"

underscore :: Doc
underscore = s2d "_"

vbar :: Doc
vbar = s2d "|"

dcolon :: Doc
dcolon = colon <> colon

-- * Translations
processModule :: Module -> FilePath -> Doc
processModule (Module _ tdefs vdefgs) name =
  header name <$>
  processTdefs tdefs <>
  line <>
  line <>
  cat (map processVdefg vdefgs) <>
  line <>
  line <>
  end <> line

processVdefg :: Vdefg -> Doc
processVdefg (Nonrec vdef) = halicore_fun <$>
  line <>
  processVdef vdef <> line
processVdefg (Rec vdefs)   = halicore_fun <$>
  line <>
  cat (punctuate (line<>line<>andDoc<>line) (map processVdef vdefs)) <>
  line

processVdef :: Vdef -> Doc
processVdef (Vdef ((_, name), ty, exp)) =
  z2d name <+> dcolon <+>
  align (dquotes (showTy ty) <+> equals) </>
  indent 4 (dquotes (processExp exp))

processTdefs :: [Tdef] -> Doc
processTdefs []    = empty
processTdefs tdefs = halicore_data <$>
  line <>
  cat (punctuate (line<>line<>andDoc<>line) (map processTdef tdefs))

processTdef :: Tdef -> Doc
processTdef (Data (_, name) tbinds cdefs) =
  z2d name <+>
  hsep (map processTbindQuoted tbinds) <$>
  indent 4 (equals <+> p (map processCdef cdefs))
  where
  p :: [Doc] -> Doc
  p []     = empty
  p [d]    = d
  p (d:ds) = d <$> vbar <+> p ds
processTdef (Newtype {}) = error "newtype not yet implemented"

processTbindQuoted :: Tbind -> Doc
processTbindQuoted (tvar, Klifted)       = z2d tvar
processTbindQuoted (tvar, k@(Karrow {})) =
  parens (z2d tvar </>
  dcolon <+> dquotes (showKind k))

processTbind :: Tbind -> Doc
processTbind (tvar, Klifted)       = z2d tvar
processTbind (tvar, k@(Karrow {})) =
  parens (z2d tvar </>
  dcolon <+> showKind k)

showKind :: Kind -> Doc
showKind Klifted        = star
showKind Kunlifted      = error "unlifted kinds not supported" -- " # "
showKind Kopen          = error "open kinds not supported"     -- " ? "
showKind (Karrow k1 k2) = showKind k1 <+> rightArrow <+> showKind k2
showKind (Keq _ _)      = error "equality kinds not supported"

processCdef :: Cdef -> Doc
processCdef (Constr (_, name) [] [])  = z2d name
processCdef (Constr (_, name) [] tys) = z2d name <+>
  sep (map (dquotes.showTy) tys)

showTy :: Ty -> Doc
showTy = showTy' False
  where
  showTy' :: Bool -> Ty -> Doc
  showTy' _ (Tvar v)               = z2d v
  showTy' b (Tapp (Tapp (Tcon (_, t)) t1) t2)
    | "ZLzmzgZR" `isSuffixOf` t = -- find the function arrow, as "(->)"
      parens (showTy' b t1 <+> rightArrow <+> showTy' b t2)
  showTy' b (Tapp t1 t2)           = parens (showTy' b t1 <+> showTy' b t2)
  showTy' _ (Tcon (_, t)) = z2d t
  showTy' True (Tforall tbind ty)  =
    processTbind tbind <> spaceOrDot ty <> showTy' True ty
  showTy' False (Tforall tbind ty) =
    parens (forall <+> processTbind tbind <> spaceOrDot ty <> showTy' True ty)
  showTy' _ t                      =
    error $ "showTy not fully implemented: " ++ show t
  spaceOrDot (Tforall {}) = space
  spaceOrDot _            = dot <> space

processExp :: Exp -> Doc
processExp e = processExp' False e
  where
  spaceOrDot (Lam {})  = empty
  spaceOrDot _         = dot
  lambdaOrEmpty True  = empty
  lambdaOrEmpty False = lambda
  nest' True  = id
  nest' False = nest 3
  processExp' :: Bool -> Exp -> Doc
  processExp' _ (Var  (_, v)) = z2d v
  processExp' _ (Dcon (_, d)) = isaDcon d
  processExp' _ (Lit  {})        = error "Embedding literals not yet supported."
  processExp' b (App  exp1 exp2) =
    parens (processExp' b exp1 <+> processExp' b exp2)
  processExp' b (Appt exp ty)    =
    parens (processExp' b exp  <+> at <> showTy ty)
  processExp' b (Lam (Vb bind) exp)   =
    lambdaOrEmpty b <+> nest' b (processVbind bind <> spaceOrDot exp <$>
    processExp' True exp)
  processExp' b (Lam (Tb bind) exp)  =
    lambdaOrEmpty b <+> nest' b (at <> processTbind bind <> spaceOrDot exp <$>
    processExp' True exp)
  processExp' b (Case exp vbind ty alts) =
    caseDoc <+> parens (showTy ty) <+>
    processExp' b exp <+> ofDoc <+> vbindDoc <+> lbrace <$>
        (indent 4 (cat (punctuate semi (map processAlt alts))))
    <$> rbrace
    where
    vars = map snd (freeVarss (map altToExp alts))
    vbindDoc
      | fst vbind `elem` vars = unVbind vbind
      | otherwise             = empty
  processExp' _ exp              = error $ "Not implemented: " ++ show exp
-- TODO: Finish this definition

processAlt :: Alt -> Doc
processAlt (Acon (_, dcon) [] vbinds exp) =
  isaDcon dcon <+>
  hang 2 (hsep (map processVbind vbinds) <+> rightArrow </>
  processExp exp)
processAlt (Adefault exp) = underscore <+> rightArrow <+> processExp exp
processAlt alt = error $ "Alt not implemented: " ++ show alt

processVbind :: Vbind -> Doc
processVbind (var, ty) = parens (z2d var <+> dcolon <+> showTy ty)
