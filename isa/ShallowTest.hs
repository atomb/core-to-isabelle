module ShallowTest where

import Language.Core.Core

type Id = String

{- A term should always get mapped to something that is a V -}

embed :: Term -> String
embed (VInt i) = "VInt (Def "++(show i)++")"
embed (VApp t t') = "V_app "++(embed t)++ " " ++ (embed t')
embed (TApp t ty) = "T_app "++(embed t)++ " " ++ (embedTy ty)
embed (VLam i t) = "V_lam (" ++ "\\<lambda> "++i++". "++(embed t)++")"
embed (TLam i t) = "T_lam (" ++ "\\<lambda> "++i++". "++(embed t)++")"
embed (TmVar i) = i
embed (VCon i) = "Vcon·(Def "++i++")"


data Term = TLam Id Term 
          | VLam Id Term
          | VApp Term Term
          | TApp Term Ty
          | VInt Int
          | VCon Id
          | TmVar Id

convert :: Exp -> Term
convert (Var (_,v)) = TmVar v
convert (Dcon (_,d)) = VCon d 
convert (Lit (Lint i)) = VInt i
convert (Lit _) = undefined {- Rationals, Strings, Chars? -}
convert (App e e') = VApp (convert e) (convert e')
convert (Appt e t') = TApp (convert e) t'
convert (Lam (Vb (v, ty)) e) = VLam v (convert e)
convert (Lam (Tb (v, k)) e) = TLam v (convert e)
convert (Let v e) = undefined
convert (Case e v _ alts) = undefined
convert (Cast e _) = convert e
convert (Note _ e) = convert e
convert (External _ _) = undefined