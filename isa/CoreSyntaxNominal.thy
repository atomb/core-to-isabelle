theory CoreSyntax
imports Nominal
begin

nominal_datatype 'a Maybe = Nothing | Just 'a

types Id = string

nominal_datatype Pname = P Id

nominal_datatype AnMname = M "Pname \<times> Id list \<times> Id"

types Mname = "AnMname Maybe"

types 't Qual = "Mname \<times> 't"

-- {* REVISIT: How to register the Var and Tvar types below as "atom" types? *}

types Var = Id
      Tvar = Id

types Tcon = Id
      Dcon = Id

nominal_datatype Kind =
    Klifted
  | Kunlifted
  | Kopen
  | Karrow Kind Kind
  | Keq Ty Ty

and Ty = 
    Tvar Tvar
  | Tcon "(Id Qual)"
  | Tapp Ty Ty
  | Tforall "(Tvar \<times> Kind)" Ty

types Vbind = "Var \<times> Ty"
      Tbind = "Tvar \<times> Kind"

nominal_datatype Bind =
    Vb Vbind
  | Tb Tbind

nominal_datatype Exp =
    Var "(Var Qual)"
  | Dcon "(Dcon Qual)"
  | App Exp Exp
  | Appt Exp Ty
  | Lam Bind Exp

end






