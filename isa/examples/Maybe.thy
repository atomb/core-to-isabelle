theory Maybe
imports "../Shallow"
begin

fixrec
  Maybe :: "T \<rightarrow> T" where
 "Maybe\<cdot>A =
    data_type [(''Nothing'',[]),
               (''Just'', [A])]"

fixrec map :: "V" where
  "map = T_lam (\<lambda>A. T_lam (\<lambda>B. V_lam (T_fun A B) (\<lambda>f. V_lam (Maybe\<cdot>A) (\<lambda>xs.
      match ''Nothing'' (\<Lambda> <>. constr ''Nothing'' [])
      (match ''Just'' (flsplit\<cdot>(\<Lambda> x <>. constr ''Just'' [A]\<bullet>(f\<bullet>x)))
      (\<lambda>x. Wrong)) xs))))"

text {*
NEXT STEPS:
   Define the deflation type for map.
   Prove that map satisfies its declared deflation type.
   Replace flsplit with (\<Lambda> (x ## <>). ...) patterns.
   Define case-like match syntax.
*}

end