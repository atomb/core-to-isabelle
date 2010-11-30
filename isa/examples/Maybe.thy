theory Maybe
imports "../Shallow"
begin

fixrec
  Maybe :: "T \<rightarrow> T" where
 "Maybe\<cdot>A =
    data_type [(''Nothing'',[]),
               (''Just'', [A])]"

text {*

NEXT STEPS:
   Define map function on Maybe type.
   Define the deflation type for map.
   Prove that map satisfies its declared deflation type.
*}