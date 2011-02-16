theory Examples
imports Halicore_Syntax
begin

subsection "Polymorphic identity function"

definition "ident = \<guillemotleft>\<lambda> @a (x::a). x\<guillemotright>"

lemma has_type_ident [type_rule]:
  "ident ::: \<langle>forall a. a \<rightarrow> a\<rangle>"
unfolding ident_def
by (intro type_rule cont_rule)

lemma ident: "x ::: a \<Longrightarrow> \<guillemotleft>ident @a x\<guillemotright> = \<guillemotleft>x\<guillemotright>"
unfolding ident_def
by (simp only: T_beta V_beta type_rule cont_rule)

lemma "\<guillemotleft>ident @(a \<rightarrow> a) (ident @a)\<guillemotright> = \<guillemotleft>ident @a\<guillemotright>"
unfolding ident_def
by (simp only: T_beta V_beta type_rule cont_rule)



subsection "Defining fmap in terms of return and bind"

term "\<guillemotleft>\<lambda>(x::forall a. a \<rightarrow> a). x\<guillemotright>"

definition
  "mk_fmap =
    \<guillemotleft>\<lambda> @(m :: \<star> \<rightarrow> \<star>) (return :: forall a. a \<rightarrow> m a)
       (bind :: forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b)
       @a @b (f :: a \<rightarrow> b) (xs :: m a).
       bind @a @b xs (\<lambda>(x::a). return @b (f x))\<guillemotright>"

lemma has_type_fmap [type_rule]:
  "mk_fmap ::: \<langle>forall m. (forall a. a \<rightarrow> m a) \<rightarrow> (forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b) \<rightarrow> (forall a b. (a \<rightarrow> b) \<rightarrow> m a \<rightarrow> m b)\<rangle>"
unfolding mk_fmap_def
by (rule type_rule cont_rule | assumption)+

lemma funT_cases:
  assumes f: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  obtains "f = \<bottom>" | h where "f = \<guillemotleft>\<lambda>(x::a). \<lbrace>h\<cdot>x\<rbrace>\<guillemotright>" and "\<And>x. x ::: a \<Longrightarrow> h\<cdot>x ::: b"
apply (rule has_type_elim [OF f])
apply (simp add: cast_T_rep_funT)
apply (case_tac y, simp_all)
apply (rule_tac h="cast\<cdot>(T_rep\<cdot>b) oo cfun" in that(2))
apply (simp add: V_lam_def cfun_map_def)
apply (simp add: has_type_def)
done

lemma V_lam_eq_iff:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "V_lam a (\<lambda> x. f x) = V_lam a (\<lambda>x. g x) \<longleftrightarrow> (\<forall>x. x ::: a \<longrightarrow> f x = g x)"
unfolding V_lam_def
apply (simp add: cfun_eq_iff cont_compose [OF f] cont_compose [OF g])
apply (auto elim!: has_type_elim)
apply (simp add: has_type_def)
done

lemma V_lam_cong:
  assumes eq: "\<And>x. x ::: a \<Longrightarrow> f x = g x"
  shows "V_lam a (\<lambda>x. f x) = V_lam a (\<lambda>x. g x)"
unfolding V_lam_def
by (simp add: eq [symmetric, unfolded has_type_def])

lemma V_ext:
  assumes "f ::: \<langle>a \<rightarrow> b\<rangle>" and "g ::: \<langle>a \<rightarrow> b\<rangle>"
  assumes "f \<noteq> \<bottom>" and "g \<noteq> \<bottom>"
  assumes "\<And>x. x ::: a \<Longrightarrow> \<guillemotleft>f x\<guillemotright> = \<guillemotleft>g x\<guillemotright>"
  shows "f = g"
using assms apply -
apply (erule funT_cases, simp)
apply (erule funT_cases, simp)
apply (simp add: V_beta cong: V_lam_cong)
done

lemma V_lam_defined: "V_lam t f \<noteq> \<bottom>"
unfolding V_lam_def by simp

lemma
  fixes m :: "\<star> \<rightarrow> \<star>" and a :: "\<star>"
  fixes return bind :: V
  assumes [type_rule]: "return ::: \<langle>forall a. a \<rightarrow> m a\<rangle>"
  assumes [type_rule]: "bind ::: \<langle>forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b\<rangle>"
  assumes return_defined: "\<guillemotleft>return @a\<guillemotright> \<noteq> \<bottom>"
  assumes right_unit: "\<And>xs. xs ::: \<langle>m a\<rangle> \<Longrightarrow> \<guillemotleft>bind @a @a xs (return @a)\<guillemotright> = xs"
  shows "\<guillemotleft>mk_fmap @m return bind @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(m a)\<guillemotright>"
unfolding mk_fmap_def
apply (simp only: T_beta V_beta type_rule cont_rule)
apply (subst V_beta)
apply (simp only: cont_rule)
(* apply (rule has_type_T_app) back back back *)
apply (rule type_rule cont_rule | assumption)+
apply (rule V_ext)
apply (rule type_rule cont_rule | assumption)+
apply (rule V_lam_defined)
apply (simp add: ident_def T_beta cont_rule V_lam_defined)
apply (rename_tac xs)
apply (simp only: V_beta cont_rule)
apply (simp add: ident)
apply (rule_tac P="\<lambda>t. \<guillemotleft>bind @a @a xs t\<guillemotright> = xs" and s="\<guillemotleft>return @a\<guillemotright>" in ssubst)
apply (rule V_ext)
apply (rule type_rule cont_rule | assumption)+
apply (rule V_lam_defined)
apply (rule return_defined)
apply (simp only: V_beta cont_rule type_rule)
apply (simp only: ident)
apply (erule right_unit)
done

lemma V_eta: "\<lbrakk>f ::: \<langle>a \<rightarrow> b\<rangle>; f \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> \<guillemotleft>\<lambda>(x::a). f x\<guillemotright> = f"
apply (erule funT_cases, simp)
apply (simp cong: V_lam_cong add: V_beta cont_rule)
done

lemma
  fixes m :: "\<star> \<rightarrow> \<star>" and a :: "\<star>"
  fixes return bind :: V
  assumes [type_rule]: "return ::: \<langle>forall a. a \<rightarrow> m a\<rangle>"
  assumes [type_rule]: "bind ::: \<langle>forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b\<rangle>"
  assumes return_defined: "\<guillemotleft>return @a\<guillemotright> \<noteq> \<bottom>"
  assumes right_unit: "\<And>xs. xs ::: \<langle>m a\<rangle> \<Longrightarrow> \<guillemotleft>bind @a @a xs (return @a)\<guillemotright> = xs"
  shows "\<guillemotleft>mk_fmap @m return bind @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(m a)\<guillemotright>"
unfolding mk_fmap_def
apply (simp only: T_beta V_beta type_rule cont_rule)
apply (subst V_beta)
apply (simp only: cont_rule)
apply (rule type_rule cont_rule | assumption)+
apply (simp cong: V_lam_cong add: ident)
apply (subst V_eta)
apply (rule type_rule cont_rule)+
apply (rule return_defined)
apply (simp cong: V_lam_cong add: right_unit)
apply (simp add: ident_def T_beta cont_rule)
done



subsection "Maybe datatype"

fixrec Maybe :: "\<star> \<rightarrow> \<star>" where [simp del]:
  "Maybe\<cdot>a = datatype [(''Nothing'', []), (''Just'', [a])]"

lemma Maybe_unfold:
  "\<langle>Maybe a\<rangle> = datatype [(''Nothing'', []), (''Just'', [a])]"
unfolding T_apply_def by (rule Maybe.simps)

definition "Nothing = \<guillemotleft>\<lambda>@(a::\<star>). \<lbrace>Vcon\<cdot>''Nothing''\<cdot>[]\<rbrace>\<guillemotright>"

definition "Just = \<guillemotleft>\<lambda>@(a::\<star>) (x::a). \<lbrace>Vcon\<cdot>''Just''\<cdot>[x]\<rbrace>\<guillemotright>"

text "Case expression syntax for Maybe type"

translations
  "_hmatch (XCONST Nothing) r m"
    => "CONST match ''Nothing'' (CONST branch0 r) m"
  "_hmquote (_hmatch (XCONST Nothing) (_hunquote r) (_hmunquote m))"
    <= "CONST match ''Nothing'' (CONST branch0 r) m"

translations
  "_hmatch (_hpat (XCONST Just) (_hvarg x a)) r m"
    => "CONST match ''Just'' (CONST branchV a (\<lambda>x. CONST branch0 r)) m"
  "_hmquote (_hmatch (_hpat (XCONST Just) (_hvarg x (_hunquote a))) (_hunquote r) (_hmunquote m))"
    <= "CONST match ''Just'' (CONST branchV a (\<lambda>x. CONST branch0 r)) m"

lemma has_type_Nothing [type_rule]:
  "Nothing ::: \<langle>forall a. Maybe a\<rangle>"
unfolding Nothing_def Maybe_unfold
by (intro type_rule cont_rule cont2cont
  has_type_datatype_intro1 have_types.intros)

lemma has_type_Just [type_rule]:
  "Just ::: \<langle>forall a. a \<rightarrow> Maybe a\<rangle>"
unfolding Just_def Maybe_unfold
by (intro type_rule cont_rule cont2cont has_type_datatype_intro1
  has_type_datatype_intro2 have_types.intros) simp_all

lemma Nothing_eq_Vcon:
  fixes a :: "\<star>" shows "\<guillemotleft>Nothing @a\<guillemotright> = Vcon\<cdot>''Nothing''\<cdot>[]"
by (simp add: Nothing_def T_beta)

lemma Just_eq_Vcon:
  assumes "x ::: a" shows "\<guillemotleft>Just @a x\<guillemotright> = Vcon\<cdot>''Just''\<cdot>[x]"
using assms by (simp add: Just_def T_beta V_beta cont_rule)

lemma Maybe_cases:
  assumes "y ::: \<langle>Maybe a\<rangle>"
  obtains "y = \<bottom>"
  | "y = \<guillemotleft>Nothing @a\<guillemotright>"
  | x where "x ::: a" and "y = \<guillemotleft>Just @a x\<guillemotright>"
using assms unfolding Maybe_unfold
apply (simp add: Nothing_eq_Vcon Just_eq_Vcon)
apply (auto elim!: has_type_datatype_elims)
done

lemma cases_bottom: "cases t \<bottom> f = \<bottom>"
unfolding cases_def by simp

text "Simplifying case expressions on Maybe datatype:"

lemma case_Maybe:
  fixes a :: "\<star>" shows
  "\<guillemotleft>case (t) (Nothing @a) of w {Nothing \<rightarrow> \<lbrace>f w\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = f \<guillemotleft>Nothing @a\<guillemotright>"
  "\<guillemotleft>case (t) (Nothing @a) of w {Just (x::a) \<rightarrow> \<lbrace>g w x\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = \<guillemotleft>case (t) (Nothing @a) of w {\<lbrace>m w\<rbrace>}\<guillemotright>"
  "x ::: a \<Longrightarrow> \<guillemotleft>case (t) (Just @a x) of w {Nothing \<rightarrow> \<lbrace>f w\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = \<guillemotleft>case (t) (Just @a x) of w {\<lbrace>m w\<rbrace>}\<guillemotright>"
  "\<lbrakk>\<And>w. cont (\<lambda>y. g w y); x ::: a\<rbrakk> \<Longrightarrow> \<guillemotleft>case (t) (Just @a x) of w {Just (y::a) \<rightarrow> \<lbrace>g w y\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = g \<guillemotleft>Just @a x\<guillemotright> x"
apply (simp add: Nothing_eq_Vcon cases_match_eq B_rep_branch0)
apply (simp add: Nothing_eq_Vcon cases_match_neq)
apply (simp add: Just_eq_Vcon cases_match_neq)
apply (simp add: Just_eq_Vcon cases_match_eq B_rep_branch0 B_rep_branchV cont_rule)
done

subsection "Example from Maybe.hcr"

definition
  "maybemap =
   \<guillemotleft>\<lambda> @aady @badzz (fadm :: aady \<rightarrow> badzz) (dsddB :: Maybe aady).
    case (Maybe badzz) dsddB of wildB1
    {Nothing \<rightarrow> Nothing @badzz; Just (xado::aady) \<rightarrow> Just @badzz (fadm xado)}\<guillemotright>"

lemma maybemap_bottom:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f \<lbrace>\<bottom>\<rbrace>\<guillemotright> = \<bottom>"
unfolding maybemap_def
apply (simp add: T_beta V_beta cont_rule type_rule has_type_bottom)
apply (simp add: cases_bottom)
done

lemma maybemap_beta:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>" "m ::: \<langle>Maybe a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f m\<guillemotright> = \<guillemotleft>case (Maybe b) m of w
    {Nothing \<rightarrow> Nothing @b; Just (x::a) \<rightarrow> Just @b (f x)}\<guillemotright>"
unfolding maybemap_def
apply (subst T_beta, intro cont_rule)
apply (subst T_beta, intro cont_rule)
apply (subst V_beta, intro cont_rule)
apply (rule type_rule)
apply (rule V_beta, intro cont_rule)
apply (intro type_rule cont_rule)
done

lemma maybemap_Nothing:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Nothing @a)\<guillemotright> = \<guillemotleft>Nothing @b\<guillemotright>"
apply (subst maybemap_beta)
apply (rule type_rule)
apply (intro type_rule cont_rule)
apply (simp add: case_Maybe)
done

lemma maybemap_Just:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  assumes [type_rule]: "x ::: \<langle>a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Just @a x)\<guillemotright> = \<guillemotleft>Just @b (f x)\<guillemotright>"
apply (subst maybemap_beta)
apply (rule type_rule cont_rule)+
apply (simp add: case_Maybe type_rule cont_rule)
done

lemma has_type_maybemap [type_rule]:
  "maybemap ::: \<langle>forall aadk badl. (aadk \<rightarrow> badl) \<rightarrow> Maybe aadk \<rightarrow> Maybe badl\<rangle>"
unfolding maybemap_def
apply (rule type_rule cont_rule)+
(* TODO: make some generic typing rules for cases *)
apply (erule Maybe_cases)
apply (simp add: cases_bottom has_type_bottom)
apply (simp add: case_Maybe)
apply (intro type_rule cont_rule)
apply (simp add: case_Maybe cont_rule type_rule)
apply (rule type_rule cont_rule | assumption)+
done

lemma ident_type: "\<guillemotleft>ident @a\<guillemotright> ::: \<langle>a \<rightarrow> a\<rangle>"
by (rule type_rule cont_rule)+

lemma maybemap_ident:
  "\<guillemotleft>maybemap @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(Maybe a)\<guillemotright>"
apply (rule V_ext)
apply (rule type_rule cont_rule)+
apply (simp add: maybemap_def T_beta V_beta cont_rule ident_type)
apply (rule V_lam_defined)
apply (simp add: ident_def T_beta cont_rule V_lam_defined)
apply (erule Maybe_cases)
apply (simp add: maybemap_bottom ident_type ident has_type_bottom)
apply (simp add: maybemap_Nothing ident_type)
apply (rule ident [symmetric])
apply (intro type_rule cont_rule)
apply (simp add: maybemap_Just ident_type)
apply (simp add: ident)
apply (rule ident [symmetric])
apply (rule type_rule cont_rule | assumption)+
done

lemma maybemap_maybemap:
  assumes [type_rule]: "m ::: \<langle>Maybe a\<rangle>" "f ::: \<langle>a \<rightarrow> b\<rangle>" "g ::: \<langle>b \<rightarrow> c\<rangle>"
  shows "\<guillemotleft>maybemap @b @c g (maybemap @a @b f m)\<guillemotright> =
    \<guillemotleft>maybemap @a @c (\<lambda>(x::a). g (f x)) m\<guillemotright>"
apply (rule Maybe_cases [OF assms(1)])
apply (simp add: maybemap_bottom type_rule)
apply (rule maybemap_bottom)
apply (rule type_rule cont_rule | assumption)+
apply (simp add: maybemap_Nothing type_rule)
apply (rule maybemap_Nothing [symmetric])
apply (rule type_rule cont_rule | assumption)+
apply (simp add: maybemap_Just type_rule)
apply (subst maybemap_Just)
apply (rule type_rule | assumption)+
apply (subst maybemap_Just)
apply (rule type_rule cont_rule | assumption)+
apply (simp add: V_beta cont_rule)
done

end
