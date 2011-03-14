theory Examples
imports Halicore
begin

subsection "Polymorphic identity function"

definition "ident = \<guillemotleft>\<lambda> @a (x::a). x\<guillemotright>"

lemma has_type_ident [type_rule]:
  "ident ::: \<langle>forall a. a \<rightarrow> a\<rangle>"
unfolding ident_def
by typecheck

lemma ident: "x ::: a \<Longrightarrow> \<guillemotleft>ident @a x\<guillemotright> = \<guillemotleft>x\<guillemotright>"
unfolding ident_def
by (simp add: T_beta V_beta)

lemma "\<guillemotleft>ident @(a \<rightarrow> a) (ident @a)\<guillemotright> = \<guillemotleft>ident @a\<guillemotright>"
unfolding ident_def
by (simp add: T_beta V_beta)

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
by typecheck

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
apply (simp add: T_beta V_beta)
apply (rule V_ext)
apply typecheck
apply typecheck
apply (rule V_lam_defined)
apply (simp add: ident_def T_beta V_lam_defined)
apply (rename_tac xs)
apply (simp add: V_beta)
apply (simp add: ident)
apply (rule_tac P="\<lambda>t. \<guillemotleft>bind @a @a xs t\<guillemotright> = xs" and s="\<guillemotleft>return @a\<guillemotright>" in ssubst)
apply (rule V_ext)
apply typecheck
apply typecheck
apply (rule V_lam_defined)
apply (rule return_defined)
apply (simp add: V_beta)
apply (simp add: ident)
apply (erule right_unit)
done

lemma V_eta: "\<lbrakk>f ::: \<langle>a \<rightarrow> b\<rangle>; f \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> \<guillemotleft>\<lambda>(x::a). f x\<guillemotright> = f"
apply (erule funT_cases, simp)
apply (simp cong: V_lam_cong add: V_beta)
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
apply (simp add: T_beta V_beta)
apply (simp cong: V_lam_cong add: ident)
apply (subst V_eta)
apply typecheck
apply (rule return_defined)
apply (simp cong: V_lam_cong add: right_unit)
apply (simp add: ident_def T_beta)
done



subsection "Maybe datatype"

fixrec Maybe :: "\<star> \<rightarrow> \<star>" where [simp del]:
  "Maybe\<cdot>a = datatype [(''Nothing'', []), (''Just'', [a])]"

thm Maybe.simps [folded T_apply_def]

lemma Maybe_unfold:
  "\<langle>Maybe a\<rangle> = datatype [(''Nothing'', []), (''Just'', [a])]"
unfolding T_apply_def by (rule Maybe.simps)

definition "Nothing = \<guillemotleft>\<lambda>@(a::\<star>). \<lbrace>Vcon\<cdot>''Nothing''\<cdot>[]\<rbrace>\<guillemotright>"

definition "Just = \<guillemotleft>\<lambda>@(a::\<star>) (x::a). \<lbrace>Vcon\<cdot>''Just''\<cdot>[x]\<rbrace>\<guillemotright>"

text "Case expression syntax for Maybe type"

translations
  "_hcon (XCONST Nothing)" => "''Nothing''"
  "CONST Nothing" <= "_htag ''Nothing''"
  "_hcon (XCONST Just)" => "''Just''"
  "CONST Just" <= "_htag ''Just''"

lemma has_type_Nothing [type_rule]:
  "Nothing ::: \<langle>forall a. Maybe a\<rangle>"
unfolding Nothing_def Maybe_unfold
by (intro has_type_T_lam cont2cont
  has_type_datatype_intro1 have_types.intros)

lemma has_type_Just [type_rule]:
  "Just ::: \<langle>forall a. a \<rightarrow> Maybe a\<rangle>"
unfolding Just_def Maybe_unfold
by (intro has_type_T_lam has_type_V_lam cont2cont has_type_datatype_intro1
  has_type_datatype_intro2 have_types.intros) simp_all

lemma Nothing_eq_Vcon:
  fixes a :: "\<star>" shows "\<guillemotleft>Nothing @a\<guillemotright> = Vcon\<cdot>''Nothing''\<cdot>[]"
by (simp add: Nothing_def T_beta)

lemma Just_eq_Vcon:
  assumes "x ::: a" shows "\<guillemotleft>Just @a x\<guillemotright> = Vcon\<cdot>''Just''\<cdot>[x]"
using assms by (simp add: Just_def T_beta V_beta type_rule)

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
apply (simp add: Just_eq_Vcon cases_match_eq B_rep_branch0 B_rep_branchV)
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
apply (simp add: T_beta V_beta has_type_bottom)
apply (simp add: cases_bottom)
done

lemma maybemap_beta:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>" "m ::: \<langle>Maybe a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f m\<guillemotright> = \<guillemotleft>case (Maybe b) m of w
    {Nothing \<rightarrow> Nothing @b; Just (x::a) \<rightarrow> Just @b (f x)}\<guillemotright>"
unfolding maybemap_def
by (simp add: T_beta V_beta)

lemma maybemap_Nothing:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Nothing @a)\<guillemotright> = \<guillemotleft>Nothing @b\<guillemotright>"
by (simp add: maybemap_beta case_Maybe)

lemma maybemap_Just:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  assumes [type_rule]: "x ::: \<langle>a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Just @a x)\<guillemotright> = \<guillemotleft>Just @b (f x)\<guillemotright>"
by (simp add: maybemap_beta case_Maybe)

definition B_type :: "B \<Rightarrow> T list \<Rightarrow> T \<Rightarrow> bool"
  where "B_type b ts u \<longleftrightarrow> (\<forall>xs. have_types xs ts \<longrightarrow> B_rep\<cdot>b\<cdot>xs ::: u)"

lemma B_type_branch0: "y ::: u \<Longrightarrow> B_type (branch0 y) [] u"
unfolding B_type_def
apply (clarify elim!: have_types_elims)
apply (simp add: B_rep_branch0)
done

lemma B_type_branchV:
  assumes "cont (\<lambda>x. b x)"
  assumes "\<And>x. x ::: t \<Longrightarrow> B_type (b x) ts u"
  shows "B_type (branchV t (\<lambda>x. b x)) (t # ts) u"
using assms unfolding B_type_def
apply (clarify elim!: have_types_elims)
apply (simp add: B_rep_branchV)
done

definition M_type :: "M \<Rightarrow> T \<Rightarrow> T \<Rightarrow> bool"
  where "M_type m t u \<longleftrightarrow> (\<forall>x. x ::: t \<longrightarrow> sfun_rep\<cdot>(M_rep\<cdot>m)\<cdot>x ::: u)"

lemma has_type_cases:
  assumes x: "x ::: t"
  assumes m: "\<And>w. w ::: t \<Longrightarrow> M_type (m w) t u"
  shows "cases u x (\<lambda>w. m w) ::: u"
using assms unfolding cases_def M_type_def by simp

lemma M_type_allmatch:
  assumes "x ::: u"
  shows "M_type (allmatch x) t u"
using assms unfolding M_type_def allmatch_def
by (simp add: M.abs_iso strictify_conv_if has_type_bottom)

lemma M_type_endmatch:
  shows "M_type endmatch' t u"
unfolding endmatch'_def
by (intro M_type_allmatch has_type_bottom)

lemma M_type_match_Nothing:
  assumes b: "B_type b [] u"
  assumes m: "M_type m \<langle>Maybe a\<rangle> u"
  shows "M_type (match ''Nothing'' b m) \<langle>Maybe a\<rangle> u"
using assms unfolding M_type_def B_type_def
apply clarify
apply (drule spec, drule (1) mp)
apply (simp add: match_def M.abs_iso strictify_cancel)
apply (erule Maybe_cases)
apply (simp add: has_type_bottom)
apply (simp add: Nothing_eq_Vcon)
apply (simp add: Just_eq_Vcon)
done

lemma M_type_match_Just:
  assumes b: "B_type b [a] u"
  assumes m: "M_type m \<langle>Maybe a\<rangle> u"
  shows "M_type (match ''Just'' b m) \<langle>Maybe a\<rangle> u"
using assms unfolding M_type_def B_type_def
apply clarify
apply (drule spec, drule (1) mp)
apply (simp add: match_def M.abs_iso strictify_cancel)
apply (erule Maybe_cases)
apply (simp add: has_type_bottom)
apply (simp add: Nothing_eq_Vcon)
apply (simp add: Just_eq_Vcon)
done

lemma has_type_maybemap [type_rule]:
  "maybemap ::: \<langle>forall aadk badl. (aadk \<rightarrow> badl) \<rightarrow> Maybe aadk \<rightarrow> Maybe badl\<rangle>"
unfolding maybemap_def
by (rule has_type_T_lam has_type_V_lam cont2cont has_type_cases M_type_match_Nothing B_type_branch0 has_type_T_app type_rule M_type_match_Just B_type_branchV has_type_V_app M_type_endmatch | assumption)+

lemma ident_type: "\<guillemotleft>ident @a\<guillemotright> ::: \<langle>a \<rightarrow> a\<rangle>"
by typecheck

lemma maybemap_ident:
  "\<guillemotleft>maybemap @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(Maybe a)\<guillemotright>"
apply (rule V_ext)
apply typecheck
apply typecheck
apply (simp add: maybemap_def T_beta V_beta V_lam_defined)
apply (simp add: ident_def T_beta V_lam_defined)
apply (erule Maybe_cases)
apply (simp add: maybemap_bottom ident has_type_bottom)
apply (simp add: maybemap_Nothing ident)
apply (simp add: maybemap_Just ident)
done

lemma maybemap_maybemap:
  assumes [type_rule]: "m ::: \<langle>Maybe a\<rangle>" "f ::: \<langle>a \<rightarrow> b\<rangle>" "g ::: \<langle>b \<rightarrow> c\<rangle>"
  shows "\<guillemotleft>maybemap @b @c g (maybemap @a @b f m)\<guillemotright> =
    \<guillemotleft>maybemap @a @c (\<lambda>(x::a). g (f x)) m\<guillemotright>"
apply (rule Maybe_cases [OF assms(1)])
apply (simp add: maybemap_bottom)
apply (simp add: maybemap_Nothing)
apply (simp add: maybemap_Just V_beta)
done

end
