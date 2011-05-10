theory Examples
imports Halicore
begin

declare Vapp_Vlam [simp]
declare Vtapp_Vtlam [simp]

subsection "Polymorphic identity function"

definition "ident = \<guillemotleft>\<lambda> @a (x::a). x\<guillemotright>"

lemma has_type_ident [type_rule]:
  "ident ::: \<langle>forall a. a \<rightarrow> a\<rangle>"
unfolding ident_def
by typecheck

lemma ident: "x ::: a \<Longrightarrow> \<guillemotleft>ident @a x\<guillemotright> = \<guillemotleft>x\<guillemotright>"
unfolding ident_def
by simp

lemma "\<guillemotleft>ident @(a \<rightarrow> a) (ident @a)\<guillemotright> = \<guillemotleft>ident @a\<guillemotright>"
unfolding ident_def
by simp

subsection "Defining fmap in terms of return and bind"

term "\<guillemotleft>\<lambda>(x::forall a. a \<rightarrow> a). x\<guillemotright>"

definition
  "mk_fmap =
    \<guillemotleft>\<lambda> @(m :: \<star> \<rightarrow> \<star>) (return :: forall a. a \<rightarrow> m a)
       (bind :: forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b)
       @a @b (f :: a \<rightarrow> b) (xs :: m a).
       bind @a @b xs (\<lambda>(x::a). return @b (f x))\<guillemotright>"

lemma has_type_fmap [type_rule]:
  "mk_fmap ::: \<langle>forall (m::\<star> \<rightarrow> \<star>). (forall a. a \<rightarrow> m a) \<rightarrow> (forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b) \<rightarrow> (forall a b. (a \<rightarrow> b) \<rightarrow> m a \<rightarrow> m b)\<rangle>"
unfolding mk_fmap_def
by typecheck

lemma Tfun_cases:
  assumes f: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  obtains "f = \<bottom>" | h where "f = \<guillemotleft>\<lambda>(x::a). \<lbrace>h\<cdot>x\<rbrace>\<guillemotright>" and "\<And>x. x ::: a \<Longrightarrow> h\<cdot>x ::: b"
apply (rule has_type_elim [OF f])
apply (simp add: cast_T_rep_Tfun)
apply (case_tac y, simp_all)
apply (rule_tac h="cast\<cdot>(T_rep\<cdot>b) oo cfun" in that(2))
apply (simp add: Vlam_def cfun_map_def)
apply (simp add: has_type_def)
done

lemma Vlam_eq_iff:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "Vlam a (\<lambda> x. f x) = Vlam a (\<lambda>x. g x) \<longleftrightarrow> (\<forall>x. x ::: a \<longrightarrow> f x = g x)"
unfolding Vlam_def
apply (simp add: cfun_eq_iff cont_compose [OF f] cont_compose [OF g])
apply (auto elim!: has_type_elim)
apply (simp add: has_type_def)
done

lemma Vlam_cong [cong]:
  assumes a: "a = a'"
  assumes f: "\<And>x. x ::: a \<Longrightarrow> f x = f' x"
  shows "Vlam a (\<lambda>x. f x) = Vlam a' (\<lambda>x. f' x)"
unfolding Vlam_def
by (simp add: a f [symmetric, unfolded has_type_def])

lemma V_ext:
  assumes "f ::: \<langle>a \<rightarrow> b\<rangle>" and "g ::: \<langle>a \<rightarrow> b\<rangle>"
  assumes "f \<noteq> \<bottom>" and "g \<noteq> \<bottom>"
  assumes "\<And>x. x ::: a \<Longrightarrow> \<guillemotleft>f x\<guillemotright> = \<guillemotleft>g x\<guillemotright>"
  shows "f = g"
using assms apply -
apply (erule Tfun_cases, simp)
apply (erule Tfun_cases, simp)
apply simp
done

lemma Vlam_defined: "Vlam t f \<noteq> \<bottom>"
unfolding Vlam_def by simp

lemma
  fixes m :: "\<star> \<rightarrow> \<star>" and a :: "\<star>"
  fixes return bind :: V
  assumes [type_rule]: "return ::: \<langle>forall a. a \<rightarrow> m a\<rangle>"
  assumes [type_rule]: "bind ::: \<langle>forall a b. m a \<rightarrow> (a \<rightarrow> m b) \<rightarrow> m b\<rangle>"
  assumes return_defined: "\<guillemotleft>return @a\<guillemotright> \<noteq> \<bottom>"
  assumes right_unit: "\<And>xs. xs ::: \<langle>m a\<rangle> \<Longrightarrow> \<guillemotleft>bind @a @a xs (return @a)\<guillemotright> = xs"
  shows "\<guillemotleft>mk_fmap @m return bind @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(m a)\<guillemotright>"
unfolding mk_fmap_def
apply simp
apply (rule V_ext)
apply typecheck
apply typecheck
apply (rule Vlam_defined)
apply (simp add: ident_def Vlam_defined)
apply (rename_tac xs)
apply simp
apply (simp add: ident)
apply (rule_tac P="\<lambda>t. \<guillemotleft>bind @a @a xs t\<guillemotright> = xs" and s="\<guillemotleft>return @a\<guillemotright>" in ssubst)
apply (rule V_ext)
apply typecheck
apply typecheck
apply (rule Vlam_defined)
apply (rule return_defined)
apply simp
apply (erule right_unit)
done

lemma V_eta: "\<lbrakk>f ::: \<langle>a \<rightarrow> b\<rangle>; f \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> \<guillemotleft>\<lambda>(x::a). f x\<guillemotright> = f"
apply (erule Tfun_cases, simp)
apply simp
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
apply simp
apply (simp add: ident)
apply (subst V_eta)
apply typecheck
apply (rule return_defined)
apply (simp add: right_unit)
apply (simp add: ident_def)
done

subsection {* Polymorphic seq function *}

text {* This example demonstrates the typecheck tactic on a
wildcard-only case expression. *}

definition seq where
  "seq = \<guillemotleft>\<lambda>@a @b (x::a) (y::b). case (b) x of w {_ \<rightarrow> y}\<guillemotright>"

lemma seq_type: "seq ::: \<langle>forall a b. a \<rightarrow> b \<rightarrow> b\<rangle>"
unfolding seq_def by typecheck


subsection "Maybe datatype"

halicore_data Maybe a = Nothing | Just "a"

lemma Nothing_eq_Vcon:
  fixes a :: "\<star>" shows "\<guillemotleft>Nothing @a\<guillemotright> = Vcon\<cdot>Nothing_tag\<cdot>[]"
by (simp add: Nothing_def)

lemma Just_eq_Vcon:
  assumes "x ::: a" shows "\<guillemotleft>Just @a x\<guillemotright> = Vcon\<cdot>Just_tag\<cdot>[x]"
using assms by (simp add: Just_def type_rule)

lemma Maybe_cases:
  assumes "y ::: \<langle>Maybe a\<rangle>"
  obtains "y = \<bottom>"
  | "y = \<guillemotleft>Nothing @a\<guillemotright>"
  | x where "x ::: a" and "y = \<guillemotleft>Just @a x\<guillemotright>"
using assms unfolding Maybe_unfold
apply (simp add: Nothing_eq_Vcon Just_eq_Vcon)
apply (auto elim!: has_type_datatype_elims)
done

lemma Vcase_bottom: "Vcase t \<bottom> f = \<bottom>"
unfolding Vcase_def by simp

text "Simplifying case expressions on Maybe datatype:"

lemma case_Maybe:
  fixes a :: "\<star>" shows
  "\<guillemotleft>case (t) (Nothing @a) of w {Nothing \<rightarrow> \<lbrace>f w\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = f \<guillemotleft>Nothing @a\<guillemotright>"
  "\<guillemotleft>case (t) (Nothing @a) of w {Just (x::a) \<rightarrow> \<lbrace>g w x\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = \<guillemotleft>case (t) (Nothing @a) of w {\<lbrace>m w\<rbrace>}\<guillemotright>"
  "x ::: a \<Longrightarrow> \<guillemotleft>case (t) (Just @a x) of w {Nothing \<rightarrow> \<lbrace>f w\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = \<guillemotleft>case (t) (Just @a x) of w {\<lbrace>m w\<rbrace>}\<guillemotright>"
  "\<lbrakk>\<And>w. cont (\<lambda>y. g w y); x ::: a\<rbrakk> \<Longrightarrow> \<guillemotleft>case (t) (Just @a x) of w {Just (y::a) \<rightarrow> \<lbrace>g w y\<rbrace>; \<lbrace>m w\<rbrace>}\<guillemotright> = g \<guillemotleft>Just @a x\<guillemotright> x"
apply (simp add: Nothing_eq_Vcon Vcase_Mbranch_eq B_rep_Bnone)
apply (simp add: Nothing_eq_Vcon Vcase_Mbranch_neq Nothing_tag_def Just_tag_def)
apply (simp add: Just_eq_Vcon Vcase_Mbranch_neq Nothing_tag_def Just_tag_def)
apply (simp add: Just_eq_Vcon Vcase_Mbranch_eq B_rep_Bnone B_rep_Bval)
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
apply (simp add: has_type_bottom)
apply (simp add: Vcase_bottom)
done

lemma maybemap_beta:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>" "m ::: \<langle>Maybe a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f m\<guillemotright> = \<guillemotleft>case (Maybe b) m of w
    {Nothing \<rightarrow> Nothing @b; Just (x::a) \<rightarrow> Just @b (f x)}\<guillemotright>"
unfolding maybemap_def
by simp

lemma maybemap_Nothing:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Nothing @a)\<guillemotright> = \<guillemotleft>Nothing @b\<guillemotright>"
by (simp add: maybemap_beta case_Maybe)

lemma maybemap_Just:
  assumes [type_rule]: "f ::: \<langle>a \<rightarrow> b\<rangle>"
  assumes [type_rule]: "x ::: \<langle>a\<rangle>"
  shows "\<guillemotleft>maybemap @a @b f (Just @a x)\<guillemotright> = \<guillemotleft>Just @b (f x)\<guillemotright>"
by (simp add: maybemap_beta case_Maybe)

lemma has_type_maybemap [type_rule]:
  "maybemap ::: \<langle>forall aadk badl. (aadk \<rightarrow> badl) \<rightarrow> Maybe aadk \<rightarrow> Maybe badl\<rangle>"
unfolding maybemap_def
by typecheck

lemma maybemap_ident:
  "\<guillemotleft>maybemap @a @a (ident @a)\<guillemotright> = \<guillemotleft>ident @(Maybe a)\<guillemotright>"
apply (rule V_ext)
apply typecheck
apply typecheck
apply (simp add: maybemap_def Vlam_defined)
apply (simp add: ident_def Vlam_defined)
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
apply (simp add: maybemap_Just)
done

end
