(* Requires Isabelle/HOLCF 2011 *)

header {* Combinators for building algebraic deflations *}

theory Defl_Lib
imports "~~/src/HOL/HOLCF/Library/Defl_Bifinite"
begin

subsection {* Identity deflation *}

lemma ID_defl_exists:
  "\<exists>(d::'a::bifinite defl). cast\<cdot>d = ID"
proof -
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain a"
    using bifinite ..
  then interpret approx_chain a .
  have chain_a: "chain (\<lambda>i. defl_principal (Abs_fin_defl (a i)))"
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def Abs_fin_defl_inverse)
    apply (rule chainE [OF chain_approx])
    done
  have "cast\<cdot>(\<Squnion>i. defl_principal (Abs_fin_defl (a i))) = ID"
    apply (simp add: contlub_cfun_arg chain_a)
    apply (simp add: cast_defl_principal Abs_fin_defl_inverse)
    done
  thus ?thesis ..
qed

definition ID_defl :: "'a::bifinite defl"
  where "ID_defl = (THE d. cast\<cdot>d = ID)"

lemma cast_ID_defl [simp]: "cast\<cdot>ID_defl = ID"
unfolding ID_defl_def
apply (rule theI')
apply (rule ex_ex1I [OF ID_defl_exists])
apply (rule cast_eq_imp_eq, simp)
done

lemma below_ID_defl [simp]: "d \<sqsubseteq> ID_defl"
apply (rule cast_below_imp_below)
apply (simp add: cast.below_ID)
done

lemmas meet_defl_rules =
  meet_defl_greatest
  meet_defl_below1 [THEN below_trans]
  meet_defl_below2 [THEN below_trans]

lemma meet_defl_ID_defl: "meet_defl\<cdot>ID_defl\<cdot>d = d"
by (fast intro: below_antisym meet_defl_rules below_ID_defl)

lemma meet_defl_commute: "meet_defl\<cdot>x\<cdot>y = meet_defl\<cdot>y\<cdot>x"
by (fast intro: below_antisym meet_defl_rules)

lemma meet_defl_assoc:
  "meet_defl\<cdot>x\<cdot>(meet_defl\<cdot>y\<cdot>z) = meet_defl\<cdot>(meet_defl\<cdot>x\<cdot>y)\<cdot>z"
by (fast intro: below_antisym meet_defl_rules)

subsection {* Finite infima for deflations *}

definition fin_Inf_defl :: "'a defl set \<Rightarrow> 'a defl"
  where "fin_Inf_defl = fold (\<lambda>x y. meet_defl\<cdot>x\<cdot>y) ID_defl"

lemma fin_Inf_defl_empty [simp]: "fin_Inf_defl {} = ID_defl"
unfolding fin_Inf_defl_def by simp

lemma fin_Inf_defl_insert [simp]:
  assumes "finite A"
  shows "fin_Inf_defl (insert x A) = meet_defl\<cdot>x\<cdot>(fin_Inf_defl A)"
unfolding fin_Inf_defl_def
apply (rule comp_fun_idem.fold_insert_idem [OF _ assms])
apply (default, unfold o_def)
apply (fast intro: below_antisym meet_defl_rules)+
done

lemma fin_Inf_defl_below:
  "\<lbrakk>finite A; x \<in> A\<rbrakk> \<Longrightarrow> fin_Inf_defl A \<sqsubseteq> x"
apply (induct A set: finite, simp_all)
apply (erule disjE)
apply (simp add: meet_defl_below1)
apply (simp add: meet_defl_below2 [THEN below_trans])
done

lemma below_fin_Inf_defl:
  "\<lbrakk>finite A; \<And>y. y \<in> A \<Longrightarrow> x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> fin_Inf_defl A"
by (induct A set: finite, simp_all add: meet_defl_greatest)

subsection {* Arbitrary infima for deflations *}

definition Inf_defl :: "'a defl set \<Rightarrow> 'a defl"
  where "Inf_defl S = defl.extension (\<lambda>a. fin_Inf_defl
    (image (\<lambda>x. meet_defl\<cdot>(defl_principal a)\<cdot>x) S))\<cdot>ID_defl"

lemma Inf_defl_lemma1:
  "finite (image (\<lambda>x. meet_defl\<cdot>(defl_principal a)\<cdot>x) S)"
apply (rule finite_subset [where B="{y. y \<sqsubseteq> defl_principal a}"])
apply (clarify intro!: meet_defl_below1)
apply (rule finite_imageD [where f=defl_set])
apply (rule finite_subset [where B="Pow (defl_set (defl_principal a))"])
apply (clarify, erule rev_subsetD, simp add: defl_set_subset_iff)
apply (simp add: compact_iff_finite_defl_set [symmetric])
apply (rule inj_onI)
apply (simp add: set_eq_subset defl_set_subset_iff below_antisym)
done

lemma Inf_defl_lemma2:
  "a \<sqsubseteq> b \<Longrightarrow>
  fin_Inf_defl (image (\<lambda>x. meet_defl\<cdot>(defl_principal a)\<cdot>x) S) \<sqsubseteq>
  fin_Inf_defl (image (\<lambda>x. meet_defl\<cdot>(defl_principal b)\<cdot>x) S)"
apply (rule below_fin_Inf_defl [OF Inf_defl_lemma1])
apply clarsimp
apply (rule fin_Inf_defl_below [OF Inf_defl_lemma1, THEN below_trans])
apply (erule imageI)
apply (simp add: monofun_cfun)
done

lemma Inf_defl_below: "x \<in> A \<Longrightarrow> Inf_defl A \<sqsubseteq> x"
unfolding Inf_defl_def
apply (subst meet_defl_ID_defl [of x, symmetric])
apply (rule defl.obtain_principal_chain [where x="ID_defl :: 'a defl"])
apply (erule ssubst)
apply (simp add: contlub_cfun_arg contlub_cfun_fun)
apply (rule lub_mono, simp, simp)
apply (subst defl.extension_principal)
apply (erule Inf_defl_lemma2)
apply (rule fin_Inf_defl_below)
apply (rule Inf_defl_lemma1)
apply auto
done

lemma below_Inf_defl:
  assumes "\<And>y. y \<in> A \<Longrightarrow> x \<sqsubseteq> y"
  shows "x \<sqsubseteq> Inf_defl A"
unfolding Inf_defl_def
apply (subst meet_defl_ID_defl [of x, symmetric])
apply (rule defl.obtain_principal_chain [where x="ID_defl :: 'a defl"])
apply (erule ssubst)
apply (simp add: contlub_cfun_arg contlub_cfun_fun)
apply (rule lub_mono, simp, simp)
apply (subst defl.extension_principal)
apply (erule Inf_defl_lemma2)
apply (rule below_fin_Inf_defl)
apply (rule Inf_defl_lemma1)
apply (auto simp add: monofun_cfun assms)
done

subsection {* Configure domain package for deflation type *}

lemma defl_algebraic_lattice:
  fixes A :: "'a defl set" shows "\<exists>x. A <<| x"
proof
  show "A <<| Inf_defl {y. \<forall>x\<in>A. x \<sqsubseteq> y}"
    apply (rule is_lubI)
    apply (rule is_ubI)
    apply (rule below_Inf_defl, simp)
    apply (rule Inf_defl_below, simp add: is_ub_def)
    done
qed

definition defl_of :: "('a \<rightarrow> 'a) \<rightarrow> 'a defl"
  where "defl_of = (\<Lambda> f. lub {d. compact d \<and> cast\<cdot>d \<sqsubseteq> f})"

lemma defl_of_beta:
  "defl_of\<cdot>f = lub {d. compact d \<and> cast\<cdot>d \<sqsubseteq> f}"
unfolding defl_of_def
apply (rule beta_cfun)
apply (rule contI2)
apply (rule monofunI)
apply (rule is_lub_thelub_ex [OF defl_algebraic_lattice])
apply (rule is_ubI, clarify, rename_tac d)
apply (rule is_ub_thelub_ex [OF defl_algebraic_lattice])
apply (simp, erule (1) below_trans)
apply (rule is_lub_thelub_ex [OF defl_algebraic_lattice])
apply (rule is_ubI, clarify, rename_tac d)
apply (simp add: compact_below_lub_iff)
apply (erule exE, rule_tac x=i in exI)
apply (rule is_ub_thelub_ex [OF defl_algebraic_lattice])
apply simp
done

lemma defl_of_cast: "defl_of\<cdot>(cast\<cdot>d) = d"
unfolding defl_of_beta
apply (simp add: cast_below_cast)
apply (rule lub_eqI)
apply (rule is_lubI)
apply (rule is_ubI)
apply simp
apply (simp add: is_ub_def)
apply (cut_tac bifinite [where 'a="'a defl"], clarify)
apply (subgoal_tac "(\<Squnion>i. a i\<cdot>d) \<sqsubseteq> u")
apply (frule approx_chain.chain_approx)
apply (frule approx_chain.lub_approx)
apply (simp add: lub_distribs)
apply (rule lub_below)
apply (simp add: approx_chain.chain_approx)
apply (drule spec, erule mp, rule conjI)
apply (rule finite_deflation.compact)
apply (erule approx_chain.finite_deflation_approx)
apply (rule deflation.below)
apply (erule approx_chain.deflation_approx)
done

lemma defl_of_ID: "defl_of\<cdot>ID = ID_defl"
using defl_of_cast [of ID_defl] by simp

definition defl_map :: "('a \<rightarrow> 'a) \<rightarrow> ('a defl \<rightarrow> 'a defl)"
  where "defl_map = (\<Lambda> f. meet_defl\<cdot>(defl_of\<cdot>f))"

lemma defl_map_ID [domain_map_ID]: "defl_map\<cdot>ID = ID"
by (simp add: cfun_eq_iff defl_map_def defl_of_ID meet_defl_ID_defl)

lemma deflation_defl_map [domain_deflation]: "deflation (defl_map\<cdot>d)"
by (simp add: defl_map_def deflation_meet_defl)

lemma cast_defl_map_emb: "cast\<cdot>(defl_map_emb\<cdot>d) = emb oo cast\<cdot>d oo prj"
apply (induct d rule: defl.principal_induct, simp)
apply (simp add: defl_map_emb_principal cast_defl_principal)
apply (simp add: Abs_fin_defl_inverse domain.finite_deflation_e_d_p finite_deflation_Rep_fin_defl)
done

lemma cast_defl_map_prj:
  "cast\<cdot>(defl_map_prj\<cdot>d :: 'a::domain defl) =
    prj oo cast\<cdot>(meet_defl\<cdot>DEFL('a)\<cdot>d) oo emb"
apply (induct d rule: defl.principal_induct, simp)
apply (subst defl_map_prj_principal)
apply (subst cast_defl_principal)
apply (rule Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_p_d_e)
apply (rule finite_deflation_cast)
apply (simp add: compact_meet_defl2)
apply (subst emb_prj)
apply (intro monofun_cfun below_refl meet_defl_below1)
done

lemma defl_map_emb_meet_defl:
  "defl_map_emb\<cdot>(meet_defl\<cdot>x\<cdot>y) = meet_defl\<cdot>(defl_map_emb\<cdot>x)\<cdot>(defl_map_emb\<cdot>y)"
  (is "?lhs = ?rhs")
apply (rule below_antisym)
apply (rule meet_defl_greatest)
apply (simp add: ep_pair.e_below_iff [OF ep_pair_defl_map_emb_defl_map_prj])
apply (rule meet_defl_below1)
apply (simp add: ep_pair.e_below_iff [OF ep_pair_defl_map_emb_defl_map_prj])
apply (rule meet_defl_below2)
apply (rule below_trans [where y="meet_defl\<cdot>DEFL('a)\<cdot>?rhs"])
apply (intro meet_defl_greatest meet_defl_below1 meet_defl_below2)
apply (rule meet_defl_below1 [THEN below_trans])
apply (rule below_eq_trans, rule monofun_cfun_arg, rule below_ID_defl)
apply (simp add: cast_eq_imp_eq cast_defl_map_emb cast_DEFL)
apply (subst defl_map_emb_defl_map_prj [symmetric])
apply (subst ep_pair_defl_map_emb_defl_map_prj [THEN ep_pair.e_below_iff])
apply (rule meet_defl_greatest)
apply (rule below_eq_trans [OF _ defl_map_prj_defl_map_emb])
apply (rule monofun_cfun_arg, rule meet_defl_below1)
apply (rule below_eq_trans [OF _ defl_map_prj_defl_map_emb])
apply (rule monofun_cfun_arg, rule meet_defl_below2)
done

lemma isodefl_defl [domain_isodefl]:
  fixes d :: "'a \<rightarrow> 'a" assumes "isodefl d t"
  shows "isodefl (defl_map\<cdot>d) (defl_defl\<cdot>t)"
proof -
  interpret d: deflation d
    using assms by (rule isodefl_imp_deflation)
  have cast_t: "cast\<cdot>t = emb oo d oo prj"
    using assms unfolding isodefl_def .
  also have "... \<sqsubseteq> emb oo (ID::'a \<rightarrow> 'a) oo prj"
    by (intro monofun_cfun below_refl d.below_ID)
  also have "... = cast\<cdot>DEFL('a)"
    by (simp add: cast_DEFL)
  finally have below_DEFL: "t \<sqsubseteq> DEFL('a)"
    by (rule cast_below_imp_below)
  hence meet_defl_DEFL: "meet_defl\<cdot>DEFL('a)\<cdot>t = t"
    by (simp add: below_antisym meet_defl_below2 meet_defl_greatest)
  have d_eq_cast: "d = cast\<cdot>(defl_map_prj\<cdot>t)"
    using assms below_DEFL
    apply (simp add: isodefl_def)
    apply (simp add: cast_defl_map_prj cfun_eq_iff)
    apply (rule allI)
    apply (rule emb_eq_iff [THEN iffD1])
    apply (rule_tac t=x in subst [OF emb_inverse])
    apply (drule_tac x="emb\<cdot>x" in spec, erule subst)
    apply (simp only: emb_prj)
    apply (subst deflation_below_comp2 [OF deflation_cast deflation_cast])
    apply (rule monofun_cfun_arg)
    apply (rule meet_defl_below1)
    apply (subst deflation_below_comp1 [OF deflation_cast deflation_cast])
    apply (rule monofun_cfun_arg)
    apply (rule meet_defl_below1)
    apply (simp add: meet_defl_DEFL)
    done
  have defl_map_emb_defl_of_d: "defl_map_emb\<cdot>(defl_of\<cdot>d) = t"
    apply (simp add: d_eq_cast defl_of_cast)
    apply (subst defl_map_emb_defl_map_prj)
    apply (rule meet_defl_DEFL)
    done
  show "isodefl (defl_map\<cdot>d) (defl_defl\<cdot>t)"
    apply (rule isodeflI)
    apply (simp add: cast_defl_defl emb_defl_def prj_defl_def)
    apply (rule cfun_arg_cong)
    apply (simp add: defl_map_def)
    apply (subst defl_map_emb_meet_defl)
    apply (subst defl_map_emb_defl_of_d)
    apply (subst defl_map_emb_defl_map_prj)
    apply (subst meet_defl_assoc)
    apply (subst meet_defl_commute [of t "DEFL('a)"])
    apply (simp add: meet_defl_DEFL)
    done
qed

setup {* Domain_Take_Proofs.add_rec_type (@{type_name "defl"}, [true]) *}

subsection {* A deflation constructor for dependent strict function space *}

definition strict_pi_defl :: "'a defl \<rightarrow> ('a \<rightarrow> 'b defl) \<rightarrow> ('a \<rightarrow>! 'b) defl"
  where "strict_pi_defl = (\<Lambda> A B. defl.extension (\<lambda>a. defl.extension (\<lambda>b.
    defl_principal (Abs_fin_defl (\<Lambda> f. sfun_abs\<cdot>(\<Lambda> x.
      cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>
        (sfun_rep\<cdot>f\<cdot>(Rep_fin_defl a\<cdot>x))))))\<cdot>ID_defl)\<cdot>A)"

lemma Abs_fin_defl_mono:
  "\<lbrakk>finite_deflation a; finite_deflation b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow>
    Abs_fin_defl a \<sqsubseteq> Abs_fin_defl b"
by (simp add: below_fin_defl_def Abs_fin_defl_inverse)

lemma finite_deflation_downward:
  "\<lbrakk>finite_deflation f; deflation d; d \<sqsubseteq> f\<rbrakk> \<Longrightarrow> finite_deflation d"
apply (rule finite_deflation_intro, assumption)
apply (rule rev_finite_subset)
apply (erule finite_deflation.finite_fixes)
apply (clarify)
apply (drule finite_deflation_imp_deflation)
apply (erule (2) deflation.belowD)
done

lemma cont2cont_Abs_fin_defl:
  assumes 1: "\<And>x. finite_deflation (f x)"
  assumes 2: "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. defl_principal (Abs_fin_defl (f x)))"
apply (rule contI2)
apply (rule monofunI)
apply (rule defl.principal_mono)
apply (rule Abs_fin_defl_mono [OF 1 1])
apply (erule cont2monofunE [OF 2])
apply (simp add: compact_below_lub_iff)
apply (simp add: below_fin_defl_def Abs_fin_defl_inverse 1)
apply (rule compactD2)
apply (rule finite_deflation_imp_compact [OF 1])
apply (erule ch2ch_cont [OF 2])
apply (simp add: cont2contlubE [OF 2])
done

lemma Rep_fin_defl_strict [simp]: "Rep_fin_defl a\<cdot>\<bottom> = \<bottom>"
using deflation_Rep_fin_defl by (rule deflation_strict)

lemma cast_strict_pi_defl:
  fixes A :: "'a defl" and B :: "'a \<rightarrow> 'b defl"
  shows "cast\<cdot>(strict_pi_defl\<cdot>A\<cdot>B) =
    (\<Lambda> f. sfun_abs\<cdot>(\<Lambda> x. cast\<cdot>(B\<cdot>(cast\<cdot>A\<cdot>x))\<cdot>(sfun_rep\<cdot>f\<cdot>(cast\<cdot>A\<cdot>x))))"
proof -
  obtain Y :: "nat \<Rightarrow> 'b fin_defl" where
    Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)" and ID: "ID_defl = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  have chain: "chain (\<lambda>i. defl_principal (Y i))"
    by (simp add: chainI Y)
  have 1: "\<And>a b B. finite_deflation (\<Lambda> f. sfun_abs\<cdot>(\<Lambda> x.
               cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>
               (sfun_rep\<cdot>f\<cdot>(Rep_fin_defl a\<cdot>x))))"
    apply (rule_tac f="sfun_map\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b)" in
      finite_deflation_downward)
    apply (intro finite_deflation_sfun_map finite_deflation_Rep_fin_defl)
    apply (rule deflation.intro)
    apply (simp add: Rep_fin_defl.idem strictify_cancel)
    apply (simp add: sfun_below_iff strictify_cancel)
    apply (rule cfun_belowI, simp, rename_tac f x)
    apply (rule below_trans [OF cast.below])
    apply (rule monofun_cfun_arg)
    apply (rule Rep_fin_defl.below)
    apply (simp add: sfun_map_def)
    apply (rule cfun_belowI)
    apply (simp add: sfun_below_iff strictify_cancel)
    apply (rule cfun_belowI, simp, rename_tac f x)
    apply (rule monofun_cfun_fun)
    apply (subst cast_defl_principal [symmetric], rule monofun_cfun_arg)
    apply (rule meet_defl_below1)
    done
  note mono_rules =
       cont2cont_LAM cont2cont defl.cont_extension
       cont2cont_Abs_fin_defl [OF 1] defl.extension_mono monofun_cfun
       defl.principal_mono Abs_fin_defl_mono [OF 1 1] monofun_LAM
       below_refl Rep_fin_defl_mono Y [rule_format]
  show ?thesis
  unfolding strict_pi_defl_def
    apply (subst beta_cfun)
    apply (simp only: mono_rules)
    apply (subst beta_cfun)
    apply (simp only: mono_rules)
    apply (induct A rule: defl.principal_induct, simp)
    apply (subst defl.extension_principal)
    apply (simp only: mono_rules)
    apply (subst ID)
    apply (subst contlub_cfun_arg [OF chain])
    apply (subst defl.extension_principal)
    apply (simp only: mono_rules)
    apply (subst contlub_cfun_arg, rule chainI)
    apply (simp only: mono_rules)
    apply (simp add: cast_defl_principal Abs_fin_defl_inverse 1)
    apply (subst lub_LAM, rule chainI)
    apply (simp only: mono_rules, simp)
    apply (subst lub_APP, simp, rule chainI, simp only: mono_rules)
    apply (subst lub_LAM, rule chainI)
    apply (simp only: mono_rules, simp)
    apply (simp only: lub_distribs chainI mono_rules lub_const)
    apply (simp add: ID [symmetric] meet_defl_ID_defl)
    done
qed

subsection {* A deflation constructor for dependent function space *}

definition pi_defl :: "'a defl \<rightarrow> ('a \<rightarrow> 'b defl) \<rightarrow> ('a \<rightarrow> 'b) defl"
  where "pi_defl = (\<Lambda> A B. defl_fun1 decode_cfun encode_cfun ID\<cdot>
    (strict_pi_defl\<cdot>(defl_fun1 ID ID u_map\<cdot>A)\<cdot>(fup\<cdot>B)))"

lemma cast_pi_defl:
  fixes A :: "'a defl" and B :: "'a \<rightarrow> 'b defl"
  shows "cast\<cdot>(pi_defl\<cdot>A\<cdot>B) = (\<Lambda> f x. cast\<cdot>(B\<cdot>(cast\<cdot>A\<cdot>x))\<cdot>(f\<cdot>(cast\<cdot>A\<cdot>x)))"
apply (simp add: pi_defl_def)
apply (simp add: cast_defl_fun1 ep_pair_def
  cast_strict_pi_defl finite_deflation_u_map)
apply (simp add: decode_cfun_def encode_cfun_def cfun_eq_iff)
done

subsection {* A deflation constructor for dependent pairs *}

definition sig_defl :: "'a defl \<rightarrow> ('a \<rightarrow> 'b defl) \<rightarrow> ('a \<times> 'b) defl"
  where "sig_defl = (\<Lambda> A B. defl.extension (\<lambda>a. defl.extension (\<lambda>b.
  defl_principal (Abs_fin_defl (\<Lambda> (x, y). (Rep_fin_defl a\<cdot>x,
  cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>y))))\<cdot>ID_defl)\<cdot>A)"

lemma cast_sig_defl:
  fixes A :: "'a defl" and B :: "'a \<rightarrow> 'b defl"
  shows "cast\<cdot>(sig_defl\<cdot>A\<cdot>B) = (\<Lambda>(x, y). (cast\<cdot>A\<cdot>x, cast\<cdot>(B\<cdot>(cast\<cdot>A\<cdot>x))\<cdot>y))"
proof -
  obtain Y :: "nat \<Rightarrow> 'b fin_defl" where
    Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)" and ID: "ID_defl = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  have 1: "\<And>a b B. finite_deflation (\<Lambda> (x, y).
               (Rep_fin_defl a\<cdot>x,
                cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>
                y))"
    apply (rule_tac f="prod_map\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b)" in
      finite_deflation_downward)
    apply (intro finite_deflation_prod_map finite_deflation_Rep_fin_defl)
    apply (rule deflation.intro)
    apply (clarsimp simp add: Rep_fin_defl.idem)
    apply (clarsimp simp add: Rep_fin_defl.below cast.below)
    apply (rule cfun_belowI, clarsimp)
    apply (rule monofun_cfun_fun)
    apply (subst cast_defl_principal [symmetric], rule monofun_cfun_arg)
    apply (rule meet_defl_below1)
    done
  note mono_rules =
       cont2cont_LAM cont2cont defl.cont_extension
       cont2cont_Abs_fin_defl [OF 1] defl.extension_mono monofun_cfun
       defl.principal_mono Abs_fin_defl_mono [OF 1 1] monofun_LAM
       below_refl Rep_fin_defl_mono monofun_pair Y [rule_format]
  show ?thesis
  unfolding sig_defl_def
    apply (subst beta_cfun, simp only: mono_rules)
    apply (subst beta_cfun, simp only: mono_rules)
    apply (induct A rule: defl.principal_induct, simp)
    apply (subst defl.extension_principal)
    apply (simp only: mono_rules)
    apply (subst ID)
    apply (subst contlub_cfun_arg, simp add: Y)
    apply (subst defl.extension_principal)
    apply (simp only: mono_rules)
    apply (subst contlub_cfun_arg, rule chainI)
    apply (intro mono_rules)
    apply (simp add: cast_defl_principal Abs_fin_defl_inverse 1)
    apply (simp only: lub_distribs lub_Pair chainI mono_rules lub_const)
    apply (simp add: ID [symmetric] meet_defl_ID_defl)
    done
qed

subsection {* Deflations on strict products *}

definition sprod_of_prod_defl :: "('a \<times> 'b) defl \<rightarrow> ('a \<otimes> 'b) defl"
  where "sprod_of_prod_defl = defl.extension (\<lambda>d.
    defl_principal (Abs_fin_defl ((\<Lambda>(x, y). (:x, y:)) oo
      Rep_fin_defl d oo (\<Lambda>(:x, y:). (x, y)))))"

lemma cast_sprod_of_prod_defl_lemma:
  assumes "finite_deflation d"
  shows "finite_deflation ((\<Lambda>(x, y). (:x, y:)) oo d oo (\<Lambda>(:x, y:). (x, y)))"
proof -
  interpret d: finite_deflation d by fact
  have d_bottom [simp]: "d\<cdot>\<bottom> = \<bottom>"
    by (rule deflation_strict) fact
  show ?thesis
    apply default
    apply (case_tac x, simp, rename_tac a b)
    apply (case_tac "d\<cdot>(a, b)", rename_tac u v)
    apply (case_tac "u = \<bottom>", simp)
    apply (case_tac "v = \<bottom>", simp)
    apply (cut_tac x="(a, b)" in d.idem, simp)
    apply (case_tac x, simp, rename_tac a b)
    apply (case_tac "d\<cdot>(a, b)", rename_tac u v)
    apply (cut_tac x="(a, b)" in d.below, simp add: monofun_cfun)
    apply (rule finite_range_imp_finite_fixes)
    apply simp
    apply (subst range_composition [where f="Rep_cfun (\<Lambda>(x, y). (:x, y:))"])
    apply (rule finite_imageI)
    apply (rule rev_finite_subset [OF d.finite_range])
    apply auto
    done
qed

lemma cast_sprod_of_prod_defl:
  "cast\<cdot>(sprod_of_prod_defl\<cdot>d) =
    (\<Lambda>(x, y). (:x, y:)) oo cast\<cdot>d oo (\<Lambda>(:x, y:). (x, y))"
unfolding sprod_of_prod_defl_def
apply (induct d rule: defl.principal_induct, simp)
apply (subst defl.extension_principal)
apply (simp only: defl.principal_mono Abs_fin_defl_mono monofun_cfun
  below_refl Rep_fin_defl_mono cast_sprod_of_prod_defl_lemma
  finite_deflation_Rep_fin_defl)
apply (simp add: cast_defl_principal Abs_fin_defl_inverse
  cast_sprod_of_prod_defl_lemma finite_deflation_Rep_fin_defl)
done

end
