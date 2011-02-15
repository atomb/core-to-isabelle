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

subsection {* A deflation constructor for dependent function space *}

definition pi_defl :: "'a defl \<rightarrow> ('a \<rightarrow> 'b defl) \<rightarrow> ('a \<rightarrow> 'b) defl"
  where "pi_defl = (\<Lambda> A B. defl.extension (\<lambda>a. defl.extension (\<lambda>b.
    defl_principal (Abs_fin_defl (\<Lambda> f x.
      cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>
        (f\<cdot>(Rep_fin_defl a\<cdot>x)))))\<cdot>ID_defl)\<cdot>A)"

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

lemma meet_defl_ID_defl: "meet_defl\<cdot>ID_defl\<cdot>d = d"
apply (rule below_antisym [OF meet_defl_below2])
apply (simp add: meet_defl_greatest)
done

text ""
(*
lemma (in ideal_completion) extension_f_principal:
  assumes f: "cont f"
  shows "extension (\<lambda>a. f (principal a))\<cdot>x = f x"
apply (induct x rule: principal_induct)
apply (simp add: f [THEN cont_compose])
apply (rule extension_principal)
apply (rule cont2monofunE [OF f])
apply (erule principal_mono)
done
*)
lemma cast_pi_defl:
  fixes A :: "'a defl" and B :: "'a \<rightarrow> 'b defl"
  shows "cast\<cdot>(pi_defl\<cdot>A\<cdot>B) = (\<Lambda> f x. cast\<cdot>(B\<cdot>(cast\<cdot>A\<cdot>x))\<cdot>(f\<cdot>(cast\<cdot>A\<cdot>x)))"
proof -
  obtain Y :: "nat \<Rightarrow> 'b fin_defl" where
    Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)" and ID: "ID_defl = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  have chain: "chain (\<lambda>i. defl_principal (Y i))"
    by (simp add: chainI Y)
  have 1: "\<And>a b B. finite_deflation (\<Lambda> f x.
               cast\<cdot>(meet_defl\<cdot>(defl_principal b)\<cdot>(B\<cdot>(Rep_fin_defl a\<cdot>x)))\<cdot>
               (f\<cdot>(Rep_fin_defl a\<cdot>x)))"
    apply (rule_tac f="cfun_map\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b)" in
      finite_deflation_downward)
    apply (intro finite_deflation_cfun_map finite_deflation_Rep_fin_defl)
    apply (rule deflation.intro)
    apply (simp add: Rep_fin_defl.idem)
    apply (rule cfun_belowI, simp, rename_tac f x)
    apply (rule below_trans [OF cast.below])
    apply (rule monofun_cfun_arg)
    apply (rule Rep_fin_defl.below)
    apply (simp add: cfun_map_def)
    apply (rule cfun_belowI, rule cfun_belowI, simp, rename_tac f x)
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
  unfolding pi_defl_def
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
    apply (subst lub_LAM, rule chainI)
    apply (simp only: mono_rules, simp)
    apply (simp only: lub_distribs chainI mono_rules lub_const)
    apply (simp add: ID [symmetric] meet_defl_ID_defl)
    done
qed

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
