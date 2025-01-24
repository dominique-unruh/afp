theory Misc_Kraus_Maps
  imports Hilbert_Space_Tensor_Product.Trace_Class
begin

(* TODO: move to BO and Tensor as suitable. *)

unbundle cblinfun_syntax

lemma infsum_in_finite:
  assumes "finite F"
  assumes \<open>Hausdorff_space T\<close>
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "infsum_in T f F = sum f F"
  using has_sum_in_finite[OF assms(1,3)]
  using assms(2) has_sum_in_infsum_in has_sum_in_unique summable_on_in_def by blast

lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp

lemma abs_summable_on_add:
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma bdd_above_transform_mono_pos:
  assumes bdd: \<open>bdd_above ((\<lambda>x. g x) ` M)\<close>
  assumes gpos: \<open>\<And>x. x \<in> M \<Longrightarrow> g x \<ge> 0\<close>
  assumes mono: \<open>mono_on (Collect ((\<le>) 0)) f\<close>
  shows \<open>bdd_above ((\<lambda>x. f (g x)) ` M)\<close>
proof (cases \<open>M = {}\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  from bdd obtain B where B: \<open>g x \<le> B\<close> if \<open>x \<in> M\<close> for x
  by (meson bdd_above.unfold imageI)
  with gpos False have \<open>B \<ge> 0\<close>
    using dual_order.trans by blast
  have \<open>f (g x) \<le> f B\<close> if \<open>x \<in> M\<close> for x
    using mono _ _ B
    apply (rule mono_onD)
    by (auto intro!: gpos that  \<open>B \<ge> 0\<close>)
  then show ?thesis
    by fast
qed

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

lemma has_sum_Sigma'_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::banach\<close>
  assumes "((\<lambda>(x,y). f x y) has_sum S) (Sigma A B)"
  shows \<open>((\<lambda>x. infsum (f x) (B x)) has_sum S) A\<close>
  by (metis (no_types, lifting) assms has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_Sigma'_banach summable_on_Sigma_banach)

lemma is_Proj_leq_id: \<open>is_Proj P \<Longrightarrow> P \<le> id_cblinfun\<close>
  by (metis diff_ge_0_iff_ge is_Proj_algebraic is_Proj_complement positive_cblinfun_squareI)

lemma sum_butterfly_leq_id: 
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>(\<Sum>i\<in>E. butterfly i i) \<le> id_cblinfun\<close>
proof -
  have \<open>is_Proj (\<Sum>\<psi>\<in>E. butterfly \<psi> \<psi>)\<close>
    using assms by (rule sum_butterfly_is_Proj)
  then show ?thesis
    by (auto intro!: is_Proj_leq_id)
qed

lemma summable_on_in_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "summable_on_in T f A \<longleftrightarrow> summable_on_in T g A"
  by (simp add: summable_on_in_def has_sum_in_cong[OF assms])

lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

lemma infsum_in_0:
  assumes \<open>Hausdorff_space T\<close> and \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>infsum_in T f M = 0\<close>
proof -
  have \<open>has_sum_in T f M 0\<close>
    using assms
    by (auto intro!: has_sum_in_0 Hausdorff_imp_t1_space)
  then show ?thesis
    by (meson assms(1) has_sum_in_infsum_in has_sum_in_unique not_summable_infsum_in_0)
qed

lemma summable_on_in_finite:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,topological_space}\<close>
  assumes "finite F"
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "summable_on_in T f F"
  using assms summable_on_in_def has_sum_in_finite by blast

thm infsum_Sigma (* TODO compare? replace? rename? *)
lemma infsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, t3_space}\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))"
proof -
  have 1: \<open>(f has_sum infsum f (Sigma A B)) (Sigma A B)\<close>
    by (simp add: assms)
  define b where \<open>b x = (\<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))\<close> for x
  have 2: \<open>((\<lambda>y. f (x, y)) has_sum b x) (B x)\<close> if \<open>x \<in> A\<close> for x
    using b_def assms(2) that by auto
  have 3: \<open>(b has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) A\<close>
    using 1 2 by (metis has_sum_SigmaD infsumI)
  have 4: \<open>(f has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) (Sigma A B)\<close>
    using 2 3 apply (rule has_sum_SigmaI)
    using assms by auto
  from 1 4 show ?thesis
    using b_def[abs_def] infsumI by blast
qed

lemma clinear_of_complex[iff]: \<open>clinear of_complex\<close>
  by (simp add: clinearI)

lemma ballI2 [intro!]: "(\<And>x y. (x,y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x,y)\<in>A. P x y"
  by auto


lemma sandwich_butterfly: \<open>sandwich a (butterfly x y) = butterfly (a x) (a y)\<close>
  by (simp add: sandwich_apply butterfly_comp_cblinfun cblinfun_comp_butterfly)

lemma sandwich_tc_eq0_D:
  assumes eq0: \<open>\<And>\<rho>. \<rho> \<ge> 0 \<Longrightarrow> norm \<rho> \<le> B \<Longrightarrow> sandwich_tc a \<rho> = 0\<close>
  assumes Bpos: \<open>B > 0\<close>
  shows \<open>a = 0\<close>
proof (rule ccontr)
  assume \<open>a \<noteq> 0\<close>
  obtain h where \<open>a h \<noteq> 0\<close>
  proof (atomize_elim, rule ccontr)
    assume \<open>\<nexists>h. a *\<^sub>V h \<noteq> 0\<close>
    then have \<open>a h = 0\<close> for h
      by blast
    then have \<open>a = 0\<close>
      by (auto intro!: cblinfun_eqI)
    with \<open>a \<noteq> 0\<close>
    show False
      by simp
  qed
  then have \<open>h \<noteq> 0\<close>
    by force

  define k where \<open>k = sqrt B *\<^sub>R sgn h\<close>
  from \<open>a h \<noteq> 0\<close> Bpos have \<open>a k \<noteq> 0\<close>
    by (smt (verit, best) cblinfun.scaleR_right k_def linordered_field_class.inverse_positive_iff_positive real_sqrt_gt_zero scaleR_simps(7) sgn_div_norm zero_less_norm_iff)
  have \<open>norm (from_trace_class (sandwich_tc a (tc_butterfly k k))) = norm (butterfly (a k) (a k))\<close>
    by (simp add: from_trace_class_sandwich_tc tc_butterfly.rep_eq sandwich_butterfly)
  also have \<open>\<dots> = (norm (a k))\<^sup>2\<close>
    by (simp add: norm_butterfly power2_eq_square)
  also from \<open>a k \<noteq> 0\<close>
  have \<open>\<dots> \<noteq> 0\<close>
    by simp
  finally have sand_neq0: \<open>sandwich_tc a (tc_butterfly k k) \<noteq> 0\<close>
    by fastforce

  have \<open>norm (tc_butterfly k k) = B\<close>
    using \<open>h \<noteq> 0\<close> Bpos
    by (simp add: norm_tc_butterfly k_def norm_sgn)
  with sand_neq0 assms
  show False
    by simp
qed

lemma flip_eq_const: \<open>(\<lambda>y. y = x) = ((=) x)\<close>
  by auto

lemma sandwich_tc_butterfly: \<open>sandwich_tc c (tc_butterfly a b) = tc_butterfly (c a) (c b)\<close>
  by (metis from_trace_class_inverse from_trace_class_sandwich_tc sandwich_butterfly tc_butterfly.rep_eq)

lemma tc_butterfly_0_left[simp]: \<open>tc_butterfly 0 t = 0\<close>
  by (metis mult_eq_0_iff norm_eq_zero norm_tc_butterfly)

lemma tc_butterfly_0_right[simp]: \<open>tc_butterfly t 0 = 0\<close>
  by (metis mult_eq_0_iff norm_eq_zero norm_tc_butterfly)


end
