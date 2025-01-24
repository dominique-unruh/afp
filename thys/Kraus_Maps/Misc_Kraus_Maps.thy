theory Misc_Kraus_Maps
  imports Hilbert_Space_Tensor_Product.Trace_Class
begin

(* TODO: move to BO and Tensor as suitable. *)

unbundle cblinfun_syntax

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

lemma infsum_Sigma_topological_monoid:
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

lemma ballI2 [intro!]: "(\<And>x y. (x,y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x,y)\<in>A. P x y"
  by auto


lemma flip_eq_const: \<open>(\<lambda>y. y = x) = ((=) x)\<close>
  by auto

(* TODO To BO library *)
lemma vector_to_cblinfun_inj: \<open>inj_on (vector_to_cblinfun :: 'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) X\<close>
proof (rule inj_onI)
  fix x y :: 'a
  assume \<open>vector_to_cblinfun x = (vector_to_cblinfun y :: 'b \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  then have \<open>vector_to_cblinfun x (1::'b) = vector_to_cblinfun y (1::'b)\<close>
    by simp
  then show \<open>x = y\<close>
    by simp
qed

(* TODO move to BO *)
lemma has_sum_bounded_clinear:
  assumes "bounded_clinear h" and "(f has_sum S) A"
  shows "((\<lambda>x. h (f x)) has_sum h S) A"
  apply (rule has_sum_bounded_linear[where h=h])
  by (auto intro!: bounded_clinear.bounded_linear assms)

(* TODO move to BO, after *) thm infsum_scaleC_right
lemma has_sum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes \<open>(f has_sum s) A\<close>
  shows \<open>((\<lambda>x. c *\<^sub>C f x) has_sum c *\<^sub>C s) A\<close>
  apply (rule has_sum_bounded_clinear[where h=\<open>(*\<^sub>C) c\<close>])
  using bounded_clinear_scaleC_right assms by auto



end
