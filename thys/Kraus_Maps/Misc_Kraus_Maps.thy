theory Misc_Kraus_Maps
  imports
    Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product
    Hilbert_Space_Tensor_Product.Von_Neumann_Algebras
begin

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

lemma flip_eq_const: \<open>(\<lambda>y. y = x) = ((=) x)\<close>
  by auto

(* TODO to Complex_Bounded_Operators *)
lemma sgn_ket[simp]: \<open>sgn (ket x) = ket x\<close>
  by (simp add: sgn_div_norm)

(* TODO to Hilbert_Space_Tensor_Product *)
lemma tensor_op_in_tensor_vn:
  assumes \<open>a \<in> A\<close> and \<open>b \<in> B\<close>
  shows \<open>a \<otimes>\<^sub>o b \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
proof -
  have \<open>a \<otimes>\<^sub>o id_cblinfun \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    by (metis (no_types, lifting) Un_iff assms(1) double_commutant_grows' image_iff tensor_vn_def)
  moreover have \<open>id_cblinfun \<otimes>\<^sub>o b \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    by (simp add: assms(2) double_commutant_grows' tensor_vn_def)
  ultimately have \<open>(a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o b) \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    using commutant_mult tensor_vn_def by blast
  then show ?thesis
    by (simp add: comp_tensor_op)
qed

(* TODO to Hilbert_Space_Tensor_Product *)
lemma commutant_tensor_vn_subset: 
  assumes \<open>von_neumann_algebra A\<close> and \<open>von_neumann_algebra B\<close>
  shows \<open>commutant A \<otimes>\<^sub>v\<^sub>N commutant B \<subseteq> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close>
proof -
  have 1: \<open>a \<otimes>\<^sub>o id_cblinfun \<in> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close> if \<open>a \<in> commutant A\<close> for a
    apply (simp add: tensor_vn_def)
    using that by (auto intro!: simp: commutant_def comp_tensor_op)
  have 2: \<open>id_cblinfun \<otimes>\<^sub>o b \<in> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close> if \<open>b \<in> commutant B\<close> for b
    apply (simp add: tensor_vn_def)
    using that by (auto intro!: simp: commutant_def comp_tensor_op)
  show ?thesis
    apply (subst tensor_vn_def)
    apply (rule double_commutant_in_vn_algI)
    using 1 2
    by (auto intro!: von_neumann_algebra_commutant von_neumann_algebra_tensor_vn assms)
qed

(* TODO to Hilbert_Space_Tensor_Product *)
lemma commutant_span[simp]: \<open>commutant (span X) = commutant X\<close>
proof (rule order_antisym)
  have \<open>commutant X \<subseteq> commutant (cspan X)\<close>
    by (simp add: commutant_cspan)
  also have \<open>\<dots> \<subseteq> commutant (span X)\<close>
    by (simp add: commutant_antimono span_subset_cspan)
  finally show \<open>commutant X \<subseteq> commutant (span X)\<close>
    by -
  show \<open>commutant (span X) \<subseteq> commutant X\<close>
    by (simp add: commutant_antimono span_superset)
qed


(* TODO to Complex_Bounded_Operators *)
lemma explicit_cblinfun_exists_0[simp]: \<open>explicit_cblinfun_exists (\<lambda>_ _. 0)\<close>
  by (auto intro!: explicit_cblinfun_exists_bounded[where B=0] simp: explicit_cblinfun_def)

(* TODO to Complex_Bounded_Operators *)
lemma explicit_cblinfun_0[simp]: \<open>explicit_cblinfun (\<lambda>_ _. 0) = 0\<close>
  by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: Rep_ell2_explicit_cblinfun_ket zero_ell2.rep_eq)

lemma cnj_of_bool[simp]: \<open>cnj (of_bool b) = of_bool b\<close>
  by simp

lemma has_sum_single: 
  fixes f :: \<open>_ \<Rightarrow> _::{comm_monoid_add,t2_space}\<close>
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  assumes \<open>s = (if i\<in>A then f i else 0)\<close>
  shows "HAS_SUM f A s"
  apply (subst has_sum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto

(* TODO to Complex_Bounded_Operators *)
lemma classical_operator_None[simp]: \<open>classical_operator (\<lambda>_. None) = 0\<close>
  by (auto intro!: equal_ket simp: classical_operator_ket inj_map_def classical_operator_exists_inj)

lemma has_sum_in_in_closedsubspace:
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<in> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>csubspace S\<close>
  shows \<open>l \<in> S\<close>
proof -
  from assms
  have \<open>limitin T (sum f) l (finite_subsets_at_top A)\<close>
    by (simp add: has_sum_in_def)
  then have \<open>limitin T (\<lambda>F. if F\<subseteq>A then sum f F else 0) l (finite_subsets_at_top A)\<close>
    apply (rule limitin_transform_eventually[rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by simp
  then show \<open>l \<in> S\<close>
    apply (rule limitin_closedin)
    using assms by (auto intro!: complex_vector.subspace_0 simp: complex_vector.subspace_sum subsetD)
qed


end
