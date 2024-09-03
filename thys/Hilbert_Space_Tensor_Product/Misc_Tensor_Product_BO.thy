section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports
    Complex_Bounded_Operators.Complex_L2
    Misc_Tensor_Product  
    "HOL-Library.Function_Algebras" 
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

instance cblinfun :: (chilbert_space,chilbert_space) ordered_comm_monoid_add
  by intro_classes

lemma rank1_scaleR[simp]: \<open>rank1 (c *\<^sub>R a)\<close> if \<open>rank1 a\<close> and \<open>c \<noteq> 0\<close>
  by (simp add: rank1_scaleC scaleR_scaleC that(1) that(2))

lemma rank1_butterfly[simp]: \<open>rank1 (butterfly x y)\<close>
  apply (cases \<open>y = 0\<close>)
  by (auto intro: exI[of _ 0] simp: rank1_def butterfly_is_rank1)

definition \<open>cfinite_dim S \<longleftrightarrow> (\<exists>B. finite B \<and> S \<subseteq> cspan B)\<close>

lemma cfinite_dim_subspace_has_basis:
  assumes \<open>cfinite_dim S\<close> and \<open>csubspace S\<close>
  shows \<open>\<exists>B. finite B \<and> cindependent B \<and> cspan B = S\<close>
proof -
  from \<open>csubspace S\<close>
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    apply (rule_tac complex_vector.maximal_independent_subset[where V=S])
    using complex_vector.span_subspace by blast
  from \<open>cfinite_dim S\<close>
  obtain C where \<open>finite C\<close> and \<open>S \<subseteq> cspan C\<close>
    using cfinite_dim_def by auto
  from \<open>cspan B = S\<close> and \<open>S \<subseteq> cspan C\<close>
  have \<open>B \<subseteq> cspan C\<close>
    using complex_vector.span_superset by force
  from \<open>finite C\<close> \<open>cindependent B\<close> this
  have \<open>finite B\<close>
    by (rule complex_vector.independent_span_bound[THEN conjunct1])
  from this and \<open>cindependent B\<close> and \<open>cspan B = S\<close>
  show ?thesis
    by auto
qed

lemma cfinite_dim_subspace_has_onb:
  assumes \<open>cfinite_dim S\<close> and \<open>csubspace S\<close>
  shows \<open>\<exists>B. finite B \<and> is_ortho_set B \<and> cspan B = S \<and> (\<forall>x\<in>B. norm x = 1)\<close>
proof -
  from assms
  obtain C where \<open>finite C\<close> and \<open>cindependent C\<close> and \<open>cspan C = S\<close>
    using cfinite_dim_subspace_has_basis by blast
  obtain B where \<open>finite B\<close> and \<open>is_ortho_set B\<close> and \<open>cspan B = cspan C\<close>
    and norm: \<open>x \<in> B \<Longrightarrow> norm x = 1\<close> for x
    using orthonormal_basis_of_cspan[OF \<open>finite C\<close>]
    by blast
  with \<open>cspan C = S\<close> have \<open>cspan B = S\<close>
    by simp
  with \<open>finite B\<close> and \<open>is_ortho_set B\<close> and norm
  show ?thesis
    by blast
qed

lemma cspan_finite_dim[intro]: \<open>cfinite_dim (cspan B)\<close> if \<open>finite B\<close>
  using cfinite_dim_def that by auto

lift_definition finite_dim_ccsubspace :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> bool\<close> is cfinite_dim.

lemma ccspan_finite_dim[intro]: \<open>finite_dim_ccsubspace (ccspan B)\<close> if \<open>finite B\<close>
  using ccspan_finite finite_dim_ccsubspace.rep_eq that by fastforce

lemma compact_scaleC:
  fixes s :: "'a::complex_normed_vector set"
  assumes "compact s"
  shows "compact (scaleC c ` s)"
  by (auto intro!: compact_continuous_image assms continuous_at_imp_continuous_on)

lemma Proj_nearest:
  assumes \<open>x \<in> space_as_set S\<close>
  shows \<open>dist (Proj S m) m \<le> dist x m\<close>
proof -
  have \<open>is_projection_on (Proj S) (space_as_set S)\<close>
    by (simp add: Proj.rep_eq)
  then have \<open>is_arg_min (\<lambda>x. dist x m) (\<lambda>x. x \<in> space_as_set S) (Proj S m)\<close>
    by (simp add: is_projection_on_def)
  with assms show ?thesis
    by (auto simp: is_arg_min_def)
qed

lemma norm_cblinfun_bound_unit:
  assumes \<open>b \<ge> 0\<close>
  assumes \<open>\<And>\<psi>. norm \<psi> = 1 \<Longrightarrow> norm (a *\<^sub>V \<psi>) \<le> b\<close>
  shows \<open>norm a \<le> b\<close>
proof (rule norm_cblinfun_bound)
  from assms show \<open>b \<ge> 0\<close> by simp
  fix x
  show \<open>norm (a *\<^sub>V x) \<le> b * norm x\<close>
  proof (cases \<open>x = 0\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    have \<open>norm (a *\<^sub>V x) = norm (a *\<^sub>V (norm x *\<^sub>C sgn x))\<close>
      by simp
    also have \<open>\<dots> = norm (a *\<^sub>V sgn x) * norm x\<close>
      by (simp add: cblinfun.scaleC_right del: norm_scaleC_sgn)
    also have \<open>\<dots> \<le> (b * norm (sgn x)) * norm x\<close>
      by (simp add: assms(2) norm_sgn)
    also have \<open>\<dots> = b * norm x\<close>
      by (simp add: norm_sgn)
    finally show ?thesis 
      by -
  qed
qed



lemma cblinfun_norm_is_Sup_cinner:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.2.13\<close>
fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes Aselfadj: \<open>selfadjoint A\<close>
  shows \<open>is_Sup ((\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))) ` {\<psi>. norm \<psi> = 1}) (norm A)\<close>
proof (rule is_SupI)
  fix b assume \<open>b \<in> (\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))) ` {\<psi>. norm \<psi> = 1}\<close>
  then obtain \<psi> where \<open>norm \<psi> = 1\<close> and b_\<psi>: \<open>b = cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))\<close>
    by blast
  have \<open>b \<le> norm (A \<psi>)\<close>
    using b_\<psi> \<open>norm \<psi> = 1\<close>
    by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right2)
  also have \<open>\<dots> \<le> norm A\<close>
    using \<open>norm \<psi> = 1\<close> 
    by (metis mult_cancel_left2 norm_cblinfun)
  finally show \<open>b \<le> norm A\<close>
    by -
next
  fix c assume asm: \<open>(\<And>b. b \<in> (\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C A \<psi>)) ` {\<psi>. norm \<psi> = 1} \<Longrightarrow> b \<le> c)\<close>
  have c_upper: \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<le> c\<close> if \<open>norm \<psi> = 1\<close> for \<psi>
    using that using asm[of \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))\<close>] by auto
  have \<open>c \<ge> 0\<close>
    by (smt (z3) ex_norm1_not_singleton c_upper norm_ge_zero)
  have *: \<open>Re (g \<bullet>\<^sub>C A h) \<le> c\<close> if \<open>norm g = 1\<close> and \<open>norm h = 1\<close> for g h
  proof -
    have c_upper': \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<le> c * (norm \<psi>)\<^sup>2\<close> for \<psi>
      apply (cases \<open>\<psi> = 0\<close>, simp)
      apply (subst (2) norm_scaleC_sgn[symmetric, of \<psi>])
      apply (subst norm_scaleC_sgn[symmetric])
      apply (simp only: cinner_scaleC_left cinner_scaleC_right cblinfun.scaleC_right)
      using c_upper[of \<open>sgn \<psi>\<close>]
      by (simp add: norm_mult norm_sgn power2_eq_square)
    from Aselfadj have 1: \<open>(h + g) \<bullet>\<^sub>C A (h + g) = h \<bullet>\<^sub>C A h + 2 * Re (g \<bullet>\<^sub>C A h) + g \<bullet>\<^sub>C A g\<close>
      apply (auto intro!: simp: cinner_add_right cinner_add_left cblinfun.add_right selfadjoint_def)
      apply (subst cinner_commute[of h])
      by (metis cinner_adj_right complex_add_cnj mult_2 of_real_add)
    from Aselfadj have 2: \<open>(h - g) \<bullet>\<^sub>C A (h - g) = h \<bullet>\<^sub>C A h - 2 * Re (g \<bullet>\<^sub>C A h) + g \<bullet>\<^sub>C A g\<close>
      apply (auto intro!: simp: cinner_diff_right cinner_diff_left cblinfun.diff_right selfadjoint_def)
      apply (subst cinner_commute[of h])
      by (metis cinner_adj_right complex_add_cnj minus_add_distrib mult_2 of_real_add uminus_add_conv_diff)
    have \<open>4 * Re (g \<bullet>\<^sub>C A h) = Re ((h + g) \<bullet>\<^sub>C A (h + g)) - Re ((h - g) \<bullet>\<^sub>C A (h - g))\<close>
      by (smt (verit, ccfv_SIG) "1" "2" Re_complex_of_real minus_complex.simps(1) plus_complex.sel(1))
    also
    have \<open>\<dots> \<le> c * (norm (h + g))\<^sup>2 - Re ((h - g) \<bullet>\<^sub>C A (h - g))\<close>
      using c_upper'[of \<open>h + g\<close>]
      by (smt (verit, best) complex_Re_le_cmod)
    also have \<open>\<dots> \<le> c * (norm (h + g))\<^sup>2 + c * (norm (h - g))\<^sup>2\<close>
      unfolding diff_conv_add_uminus
      apply (rule add_left_mono)
      using c_upper'[of \<open>h - g\<close>]
      by (smt (verit) abs_Re_le_cmod add_uminus_conv_diff)
    also have \<open>\<dots> = 2 * c * ((norm h)\<^sup>2 + (norm g)\<^sup>2)\<close>
      by (auto intro!: simp: polar_identity polar_identity_minus ring_distribs)
    also have \<open>\<dots> \<le> 4 * c\<close>
      by (simp add: \<open>norm h = 1\<close> \<open>norm g = 1\<close>)
    finally show \<open>Re (g \<bullet>\<^sub>C (A *\<^sub>V h)) \<le> c\<close>
      by simp
  qed      
  have *: \<open>cmod (g \<bullet>\<^sub>C A h) \<le> c\<close> if \<open>norm g = 1\<close> and \<open>norm h = 1\<close> for g h
  proof -
    define \<gamma> where \<open>\<gamma> = (if g \<bullet>\<^sub>C A h = 0 then 1 else sgn (g \<bullet>\<^sub>C A h))\<close>
    have \<gamma>: \<open>\<gamma> * cmod (g \<bullet>\<^sub>C A h) = g \<bullet>\<^sub>C A h\<close>
      by (simp add: \<gamma>_def sgn_eq)
    have \<open>norm \<gamma> = 1\<close>
      by (simp add: \<gamma>_def norm_sgn)
    have \<open>cmod (g \<bullet>\<^sub>C A h) = Re (complex_of_real (norm (g \<bullet>\<^sub>C A h)))\<close>
      by simp
    also have \<open>\<dots> = Re (g \<bullet>\<^sub>C (A (h /\<^sub>C \<gamma>)))\<close>
      using \<gamma> \<open>cmod \<gamma> = 1\<close>
      by (smt (verit) Groups.mult_ac(2) Groups.mult_ac(3) cblinfun.scaleC_right cinner_scaleC_right left_inverse more_arith_simps(6) norm_eq_zero)
    also have \<open>\<dots> \<le> c\<close>
      using \<open>norm \<gamma> = 1\<close>
      by (auto intro!: * simp: that norm_inverse)
    finally show \<open>cmod (g \<bullet>\<^sub>C (A *\<^sub>V h)) \<le> c\<close>
      by -
  qed
  have \<open>norm (A h) \<le> c\<close> if \<open>norm h = 1\<close> for h
    apply (cases \<open>A h = 0\<close>, simp add: \<open>0 \<le> c\<close>)
    using *[OF _ that, of \<open>sgn (A h)\<close>]
    by (simp add: norm_sgn)
  then show \<open>norm A \<le> c\<close>
    using \<open>c \<ge> 0\<close> by (auto intro!: norm_cblinfun_bound_unit)
qed

lemma cblinfun_norm_approx_witness_cinner:
  fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>selfadjoint A\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
  using is_Sup_approx_below[OF cblinfun_norm_is_Sup_cinner[OF assms(1)] assms(2)]
  by blast

lemma cblinfun_norm_approx_witness_cinner':
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>selfadjoint A\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. cmod (\<psi> \<bullet>\<^sub>C A \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>cmod (\<psi> \<bullet>\<^sub>C A \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using chilbert_space_axioms True assms
    by (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
  then have \<open>cmod (\<psi> \<bullet>\<^sub>C A \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma has_sum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms 
  have sum_hfh: \<open>((\<lambda>x. h \<bullet>\<^sub>C f x h) has_sum h \<bullet>\<^sub>C a h) A\<close> for h
    by (intro has_sum_cinner_left has_sum_cblinfun_apply_left)
  from assms
  have sum_hgh: \<open>((\<lambda>x. h \<bullet>\<^sub>C g x h) has_sum h \<bullet>\<^sub>C b h) B\<close> for h
    by (intro has_sum_cinner_left has_sum_cblinfun_apply_left)
  from sum_hfh sum_hgh
  have \<open>h \<bullet>\<^sub>C a h \<le> h \<bullet>\<^sub>C b h\<close> for h
    apply (rule has_sum_mono_neutral_complex)
    using assms
    by (auto intro!: simp: less_eq_cblinfun_def)
  then show \<open>a \<le> b\<close>
    by (simp add: less_eq_cblinfun_def)
qed

lemma sums_mono_cblinfun:
  fixes f :: "nat \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>f sums a\<close> and "g sums b"
  assumes \<open>\<And>n. f n \<le> g n\<close>
  shows "a \<le> b"
proof (rule cblinfun_leI)
  fix h
  from \<open>f sums a\<close>
  have sum1: \<open>(\<lambda>n. h \<bullet>\<^sub>C (f n *\<^sub>V h)) sums (h \<bullet>\<^sub>C (a *\<^sub>V h))\<close>
    apply (rule bounded_linear.sums[rotated])
    using bounded_clinear.bounded_linear bounded_clinear_cinner_right bounded_linear_compose cblinfun.real.bounded_linear_left by blast 
  from \<open>g sums b\<close>
  have sum2: \<open>(\<lambda>n. h \<bullet>\<^sub>C (g n *\<^sub>V h)) sums (h \<bullet>\<^sub>C (b *\<^sub>V h))\<close>
    apply (rule bounded_linear.sums[rotated])
    by (metis bounded_linear_compose cblinfun.real.bounded_linear_left cblinfun.real.bounded_linear_right cblinfun_cinner_right.rep_eq) 
  have \<open>h \<bullet>\<^sub>C (f n *\<^sub>V h) \<le> h \<bullet>\<^sub>C (g n *\<^sub>V h)\<close> for n
    using assms(3) less_eq_cblinfun_def by auto 
  with sum1 sum2
  show \<open>h \<bullet>\<^sub>C (a *\<^sub>V h) \<le> h \<bullet>\<^sub>C (b *\<^sub>V h)\<close>
    by (rule sums_le_complex[rotated])
qed

lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)


lemma sandwich_scaleC_left: \<open>sandwich (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich e\<close>
  by (auto intro!: cblinfun_eqI simp: sandwich_apply cnj_x_x abs_complex_def)

lemma sandwich_scaleR_left: \<open>sandwich (r *\<^sub>R e) = r^2 *\<^sub>R sandwich e\<close>
  by (simp add: scaleR_scaleC sandwich_scaleC_left flip: of_real_power)

lemma infsum_product:
  fixes f :: \<open>'a \<Rightarrow> 'c :: {topological_semigroup_mult,division_ring,banach}\<close>
  assumes \<open>(\<lambda>(x, y). f x * g y) summable_on X \<times> Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: infsum_cmult_right' infsum_cmult_left' flip: infsum_Sigma'_banach)

lemma infsum_product':
  fixes f :: \<open>'a \<Rightarrow> 'c :: {banach,times,real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>f abs_summable_on X\<close>
  assumes \<open>g abs_summable_on Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: abs_summable_times infsum_cmult_right infsum_cmult_left abs_summable_summable flip: infsum_Sigma'_banach)

lemma Proj_o_Proj_subspace_right:
  assumes \<open>A \<ge> B\<close>
  shows \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj B\<close>
  by (simp add: Proj_compose_cancelI assms) 

lemma Proj_o_Proj_subspace_left:
  assumes \<open>A \<le> B\<close>
  shows \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj A\<close>
  by (metis Proj_o_Proj_subspace_right adj_Proj adj_cblinfun_compose assms) 

lemma orthogonal_spaces_SUP_left:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> orthogonal_spaces (A x) B\<close>
  shows \<open>orthogonal_spaces (\<Squnion>x\<in>X. A x) B\<close>
  by (meson SUP_least assms orthogonal_spaces_leq_compl) 

lemma orthogonal_spaces_SUP_right:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> orthogonal_spaces A (B x)\<close>
  shows \<open>orthogonal_spaces A (\<Squnion>x\<in>X. B x)\<close>
  by (meson assms orthogonal_spaces_SUP_left orthogonal_spaces_sym) 

(* Should be put next to orthogonal_bot *)
lemma orthogonal_bot_left[simp]: \<open>orthogonal_spaces bot S\<close>
  by (simp add: orthogonal_spaces_def)

lemma infsum_bounded_linear_invertible:
  assumes \<open>bounded_linear h\<close>
  assumes \<open>bounded_linear h'\<close>
  assumes \<open>h' o h = id\<close>
  shows \<open>infsum (\<lambda>x. h (f x)) A = h (infsum f A)\<close>
proof (cases \<open>f summable_on A\<close>)
  case True
  then show ?thesis
    using assms(1) infsum_bounded_linear by blast
next
  case False
  have \<open>\<not> (\<lambda>x. h (f x)) summable_on A\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> (\<lambda>x. h (f x)) summable_on A\<close>
    with \<open>bounded_linear h'\<close> have \<open>h' o h o f summable_on A\<close>
      by (auto intro: summable_on_bounded_linear simp: o_def)
    then have \<open>f summable_on A\<close>
      by (simp add: assms(3))
    with False show False
      by blast
  qed
  then show ?thesis
    by (simp add: False assms(1) infsum_not_exists linear_simps(3))
qed

lemma cblinfun_eq_from_separatingI:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> a x = b x\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma cblinfun_eq_from_separatingI2:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> a (h x y) = b (h x y)\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI2)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma separating_set_bounded_clinear_dense:
  assumes \<open>ccspan S = \<top>\<close>
  shows \<open>separating_set bounded_clinear S\<close>
  using assms
  apply (auto intro!: ext simp: separating_set_def)
  apply (rule bounded_clinear_eq_on_closure[where G=S])
  apply auto
  using ccspan.rep_eq by force


lemma separating_set_ket: \<open>separating_set bounded_clinear (range ket)\<close>
  by (simp add: bounded_clinear_equal_ket separating_setI)

lemma separating_set_bounded_cbilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_cbilinear h\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)

  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF assms(3)])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF assms(4)])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed


lemma separating_set_bounded_clinear_antilinear:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector conjugate_space) \<Rightarrow> _) A\<close>
  shows \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume \<open>bounded_antilinear f\<close>
  then have lin_f: \<open>bounded_clinear (to_conjugate_space o f)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>bounded_antilinear g\<close>
  then have lin_g: \<open>bounded_clinear (to_conjugate_space o g)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>f x = g x\<close> if \<open>x \<in> A\<close> for x
  then have \<open>(to_conjugate_space o f) x = (to_conjugate_space o g) x\<close> if \<open>x \<in> A\<close> for x
    by (simp add: that)
  with lin_f lin_g
  have \<open>to_conjugate_space o f = to_conjugate_space o g\<close>
    by (rule eq_from_separatingI[OF assms])
  then show \<open>f = g\<close>
    by (metis UNIV_I fun.inj_map_strong to_conjugate_space_inverse)
qed

lemma separating_set_bounded_sesquilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_sesquilinear h\<close>
  assumes sep_A: \<open>separating_set (bounded_clinear :: (_ => 'e conjugate_space) \<Rightarrow> _) A\<close>
  assumes sep_B: \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_antilinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_antilinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)

  from sep_A have sep_A': \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
    by (rule separating_set_bounded_clinear_antilinear)
  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF sep_A'])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF sep_B])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed


end
