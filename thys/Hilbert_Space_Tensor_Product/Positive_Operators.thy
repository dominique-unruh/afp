section \<open>\<open>Positive_Operators\<close> -- Positive bounded operators\<close>

theory Positive_Operators
  imports Tensor_Product.Misc_Tensor_Product_BO Tensor_Product.Strong_Operator_Topology
    Ordinary_Differential_Equations.Cones
begin

no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
hide_const (open) Infinite_Set_Sum.abs_summable_on
hide_fact (open) Infinite_Set_Sum.abs_summable_on_Sigma_iff

unbundle cblinfun_notation

lemma cinner_pos_if_pos: \<open>f \<bullet>\<^sub>C (A *\<^sub>V f) \<ge> 0\<close> if \<open>A \<ge> 0\<close>
  using less_eq_cblinfun_def that by force

definition sqrt_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<open>sqrt_op a = (if (\<exists>b :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a) then (SOME b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a) else 0)\<close>

lemma sqrt_op_nonpos: \<open>sqrt_op a = 0\<close> if \<open>\<not> a \<ge> 0\<close>
proof -
  have \<open>\<not> (\<exists>b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a)\<close>
    using positive_cblinfun_squareI that by blast
  then show ?thesis
    by (auto simp add: sqrt_op_def)
qed

(* lemma nonneg_quadratic_function_discriminant:
  fixes a b c :: real
  assumes \<open>a > 0\<close>
  assumes \<open>\<And>x. a * x\<^sup>2 + b * x + c \<ge> 0\<close>
  shows \<open>b\<^sup>2 - 4 * a * c \<le> 0\<close>
proof (rule ccontr)
  define D where \<open>D = b\<^sup>2 - 4 * a * c\<close>
  assume \<open>\<not> D \<le> 0\<close>
  then have \<open>D > 0\<close> by auto
  define x\<^sub>1 x\<^sub>2 x where "x\<^sub>1 = (-b + sqrt D) / (2 * a)" and "x\<^sub>2 = (-b - sqrt D) / (2 * a)"
    and \<open>x = (x\<^sub>1 + x\<^sub>2) / 2\<close>
  have \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>
    unfolding x\<^sub>1_def x\<^sub>2_def using \<open>a > 0\<close> \<open>D > 0\<close> by auto
  have \<open>a * x\<^sup>2 + b * x + c = a * (x - x\<^sub>1) * (x - x\<^sub>2)\<close>
    using D_def _ x\<^sub>1_def x\<^sub>2_def apply (rule quadratic_eq_factoring[where D=D])
    using \<open>a > 0\<close> \<open>D > 0\<close> by auto
  then have \<open>a * (x - x\<^sub>1) * (x - x\<^sub>2) \<ge> 0\<close>
    by (metis assms(2))
  then have \<open>(x - x\<^sub>1) * (x - x\<^sub>2) \<ge> 0\<close>
    by (metis assms(1) linorder_not_less ordered_field_class.sign_simps(33) ordered_field_class.sign_simps(6) zero_le_mult_iff)
  moreover from \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>
  have \<open>(x - x\<^sub>1) * (x - x\<^sub>2) < 0\<close>
    unfolding x_def
    using diff_gt_0_iff_gt mult_2 mult_less_0_iff by fastforce
  ultimately show False
    by simp
qed *)

lemma generalized_Cauchy_Schwarz:
  fixes inner A
  assumes Apos: \<open>A \<ge> 0\<close>
  defines "inner x y \<equiv> x \<bullet>\<^sub>C (A *\<^sub>V y)"
  shows \<open>complex_of_real ((norm (inner x y))\<^sup>2) \<le> inner x x * inner y y\<close>
proof (cases \<open>inner y y = 0\<close>)
  case True
  have [simp]: \<open>inner (s *\<^sub>C x) y = cnj s * inner x y\<close> for s x y
    by (simp add: assms(2))
  have [simp]: \<open>inner x (s *\<^sub>C y) = s * inner x y\<close> for s x y
    by (simp add: assms(2) cblinfun.scaleC_right)
  have [simp]: \<open>inner (x - x') y = inner x y - inner x' y\<close> for x x' y
    by (simp add: cinner_diff_left inner_def)
  have [simp]: \<open>inner x (y - y') = inner x y - inner x y'\<close> for x y y'
    by (simp add: cblinfun.diff_right cinner_diff_right inner_def)
  have Re0: \<open>Re (inner x y) = 0\<close> for x
  proof -
    have *: \<open>Re (inner x y) = (inner x y + inner y x) / 2\<close>
      by (smt (verit, del_insts) assms(1) assms(2) cinner_adj_left cinner_commute complex_Re_numeral complex_add_cnj field_sum_of_halves numeral_One numeral_plus_numeral of_real_divide of_real_numeral one_complex.simps(1) positive_hermitianI semiring_norm(2))
    have \<open>0 \<le> Re (inner (x - s *\<^sub>C y) (x - s *\<^sub>C y))\<close> for s
      by (metis Re_mono assms(1) assms(2) cinner_pos_if_pos zero_complex.simps(1))
    also have \<open>\<dots> s = Re (inner x x) - s * 2 * Re (inner x y)\<close> for s
      apply (auto simp: True)
      by (smt (verit, ccfv_threshold) Re_complex_of_real assms(1) assms(2) cinner_adj_right cinner_commute complex_add_cnj diff_minus_eq_add minus_complex.simps(1) positive_hermitianI uminus_complex.sel(1))
    finally show \<open>Re (inner x y) = 0\<close>
      by (metis add_le_same_cancel1 ge_iff_diff_ge_0 nonzero_eq_divide_eq not_numeral_le_zero zero_neq_numeral)
  qed
  have \<open>Im (inner x y) = Re (inner (imaginary_unit *\<^sub>C x) y)\<close>
    by simp
  also have \<open>\<dots> = 0\<close>
    by (rule Re0)
  finally have \<open>inner x y = 0\<close>
    using Re0[of x]
    using complex_eq_iff zero_complex.simps(1) zero_complex.simps(2) by presburger
  then show ?thesis
    by (auto simp: True)
next
  case False
  have inner_commute: \<open>inner x y = cnj (inner y x)\<close>
    by (metis Apos cinner_adj_left cinner_commute' inner_def positive_hermitianI)
  have [simp]: "cnj (inner y y) = inner y y" for y
    by (metis assms(1) cinner_adj_right cinner_commute' inner_def positive_hermitianI)
  define r where "r = cnj (inner x y) / inner y y"
  have "0 \<le> inner (x - scaleC r y) (x - scaleC r y)"
    by (simp add: Apos inner_def cinner_pos_if_pos)
  also have "\<dots> = inner x x - r * inner x y - cnj r * inner y x + r * cnj r * inner y y"
    unfolding cinner_diff_left cinner_diff_right cinner_scaleC_left cinner_scaleC_right inner_def
    by (smt (verit, ccfv_threshold) cblinfun.diff_right cblinfun.scaleC_right cblinfun_cinner_right.rep_eq cinner_scaleC_left cinner_scaleC_right diff_add_eq diff_diff_eq2 mult.assoc)
  also have "\<dots> = inner x x - inner y x * cnj r"
    unfolding r_def by auto
  also have "\<dots> = inner x x - inner x y * cnj (inner x y) / inner y y"
    unfolding r_def
    by (metis assms(1) assms(2) cinner_adj_right cinner_commute complex_cnj_divide mult.commute positive_hermitianI times_divide_eq_left)
  finally have "0 \<le> inner x x - inner x y * cnj (inner x y) / inner y y" .
  hence "inner x y * cnj (inner x y) / inner y y \<le> inner x x"
    by (simp add: le_diff_eq)
  hence \<open>(norm (inner x y)) ^ 2 / inner y y \<le> inner x x\<close>
    using complex_norm_square by presburger
  then show ?thesis
    by (metis False assms(1) assms(2) cinner_pos_if_pos mult_right_mono nonzero_eq_divide_eq)
qed

lemma sandwich_pos[intro]: \<open>sandwich b a \<ge> 0\<close> if \<open>a \<ge> 0\<close>
  by (metis (no_types, opaque_lifting) positive_cblinfunI cblinfun_apply_cblinfun_compose cinner_adj_left cinner_pos_if_pos sandwich_apply that)

lemma cblinfun_power_pos: \<open>cblinfun_power a n \<ge> 0\<close> if \<open>a \<ge> 0\<close>
proof (cases \<open>even n\<close>)
  case True
  have \<open>0 \<le> (cblinfun_power a (n div 2))* o\<^sub>C\<^sub>L (cblinfun_power a (n div 2))\<close>
    using positive_cblinfun_squareI by blast
  also have \<open>\<dots> = cblinfun_power a (n div 2 + n div 2)\<close>
    by (metis cblinfun_power_adj cblinfun_power_compose positive_hermitianI that)
  also from True have \<open>\<dots> = cblinfun_power a n\<close>
    by (metis add_self_div_2 div_plus_div_distrib_dvd_right) 
  finally show ?thesis
    by -
next
  case False
  have \<open>0 \<le> sandwich (cblinfun_power a (n div 2)) a\<close>
    using \<open>a \<ge> 0\<close> by (rule sandwich_pos)
  also have \<open>\<dots> = cblinfun_power a (n div 2 + 1 + n div 2)\<close>
    unfolding sandwich_apply
    by (metis (no_types, lifting) One_nat_def cblinfun_compose_id_right cblinfun_power_0 cblinfun_power_Suc' cblinfun_power_adj cblinfun_power_compose positive_hermitianI that)
  also from False have \<open>\<dots> = cblinfun_power a n\<close>
    by (smt (verit, del_insts) Suc_1 add.commute add.left_commute add_mult_distrib2 add_self_div_2 nat.simps(3) nonzero_mult_div_cancel_left odd_two_times_div_two_succ)
  finally show ?thesis
    by -
qed

(* Proof follows https://link.springer.com/article/10.1007%2FBF01448052,
      @{cite wecken35linearer} *)
lemma sqrt_op_existence:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes Apos: \<open>A \<ge> 0\<close>
  shows \<open>\<exists>B. B \<ge> 0 \<and> B o\<^sub>C\<^sub>L B = A \<and> (\<forall>F. A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<longrightarrow> B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B)\<close>
proof -
  define k S where \<open>k = norm A\<close> and \<open>S = A /\<^sub>R k - id_cblinfun\<close>
  have \<open>S \<le> 0\<close>
  proof (rule cblinfun_leI, simp)
    fix x :: 'a assume [simp]: \<open>norm x = 1\<close>
    show \<open>x \<bullet>\<^sub>C (S *\<^sub>V x) \<le> 0\<close>
      apply (auto simp: S_def cinner_diff_right cblinfun.diff_left scaleR_scaleC cdot_square_norm k_def complex_of_real_mono_iff[where y=1, simplified]
          simp flip: assms of_real_inverse of_real_power of_real_mult power_mult_distrib power_inverse
          intro!: power_le_one)
      by (smt (z3) \<open>norm x = 1\<close> assms cinner_pos_if_pos complex_inner_class.Cauchy_Schwarz_ineq2 complex_of_real_cmod complex_of_real_leq_1_iff left_inverse linordered_field_class.inverse_nonnegative_iff_nonnegative mult_cancel_left2 mult_cancel_right1 mult_left_mono norm_cblinfun norm_of_real of_real_mult)
  qed
  have [simp]: \<open>S* = S\<close>
    using \<open>S \<le> 0\<close> adj_0 comparable_hermitean' by blast
  have \<open>- id_cblinfun \<le> S\<close>
    by (simp add: S_def assms k_def scaleR_nonneg_nonneg)
  then have \<open>norm (S *\<^sub>V f) \<le> norm f\<close> for f
  proof -
    have 1: \<open>- S \<ge> 0\<close>
      by (simp add: \<open>S \<le> 0\<close>)
    have 2: \<open>f \<bullet>\<^sub>C (- S *\<^sub>V f) \<le> f \<bullet>\<^sub>C f\<close>
      by (metis \<open>- id_cblinfun \<le> S\<close> id_cblinfun_apply less_eq_cblinfun_def minus_le_iff)

    have \<open>(norm (S *\<^sub>V f))^4 = complex_of_real ((cmod ((- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f)))\<^sup>2)\<close>
      by (auto simp: power4_eq_xxxx cblinfun.minus_left complex_of_real_cmod power2_eq_square simp flip: power2_norm_eq_cinner)
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V - S *\<^sub>V f) * (f \<bullet>\<^sub>C (- S *\<^sub>V f))\<close>
      apply (rule generalized_Cauchy_Schwarz[where A=\<open>-S\<close> and x = \<open>-S *\<^sub>V f\<close> and y = f])
      by (fact 1)
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V - S *\<^sub>V f) * (f \<bullet>\<^sub>C f)\<close>
      using 2 apply (rule mult_left_mono)
      using "1" cinner_pos_if_pos by blast
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f) * (f \<bullet>\<^sub>C f)\<close>
      apply (rule mult_right_mono)
      apply (metis \<open>- id_cblinfun \<le> S\<close> id_cblinfun_apply less_eq_cblinfun_def neg_le_iff_le verit_minus_simplify(4))
      by simp
    also have \<open>\<dots> = (norm (-S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (norm (S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      by (simp add: cblinfun.minus_left)
    finally have \<open>norm (S *\<^sub>V f) ^ 4 \<le> (norm (S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      using complex_of_real_mono_iff by blast
    then have \<open>(norm (S *\<^sub>V f))\<^sup>2 \<le> (norm f)\<^sup>2\<close>
      by (smt (verit, best) \<open>complex_of_real (norm (S *\<^sub>V f) ^ 4) = complex_of_real ((cmod ((- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f)))\<^sup>2)\<close> cblinfun.minus_left cdot_square_norm cinner_commute cinner_ge_zero complex_norm_square complex_of_real_cmod mult.commute mult_cancel_left mult_right_mono norm_minus_cancel norm_mult norm_power of_real_eq_iff of_real_power realpow_square_minus_le)
    then show \<open>norm (S *\<^sub>V f) \<le> norm f\<close>
      by auto
  qed
  then have norm_Snf: \<open>norm (cblinfun_power S n *\<^sub>V f) \<le> norm f\<close> for f n
    by (induction n, auto simp: cblinfun_power_Suc' intro: order.trans)
  have fSnf: \<open>cmod (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f)) \<le> cmod (f \<bullet>\<^sub>C f)\<close> for f n
    by (smt (verit, ccfv_SIG) Re_complex_of_real cinner_ge_zero complex_inner_class.Cauchy_Schwarz_ineq2 complex_of_real_cmod mult_left_mono norm_Snf norm_ge_zero power2_eq_square power2_norm_eq_cinner')
  define b where \<open>b = (\<lambda>n. (1/2 gchoose n) *\<^sub>R cblinfun_power S n)\<close>
  define B0 B where \<open>B0 = infsum_in cstrong_operator_topology b UNIV\<close> and \<open>B = sqrt k *\<^sub>R B0\<close>
  have summable_sot_b: \<open>summable_on_in cstrong_operator_topology b UNIV\<close>    
  proof (rule summable_sot_absI)
    have [simp]: \<open>\<lceil>1 / 2 :: real\<rceil> = 1\<close>
      by (simp add: ceiling_eq_iff)
    fix F :: \<open>nat set\<close> and f :: \<open>'a\<close> assume \<open>finite F\<close>
    then obtain d where \<open>F \<subseteq> {..d}\<close> and [simp]: \<open>d > 0\<close>
      by (metis Icc_subset_Iic_iff atLeast0AtMost bot_nat_0.extremum bot_nat_0.not_eq_extremum dual_order.trans finite_nat_iff_bounded_le less_one)
    show \<open>(\<Sum>n\<in>F. norm (b n *\<^sub>V f)) \<le> 3 * norm f\<close> (is \<open>?lhs \<le> ?rhs\<close>)
    proof -
      have \<open>?lhs = (\<Sum>n\<in>F. norm ((1 / 2 gchoose n) *\<^sub>R (cblinfun_power S n *\<^sub>V f)))\<close>
        by (simp add: b_def scaleR_cblinfun.rep_eq)
      also have \<open>\<dots> \<le> (\<Sum>n\<in>F. norm ((1 / 2 gchoose n) *\<^sub>R f))\<close>
        by (simp add: mult_left_mono norm_Snf sum_mono)
      also have \<open>\<dots> = (\<Sum>n\<in>F. abs (1/2 gchoose n)) * norm f\<close>
        by (simp add: vector_space_over_itself.scale_sum_left)
      also have \<open>\<dots> \<le> (\<Sum>n\<le>d. abs (1/2 gchoose n)) * norm f\<close>
        using \<open>F \<subseteq> {..d}\<close> by (auto intro!: mult_right_mono sum_mono2)
      also have \<open>\<dots> = (2 - (- 1) ^ d * (- (1 / 2) gchoose d)) * norm f\<close>
        apply (subst gbinomial_sum_lower_abs)
        by auto
      also have \<open>\<dots> \<le> (2 + norm (- (1/2) gchoose d :: real)) * norm f\<close>
        apply (auto intro!: mult_right_mono)
        by (smt (verit) left_minus_one_mult_self mult.assoc mult_minus_left power2_eq_iff power2_eq_square)
      also have \<open>\<dots> \<le> 3 * norm f\<close>
        apply (subgoal_tac \<open>abs (- (1/2) gchoose d :: real) \<le> 1\<close>)
        apply (metis add_le_cancel_left is_num_normalize(1) mult.commute mult_left_mono norm_ge_zero numeral_Bit0 numeral_Bit1 one_add_one real_norm_def)
        apply (rule abs_gbinomial_leq1)
        by auto
      finally show ?thesis
        by -
    qed
  qed
  then have has_sum_b: \<open>has_sum_in cstrong_operator_topology b UNIV B0\<close>
    using B0_def has_sum_in_infsum_in hausdorff_sot by blast
  have \<open>B0 \<ge> 0\<close>
  proof (rule positive_cblinfunI)
    fix f :: 'a assume [simp]: \<open>norm f = 1\<close>
    from has_sum_b
    have sum1: \<open>(\<lambda>n. f \<bullet>\<^sub>C (b n *\<^sub>V f)) summable_on UNIV\<close>
      using has_sum_cinner_left has_sum_in_cstrong_operator_topology summable_on_def by blast
    have sum2: \<open>(\<lambda>x. - (complex_of_real \<bar>1 / 2 gchoose x\<bar> * (f \<bullet>\<^sub>C f))) summable_on UNIV - {0}\<close>
      apply (rule abs_summable_summable)
      using gbinomial_abs_summable_1[of \<open>1/2\<close>]
      by (auto simp add: cnorm_eq_1[THEN iffD1])
    from sum1 have sum3: \<open>(\<lambda>n. complex_of_real (1 / 2 gchoose n) * (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f))) summable_on UNIV - {0}\<close>
      unfolding b_def
      by (metis (no_types, lifting) cinner_scaleR_right finite.emptyI finite_insert 
          scaleR_cblinfun.rep_eq summable_on_cofin_subset summable_on_cong)

    have aux: \<open>a \<ge> - b\<close> if \<open>norm a \<le> norm b\<close> and \<open>a \<in> \<real>\<close> and \<open>b \<ge> 0\<close> for a b :: complex
      using cmod_eq_Re complex_is_Real_iff less_eq_complex_def that(1) that(2) that(3) by force

    from has_sum_b
    have \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) = (\<Sum>\<^sub>\<infinity>n. f \<bullet>\<^sub>C (b n *\<^sub>V f))\<close>
      by (metis has_sum_cinner_left has_sum_in_cstrong_operator_topology infsumI)
    moreover have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C (b n *\<^sub>V f)) + f \<bullet>\<^sub>C (b 0 *\<^sub>V f)\<close>
      apply (subst infsum_Diff)
      using sum1 by auto
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C ((1/2 gchoose n) *\<^sub>R cblinfun_power S n *\<^sub>V f))\<close>
      unfolding b_def by simp
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (1/2 gchoose n) * (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f)))\<close>
      by (simp add: scaleR_cblinfun.rep_eq)
    moreover have \<open>\<dots> \<ge> f \<bullet>\<^sub>C (b 0 *\<^sub>V f) - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (abs (1/2 gchoose n)) * (f \<bullet>\<^sub>C f))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    proof -
      have *: \<open>- (complex_of_real (abs (1 / 2 gchoose x)) * (f \<bullet>\<^sub>C f))
         \<le> complex_of_real (1 / 2 gchoose x) * (f \<bullet>\<^sub>C (cblinfun_power S x *\<^sub>V f))\<close> for x
        apply (rule aux)
        by (auto simp: cblinfun_power_adj norm_mult fSnf
            intro!: cinner_real cinner_hermitian_real mult_left_mono Reals_mult mult_nonneg_nonneg)
      show ?thesis
        apply (subst diff_conv_add_uminus) apply (rule add_left_mono)
        apply (subst infsum_uminus[symmetric]) apply (rule infsum_mono_complex)
        apply (rule sum2)
        apply (rule sum3)
        by (rule *)
    qed
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (abs (1/2 gchoose n))) * (f \<bullet>\<^sub>C f)\<close>
      by (simp add: infsum_cmult_left')
    moreover have \<open>\<dots> = of_real (1 - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. (abs (1/2 gchoose n)))) * (f \<bullet>\<^sub>C f)\<close>
      by (simp add: b_def left_diff_distrib infsum_of_real)
    moreover have \<open>\<dots> \<ge> 0 * (f \<bullet>\<^sub>C f)\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (auto intro!: mult_nonneg_nonneg)
      using gbinomial_abs_has_sum_1[where a=\<open>1/2\<close>]
      by (auto simp add: infsumI)
    moreover have \<open>\<dots> = 0\<close>
      by simp
    ultimately show \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) \<ge> 0\<close>
      by force
  qed
  then have \<open>B \<ge> 0\<close>
    by (simp add: B_def k_def scaleR_nonneg_nonneg)
  then have \<open>B = B*\<close>
    by (simp add: positive_hermitianI)
  have \<open>B0 o\<^sub>C\<^sub>L B0 = id_cblinfun + S\<close>
  proof (rule cblinfun_cinner_eqI)
    fix \<psi>
    define s bb where \<open>s = \<psi> \<bullet>\<^sub>C ((B0 o\<^sub>C\<^sub>L B0) *\<^sub>V \<psi>)\<close> and \<open>bb k = (\<Sum>n\<le>k. (b n *\<^sub>V \<psi>) \<bullet>\<^sub>C (b (k - n) *\<^sub>V \<psi>))\<close> for k

    have \<open>bb k = (\<Sum>n\<le>k. of_real ((1 / 2 gchoose (k - n)) * (1 / 2 gchoose n)) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>)))\<close> for k
      by (simp add: bb_def[abs_def] b_def cblinfun.scaleR_left cblinfun_power_adj mult.assoc
          flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots>k = of_real (\<Sum>n\<le>k. ((1 / 2 gchoose n) * (1 / 2 gchoose (k - n)))) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      apply (subst mult.commute) by (simp add: sum_distrib_right)
    also have \<open>\<dots>k = of_real (1 gchoose k) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      apply (simp only: atMost_atLeast0 gbinomial_Vandermonde)
      by simp
    also have \<open>\<dots>k = of_bool (k \<le> 1) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      by (simp add: gbinomial_1)
    finally have bb_simp: \<open>bb k = of_bool (k \<le> 1) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      by -

    have bb_sum: \<open>bb summable_on UNIV\<close>
      apply (rule summable_on_cong_neutral[where T=\<open>{..1}\<close> and g=bb, THEN iffD2])
      by (auto simp: bb_simp)

    from has_sum_b have b\<psi>_sum: \<open>(\<lambda>n. b n *\<^sub>V \<psi>) summable_on UNIV\<close>
      using has_sum_in_cstrong_operator_topology summable_on_def by blast

    have b2_pos: \<open>(b i *\<^sub>V \<psi>) \<bullet>\<^sub>C (b j *\<^sub>V \<psi>) \<ge> 0\<close> if \<open>i\<noteq>0\<close> \<open>j\<noteq>0\<close> for i j
    proof -
      have gchoose_sign: \<open>(-1) ^ (i+1) * ((1/2 :: real) gchoose i) \<ge> 0\<close> if \<open>i\<noteq>0\<close> for i
      proof -
        obtain j where j: \<open>Suc j = i\<close>
          using \<open>i \<noteq> 0\<close> not0_implies_Suc by blast
        show ?thesis
        proof (unfold j[symmetric], induction j)
          case 0
          then show ?case
            by simp
        next
          case (Suc j)
          have \<open>(- 1) ^ (Suc (Suc j) + 1) * (1 / 2 gchoose Suc (Suc j))
               = ((- 1) ^ (Suc j + 1) * (1 / 2 gchoose Suc j)) * ((-1) * (1/2-Suc j) / (Suc (Suc j)))\<close>
            apply (simp add: gbinomial_a_Suc_n)
            by (smt (verit, ccfv_threshold) divide_divide_eq_left' divide_divide_eq_right minus_divide_right)
          also have \<open>\<dots> \<ge> 0\<close>
            apply (rule mult_nonneg_nonneg)
             apply (rule Suc.IH)
            apply (rule divide_nonneg_pos)
             apply (rule mult_nonpos_nonpos)
            by auto
          finally show ?case
            by -
        qed
      qed
      from \<open>S \<le> 0\<close>
      have Sn_sign: \<open>\<psi> \<bullet>\<^sub>C (cblinfun_power (- S) (i + j) *\<^sub>V \<psi>) \<ge> 0\<close>
        by (auto intro!: cinner_pos_if_pos cblinfun_power_pos)
      have *: \<open>(- 1) ^ (i + (j + (i + j))) = (1::complex)\<close>
        by (metis Parity.ring_1_class.power_minus_even even_add power_one)

      have \<open>(b i *\<^sub>V \<psi>) \<bullet>\<^sub>C (b j *\<^sub>V \<psi>)
          = complex_of_real (1 / 2 gchoose i) * complex_of_real (1 / 2 gchoose j)
             * (\<psi> \<bullet>\<^sub>C (cblinfun_power S (i + j) *\<^sub>V \<psi>))\<close>
        by (simp add: b_def cblinfun.scaleR_right cblinfun.scaleR_left cblinfun_power_adj
            flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
      also have \<open>\<dots> = complex_of_real ((-1)^(i+1) * (1 / 2 gchoose i)) * complex_of_real ((-1)^(j+1) * (1 / 2 gchoose j))
             * (\<psi> \<bullet>\<^sub>C (cblinfun_power (-S) (i + j) *\<^sub>V \<psi>))\<close>
        by (simp add: cblinfun.scaleR_left cblinfun_power_uminus * flip: power_add)
      also have \<open>\<dots> \<ge> 0\<close>
        apply (rule mult_nonneg_nonneg)
        apply (rule mult_nonneg_nonneg)
        using complex_of_real_nn_iff gchoose_sign that(1) apply blast
        using complex_of_real_nn_iff gchoose_sign that(2) apply blast
        by (fact Sn_sign)
      finally show ?thesis
        by -
    qed

    have \<open>s = (B0 *\<^sub>V \<psi>) \<bullet>\<^sub>C (B0 *\<^sub>V \<psi>)\<close>
      by (metis \<open>0 \<le> B0\<close> cblinfun_apply_cblinfun_compose cinner_adj_left positive_hermitianI s_def)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. b n *\<^sub>V \<psi>) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>n. b n *\<^sub>V \<psi>)\<close>
      by (metis has_sum_b has_sum_in_cstrong_operator_topology infsumI)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. bb n)\<close>
      using b\<psi>_sum b\<psi>_sum unfolding bb_def
      apply (rule Cauchy_cinner_product_infsum[symmetric])
      using b\<psi>_sum b\<psi>_sum
      apply (rule Cauchy_cinner_product_summable[where X=\<open>{0}\<close> and Y=\<open>{0}\<close>])
      using b2_pos by auto
    also have \<open>\<dots> = bb 0 + bb 1\<close>
      apply (subst infsum_cong_neutral[where T=\<open>{..1}\<close> and g=bb])
      by (auto simp: bb_simp)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C ((id_cblinfun + S) *\<^sub>V \<psi>)\<close>
      by (simp add: cblinfun_power_Suc cblinfun.add_left cinner_add_right bb_simp)
    finally show \<open>s = \<psi> \<bullet>\<^sub>C ((id_cblinfun + S) *\<^sub>V \<psi>)\<close>
      by -
  qed
  then have \<open>B o\<^sub>C\<^sub>L B = norm A *\<^sub>C (id_cblinfun + S)\<close>
    apply (simp add: k_def B_def power2_eq_square scaleR_scaleC)
    by (metis norm_imp_pos_and_ge of_real_power power2_eq_square real_sqrt_pow2)
  also have \<open>\<dots> = A\<close>
    by (metis (no_types, lifting) k_def S_def add.commute cancel_comm_monoid_add_class.diff_cancel diff_add_cancel norm_eq_zero of_real_1 of_real_mult right_inverse scaleC_diff_right scaleC_one scaleC_scaleC scaleR_scaleC)
  finally have B2A: \<open>B o\<^sub>C\<^sub>L B = A\<close>
    by -
  have BF_comm: \<open>B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B\<close> if \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close> for F
  proof -
    define b' F' where \<open>b' n = Abs_cblinfun_sot (b n)\<close> and \<open>F' = Abs_cblinfun_sot F\<close> for n
    have \<open>S o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L S\<close>
      by (simp add: S_def that[symmetric] cblinfun_compose_minus_right cblinfun_compose_minus_left 
          flip: cblinfun_compose_assoc)
    then have \<open>cblinfun_power S n o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L cblinfun_power S n\<close> for n
      apply (induction n)
       apply (simp_all add: cblinfun_power_Suc' cblinfun_compose_assoc)
      by (simp flip: cblinfun_compose_assoc)
    then have \<open>b n o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L b n\<close> for n
      by (simp add: b_def)
    then have *: \<open>cblinfun_compose_sot (b' n) F' = cblinfun_compose_sot F' (b' n)\<close> for n
      unfolding b'_def F'_def apply transfer by simp
    have \<open>cblinfun_compose_sot (\<Sum>\<^sub>\<infinity>n. b' n) F' = cblinfun_compose_sot F' (\<Sum>\<^sub>\<infinity>n. b' n)\<close>
    proof -
      have [simp]: \<open>b' summable_on UNIV\<close>
        unfolding b'_def apply (transfer fixing: b)
        by (rule summable_sot_b)
      have \<open>cblinfun_compose_sot (\<Sum>\<^sub>\<infinity>n. b' n) F' = (\<Sum>\<^sub>\<infinity>n. cblinfun_compose_sot (b' n) F')\<close>
        apply (subst infsum_comm_additive[where f=\<open>\<lambda>x. cblinfun_compose_sot x F'\<close>, symmetric])
        by (auto simp: o_def)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. cblinfun_compose_sot F' (b' n))\<close>
        by (simp add: *)
      also have \<open>\<dots> = cblinfun_compose_sot F' (\<Sum>\<^sub>\<infinity>n. b' n)\<close>
        apply (subst infsum_comm_additive[where f=\<open>\<lambda>x. cblinfun_compose_sot F' x\<close>, symmetric])
        by (auto simp: o_def)
      finally show ?thesis
        by -
    qed
    then have \<open>B0 o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B0\<close>
      unfolding B0_def b'_def F'_def
      unfolding infsum_euclidean_eq[abs_def, symmetric]
      apply (transfer fixing: b F)
      by simp
    then show ?thesis
      by (auto simp: B_def)
  qed
  from \<open>B \<ge> 0\<close> B2A BF_comm
  show ?thesis
    by metis
qed


(* TODO: From @{cite wecken35linearer} *)
lemma wecken35hilfssatz:
  \<open>\<exists>P. is_Proj P \<and> (\<forall>F. F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F \<longrightarrow> F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F)
     \<and> (\<forall>f. W f = 0 \<longrightarrow> P f = f)
     \<and> (W = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L T)\<close>
  if WT_comm: \<open>W o\<^sub>C\<^sub>L T = T o\<^sub>C\<^sub>L W\<close> and \<open>W = W*\<close> and \<open>T = T*\<close> 
    and WW_TT: \<open>W o\<^sub>C\<^sub>L W = T o\<^sub>C\<^sub>L T\<close>
  for W T :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof (rule exI, intro conjI allI impI)
  define P where \<open>P = Proj (kernel (W-T))\<close>
  show \<open>is_Proj P\<close>
    by (simp add: P_def)
  show thesis1: \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close> if \<open>F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F\<close> for F
  proof -
    have 1: \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P\<close> if \<open>F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F\<close> for F
    proof (rule cblinfun_eqI)
      fix \<psi>
      have \<open>P *\<^sub>V \<psi> \<in> space_as_set (kernel (W - T))\<close>
        by (metis P_def Proj_range cblinfun_apply_in_image)
      then have \<open>(W - T) *\<^sub>V P *\<^sub>V \<psi> = 0\<close>
        using kernel_memberD by blast
      then have \<open>(W - T) *\<^sub>V F *\<^sub>V P *\<^sub>V \<psi> = 0\<close>
        by (metis cblinfun.zero_right cblinfun_apply_cblinfun_compose that)
      then have \<open>F *\<^sub>V P *\<^sub>V \<psi> \<in> space_as_set (kernel (W - T))\<close>
        using kernel_memberI by blast
      then have \<open>P *\<^sub>V (F *\<^sub>V P *\<^sub>V \<psi>) = F *\<^sub>V P *\<^sub>V \<psi>\<close>
        using P_def Proj_fixes_image by blast
      then show \<open>(F o\<^sub>C\<^sub>L P) *\<^sub>V \<psi> = (P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P) *\<^sub>V \<psi>\<close>
        by simp
    qed
    have 2: \<open>F* o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F*\<close>
      by (metis \<open>T = T*\<close> \<open>W = W*\<close> adj_cblinfun_compose adj_minus that)
    have \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P\<close> and \<open>F* o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F* o\<^sub>C\<^sub>L P\<close>
      using 1[OF that] 1[OF 2] by auto
    then show \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close>
      by (metis P_def adj_Proj adj_cblinfun_compose cblinfun_assoc_left(1) double_adj)
  qed
  show thesis2: \<open>P *\<^sub>V f = f\<close> if \<open>W *\<^sub>V f = 0\<close> for f
  proof -
    from that
    have \<open>0 = (W *\<^sub>V f) \<bullet>\<^sub>C (W *\<^sub>V f)\<close>
      by simp
    also from \<open>W = W*\<close> have \<open>\<dots> = f \<bullet>\<^sub>C ((W o\<^sub>C\<^sub>L W) *\<^sub>V f)\<close>
      by (simp add: that)
    also from WW_TT have \<open>\<dots> = f \<bullet>\<^sub>C ((T o\<^sub>C\<^sub>L T) *\<^sub>V f)\<close>
      by simp
    also from \<open>T = T*\<close> have \<open>\<dots> = (T *\<^sub>V f) \<bullet>\<^sub>C (T *\<^sub>V f)\<close>
      by (metis cblinfun_apply_cblinfun_compose cinner_adj_left)
    finally have \<open>T *\<^sub>V f = 0\<close>
      by simp
    then have \<open>(W - T) *\<^sub>V f = 0\<close>
      by (simp add: cblinfun.diff_left that)
    then show \<open>P *\<^sub>V f = f\<close>
      using P_def Proj_fixes_image kernel_memberI by blast
  qed
  show thesis3: \<open>W = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L T\<close>
  proof -
    from WW_TT WT_comm have WT_binomial: \<open>(W - T) o\<^sub>C\<^sub>L (W + T) = 0\<close>
      by (simp add: cblinfun_compose_add_right cblinfun_compose_minus_left)
    have PWT: \<open>P o\<^sub>C\<^sub>L (W + T) = W + T\<close>
    proof (rule cblinfun_eqI)
      fix \<psi>
      from WT_binomial have \<open>(W + T) *\<^sub>V \<psi> \<in> space_as_set (kernel (W-T))\<close>
        by (metis cblinfun_apply_cblinfun_compose kernel_memberI zero_cblinfun.rep_eq)
      then show \<open>(P o\<^sub>C\<^sub>L (W + T)) *\<^sub>V \<psi> = (W + T) *\<^sub>V \<psi>\<close>
        by (metis P_def Proj_idempotent Proj_range cblinfun_apply_cblinfun_compose cblinfun_fixes_range)
    qed
    from P_def have \<open>(W - T) o\<^sub>C\<^sub>L P = 0\<close>
      by (metis Proj_range thesis1 cblinfun_apply_cblinfun_compose cblinfun_apply_in_image
          cblinfun_eqI kernel_memberD zero_cblinfun.rep_eq)
    with PWT WT_comm thesis1 have \<open>2 *\<^sub>C T o\<^sub>C\<^sub>L P = W + T\<close>
      by (metis (no_types, lifting) bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose cblinfun_compose_add_right cblinfun_compose_minus_left cblinfun_compose_minus_right eq_iff_diff_eq_0 scaleC_2)
    with  that(2) that(3) show ?thesis
      by (smt (verit, ccfv_threshold) P_def add_diff_cancel adj_Proj adj_cblinfun_compose adj_plus cblinfun_compose_id_right cblinfun_compose_minus_left cblinfun_compose_scaleC_left id_cblinfun_adjoint scaleC_2)
  qed
qed

(* Proof follows https://link.springer.com/article/10.1007%2FBF01448052,
      @{cite wecken35linearer} *)
lemma TODO_name:
  assumes Aherm: \<open>A = A*\<close>
  shows \<open>\<exists>E. is_Proj E \<and> (\<forall>F. A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<longrightarrow> A o\<^sub>C\<^sub>L E = E o\<^sub>C\<^sub>L A) 
      \<and> A o\<^sub>C\<^sub>L E \<ge> 0 \<and> A o\<^sub>C\<^sub>L (id_cblinfun - E) \<le> 0 
      \<and> (\<forall>f. A *\<^sub>V f = 0 \<longrightarrow> E *\<^sub>V f = f)\<close>
proof -
  obtain B where \<open>B \<ge> 0\<close> and B2A2: \<open>B o\<^sub>C\<^sub>L B = A* o\<^sub>C\<^sub>L A\<close> and AAF: \<open>A* o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L (A* o\<^sub>C\<^sub>L A) \<Longrightarrow> B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B\<close> for F
    apply atomize_elim
    apply (rule sqrt_op_existence)
    by (simp add: positive_cblinfun_squareI)
  from \<open>B \<ge> 0\<close> have \<open>B = B*\<close>
    by (simp add: comparable_hermitean)
  from AAF have \<open>B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B\<close> if \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close> for F
    by (metis assms cblinfun_assoc_left(1) that)
  then have \<open>B o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L B\<close>
    by blast
  then obtain E where \<open>is_Proj E\<close>
    and 1: \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<Longrightarrow> A o\<^sub>C\<^sub>L E = E o\<^sub>C\<^sub>L A\<close> 
    and 3: \<open>A *\<^sub>V f = 0 \<Longrightarrow> E *\<^sub>V f = f\<close>
    and A2EB: \<open>A = (2 *\<^sub>C E - id_cblinfun) o\<^sub>C\<^sub>L B\<close>
  for F f
    apply atomize_elim
    using wecken35hilfssatz[where W=A and T=B]
    by (metis B2A2 \<open>B = B*\<close> assms cblinfun_compose_minus_left cblinfun_compose_minus_right)
  then have AE_BE: \<open>A o\<^sub>C\<^sub>L E = B o\<^sub>C\<^sub>L E\<close>
    by (smt (verit, ccfv_SIG) \<open>B = B*\<close> \<open>is_Proj E\<close> add_right_imp_eq adj_cblinfun_compose adj_plus assms cblinfun_compose_add_left cblinfun_compose_assoc cblinfun_compose_id_right diff_add_cancel id_cblinfun_adjoint is_Proj_algebraic scaleC_2)
  then have AmE_BmE: \<open>- A o\<^sub>C\<^sub>L (id_cblinfun - E) = B o\<^sub>C\<^sub>L (id_cblinfun - E)\<close>
    apply (simp add: cblinfun_compose_minus_right)
    by (smt (z3) A2EB \<open>B = B*\<close> \<open>is_Proj E\<close> add_diff_cancel_left' adj_cblinfun_compose adj_plus adj_uminus arith_special(3) assms cblinfun_compose_id_right cblinfun_compose_minus_right complex_vector.vector_space_assms(4) diff_0 diff_add_cancel diff_diff_eq2 id_cblinfun_adjoint is_Proj_algebraic pth_2 scaleC_left.add)
  from AE_BE have Apos: \<open>A o\<^sub>C\<^sub>L E \<ge> 0\<close>
    by (smt (verit, ccfv_threshold) 1 \<open>0 \<le> B\<close> \<open>is_Proj E\<close> cblinfun.zero_left cblinfun_apply_cblinfun_compose cinner_adj_right cinner_zero_right is_Proj_algebraic less_eq_cblinfun_def)
  have "1'": \<open>- A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L - A \<Longrightarrow> - A o\<^sub>C\<^sub>L (id_cblinfun - E) = (id_cblinfun - E) o\<^sub>C\<^sub>L - A\<close> and \<open>is_Proj (id_cblinfun - E)\<close> for F
    apply (metis (no_types, opaque_lifting) "1" cblinfun_compose_id_left cblinfun_compose_id_right cblinfun_compose_minus_left cblinfun_compose_minus_right cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_minus1_left)
    using \<open>is_Proj E\<close> is_Proj_complement by blast
  from AmE_BmE have \<open>- A o\<^sub>C\<^sub>L (id_cblinfun - E) \<ge> 0\<close>
    by (smt (verit, ccfv_threshold) "1'" \<open>0 \<le> B\<close> \<open>is_Proj (id_cblinfun - E)\<close> cblinfun.zero_left cblinfun_apply_cblinfun_compose cinner_adj_right cinner_zero_right is_Proj_algebraic less_eq_cblinfun_def)
  then have Aneg: \<open>A o\<^sub>C\<^sub>L (id_cblinfun - E) \<le> 0\<close>
    by (metis cblinfun_compose_scaleC_left neg_0_le_iff_le scaleC_minus1_left)
  from Apos Aneg 1 3 \<open>is_Proj E\<close> show ?thesis
    by auto
qed

lemma 
  assumes \<open>a \<ge> 0\<close>
  shows sqrt_op_pos[simp]: \<open>sqrt_op a \<ge> 0\<close>
    and sqrt_op_square[simp]: \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
proof -
  from sqrt_op_existence[OF assms]
  have *: \<open>\<exists>b::'a \<Rightarrow>\<^sub>C\<^sub>L 'a. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a\<close>
    by (metis positive_hermitianI)
  show \<open>sqrt_op a \<ge>0\<close> and \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
    using * apply (smt (verit, ccfv_threshold) someI_ex sqrt_op_def)
    using * by (metis (mono_tags, lifting) someI_ex sqrt_op_def)
qed

(* Also in @{cite wecken35linearer} *)
lemma sqrt_op_unique:
  assumes \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close>
  shows \<open>b = sqrt_op a\<close>
proof -
  have \<open>a \<ge> 0\<close>
    using assms(2) positive_cblinfun_squareI by blast 
  from sqrt_op_existence[OF \<open>a \<ge> 0\<close>]
  obtain sq where \<open>sq \<ge> 0\<close> and \<open>sq o\<^sub>C\<^sub>L sq = a\<close> and a_comm: \<open>a o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L a \<Longrightarrow> sq o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L sq\<close> for F
    by metis
  have eq_sq: \<open>b = sq\<close> if \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close> for b
  proof -
    have \<open>b o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L b\<close>
      by (metis cblinfun_assoc_left(1) positive_hermitianI that(1) that(2))
    then have b_sqrt_comm: \<open>b o\<^sub>C\<^sub>L sq = sq o\<^sub>C\<^sub>L b\<close>
      using a_comm by force
    from \<open>b \<ge> 0\<close> have \<open>b = b*\<close>
      by (simp add: assms(1) positive_hermitianI)
    have sqrt_adj: \<open>sq = sq*\<close>
      by (simp add: \<open>0 \<le> sq\<close> positive_hermitianI)
    have bb_sqrt: \<open>b o\<^sub>C\<^sub>L b = sq o\<^sub>C\<^sub>L sq\<close>
      using \<open>b = b*\<close> \<open>sq o\<^sub>C\<^sub>L sq = a\<close> that(2) by fastforce

    from wecken35hilfssatz[OF b_sqrt_comm \<open>b = b*\<close> sqrt_adj bb_sqrt]
    obtain P where \<open>is_Proj P\<close> and b_P_sq: \<open>b = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L sq\<close>
      and Pcomm: \<open>F o\<^sub>C\<^sub>L (b - sq) = (b - sq) o\<^sub>C\<^sub>L F \<Longrightarrow> F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close> for F
      by metis

    have 1: \<open>sandwich (id_cblinfun - P) b = (id_cblinfun - P) o\<^sub>C\<^sub>L b\<close>
      by (smt (verit, del_insts) Pcomm \<open>is_Proj P\<close> b_sqrt_comm cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right cblinfun_compose_minus_left cblinfun_compose_minus_right cblinfun_compose_zero_left diff_0_right is_Proj_algebraic is_Proj_complement is_Proj_idempotent sandwich_apply)
    also have 2: \<open>\<dots> = - (id_cblinfun - P) o\<^sub>C\<^sub>L sq\<close>
      apply (simp add: b_P_sq)
      by (smt (verit, del_insts) \<open>0 \<le> sq\<close> \<open>is_Proj P\<close> add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_compose_minus_right diff_diff_eq2 is_Proj_algebraic is_Proj_complement minus_diff_eq scaleC_2)
    also have \<open>\<dots> = - sandwich (id_cblinfun - P) sq\<close>
      by (metis \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L b = - (id_cblinfun - P) o\<^sub>C\<^sub>L sq\<close> calculation cblinfun_compose_uminus_left sandwich_apply)
    also have \<open>\<dots> \<le> 0\<close>
      by (simp add: \<open>0 \<le> sq\<close> sandwich_pos)
    finally have \<open>sandwich (id_cblinfun - P) b \<le> 0\<close>
      by -
    moreover from \<open>b \<ge> 0\<close> have \<open>sandwich (id_cblinfun - P) b \<ge> 0\<close>
      by (simp add: sandwich_pos)
    ultimately have \<open>sandwich (id_cblinfun - P) b = 0\<close>
      by auto
    with 1 2 have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L sq = 0\<close>
      by (metis add.inverse_neutral cblinfun_compose_uminus_left minus_diff_eq)
    with b_P_sq show \<open>b = sq\<close>
      by (metis (no_types, lifting) add.inverse_neutral add_diff_cancel_right' adj_cblinfun_compose cblinfun_compose_id_right cblinfun_compose_minus_left diff_0 diff_eq_diff_eq id_cblinfun_adjoint scaleC_2 sqrt_adj)
  qed
  
  from eq_sq have \<open>sqrt_op a = sq\<close>
    by (simp add: \<open>0 \<le> a\<close>)
  moreover from eq_sq have \<open>b = sq\<close>
    by (simp add: assms(1) assms(2))
  ultimately show \<open>b = sqrt_op a\<close>
    by simp
qed

lemma sqrt_op_commute:
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close>
  shows \<open>sqrt_op A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L sqrt_op A\<close>
  by (metis assms(1) assms(2) positive_hermitianI sqrt_op_existence sqrt_op_unique)

lemma sqrt_op_0[simp]: \<open>sqrt_op 0 = 0\<close>
  apply (rule sqrt_op_unique[symmetric])
  by auto

lemma sqrt_op_scaleC: 
  assumes \<open>c \<ge> 0\<close> and \<open>a \<ge> 0\<close>
  shows \<open>sqrt_op (c *\<^sub>C a) = sqrt c *\<^sub>C sqrt_op a\<close>
  apply (rule sqrt_op_unique[symmetric])
  using assms apply (auto simp: split_scaleC_pos_le)
  by (metis of_real_power power2_eq_square real_sqrt_pow2)

definition abs_op :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>abs_op a = sqrt_op (a* o\<^sub>C\<^sub>L a)\<close>

lemma abs_op_pos[simp]: \<open>abs_op a \<ge> 0\<close>
  by (simp add: abs_op_def positive_cblinfun_squareI sqrt_op_pos)

lemma abs_op_0[simp]: \<open>abs_op 0 = 0\<close>
  unfolding abs_op_def by auto

lemma abs_op_idem[simp]: \<open>abs_op (abs_op a) = abs_op a\<close>
  by (metis abs_op_def abs_op_pos sqrt_op_unique)

lemma abs_op_uminus[simp]: \<open>abs_op (- a) = abs_op a\<close>
  by (simp add: abs_op_def adj_uminus bounded_cbilinear.minus_left 
      bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemma selfbutter_pos[simp]: \<open>selfbutter x \<ge> 0\<close>
  by (metis butterfly_def double_adj positive_cblinfun_squareI)


lemma abs_op_butterfly[simp]: \<open>abs_op (butterfly x y) = (norm x / norm y) *\<^sub>R selfbutter y\<close> for x :: \<open>'a::chilbert_space\<close> and y :: \<open>'b::chilbert_space\<close>
proof (cases \<open>y=0\<close>)
  case False
  have \<open>abs_op (butterfly x y) = sqrt_op (cinner x x *\<^sub>C selfbutter y)\<close>
    unfolding abs_op_def by simp
  also have \<open>\<dots> = (norm x / norm y) *\<^sub>R selfbutter y\<close>
    apply (rule sqrt_op_unique[symmetric])
    using False by (auto intro!: scaleC_nonneg_nonneg simp: scaleR_scaleC power2_eq_square simp flip: power2_norm_eq_cinner)
  finally show ?thesis
    by -
next
  case True
  then show ?thesis
    by simp
qed

lemma abs_op_nondegenerate: \<open>a = 0\<close> if \<open>abs_op a = 0\<close>
proof -
  from that
  have \<open>sqrt_op (a* o\<^sub>C\<^sub>L a) = 0\<close>
    by (simp add: abs_op_def)
  then have \<open>0* o\<^sub>C\<^sub>L 0 = (a* o\<^sub>C\<^sub>L a)\<close>
    by (metis cblinfun_compose_zero_right positive_cblinfun_squareI sqrt_op_square)
  then show \<open>a = 0\<close>
    apply (rule_tac op_square_nondegenerate)
    by simp
qed

lemma abs_op_scaleC: \<open>abs_op (c *\<^sub>C a) = \<bar>c\<bar> *\<^sub>C abs_op a\<close>
proof -
  define aa where \<open>aa = a* o\<^sub>C\<^sub>L a\<close>
  have \<open>abs_op (c *\<^sub>C a) = sqrt_op (\<bar>c\<bar>\<^sup>2 *\<^sub>C aa)\<close>
    by (simp add: abs_op_def x_cnj_x aa_def)
  also have \<open>\<dots> = \<bar>c\<bar> *\<^sub>C sqrt_op aa\<close>
    by (smt (verit, best) aa_def abs_complex_def abs_nn cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right complex_cnj_complex_of_real o_apply positive_cblinfun_squareI power2_eq_square scaleC_adj scaleC_nonneg_nonneg scaleC_scaleC sqrt_op_pos sqrt_op_square sqrt_op_unique)
  also have \<open>\<dots> = \<bar>c\<bar> *\<^sub>C abs_op a\<close>
    by (simp add: aa_def abs_op_def)
  finally show ?thesis
    by -
qed


lemma kernel_abs_op[simp]: \<open>kernel (abs_op a) = kernel a\<close>
proof (rule ccsubspace_eqI)
  fix x
  have \<open>x \<in> space_as_set (kernel (abs_op a)) \<longleftrightarrow> abs_op a x = 0\<close>
    using kernel_memberD kernel_memberI by blast
  also have \<open>\<dots> \<longleftrightarrow> abs_op a x \<bullet>\<^sub>C abs_op a x = 0\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> x \<bullet>\<^sub>C ((abs_op a)* o\<^sub>C\<^sub>L abs_op a) x = 0\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> \<longleftrightarrow> x \<bullet>\<^sub>C (a* o\<^sub>C\<^sub>L a) x = 0\<close>
    by (simp add: abs_op_def positive_cblinfun_squareI)
  also have \<open>\<dots> \<longleftrightarrow> a x \<bullet>\<^sub>C a x = 0\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> \<longleftrightarrow> a x = 0\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> x \<in> space_as_set (kernel a)\<close>
    using kernel_memberD kernel_memberI by auto
  finally show \<open>x \<in> space_as_set (kernel (abs_op a)) \<longleftrightarrow> x \<in> space_as_set (kernel a)\<close>
    by -
qed

definition polar_decomposition where
  \<comment> \<open>@{cite conway00operator}, 3.9 Polar Decomposition\<close>
  \<open>polar_decomposition A = cblinfun_extension (range (abs_op A)) (\<lambda>\<psi>. A *\<^sub>V inv (abs_op A) \<psi>) o\<^sub>C\<^sub>L Proj (abs_op A *\<^sub>S top)\<close>
    for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>

lemma 
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  \<comment> \<open>@{cite conway00operator}, 3.9 Polar Decomposition\<close>
  shows polar_decomposition_correct: \<open>polar_decomposition A o\<^sub>C\<^sub>L abs_op A = A\<close>
    and polar_decomposition_final_space: \<open>polar_decomposition A *\<^sub>S top = A *\<^sub>S top\<close> (* Should be more precise: range (polar_decomposition A) = closure (range A) *)
    and polar_decomposition_initial_space[simp]: \<open>kernel (polar_decomposition A) = kernel A\<close>
    and polar_decomposition_partial_isometry[simp]: \<open>partial_isometry (polar_decomposition A)\<close>
proof -
  have abs_A_norm: \<open>norm (abs_op A h) = norm (A h)\<close> for h
  proof -
    have \<open>complex_of_real ((norm (A h))\<^sup>2) = A h \<bullet>\<^sub>C A h\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (A* o\<^sub>C\<^sub>L A) h \<bullet>\<^sub>C h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = ((abs_op A)* o\<^sub>C\<^sub>L abs_op A) h \<bullet>\<^sub>C h\<close>
      by (simp add: abs_op_def positive_cblinfun_squareI)
    also have \<open>\<dots> = abs_op A h \<bullet>\<^sub>C abs_op A h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = complex_of_real ((norm (abs_op A h))\<^sup>2)\<close>
      using cnorm_eq_square by blast
    finally show ?thesis
      by (simp add: cdot_square_norm cnorm_eq)
  qed

  define W W' P
    where \<open>W = (\<lambda>\<psi>. A *\<^sub>V inv (abs_op A) \<psi>)\<close> 
    and \<open>W' = cblinfun_extension (range (abs_op A)) W\<close>
    and \<open>P = Proj (abs_op A *\<^sub>S top)\<close>

  have pdA: \<open>polar_decomposition A = W' o\<^sub>C\<^sub>L P\<close>
    by (auto simp: polar_decomposition_def W'_def W_def P_def) 

  have AA_norm: \<open>norm (W \<psi>) = norm \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
  proof -
    define h where \<open>h = inv (abs_op A) \<psi>\<close>
    from that have absA_h: \<open>abs_op A h = \<psi>\<close>
      by (simp add: f_inv_into_f h_def)
    have \<open>complex_of_real ((norm (W \<psi>))\<^sup>2) = complex_of_real ((norm (A h))\<^sup>2)\<close>
      using W_def h_def by blast 
    also have \<open>\<dots> = A h \<bullet>\<^sub>C A h\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (A* o\<^sub>C\<^sub>L A) h \<bullet>\<^sub>C h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = ((abs_op A)* o\<^sub>C\<^sub>L abs_op A) h \<bullet>\<^sub>C h\<close>
      by (simp add: abs_op_def positive_cblinfun_squareI)
    also have \<open>\<dots> = abs_op A h \<bullet>\<^sub>C abs_op A h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = complex_of_real ((norm (abs_op A h))\<^sup>2)\<close>
      using cnorm_eq_square by blast
    also have \<open>\<dots> = complex_of_real ((norm \<psi>)\<^sup>2)\<close>
      using absA_h by fastforce
    finally show \<open>norm (W \<psi>) = norm \<psi>\<close>
      by (simp add: cdot_square_norm cnorm_eq)
  qed
  then have AA_norm': \<open>norm (W \<psi>) \<le> 1 * norm \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    using that by simp

  have W_absA: \<open>W (abs_op A h) = A h\<close> for h
  proof -
    have \<open>A h = A h'\<close> if \<open>abs_op A h = abs_op A h'\<close> for h h'
    proof -
      from that have \<open>norm (abs_op A (h - h')) = 0\<close>
        by (simp add: cblinfun.diff_right)
      with AA_norm have \<open>norm (A (h - h')) = 0\<close>
        by (simp add: abs_A_norm)
      then show \<open>A h = A h'\<close>
        by (simp add: cblinfun.diff_right)
    qed
    then show ?thesis
      by (metis W_def f_inv_into_f rangeI)
  qed

  have range_subspace: \<open>csubspace (range (abs_op A))\<close>
    by (auto intro!: range_is_csubspace)

  have exP: \<open>\<exists>P. is_Proj P \<and> range ((*\<^sub>V) P) = closure (range ((*\<^sub>V) (abs_op A)))\<close>
    apply (rule exI[of _ \<open>Proj (abs_op A *\<^sub>S \<top>)\<close>])
    by (metis (no_types, opaque_lifting) Proj_is_Proj Proj_range Proj_range_closed cblinfun_image.rep_eq closure_closed space_as_set_top)

  have add: \<open>W (x + y) = W x + W y\<close> if x_in: \<open>x \<in> range (abs_op A)\<close> and y_in: \<open>y \<in> range (abs_op A)\<close> for x y
  proof -
    obtain x' y' where \<open>x = abs_op A x'\<close> and \<open>y = abs_op A y'\<close>
      using x_in y_in by blast
    then show ?thesis
      by (simp flip: cblinfun.add_right add: W_absA)
  qed

  have scale: \<open>W (c *\<^sub>C x) = c *\<^sub>C W x\<close> if x_in: \<open>x \<in> range (abs_op A)\<close> for c x
  proof -
    obtain x' where \<open>x = abs_op A x'\<close>
      using x_in by blast
    then show ?thesis
      by (simp flip: cblinfun.scaleC_right add: W_absA)
  qed

  have \<open>cblinfun_extension_exists (range (abs_op A)) W\<close>
    using range_subspace exP add scale AA_norm'
    by (rule cblinfun_extension_exists_proj)

  then have W'_apply: \<open>W' *\<^sub>V \<psi> = W \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    by (simp add: W'_def cblinfun_extension_apply that)

   have \<open>norm (W' \<psi>) - norm \<psi> = 0\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    by (simp add: W'_apply AA_norm that)
  then have \<open>norm (W' \<psi>) - norm \<psi> = 0\<close> if \<open>\<psi> \<in> closure (range (abs_op A))\<close> for \<psi>
    apply (rule_tac continuous_constant_on_closure[where S=\<open>range (abs_op A)\<close>])
    using that by (auto intro!: continuous_at_imp_continuous_on)
  then have norm_W': \<open>norm (W' \<psi>) = norm \<psi>\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S top)\<close> for \<psi>
    using cblinfun_image.rep_eq that by force

  show correct: \<open>polar_decomposition A o\<^sub>C\<^sub>L abs_op A = A\<close>
  proof (rule cblinfun_eqI)
    fix \<psi> :: 'a
    have \<open>(polar_decomposition A o\<^sub>C\<^sub>L abs_op A) *\<^sub>V \<psi> = W (P (abs_op A \<psi>))\<close>
      by (simp add: W'_apply P_def pdA Proj_fixes_image) 
    also have \<open>\<dots> = W (abs_op A \<psi>)\<close>
      by (auto simp: P_def Proj_fixes_image)
    also have \<open>\<dots> = A \<psi>\<close>
      by (simp add: W_absA)
(*     also have \<open>\<dots> = A (inv (abs_op A) (abs_op A \<psi>))\<close>
      using W_def by fastforce
    also have \<open>\<dots> = A \<psi>\<close>
       *)
    finally show \<open>(polar_decomposition A o\<^sub>C\<^sub>L abs_op A) *\<^sub>V \<psi> = A *\<^sub>V \<psi>\<close>
      by -
  qed

  show \<open>polar_decomposition A *\<^sub>S top = A *\<^sub>S top\<close>
  proof (rule antisym)
    have *: \<open>A *\<^sub>S top = polar_decomposition A *\<^sub>S abs_op A *\<^sub>S top\<close>
      by (simp add: cblinfun_assoc_left(2) correct)
    also have \<open>\<dots> \<le> polar_decomposition A *\<^sub>S top\<close>
      by (simp add: cblinfun_image_mono)
    finally show \<open>A *\<^sub>S top \<le> polar_decomposition A *\<^sub>S top\<close>
      by -

    have \<open>W' \<psi> \<in> range A\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
      using W'_apply W_def that by blast
    then have \<open>W' \<psi> \<in> closure (range A)\<close> if \<open>\<psi> \<in> closure (range (abs_op A))\<close> for \<psi>
      using * 
      by (metis (mono_tags, lifting) P_def Proj_range Proj_fixes_image cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_compose_image cblinfun_image.rep_eq pdA that top_ccsubspace.rep_eq)
    then have \<open>W' \<psi> \<in> space_as_set (A *\<^sub>S top)\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S top)\<close> for \<psi>
      by (metis cblinfun_image.rep_eq that top_ccsubspace.rep_eq)
    then have \<open>polar_decomposition A \<psi> \<in> space_as_set (A *\<^sub>S top)\<close> for \<psi>
      by (metis P_def Proj_range cblinfun_apply_cblinfun_compose cblinfun_apply_in_image pdA)
    then show \<open>polar_decomposition A *\<^sub>S top \<le> A *\<^sub>S top\<close>
      using * 
      by (metis (no_types, lifting) Proj_idempotent Proj_range cblinfun_compose_image dual_order.eq_iff polar_decomposition_def)
  qed

  show \<open>partial_isometry (polar_decomposition A)\<close>
    apply (rule partial_isometryI'[where V=\<open>abs_op A *\<^sub>S top\<close>])
    by (auto simp add: P_def Proj_fixes_image norm_W' pdA kernel_memberD)

  have \<open>kernel (polar_decomposition A) = - (abs_op A *\<^sub>S top)\<close>
    apply (rule partial_isometry_initial[where V=\<open>abs_op A *\<^sub>S top\<close>])
    by (auto simp add: P_def Proj_fixes_image norm_W' pdA kernel_memberD)
  also have \<open>\<dots> = kernel (abs_op A)\<close>
    by (metis abs_op_pos kernel_compl_adj_range positive_hermitianI)
  also have \<open>\<dots> = kernel A\<close>
    by (simp add: kernel_abs_op)
  finally show \<open>kernel (polar_decomposition A) = kernel A\<close>
    by -
qed

lemma polar_decomposition_correct': \<open>(polar_decomposition A)* o\<^sub>C\<^sub>L A = abs_op A\<close>
  for A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
proof -
  have \<open>polar_decomposition A* o\<^sub>C\<^sub>L A = (polar_decomposition A* o\<^sub>C\<^sub>L polar_decomposition A) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: cblinfun_compose_assoc polar_decomposition_correct)
  also have \<open>\<dots> = Proj (- kernel (polar_decomposition A)) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: partial_isometry_adj_a_o_a polar_decomposition_partial_isometry)
  also have \<open>\<dots> = Proj (- kernel A) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: polar_decomposition_initial_space)
  also have \<open>\<dots> = Proj (- kernel (abs_op A)) o\<^sub>C\<^sub>L abs_op A\<close>
    by simp
  also have \<open>\<dots> = Proj (abs_op A *\<^sub>S top) o\<^sub>C\<^sub>L abs_op A\<close>
    by (metis abs_op_pos kernel_compl_adj_range ortho_involution positive_hermitianI)
  also have \<open>\<dots> = abs_op A\<close>
    by (simp add: Proj_fixes_image cblinfun_eqI)
  finally show ?thesis
    by -
qed

lemma abs_op_adj: \<open>abs_op (a*) = sandwich (polar_decomposition a) (abs_op a)\<close>
proof -
  have pos: \<open>sandwich (polar_decomposition a) (abs_op a) \<ge> 0\<close>
    by (simp add: sandwich_pos)
  have \<open>(sandwich (polar_decomposition a) (abs_op a))* o\<^sub>C\<^sub>L (sandwich (polar_decomposition a) (abs_op a))
     = polar_decomposition a o\<^sub>C\<^sub>L (abs_op a)* o\<^sub>C\<^sub>L abs_op a o\<^sub>C\<^sub>L (polar_decomposition a)*\<close>
    apply (simp add: sandwich_apply)
    by (metis (no_types, lifting) cblinfun_assoc_left(1) polar_decomposition_correct polar_decomposition_correct')
  also have \<open>\<dots> = a o\<^sub>C\<^sub>L a*\<close>
    by (metis abs_op_pos adj_cblinfun_compose cblinfun_assoc_left(1) polar_decomposition_correct positive_hermitianI)
  finally have \<open>sandwich (polar_decomposition a) (abs_op a) = sqrt_op (a o\<^sub>C\<^sub>L a*)\<close>
    using pos by (simp add: sqrt_op_unique)
  also have \<open>\<dots> = abs_op (a*)\<close>
    by (simp add: abs_op_def)
  finally show ?thesis
    by simp
qed

lemma abs_opI: 
  assumes \<open>a* o\<^sub>C\<^sub>L a = b* o\<^sub>C\<^sub>L b\<close>
  assumes \<open>a \<ge> 0\<close>
  shows \<open>a = abs_op b\<close>
  by (simp add: abs_op_def assms(1) assms(2) sqrt_op_unique)

lemma norm_abs_op[simp]: \<open>norm (abs_op a) = norm a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have \<open>(norm (abs_op a))\<^sup>2 = norm (abs_op a* o\<^sub>C\<^sub>L abs_op a)\<close>
    by simp
  also have \<open>\<dots> = norm (a* o\<^sub>C\<^sub>L a)\<close>
    by (simp add: abs_op_def positive_cblinfun_squareI)
  also have \<open>\<dots> = (norm a)\<^sup>2\<close>
    by simp
  finally show ?thesis
    by simp
qed

end
