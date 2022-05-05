section \<open>\<open>Positive_Operators\<close> -- Positive bounded operators\<close>

theory Positive_Operators
  imports Tensor_Product.Misc_Tensor_Product_BO Tensor_Product.Strong_Operator_Topology
    Ordinary_Differential_Equations.Cones
begin

no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)

unbundle cblinfun_notation

lemma cinner_pos_if_pos: \<open>f \<bullet>\<^sub>C (A *\<^sub>V f) \<ge> 0\<close> if \<open>A \<ge> 0\<close>
  using less_eq_cblinfun_def that by force

definition sqrt_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<open>sqrt_op a = (SOME b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a)\<close>

lemma norm_pos_op_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>0 \<le> A\<close> and \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
(* Can probably be proved using abs_op below. Needed? *)
  unfolding cinner_sup_norm_cblinfun
  sorry

lemma nonneg_quadratic_function_discriminant:
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
qed

lemma cnj_sgn_sgn: \<open>x \<noteq> 0 \<Longrightarrow> cnj (sgn x) * sgn x = 1\<close>
  oops

(* lemma generalized_Cauchy_Schwarz:
  fixes inner A
  assumes Apos: \<open>A \<ge> 0\<close>
  defines "\<And>x y. inner x y \<equiv> x \<bullet>\<^sub>C (A *\<^sub>V y)"
  shows "(inner x y) * (inner y x) \<le> inner x x * inner y y"
proof (cases \<open>y = 0\<close>)
  case True
  then show ?thesis 
    by (simp add: inner_def)
next
  case False
  define y' where \<open>y' = y /\<^sub>C sgn (inner y y)\<close>
  have \<open>inner y' y' = inner y y\<close>
    unfolding  
    apply (auto simp: inner_def y'_def cblinfun.scaleC_right simp flip: inverse_mult_distrib)
    by auto

  have \<open>cmod z = Re (z / sgn z)\<close>
    using sgn_eq by force
  obtain \<gamma> where \<open>cmod (\<gamma> * inner x y) = Re (inner x y)\<close> and \<open>cmod \<gamma> = 1\<close>
    by (metis Re_complex_of_real mult_eq_0_iff nonzero_mult_div_cancel_rxight norm_zero times_divide_eq_left zero_complex.simps(1))

    by -

    then show ?thesis
    
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

lemma cinner_hermitian_real: \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close> if \<open>A* = A\<close>
  by (metis Reals_cnj_iff cinner_adj_right cinner_commute' that)

lemma complex_of_real_leq_1_iff[iff]: \<open>complex_of_real x \<le> 1 \<longleftrightarrow> x \<le> 1\<close>
  by (metis complex_of_real_mono_iff of_real_1)

(* TODO move *)
lemma cblinfun_power_adj: \<open>(cblinfun_power S n)* = cblinfun_power (S*) n\<close>
  apply (induction n)
   apply simp
  apply (subst cblinfun_power_Suc)
  apply (subst cblinfun_power_Suc')
  by auto

(* TODO: move *)
lemma adj_minus: \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis add_implies_diff adj_plus diff_add_cancel)

(* TODO move *)
lemma The_eqI1:
  assumes \<open>\<And>x y. F x \<Longrightarrow> F y \<Longrightarrow> x = y\<close>
  assumes \<open>\<exists>z. F z\<close>
  assumes \<open>\<And>x. F x \<Longrightarrow> P x = Q x\<close>
  shows \<open>P (The F) = Q (The F)\<close>
  by (metis assms(1) assms(2) assms(3) theI)

lemma summable_on_uminus[intro!]: 
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close> (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  shows \<open>(\<lambda>i. - f i) summable_on A\<close>
  apply (subst asm_rl[of \<open>(\<lambda>i. - f i) = (\<lambda>i. (-1) *\<^sub>R f i)\<close>])
   apply simp
  using assms by (rule summable_on_scaleR_right)

(* Proof follows https://link.springer.com/article/10.1007%2FBF01448052,
      @{cite wecken35linearer} *)
lemma TODO_name:
  assumes Aherm: \<open>A = A*\<close>
  shows \<open>\<exists>E. is_Proj E \<and> (\<forall>F. A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<longrightarrow> A o\<^sub>C\<^sub>L E = E o\<^sub>C\<^sub>L A) 
      \<and> A o\<^sub>C\<^sub>L E \<ge> 0 \<and> A o\<^sub>C\<^sub>L (id_cblinfun - E) \<le> 0 
      \<and> (\<forall>f. A *\<^sub>V f = 0 \<longrightarrow> E *\<^sub>V f = f)\<close>
proof -
  have hilfssatz:
    \<open>\<exists>P. is_Proj P \<and> (\<forall>F. F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F \<longrightarrow> F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F)
       \<and> (\<forall>f. W f = 0 \<longrightarrow> P f = f)
       \<and> (W = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L T)\<close>
    if \<open>W o\<^sub>C\<^sub>L T = T o\<^sub>C\<^sub>L W\<close> and \<open>W = W*\<close> and \<open>T = T*\<close> and \<open>W o\<^sub>C\<^sub>L W = T o\<^sub>C\<^sub>L T\<close>
    for W T :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    sorry

  define k S where \<open>k = norm A\<close> and \<open>S = (A o\<^sub>C\<^sub>L A) /\<^sub>R k\<^sup>2 - id_cblinfun\<close>
  have \<open>S \<le> 0\<close>
  proof (rule cblinfun_leI, simp)
    fix x :: 'a assume [simp]: \<open>norm x = 1\<close>
    show \<open>x \<bullet>\<^sub>C (S *\<^sub>V x) \<le> 0\<close>
      apply (auto simp: S_def cinner_diff_right cblinfun.diff_left scaleR_scaleC cdot_square_norm k_def complex_of_real_mono_iff[where y=1, simplified]
          simp flip: cinner_adj_left[where x=x] assms of_real_inverse of_real_power of_real_mult power_mult_distrib power_inverse
          intro!: power_le_one)
      by (metis \<open>norm x = 1\<close> inverse_nonzero_iff_nonzero left_inverse linordered_field_class.inverse_nonnegative_iff_nonnegative mult_cancel_left1 mult_left_mono norm_cblinfun norm_ge_zero)
  qed
  have [simp]: \<open>S* = S\<close>
    by (simp add: S_def adj_minus flip: Aherm)
  have \<open>- id_cblinfun \<le> S\<close>
    by (auto intro!: cblinfun_leI simp: S_def scaleR_scaleC cdot_square_norm k_def power2_eq_square
        simp flip: cinner_adj_left[where y=\<open>_ *\<^sub>V _\<close>] assms)
(*   have \<open>norm S \<le> 1\<close>
  proof (rule norm_cblinfun_bound)
    show \<open>0 \<le> (1 :: real)\<close>
      by simp
    show \<open>norm (S *\<^sub>V f) \<le> 1 * norm f\<close> for f
    
  qed
    with \<open>S \<le> 0\<close> have \<open>norm S \<le> 1\<close>
    using norm_pos_op_mono (* TODO: check whether norm_pos_op_mono has a proof that doesn't use sqrt's of operators *)
    by (metis (no_types, opaque_lifting) Complex_Bounded_Linear_Function0.norm_blinfun_id_le dual_order.trans minus_le_iff neg_0_le_iff_le norm_minus_cancel) *)
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
  (* then have fSnf: \<open>f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f) \<le> f \<bullet>\<^sub>C f\<close> for f n
    (* TODO: can we add a cmod on the rhs? then we can use Cauchy_Schwarz_ineq2 a little more directly.
       Check how it is used below. *)
    thm Cauchy_Schwarz_ineq2
     *)
  have fSnf: \<open>cmod (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f)) \<le> cmod (f \<bullet>\<^sub>C f)\<close> for f n
    by (smt (verit, ccfv_SIG) Re_complex_of_real cinner_ge_zero complex_inner_class.Cauchy_Schwarz_ineq2 complex_of_real_cmod mult_left_mono norm_Snf norm_ge_zero power2_eq_square power2_norm_eq_cinner')
(*   then have Sn_herm: \<open>(pow S n)* = pow S n\<close> for n
    apply (rule_tac cinner_real_hermiteanI[symmetric])
    apply auto
    by - *)
  define b where \<open>b = (\<lambda>n. (1/2 gchoose n) *\<^sub>R cblinfun_power S n)\<close>
  define B0 B where \<open>B0 = infsum_in cstrong_operator_topology b UNIV\<close> and \<open>B = norm A *\<^sub>R B0\<close>
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
(*   then have \<open>has_sum_in cstrong_operator_topology b UNIV B0\<close>
    by -
  then have \<open>B0* = B0\<close>
    apply (rule hermitian_sum_hermitian_sot[rotated])
    by auto
  then have \<open>B = B*\<close>
    apply (rule hermitian_limit_hermitian_sot[symmetric])
     *)
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
    by (simp add: B_def scaleR_nonneg_nonneg)
  then have \<open>B = B*\<close> (* If B\<ge>0 need hermitian in the proof, uncomment the proof sketch of B=B* above *)
    by (simp add: positive_hermitianI)
  have \<open>B o\<^sub>C\<^sub>L B = (norm A)\<^sup>2 *\<^sub>C (id_cblinfun + S)\<close>
(* For S being a scalar, shown in q.s. p16.
Here, sandwich B^2 in f's, and then 
Use Cauchy_cinner_product_sums 
 *)
    sorry
  also have \<open>\<dots> = A o\<^sub>C\<^sub>L A\<close>
    by (metis (no_types, lifting) k_def S_def add.commute assms cancel_comm_monoid_add_class.diff_cancel diff_add_cancel norm_AAadj norm_eq_zero of_real_1 of_real_mult right_inverse scaleC_diff_right scaleC_one scaleC_scaleC scaleR_scaleC)
  finally have B2A2: \<open>B o\<^sub>C\<^sub>L B = A o\<^sub>C\<^sub>L A\<close>
    by -
  have \<open>B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B\<close> if \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close> for F
  proof -
    define b' F' where \<open>b' n = Abs_cblinfun_sot (b n)\<close> and \<open>F' = Abs_cblinfun_sot F\<close> for n
    have \<open>S o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L S\<close>
      apply (simp add: S_def that[symmetric] cblinfun_compose_minus_right cblinfun_compose_minus_left 
          flip: cblinfun_compose_assoc)
      by (simp add: that[symmetric] cblinfun_compose_assoc)
    then have \<open>cblinfun_power S n o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L cblinfun_power S n\<close> for n
      apply (induction n)
      apply simp
      apply (simp add: cblinfun_power_Suc cblinfun_compose_assoc)
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
(* Up to here we could package in separate lemma for existence of pos sqrt, plus the prop that B commutes with anything that A commutes with *)
  then have \<open>B o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L B\<close>
    by blast
  then obtain E where \<open>is_Proj E\<close>
    and 1: \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<Longrightarrow> A o\<^sub>C\<^sub>L E = E o\<^sub>C\<^sub>L A\<close> 
    and 3: \<open>A *\<^sub>V f = 0 \<Longrightarrow> E *\<^sub>V f = f\<close>
    and A2EB: \<open>A = (2 *\<^sub>C E - id_cblinfun) o\<^sub>C\<^sub>L B\<close>
  for F f
    apply atomize_elim
    using hilfssatz[where W=A and T=B]
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
  shows sqrt_op_pos[simp]: \<open>sqrt_op a \<ge> 0\<close> and sqrt_op_square[simp]: \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
proof -
  have *: \<open>\<exists>b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a\<close>
(* For an elementary proof (w/o functional calculus, see maybe
https://www.jstor.org/stable/2028176?seq=1#metadata_info_tab_contents or references [2,3] therein.
[2]: https://libgen.rocks/ads.php?md5=c66b6b15b434e145a5adf92ba3900144&downloadname=10.1007/bf01448052 -- short proof = https://link.springer.com/article/10.1007%2FBF01448052:-)
[3]: https://libgen.rocks/ads.php?md5=0b8573c90cf9d9a0e51b0746bcb22452 -- Didn't find elementary proof *)
    sorry
  show \<open>sqrt_op a \<ge>0\<close> and \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
    using * apply (smt (verit, ccfv_threshold) someI_ex sqrt_op_def)
    using * by (metis (mono_tags, lifting) someI_ex sqrt_op_def)
qed

(* Also in the "elementary proof" mentioned in sqrt_op_pos *)
lemma sqrt_op_unique:
  assumes \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close>
  shows \<open>b = sqrt_op a\<close>
  sorry

lemma sqrt_op_0[simp]: \<open>sqrt_op 0 = 0\<close>
  apply (rule sqrt_op_unique[symmetric])
  by auto

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


end
