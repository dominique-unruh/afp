theory Positive_Operators
  imports Tensor_Product.Misc_Tensor_Product_BO Tensor_Product.Strong_Operator_Topology
begin

unbundle cblinfun_notation

lemma cinner_pos_if_pos: \<open>f \<bullet>\<^sub>C (A *\<^sub>V f) \<ge> 0\<close> if \<open>A \<ge> 0\<close>
  using less_eq_cblinfun_def that by force

definition sqrt_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where \<open>sqrt_op a = (SOME b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a)\<close>

lemma norm_pos_op_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>0 \<le> A\<close> and \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
  unfolding cinner_sup_norm_cblinfun
  sorry


(* Proof follows https://link.springer.com/article/10.1007%2FBF01448052 *)
lemma TODO_name:
  assumes \<open>A = A*\<close>
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
  have \<open>- id_cblinfun \<le> S\<close>
    by (auto intro!: cblinfun_leI simp: S_def scaleR_scaleC cdot_square_norm k_def power2_eq_square
        simp flip: cinner_adj_left[where y=\<open>_ *\<^sub>V _\<close>] assms)
  with \<open>S \<le> 0\<close> have \<open>norm S \<le> 1\<close>
    using norm_pos_op_mono
    by (metis (no_types, opaque_lifting) Complex_Bounded_Linear_Function0.norm_blinfun_id_le dual_order.trans minus_le_iff neg_0_le_iff_le norm_minus_cancel)
  then have \<open>norm (S *\<^sub>V f) \<le> norm f\<close> for f
    by (meson dual_order.trans mult_left_le_one_le norm_cblinfun norm_ge_zero)
  then have norm_Snf: \<open>norm (cblinfun_power S n *\<^sub>V f) \<le> norm f\<close> for f n
    by (induction n, auto simp: cblinfun_power_Suc' intro: order.trans)
  then have fSnf: \<open>f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f) \<le> f \<bullet>\<^sub>C f\<close> for f n
    (* TODO: can we add a cmod on the rhs? then we can use Cauchy_Schwarz_ineq2 a little more directly.
       Check how it is used below. *)
    sorry
(*   then have Sn_herm: \<open>(pow S n)* = pow S n\<close> for n
    apply (rule_tac cinner_real_hermiteanI[symmetric])
    apply auto
    by - *)
  define b where \<open>b = (\<lambda>n. (1/2 gchoose n) *\<^sub>R cblinfun_power S n)\<close>
  define B0 B where \<open>B0 = infsum_in cstrong_operator_topology b UNIV\<close> and \<open>B = norm A *\<^sub>R B0\<close>
  have \<open>summable_on_in cstrong_operator_topology b UNIV\<close>    
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
    sorry
(*   then have \<open>has_sum_in cstrong_operator_topology b UNIV B0\<close>
    by -
  then have \<open>B0* = B0\<close>
    apply (rule hermitian_sum_hermitian_sot[rotated])
    by auto
  then have \<open>B = B*\<close>
    apply (rule hermitian_limit_hermitian_sot[symmetric])
    sorry *)
  have \<open>B0 \<ge> 0\<close>
  proof (rule positive_cblinfunI)
    fix f
    from has_sum_b
    have sum1: \<open>(\<lambda>n. f \<bullet>\<^sub>C (b n *\<^sub>V f)) summable_on UNIV\<close>
      using has_sum_cinner_left has_sum_in_cstrong_operator_topology summable_on_def by blast
    then have sum2: \<open>(\<lambda>n. f \<bullet>\<^sub>C (b n *\<^sub>V f)) summable_on UNIV - {0}\<close>
      sorry
    have sum3: \<open>(\<lambda>n. f \<bullet>\<^sub>C \<bar>1 / 2 gchoose n\<bar> *\<^sub>R f) summable_on UNIV - {0}\<close>
      sorry
    have sum4: \<open>(\<lambda>n. f \<bullet>\<^sub>C ((1 / 2 gchoose n) *\<^sub>R cblinfun_power S n *\<^sub>V f)) summable_on UNIV - {0}\<close>
      using b_def sum2 by force

    from has_sum_b
    have \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) = (\<Sum>\<^sub>\<infinity>n. f \<bullet>\<^sub>C (b n *\<^sub>V f))\<close>
      by (metis has_sum_cinner_left has_sum_in_cstrong_operator_topology infsumI)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C (b n *\<^sub>V f)) + f \<bullet>\<^sub>C (b 0 *\<^sub>V f)\<close>
      apply (subst infsum_Diff)
      using sum1 by auto
    also have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C ((1/2 gchoose n) *\<^sub>R cblinfun_power S n *\<^sub>V f))\<close>
      unfolding b_def by simp

(* TODO see paper. Note: S is negative *)

(*     also have \<open>\<dots> \<ge> f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C (- abs (1/2 gchoose n) *\<^sub>R cblinfun_power S n *\<^sub>V f))\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (simp flip: add: scaleR_scaleC del: of_real_minus)
      apply (rule infsum_mono_complex)
      subgoal sorry
      subgoal sorry
      apply (auto intro!: mult_right_mono complex_of_real_mono simp del: of_real_minus)
      apply auto
       apply (rule complex_of_real_mono)
      apply auto
    proof -
      fix x
      show \<open>- (complex_of_real \<bar>1 / 2 gchoose x\<bar> * (f \<bullet>\<^sub>C f))
         \<le> complex_of_real (1 / 2 gchoose x) * (f \<bullet>\<^sub>C (cblinfun_power S x *\<^sub>V f))\<close>
        by -
    qed *)
    also have \<open>\<dots> \<ge> (\<Sum>n. (1/2 gchoose n) * (f \<bullet>\<^sub>C f)) + (f \<bullet>\<^sub>C f)\<close> (is \<open>_ \<ge> \<dots>\<close>)
      sorry
    also have \<open>\<dots> = 0\<close>
      sorry
    finally show \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) \<ge> 0\<close>
      by simp
  qed
  then have \<open>B \<ge> 0\<close>
    sorry
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
    have \<open>S o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L S\<close>
      sorry
    then show ?thesis
      sorry
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
