theory Compact_Operators
  imports Tensor_Product.Misc_Tensor_Product_BO
"HOL-ex.Sketch_and_Explore"
begin

definition rank1 where \<open>rank1 A \<longleftrightarrow> (\<exists>x y. A = butterfly x y)\<close>

lemma rank1_0[simp]: \<open>rank1 0\<close>
  by (metis butterfly_0_right rank1_def)

lemma rank1_scaleC[simp]: \<open>rank1 (c *\<^sub>C a)\<close> if \<open>rank1 a\<close>
  by (metis butterfly_scaleC_left rank1_def that)

lemma rank1_scaleR[simp]: \<open>rank1 (c *\<^sub>R a)\<close> if \<open>rank1 a\<close>
  by (simp add: scaleR_scaleC that)

lemma rank1_uminus[simp]: \<open>rank1 (-a) = rank1 a\<close>
  by (metis add.inverse_inverse rank1_scaleC scaleC_minus1_left)

definition finite_rank where \<open>finite_rank A \<longleftrightarrow> A \<in> cspan (Collect rank1)\<close>

lemma finite_rank_0[simp]: \<open>finite_rank 0\<close>
  by (simp add: complex_vector.span_zero finite_rank_def)

lemma finite_rank_scaleC[simp]: \<open>finite_rank (c *\<^sub>C a)\<close> if \<open>finite_rank a\<close>
  using complex_vector.span_scale finite_rank_def that by blast

lemma finite_rank_scaleR[simp]: \<open>finite_rank (c *\<^sub>R a)\<close> if \<open>finite_rank a\<close>
  by (simp add: scaleR_scaleC that)

lemma finite_rank_uminus[simp]: \<open>finite_rank (-a) = finite_rank a\<close>
  by (metis add.inverse_inverse complex_vector.span_neg finite_rank_def)

lemma finite_rank_plus[simp]: \<open>finite_rank (a + b)\<close> if \<open>finite_rank a\<close> and \<open>finite_rank b\<close>
  using that by (auto simp: finite_rank_def complex_vector.span_add_eq2)

lemma finite_rank_minus[simp]: \<open>finite_rank (a - b)\<close> if \<open>finite_rank a\<close> and \<open>finite_rank b\<close>
  using complex_vector.span_diff finite_rank_def that(1) that(2) by blast

definition compact_op where \<open>compact_op A \<longleftrightarrow> A \<in> closure (Collect finite_rank)\<close>

lemma compact_op_0[simp]: \<open>compact_op 0\<close>
  by (meson closure_subset compact_op_def finite_rank_0 in_mono mem_Collect_eq)

lemma compact_op_scaleC[simp]: \<open>compact_op (c *\<^sub>C a)\<close> if \<open>compact_op a\<close>
proof (cases \<open>c = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  from that
  have \<open>a \<in> closure (Collect finite_rank)\<close>
    using compact_op_def by blast
  then have \<open>c *\<^sub>C a \<in> scaleC c ` closure (Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> = closure (scaleC c ` Collect finite_rank)\<close>
    by (simp add: closure_scaleC)
  also have \<open>\<dots> = closure (Collect finite_rank)\<close>
    by (simp add: False complex_vector.subspace_def csubspace_scaleC_invariant)
  finally show ?thesis
    using compact_op_def by blast
qed

lemma compact_op_scaleR[simp]: \<open>compact_op (c *\<^sub>R a)\<close> if \<open>compact_op a\<close>
  by (simp add: scaleR_scaleC that)
  

lemma compact_op_uminus[simp]: \<open>compact_op (-a) = compact_op a\<close>
  by (metis compact_op_scaleC scaleC_minus1_left verit_minus_simplify(4))

(* TODO move *)
lemma norm_plus_leq_norm_prod: \<open>norm (a + b) \<le> sqrt 2 * norm (a, b)\<close>
proof -
  have \<open>(norm (a + b))\<^sup>2 \<le> (norm a + norm b)\<^sup>2\<close>
    using norm_triangle_ineq by auto
  also have \<open>\<dots> \<le> 2 * ((norm a)\<^sup>2 + (norm b)\<^sup>2)\<close>
    by (smt (verit, best) power2_sum sum_squares_bound)
  also have \<open>\<dots> \<le> (sqrt 2 * norm (a, b))\<^sup>2\<close>
    by (auto simp: power_mult_distrib norm_prod_def simp del: power_mono_iff)
  finally show ?thesis
    by auto
qed

(* TODO move *)
lemma onorm_case_prod_plus_leq: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::real_normed_vector) \<le> sqrt 2\<close>
  apply (rule onorm_bound)
  using norm_plus_leq_norm_prod by auto

(* TODO move *)
lemma onorm_case_prod_plus: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::{real_normed_vector, not_singleton}) = sqrt 2\<close>
proof -
  obtain x :: 'a where \<open>x \<noteq> 0\<close>
    apply atomize_elim by auto
  show ?thesis
    apply (rule onormI[where x=\<open>(x,x)\<close>])
    using norm_plus_leq_norm_prod apply force
    using  \<open>x \<noteq> 0\<close>
    by (auto simp add: zero_prod_def norm_prod_def real_sqrt_mult
        simp flip: scaleR_2)
qed

(* TODO move *)
lemma bounded_linear_case_prod_plus[simp]: \<open>bounded_linear (case_prod plus)\<close>
  apply (rule bounded_linear_intro[where K=\<open>sqrt 2\<close>])
  by (auto simp add: scaleR_right_distrib norm_plus_leq_norm_prod mult.commute)

lemma compact_op_plus[simp]: \<open>compact_op (a + b)\<close> if \<open>compact_op a\<close> and \<open>compact_op b\<close>
proof -
  have \<open>a \<in> closure (Collect finite_rank)\<close> and \<open>b \<in> closure (Collect finite_rank)\<close>
    using compact_op_def that by auto
  then have \<open>(a,b) \<in> closure (Collect finite_rank \<times> Collect finite_rank)\<close>
    using closure_Times by blast
  then have \<open>a + b \<in> case_prod plus ` closure (Collect finite_rank \<times> Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> \<subseteq> closure (case_prod plus ` closure (Collect finite_rank \<times> Collect finite_rank))\<close>
    by (meson closure_subset)
  also have \<open>\<dots> = closure (case_prod plus ` (Collect finite_rank \<times> Collect finite_rank))\<close>
    apply (rule closure_bounded_linear_image_subset_eq)
    by simp
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank)\<close>
    by (simp add: closure_mono image_subset_iff)
  finally show ?thesis
    using compact_op_def by blast
qed

lemma compact_op_minus[simp]: \<open>compact_op (a - b)\<close> if \<open>compact_op a\<close> and \<open>compact_op b\<close>
  by (metis compact_op_plus compact_op_uminus that(1) that(2) uminus_add_conv_diff)

lemma compact_op_sgn[simp]: \<open>compact_op (sgn a) = compact_op a\<close>
proof (cases \<open>a = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  have \<open>compact_op (sgn a)\<close> if \<open>compact_op a\<close>
    by (simp add: sgn_cblinfun_def that)
  moreover have \<open>compact_op (norm a *\<^sub>R sgn a)\<close> if \<open>compact_op (sgn a)\<close>
    by (simp add: scaleR_scaleC that)
  moreover have \<open>norm a *\<^sub>R sgn a = a\<close>
    by (simp add: False sgn_div_norm)
  ultimately show ?thesis
    by auto
qed

typedef (overloaded) ('a::chilbert_space,'b::complex_normed_vector) compact_op = \<open>Collect compact_op :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_compact_op

instantiation compact_op :: (chilbert_space, complex_normed_vector) complex_normed_vector begin
lift_definition scaleC_compact_op :: \<open>complex \<Rightarrow> ('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is scaleC by simp
lift_definition uminus_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is uminus by simp
lift_definition zero_compact_op :: \<open>('a, 'b) compact_op\<close> is 0 by simp
lift_definition minus_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is minus by simp
lift_definition plus_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is plus by simp
lift_definition sgn_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is sgn by simp
lift_definition norm_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> real\<close> is norm .
lift_definition scaleR_compact_op :: \<open>real \<Rightarrow> ('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op\<close> is scaleR by simp
lift_definition dist_compact_op :: \<open>('a, 'b) compact_op \<Rightarrow> ('a, 'b) compact_op \<Rightarrow> real\<close> is dist .
definition [code del]:
  \<open>(uniformity :: (('a, 'b) compact_op \<times> ('a, 'b) compact_op) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})\<close>
definition open_compact_op :: "('a, 'b) compact_op set \<Rightarrow> bool"
  where [code del]: "open_compact_op S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"
instance
proof
  show "((*\<^sub>R) r :: ('a, 'b) compact_op \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r
    apply (rule ext) apply transfer 
    by (simp add: scaleR_scaleC)
  show "a + b + c = a + (b + c)"
    for a b c :: "('a, 'b) compact_op"
    apply transfer by simp
  show "a + b = b + a"
    for a b :: "('a, 'b) compact_op"
    apply transfer by simp
  show "0 + a = a"
    for a :: "('a, 'b) compact_op"
    apply transfer by simp
  show "- (a::('a, 'b) compact_op) + a = 0"
    for a :: "('a, 'b) compact_op"
    apply transfer by simp
  show "a - b = a + - b"
    for a b :: "('a, 'b) compact_op"
    apply transfer by simp
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex and x y :: "('a, 'b) compact_op"
    apply transfer by (simp add: scaleC_add_right)
  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a b :: complex and x :: "('a, 'b) compact_op"
    apply transfer by (simp add: scaleC_left.add)
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a b :: complex and x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "1 *\<^sub>C x = x"
    for x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "dist x y = norm (x - y)"
    for x y :: "('a, 'b) compact_op"
    apply transfer using dist_norm by auto
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real and x y :: "('a, 'b) compact_op"
    apply transfer
    by (simp add: scaleR_right_distrib)
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    for a b :: real and x :: "('a, 'b) compact_op"
    apply transfer by (simp add: scaleR_left.add)
  show "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
    for a b :: real and x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "1 *\<^sub>R x = x"
    for x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "sgn x = inverse (norm x) *\<^sub>R x"
    for x :: "('a, 'b) compact_op"
    apply transfer by (simp add: sgn_div_norm)
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) compact_op) y < e})"
    using uniformity_compact_op_def by blast
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    for U :: "('a, 'b) compact_op set"
    by (simp add: open_compact_op_def)
  show "(norm x = 0) \<longleftrightarrow> (x = 0)"
    for x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "norm (x + y) \<le> norm x + norm y"
    for x y :: "('a, 'b) compact_op"
    apply transfer using norm_triangle_ineq by blast
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    for a :: real and x :: "('a, 'b) compact_op"
    apply transfer by simp
  show "norm (a *\<^sub>C x) = cmod a * norm x"
    for a :: complex and x :: "('a, 'b) compact_op"
    apply transfer by simp
qed

end
