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

lemma rank1_butterfly[simp]: \<open>rank1 (butterfly x y)\<close>
  using rank1_def by blast

subsection \<open>Finite rank operators\<close>

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

lemma finite_rank_butterfly[simp]: \<open>finite_rank (butterfly x y)\<close>
  by (simp add: complex_vector.span_base finite_rank_def)

lemma finite_rank_sum_butterfly:
  assumes \<open>finite_rank a\<close>
  shows \<open>\<exists>x y (n::nat). a = (\<Sum>i<n. butterfly (x i) (y i))\<close>
proof -
  from assms
  have \<open>a \<in> cspan (Collect rank1)\<close>
    by (simp add: finite_rank_def)
  then obtain r t where \<open>finite t\<close> and t_rank1: \<open>t \<subseteq> Collect rank1\<close> and a_sum: \<open>a = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
  by (smt (verit, best) complex_vector.span_alt mem_Collect_eq)
  from \<open>finite t\<close> obtain \<iota> and n::nat where \<iota>: \<open>bij_betw \<iota> {..<n} t\<close>
    using bij_betw_from_nat_into_finite by blast
  define c where \<open>c i = r (\<iota> i) *\<^sub>C \<iota> i\<close> for i
  from \<iota> t_rank1
  have c_rank1: \<open>rank1 (c i)\<close> if \<open>i < n\<close> for i
    by (auto intro!: rank1_scaleC simp: c_def bij_betw_apply subset_iff that)
  have ac_sum: \<open>a = (\<Sum>i<n. c i)\<close>
    by (smt (verit, best) a_sum \<iota> c_def sum.cong sum.reindex_bij_betw)
  from c_rank1
  obtain x y where \<open>c i = butterfly (x i) (y i)\<close> if \<open>i < n\<close> for i
    apply atomize_elim unfolding rank1_def by metis
  with ac_sum show ?thesis
    by auto
qed    

subsection \<open>Compact operators\<close>

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
    by (simp add: that)
  moreover have \<open>norm a *\<^sub>R sgn a = a\<close>
    by (simp add: False sgn_div_norm)
  ultimately show ?thesis
    by auto
qed

typedef (overloaded) ('a::chilbert_space,'b::complex_normed_vector) compact_op = \<open>Collect compact_op :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  morphisms from_compact_op Abs_compact_op
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
end (* instantiation compact_op :: complex_normed_vector *)


lemma from_compact_op_plus: \<open>from_compact_op (a + b) = from_compact_op a + from_compact_op b\<close>
  apply transfer by simp

lemma from_compact_op_scaleC: \<open>from_compact_op (c *\<^sub>C a) = c *\<^sub>C from_compact_op a\<close>
  apply transfer by simp

lemma from_compact_op_norm[simp]: \<open>norm (from_compact_op a) = norm a\<close>
  apply transfer by simp

lemma compact_op_butterfly[simp]: \<open>compact_op (butterfly x y)\<close>
  by (metis closure_subset compact_op_def finite_rank_butterfly in_mono mem_Collect_eq)

lift_definition butterfly_co :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) compact_op\<close> is butterfly
  by simp

lemma butterfly_co_add_left: \<open>butterfly_co (a + a') b = butterfly_co a b + butterfly_co a' b\<close>
  apply transfer by (rule butterfly_add_left)

lemma butterfly_co_add_right: \<open>butterfly_co a (b + b') = butterfly_co a b + butterfly_co a b'\<close>
  apply transfer by (rule butterfly_add_right)

lemma butterfly_co_scaleR_left[simp]: "butterfly_co (r *\<^sub>R \<psi>) \<phi> = r *\<^sub>C butterfly_co \<psi> \<phi>"
  apply transfer by (rule butterfly_scaleR_left)

lemma butterfly_co_scaleR_right[simp]: "butterfly_co \<psi> (r *\<^sub>R \<phi>) = r *\<^sub>C butterfly_co \<psi> \<phi>"
  apply transfer by (rule butterfly_scaleR_right)

lemma butterfly_co_scaleC_left[simp]: "butterfly_co (r *\<^sub>C \<psi>) \<phi> = r *\<^sub>C butterfly_co \<psi> \<phi>"
  apply transfer by (rule butterfly_scaleC_left)

lemma butterfly_co_scaleC_right[simp]: "butterfly_co \<psi> (r *\<^sub>C \<phi>) = cnj r *\<^sub>C butterfly_co \<psi> \<phi>"
  apply transfer by (rule butterfly_scaleC_right)

lemma finite_rank_separating_on_compact_op:
  fixes F G :: \<open>('a::chilbert_space,'b::chilbert_space) compact_op \<Rightarrow> 'c::complex_normed_vector\<close>
  assumes \<open>\<And>x. finite_rank (from_compact_op x) \<Longrightarrow> F x = G x\<close>
  assumes \<open>bounded_clinear F\<close>
  assumes \<open>bounded_clinear G\<close>
  shows \<open>F = G\<close>
proof -
  define FG where \<open>FG x = F x - G x\<close> for x
  from \<open>bounded_clinear F\<close> and \<open>bounded_clinear G\<close>
  have \<open>bounded_clinear FG\<close>
    by (auto simp: FG_def[abs_def] intro!: bounded_clinear_sub)
  then have contFG': \<open>continuous_map euclidean euclidean FG\<close>
    by (simp add: Complex_Vector_Spaces.bounded_clinear.bounded_linear linear_continuous_on)
  have \<open>continuous_on (Collect compact_op) (FG o Abs_compact_op)\<close>
  proof
    fix a :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b" and e :: real
    assume "0 < e" and a_compact: "a \<in> Collect compact_op"
    have dist_rw: \<open>dist x' a = dist (Abs_compact_op x') (Abs_compact_op a)\<close> if \<open>compact_op x'\<close> for x'
      by (metis Abs_compact_op_inverse a_compact dist_compact_op.rep_eq mem_Collect_eq that)

    from \<open>bounded_clinear FG\<close>
    have \<open>continuous_on UNIV FG\<close>
      using contFG' continuous_map_iff_continuous2 by blast
    then have \<open>\<exists>d>0. \<forall>x'. dist x' (Abs_compact_op a) < d \<longrightarrow> dist (FG x') (FG (Abs_compact_op a)) \<le> e\<close>
      using \<open>e > 0\<close> apply (auto simp: continuous_on_iff) by (meson less_eq_real_def)
    then have \<open>\<exists>d>0. \<forall>x'. compact_op x' \<longrightarrow> dist (Abs_compact_op x') (Abs_compact_op a) < d \<longrightarrow> 
                  dist (FG (Abs_compact_op x')) (FG (Abs_compact_op a)) \<le> e\<close>
      by blast
    then show "\<exists>d>0. \<forall>x'\<in>Collect compact_op. dist x' a < d \<longrightarrow> dist ((FG \<circ> Abs_compact_op) x') ((FG \<circ> Abs_compact_op) a) \<le> e"
      by (simp add: dist_rw o_def)
  qed
  then have contFG: \<open>continuous_on (closure (Collect finite_rank)) (FG o Abs_compact_op)\<close>
    by (auto simp: compact_op_def[abs_def])

  have FG0: \<open>finite_rank a \<Longrightarrow> (FG o Abs_compact_op) a = 0\<close> for a
    by (metis (no_types, lifting) Abs_compact_op_inverse FG_def assms(1) closure_subset comp_apply compact_op_def eq_iff_diff_eq_0 mem_Collect_eq subset_eq)

  have \<open>(FG o Abs_compact_op) a = 0\<close> if \<open>compact_op a\<close> for a
    using contFG FG0
    apply (rule continuous_constant_on_closure)
    using that by (auto simp: compact_op_def)

  then have \<open>FG a = 0\<close> for a
    by (metis Abs_compact_op_cases comp_apply mem_Collect_eq)

  then show \<open>F = G\<close>
    by (auto intro!: ext simp: FG_def[abs_def])
qed



end
