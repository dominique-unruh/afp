theory Compact_Operators
  imports Tensor_Product.Misc_Tensor_Product_BO HS2Ell2
    Sqrt_Babylonian.Sqrt_Babylonian_Auxiliary Wlog.Wlog
    "HOL-Analysis.Abstract_Metric_Spaces"
    Strong_Operator_Topology
begin

unbundle cblinfun_notation

(* TODO move to BO *)
lemma rank1_scaleR[simp]: \<open>rank1 (c *\<^sub>R a)\<close> if \<open>rank1 a\<close> and \<open>c \<noteq> 0\<close>
  by (simp add: rank1_scaleC scaleR_scaleC that(1) that(2))

lemma rank1_butterfly[simp]: \<open>rank1 (butterfly x y)\<close>
  apply (cases \<open>y = 0\<close>)
  by (auto intro: exI[of _ 0] simp: rank1_def butterfly_is_rank1)
  
subsection \<open>Finite rank operators\<close>

(* TODO: Actually should be defined as "finite_dimensional (range A)" *)
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
  apply (cases \<open>x \<noteq> 0 \<and> y \<noteq> 0\<close>)
  by (auto intro: complex_vector.span_base complex_vector.span_zero simp add: finite_rank_def rank1_butterfly)

lemma finite_rank_sum_butterfly:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>finite_rank a\<close>
  shows \<open>\<exists>x y (n::nat). a = (\<Sum>i<n. butterfly (x i) (y i))\<close>
proof -
  from assms
  have \<open>a \<in> cspan (Collect rank1)\<close>
    by (simp add: finite_rank_def)
  then obtain r t where \<open>finite t\<close> and t_rank1: \<open>t \<subseteq> Collect rank1\<close>
    and a_sum: \<open>a = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    by (smt (verit, best) complex_vector.span_alt mem_Collect_eq)
  from \<open>finite t\<close> obtain \<iota> and n::nat where \<iota>: \<open>bij_betw \<iota> {..<n} t\<close>
    using bij_betw_from_nat_into_finite by blast
  define c where \<open>c i = r (\<iota> i) *\<^sub>C \<iota> i\<close> for i
  from \<iota> t_rank1
  have c_rank1: \<open>rank1 (c i) \<or> c i = 0\<close> if \<open>i < n\<close> for i
    by (auto intro!: rank1_scaleC simp: c_def bij_betw_apply subset_iff that)
  have ac_sum: \<open>a = (\<Sum>i<n. c i)\<close>
    by (smt (verit, best) a_sum \<iota> c_def sum.cong sum.reindex_bij_betw)
  from c_rank1
  obtain x y where \<open>c i = butterfly (x i) (y i)\<close> if \<open>i < n\<close> for i
    apply atomize_elim
    apply (rule SMT.choices)
    using rank1_iff_butterfly by fastforce
  with ac_sum show ?thesis
    by auto
qed    

lemma finite_rank_sum: \<open>finite_rank (\<Sum>x\<in>F. f x)\<close> if \<open>\<And>x. x\<in>F \<Longrightarrow> finite_rank (f x)\<close>
  using that apply (induction F rule:infinite_finite_induct)
  by (auto intro!: finite_rank_plus)

lemma rank1_finite_rank: \<open>finite_rank a\<close> if \<open>rank1 a\<close>
  by (simp add: complex_vector.span_base finite_rank_def that)


lemma finite_rank_compose_left: 
  assumes \<open>finite_rank B\<close>
  shows \<open>finite_rank (A o\<^sub>C\<^sub>L B)\<close>
proof -
  from assms have \<open>B \<in> cspan (Collect rank1)\<close>
    by (simp add: finite_rank_def)
  then obtain F t where \<open>finite F\<close> and F_rank1: \<open>F \<subseteq> Collect rank1\<close> and \<open>B = (\<Sum>x\<in>F. t x *\<^sub>C x)\<close>
    by (smt (verit, best) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>A o\<^sub>C\<^sub>L B = (\<Sum>x\<in>F. t x *\<^sub>C (A o\<^sub>C\<^sub>L x))\<close>
    by (metis (mono_tags, lifting) cblinfun_compose_scaleC_right cblinfun_compose_sum_right sum.cong)
  also have \<open>\<dots> \<in> cspan (Collect finite_rank)\<close>
    apply (intro complex_vector.span_sum complex_vector.span_scale)
    using F_rank1
    by (auto intro!: complex_vector.span_base rank1_finite_rank rank1_compose_left simp: )
  also have \<open>\<dots> = Collect finite_rank\<close>
    by (metis (no_types, lifting) complex_vector.span_superset cspan_eqI finite_rank_def mem_Collect_eq subset_antisym subset_iff)
  finally show ?thesis
    by simp
qed


lemma finite_rank_compose_right:
  assumes \<open>finite_rank A\<close>
  shows \<open>finite_rank (A o\<^sub>C\<^sub>L B)\<close>
proof -
  from assms have \<open>A \<in> cspan (Collect rank1)\<close>
    by (simp add: finite_rank_def)
  then obtain F t where \<open>finite F\<close> and F_rank1: \<open>F \<subseteq> Collect rank1\<close> and \<open>A = (\<Sum>x\<in>F. t x *\<^sub>C x)\<close>
    by (smt (verit, best) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>A o\<^sub>C\<^sub>L B = (\<Sum>x\<in>F. t x *\<^sub>C (x o\<^sub>C\<^sub>L B))\<close>
    by (metis (mono_tags, lifting) cblinfun_compose_scaleC_left cblinfun_compose_sum_left sum.cong)
  also have \<open>\<dots> \<in> cspan (Collect finite_rank)\<close>
    apply (intro complex_vector.span_sum complex_vector.span_scale)
    using F_rank1
    by (auto intro!: complex_vector.span_base rank1_finite_rank rank1_compose_right simp: )
  also have \<open>\<dots> = Collect finite_rank\<close>
    by (metis (no_types, lifting) complex_vector.span_superset cspan_eqI finite_rank_def mem_Collect_eq subset_antisym subset_iff)
  finally show ?thesis
    by simp
qed

lemma rank1_Proj_singleton[iff]: \<open>rank1 (Proj (ccspan {x}))\<close>
  using Proj_range rank1_def by blast

lemma finite_rank_Proj_singleton[iff]: \<open>finite_rank (Proj (ccspan {x}))\<close>
  by (simp add: rank1_finite_rank)

(* TODO move *)
definition \<open>cfinite_dim S \<longleftrightarrow> (\<exists>B. finite B \<and> S \<subseteq> cspan B)\<close>

(* TODO move *)
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

(* TODO move *)
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

(* TODO move *)
lift_definition finite_dim_ccsubspace :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> bool\<close> is cfinite_dim.

lemma ccspan_finite_dim[intro]: \<open>finite_dim_ccsubspace (ccspan B)\<close> if \<open>finite B\<close>
  using ccspan_finite finite_dim_ccsubspace.rep_eq that by fastforce

lemma finite_rank_Proj_finite_dim:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>finite_rank (Proj S)\<close>
proof -
  from assms
  obtain B where \<open>is_ortho_set B\<close> and \<open>finite B\<close> and spanB: \<open>cspan B = space_as_set S\<close>
    unfolding finite_dim_ccsubspace.rep_eq
    using cfinite_dim_subspace_has_onb by force
  have \<open>Proj S = Proj (ccspan B)\<close>
    by (metis Proj.rep_eq \<open>finite B\<close> cblinfun_apply_inject ccspan_finite spanB)
  moreover have \<open>finite_rank (Proj (ccspan B))\<close>
    using \<open>finite B\<close> \<open>is_ortho_set B\<close> 
  proof induction
    case empty
    then show ?case
      by simp
  next
    case (insert x F)
    then have \<open>is_ortho_set F\<close>
      by (meson is_ortho_set_antimono subset_insertI)
    have \<open>Proj (ccspan (insert x F)) = proj x + Proj (ccspan F)\<close>
      apply (subst Proj_orthog_ccspan_insert)
      using insert apply (simp_all add: is_onb_def is_ortho_set_def)
      by fast
    moreover have \<open>finite_rank \<dots>\<close>
      apply (rule finite_rank_plus)
      by (auto intro!: finite_rank_Proj_singleton \<open>is_ortho_set F\<close> insert)
    ultimately show ?case 
      by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma finite_rank_Proj_finite:
  fixes F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>finite F\<close>
  shows \<open>finite_rank (Proj (ccspan F))\<close>
proof -
  obtain B where \<open>is_ortho_set B\<close> and \<open>finite B\<close> and \<open>cspan B = cspan F\<close>
    by (meson assms orthonormal_basis_of_cspan)
  have \<open>Proj (ccspan F) = Proj (ccspan B)\<close>
    by (simp add: \<open>cspan B = cspan F\<close> ccspan.abs_eq)
  moreover have \<open>finite_rank (Proj (ccspan B))\<close>
    using \<open>finite B\<close> \<open>is_ortho_set B\<close> 
  proof induction
    case empty
    then show ?case
      by simp
  next
    case (insert x F)
    then have \<open>is_ortho_set F\<close>
      by (meson is_ortho_set_antimono subset_insertI)
    have \<open>Proj (ccspan (insert x F)) = proj x + Proj (ccspan F)\<close>
      apply (subst Proj_orthog_ccspan_insert)
      using insert apply (simp_all add: is_onb_def is_ortho_set_def)
      by fast
    moreover have \<open>finite_rank \<dots>\<close>
      apply (rule finite_rank_plus)
      by (auto intro!: finite_rank_Proj_singleton \<open>is_ortho_set F\<close> insert)
    ultimately show ?case 
      by simp
  qed
  ultimately show ?thesis
    by simp
qed

(* TODO move *)
lemma finite_rank_cfinite_dim[simp]: \<open>finite_rank (a :: 'a :: {cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b :: complex_normed_vector)\<close>
proof -
  obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
    using is_onb_some_chilbert_basis by blast
  from \<open>is_onb B\<close> have [simp]: \<open>finite B\<close>
    by (auto intro!: cindependent_cfinite_dim_finite is_ortho_set_cindependent simp add: is_onb_def)
  have [simp]: \<open>cspan B = UNIV\<close>
  proof -
    from \<open>is_onb B\<close> have \<open>ccspan B = \<top>\<close>
      using is_onb_def by blast
    then have \<open>closure (cspan B) = UNIV\<close>
      by (metis ccspan.rep_eq space_as_set_top)
    then show ?thesis
      by simp
  qed
  have a_sum: \<open>a = (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b)\<close>
  proof (rule cblinfun_eq_on_UNIV_span[OF \<open>cspan B = UNIV\<close>])
    fix s assume [simp]: \<open>s \<in> B\<close>
    with \<open>is_onb B\<close> have \<open>norm s = 1\<close>
      by (simp add: is_onb_def)
    have 1: \<open>j \<noteq> s \<Longrightarrow> j \<in> B \<Longrightarrow> (a o\<^sub>C\<^sub>L selfbutter j) *\<^sub>V s = 0\<close> for j
      apply auto
      by (metis \<open>is_onb B\<close> \<open>s \<in> B\<close> cblinfun.scaleC_right is_onb_def is_ortho_set_def scaleC_eq_0_iff)
    have 2: \<open>a *\<^sub>V s = (if s \<in> B then (a o\<^sub>C\<^sub>L selfbutter s) *\<^sub>V s else 0)\<close>
      using \<open>norm s = 1\<close> \<open>s \<in> B\<close> by (simp add: cnorm_eq_1)
    show \<open>a *\<^sub>V s = (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b) *\<^sub>V s\<close>
      apply (subst cblinfun.sum_left)
      apply (subst sum_single[where i=s])
      using 1 2 by auto
  qed
  have \<open>finite_rank (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b)\<close>
    by (auto intro!: finite_rank_sum simp: cblinfun_comp_butterfly)
  with a_sum show ?thesis
    by simp
qed


subsection \<open>Compact operators\<close>

definition compact_map where \<open>compact_map f \<longleftrightarrow> clinear f \<and> compact (closure (f ` cball 0 1))\<close>

lemma \<open>bounded_clinear f\<close> if \<open>compact_map f\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.4.2 (a)\<close>
  thm bounded_clinear_def
proof (unfold bounded_clinear_def bounded_clinear_axioms_def, intro conjI)
  show \<open>clinear f\<close>
    using compact_map_def that by blast
  have \<open>compact (closure (f ` cball 0 1))\<close>
    using compact_map_def that by blast
  then have \<open>bounded (f ` cball 0 1)\<close>
    by (meson bounded_subset closure_subset compact_imp_bounded)
  then obtain K where *: \<open>norm (f x) \<le> K\<close> if \<open>norm x \<le> 1\<close> for x
    apply atomize_elim
    apply (simp add: bounded_iff dist_norm ball_def)
    by force
  have \<open>norm (f x) \<le> norm x * K\<close> for x
  proof (cases \<open>x = 0\<close>)
    case True
    then show ?thesis
      using \<open>clinear f\<close> complex_vector.linear_0 by force
  next
    case False
    have \<open>norm (f x) = norm (f (norm x *\<^sub>C sgn x))\<close>
      by simp
    also have \<open>\<dots> = norm x * norm (f (sgn x))\<close>
      by (smt (verit, best) \<open>clinear f\<close> complex_vector.linear_scale norm_ge_zero norm_of_real norm_scaleC)
    also have \<open>\<dots> \<le> norm x * K\<close>
      by (simp add: "*" mult_left_mono norm_sgn)
    finally show ?thesis
      by -
  qed
  then show \<open>\<exists>K. \<forall>x. norm (f x) \<le> norm x * K\<close>
    by blast
qed

lift_definition compact_op :: \<open>('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) \<Rightarrow> bool\<close> is compact_map.

lemma compact_op_def2: \<open>compact_op a \<longleftrightarrow> compact (closure (a ` cball 0 1))\<close>
  apply transfer
  using bounded_clinear.clinear compact_map_def by blast

(* TODO move *)
lemma compact_scaleC:
  fixes s :: "'a::complex_normed_vector set"
  assumes "compact s"
  shows "compact (scaleC c ` s)"
  by (auto intro!: compact_continuous_image assms continuous_at_imp_continuous_on)

lemma compact_op_0[simp]: \<open>compact_op 0\<close>
  by (simp add: compact_op_def2 image_constant[where x=0] mem_cball_leI[where x=0])

lemma compact_op_scaleC[simp]: \<open>compact_op (c *\<^sub>C a)\<close> if \<open>compact_op a\<close>
proof -
  have \<open>compact (closure (a ` cball 0 1))\<close>
    using compact_op_def2 that by blast
  then have *: \<open>compact (scaleC c ` closure (a ` cball 0 1))\<close>
    using compact_scaleC by blast
  have \<open>closure ((c *\<^sub>C a) ` cball 0 1) = closure (scaleC c ` a ` cball 0 1)\<close>
    by (metis (no_types, lifting) cblinfun.scaleC_left image_cong image_image)
  also have \<open>\<dots> = scaleC c ` closure (a ` cball 0 1)\<close>
    using closure_scaleC by blast
  finally have \<open>compact (closure ((c *\<^sub>C a) ` cball 0 1))\<close>
    using "*" by simp
  then show ?thesis
    using compact_op_def2 by blast
qed

lemma compact_op_scaleR[simp]: \<open>compact_op (c *\<^sub>R a)\<close> if \<open>compact_op a\<close>
  by (simp add: scaleR_scaleC that)

lemma compact_op_uminus[simp]: \<open>compact_op (-a) = compact_op a\<close>
  by (metis compact_op_scaleC scaleC_minus1_left verit_minus_simplify(4))

(* TODO move *)
lemma compact_closed_subset:
  assumes \<open>compact s\<close>
  assumes \<open>closed t\<close>
  assumes \<open>t \<subseteq> s\<close>
  shows \<open>compact t\<close>
  by (metis assms(1) assms(2) assms(3) compact_Int_closed inf.absorb_iff2)

lemma compact_op_plus[simp]: \<open>compact_op (a + b)\<close> if \<open>compact_op a\<close> and \<open>compact_op b\<close>
proof -
  have \<open>compact (closure (a ` cball 0 1))\<close>
    using compact_op_def2 that by blast
  moreover have \<open>compact (closure (b ` cball 0 1))\<close>
    using compact_op_def2 that by blast
  ultimately have compact_sum: 
    \<open>compact {x + y |x y. x \<in> closure ((*\<^sub>V) a ` cball 0 1) 
                        \<and> y \<in> closure ((*\<^sub>V) b ` cball 0 1)}\<close> (is \<open>compact ?sum\<close>)
    by (rule compact_sums)
  have \<open>compact (closure ((a + b) ` cball 0 1))\<close>
  proof -
    have \<open>((*\<^sub>V) (a + b) ` cball 0 1) \<subseteq> ?sum\<close>
      using cblinfun.real.add_left closure_subset image_subset_iff by blast
    then have \<open>closure ((*\<^sub>V) (a + b) ` cball 0 1) \<subseteq> closure ?sum\<close>
      by (meson closure_mono)
    also have \<open>\<dots> = ?sum\<close>
      using compact_sum
      by (auto intro!: closure_closed compact_imp_closed)
    finally show ?thesis
      apply (rule compact_closed_subset[rotated 2])
      using compact_sum by auto
  qed
  then show ?thesis
    using compact_op_def2 by blast
qed

lemma csubspace_compact_op: \<open>csubspace (Collect compact_op)\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.4.2 (b)\<close>
  by (simp add: complex_vector.subspace_def)

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


(* lemma compact_eq_totally_bounded':
  fixes s :: \<open>'a::metric_space set\<close>
  shows "compact s \<longleftrightarrow> complete s \<and> totally_bounded s"
  by (simp add: compact_eq_totally_bounded totally_bounded_metric ball_def) *)

(* lemma mtotally_bounded_totally_bounded:
  \<open>Met_TC.mtotally_bounded = (totally_bounded :: 'a::metric_space set \<Rightarrow> _)\<close>
proof (intro ext iffI)
  fix S :: \<open>'a set\<close>
  assume \<open>Met_TC.mtotally_bounded S\<close>
  then show \<open>totally_bounded S\<close>
    by (auto simp: Met_TC.mtotally_bounded_def totally_bounded_metric ball_def)
next
  fix S :: \<open>'a set\<close>
  assume asm: \<open>totally_bounded S\<close>
  show \<open>Met_TC.mtotally_bounded S\<close>
  proof (unfold Met_TC.mtotally_bounded_def, intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    from totally_bounded_metric[THEN iffD1, rule_format, OF asm this]
    obtain K where \<open>finite K\<close> and \<open>S \<subseteq> (\<Union>x\<in>K. {y. dist x y < \<epsilon>})\<close>
      by blast

    show \<open>\<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. Met_TC.mball x \<epsilon>)\<close>
      apply simp

    apply (simp add: Met_TC.mtotally_bounded_def totally_bounded_metric ball_def)

try0
sledgehammer [dont_slice]
by - *)

(* lemma totally_bounded_closure:
  fixes S :: \<open>'a::metric_space set\<close>
  assumes "totally_bounded S"
  shows "totally_bounded (closure S)"
  using Met_TC.mtotally_bounded_closure_of[of S] assms
  by (simp add: mtotally_bounded_totally_bounded) *)

lemma closed_compact_op: 
  shows \<open>closed (Collect (compact_op :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> bool))\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.4.2 (b)\<close>
proof (intro closed_sequential_limits[THEN iffD2] allI impI conjI)
  fix T and A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume asm: \<open>(\<forall>n. T n \<in> Collect compact_op) \<and> T \<longlonglongrightarrow> A\<close>
  have \<open>Met_TC.mtotally_bounded (A ` cball 0 1)\<close>
  proof (unfold Met_TC.mtotally_bounded_def, intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    define \<delta> where \<open>\<delta> = \<epsilon>/3\<close>
    then have \<open>\<delta> > 0\<close>
      using \<open>\<epsilon> > 0\<close> by simp
    from asm[unfolded LIMSEQ_def, THEN conjunct2, rule_format, OF \<open>\<delta> > 0\<close>]
    obtain n where dist_TA: \<open>dist (T n) A < \<delta>\<close>
      apply atomize_elim by auto
    from asm have \<open>compact_op (T n)\<close>
      by simp
    then have \<open>Met_TC.mtotally_bounded (T n ` cball 0 1)\<close>
      apply (subst Met_TC.mtotally_bounded_eq_compact_closure_of)
      by (auto intro!: simp: compact_op_def2 Met_TC.mtotally_bounded_eq_compact_closure_of)
    then obtain K where \<open>finite K\<close> and K_T: \<open>K \<subseteq> T n ` cball 0 1\<close> and 
      TK: \<open>T n ` cball 0 1 \<subseteq> (\<Union>k\<in>K. Met_TC.mball k \<delta>)\<close> 
      apply atomize_elim unfolding Met_TC.mtotally_bounded_def using \<open>\<delta> > 0\<close>
      by blast
    from \<open>finite K\<close> and K_T obtain H where \<open>finite H\<close> and \<open>H \<subseteq> cball 0 1\<close>
      and KTH: \<open>K = T n ` H\<close>
      by (meson finite_subset_image)
    from TK have TH: \<open>T n ` cball 0 1 \<subseteq> (\<Union>h\<in>H. ball (T n *\<^sub>V h) \<delta>)\<close>
      by (simp add: KTH)
    have \<open>A ` cball 0 1 \<subseteq> (\<Union>h\<in>H. ball (A h) \<epsilon>)\<close>
    proof (rule subsetI)
      fix x assume \<open>x \<in> (*\<^sub>V) A ` cball 0 1\<close>
      then obtain l where \<open>l \<in> cball 0 1\<close> and xl: \<open>x = A l\<close>
        by blast
      then have \<open>T n l \<in> T n ` cball 0 1\<close>
        by auto
      with TH obtain h where \<open>h \<in> H\<close> and \<open>T n l \<in> ball (T n h) \<delta>\<close>
        by blast
      then have dist_Tlh: \<open>dist (T n l) (T n h) < \<delta>\<close>
        by (simp add: dist_commute)
      have \<open>dist (A h) (A l) < \<epsilon>\<close>
      proof -
        have norm_h: \<open>norm h \<le> 1\<close>
          using \<open>H \<subseteq> cball 0 1\<close> \<open>h \<in> H\<close> mem_cball_0 by blast
        have norm_l: \<open>norm l \<le> 1\<close>
          using \<open>l \<in> cball 0 1\<close> by auto
        from dist_TA norm_h have \<open>dist (A h) (T n h) < \<delta>\<close>
          apply (subst dist_commute)
          using norm_cblinfun[of \<open>T n - A\<close> h]
          apply (simp add: dist_norm flip: cblinfun.diff_left)
          by (smt (verit, del_insts) mult.commute mult_left_le_one_le norm_ge_zero)
        moreover have \<open>dist (T n h) (T n l) < \<delta>\<close>
          using dist_Tlh by (metis dist_commute)
        moreover from dist_TA norm_l have \<open>dist (T n l) (A l) < \<delta>\<close>
          using norm_cblinfun[of \<open>T n - A\<close> l]
          apply (simp add: dist_norm flip: cblinfun.diff_left)
          by (smt (verit, del_insts) mult.commute mult_left_le_one_le norm_ge_zero)
        ultimately show ?thesis
          unfolding \<delta>_def
          by (rule dist_triangle_third)
      qed
      then show \<open>x \<in> (\<Union>h\<in>H. ball (A h) \<epsilon>) \<close>
        using \<open>h \<in> H\<close> by (auto intro!: simp: xl)
    qed
    then show \<open>\<exists>K. finite K \<and> K \<subseteq> (*\<^sub>V) A ` cball 0 1 \<and> 
              (*\<^sub>V) A ` cball 0 1 \<subseteq> (\<Union>x\<in>K. Met_TC.mball x \<epsilon>)\<close>
      using \<open>H \<subseteq> cball 0 1\<close>
      apply (auto intro!: exI[of _ \<open>A ` H\<close>] \<open>finite H\<close> simp: ball_def)
      by fastforce
  qed
  then have \<open>Met_TC.mtotally_bounded (closure (A ` cball 0 1))\<close>
    using Met_TC.mtotally_bounded_closure_of by auto
  then have \<open>compact (closure (A ` cball 0 1))\<close>
    by (simp_all add: Met_TC.mtotally_bounded_eq_compact_closure_of complete_UNIV_cuspace)
  then show \<open>A \<in> Collect compact_op\<close>
    using compact_op_def2 by blast
qed

lemma rank1_compact_op: \<open>compact_op a\<close> if \<open>rank1 a\<close>
proof -
  wlog \<open>a \<noteq> 0\<close>
    using negation by simp
  with that obtain \<psi> where im_a: \<open>a *\<^sub>S \<top> = ccspan {\<psi>}\<close> and \<open>\<psi> \<noteq> 0\<close>
    using rank1_def by fastforce
  define c where \<open>c = norm a / norm \<psi>\<close>
  have compact_\<psi>c: \<open>compact ((\<lambda>x. x *\<^sub>C \<psi>) ` cball 0 c)\<close>
  proof -
    have \<open>continuous_on (cball 0 c) (\<lambda>x. x *\<^sub>C \<psi>)\<close>
      by (auto intro!: continuous_at_imp_continuous_on)
    moreover have \<open>compact (cball (0::complex) c)\<close>
      by (simp add: compact_eq_bounded_closed)
    ultimately show ?thesis
      by (rule compact_continuous_image)
  qed
  have \<open>a ` cball 0 1 \<subseteq> (\<lambda>x. x *\<^sub>C \<psi>) ` cball 0 c\<close>
  proof (rule subsetI)
    fix \<phi>
    assume asm: \<open>\<phi> \<in> a ` cball 0 1\<close>
    then have \<open>\<phi> \<in> space_as_set (a *\<^sub>S \<top>)\<close>
      using cblinfun_apply_in_image by blast
    also have \<open>\<dots> = cspan {\<psi>}\<close>
      by (simp add: ccspan.rep_eq im_a)
    finally obtain d where d: \<open>\<phi> = d *\<^sub>C \<psi>\<close>
      by (metis complex_vector.span_breakdown_eq complex_vector.span_empty eq_iff_diff_eq_0 singletonD)
    from asm obtain \<gamma> where \<open>\<phi> = a \<gamma>\<close> and \<open>norm \<gamma> \<le> 1\<close>
      by force
    have \<open>cmod d * norm \<psi> = norm \<phi>\<close>
      by (simp add: d)
    also have \<open>\<dots> \<le> norm a * norm \<gamma>\<close>
      using \<open>\<phi> = a *\<^sub>V \<gamma>\<close> complex_of_real_mono norm_cblinfun by blast
    also have \<open>\<dots> \<le> norm a\<close>
      by (metis \<open>norm \<gamma> \<le> 1\<close> complex_of_real_mono mult.commute mult_left_le_one_le norm_ge_zero)
    finally have \<open>cmod d \<le> c\<close>
      by (smt (verit, ccfv_threshold) \<open>\<psi> \<noteq> 0\<close> c_def linordered_field_class.pos_divide_le_eq nonzero_eq_divide_eq norm_le_zero_iff)
    then show \<open>\<phi> \<in> (\<lambda>x. x *\<^sub>C \<psi>) ` cball 0 c\<close>
      by (auto simp: d)
  qed
  with compact_\<psi>c have cl_in_cl: \<open>closure (a ` cball 0 1) \<subseteq> ((\<lambda>x. x *\<^sub>C \<psi>) ` cball 0 c)\<close>
    using closure_mono[of _ \<open>((\<lambda>x. x *\<^sub>C \<psi>) ` cball 0 c)\<close>] compact_\<psi>c
    by (simp add: compact_imp_closed)
  with compact_\<psi>c show \<open>compact_op a\<close>
    using compact_closed_subset compact_op_def2 by blast
qed

lemma finite_rank_compact_op: \<open>compact_op a\<close> if \<open>finite_rank a\<close>
proof -
  from that obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> Collect rank1\<close>
    and a_decomp: \<open>a = (\<Sum>x\<in>t. r x *\<^sub>C x)\<close>
    by (auto simp: finite_rank_def complex_vector.span_explicit)
  from \<open>finite t\<close> \<open>t \<subseteq> Collect rank1\<close> show \<open>compact_op a\<close>
    apply (unfold a_decomp, induction)
    by (auto intro!: compact_op_plus compact_op_scaleC intro: rank1_compact_op)
qed

(* TODO move *)
definition separable where \<open>separable S \<longleftrightarrow> (\<exists>B. countable B \<and> S \<subseteq> closure B)\<close>

(* TODO move *)
lemma compact_imp_separable: \<open>separable S\<close> if \<open>compact S\<close> for S :: \<open>'a::metric_space set\<close>
proof -
  from that
  obtain K where \<open>finite (K n)\<close> and K_cover_S: \<open>S \<subseteq> (\<Union>k\<in>K n. ball k (1 / of_nat (n+1)))\<close> for n :: nat
  proof (atomize_elim, intro choice2 allI)
    fix n
    have \<open>S \<subseteq> (\<Union>k\<in>UNIV. ball k (1 / of_nat (n+1)))\<close>
      apply (auto intro!: simp: )
      by (smt (verit, del_insts) dist_eq_0_iff linordered_field_class.divide_pos_pos of_nat_less_0_iff)
    then show \<open>\<exists>K. finite K \<and> S \<subseteq> (\<Union>k\<in>K. ball k (1 / real (n + 1)))\<close>
      apply (simp add: compact_eq_Heine_Borel)
      by (meson Elementary_Metric_Spaces.open_ball compactE_image \<open>compact S\<close>)
  qed
  define B where \<open>B = (\<Union>n. K n)\<close>
  have \<open>countable B\<close>
    using B_def \<open>finite (K _)\<close> uncountable_infinite by blast
  have \<open>S \<subseteq> closure B\<close>
  proof (intro subsetI closure_approachable[THEN iffD2, rule_format])
    fix x assume \<open>x \<in> S\<close>
    fix e :: real assume \<open>e > 0\<close>
    define n :: nat where \<open>n = nat (ceiling (1/e))\<close>
    with \<open>e > 0\<close> have ne: \<open>1 / real (n+1) \<le> e\<close>
    proof -
      have \<open>1 / real (n+1) \<le> 1 / ceiling (1/e)\<close>
        by (simp add: \<open>0 < e\<close> linordered_field_class.frac_le n_def)
      also have \<open>\<dots> \<le> 1 / (1/e)\<close>
        by (smt (verit, del_insts) \<open>0 < e\<close> le_of_int_ceiling linordered_field_class.divide_pos_pos linordered_field_class.frac_le)
      also have \<open>\<dots> = e\<close>
        by simp
      finally show ?thesis
        by -
    qed
    have \<open>S \<subseteq> (\<Union>k\<in>K n. ball k (1 / of_nat (n+1)))\<close>
      using K_cover_S by presburger
    then obtain k where \<open>k \<in> K n\<close> and x_ball: \<open>x \<in> ball k (1 / of_nat (n+1))\<close>
      using \<open>x \<in> S\<close> by auto
    from \<open>k \<in> K n\<close> have \<open>k \<in> B\<close>
      using B_def by blast
    moreover from x_ball have \<open>dist k x < e\<close>
      by (smt (verit) ne mem_ball)
    ultimately show \<open>\<exists>k\<in>B. dist k x < e\<close>
      by fast
  qed
  show \<open>separable S\<close>
    using \<open>S \<subseteq> closure B\<close> \<open>countable B\<close> separable_def by blast
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


lemma bounded_products_sot_lim_imp_lim:
  \<comment> \<open>Implicit in the proof of \<^cite>\<open>conway2013course\<close>, Proposition II.4.4 (c)\<close>
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes lim_PA: \<open>limitin cstrong_operator_topology (\<lambda>x. P x o\<^sub>C\<^sub>L A) A F\<close>
    and \<open>compact_op A\<close>
    and P_leq_B: \<open>\<And>x. norm (P x) \<le> B\<close>
  shows \<open>((\<lambda>x. P x o\<^sub>C\<^sub>L A) \<longlongrightarrow> A) F\<close>
proof -
  wlog \<open>F \<noteq> \<bottom>\<close>
    using negation by simp
  wlog \<open>B \<noteq> 0\<close>
  proof -
    from negation assms have P0: \<open>P x = 0\<close> for x
      by auto
    from lim_PA have \<open>((\<lambda>x. 0) \<longlongrightarrow> Abs_cblinfun_sot A) F\<close>
      apply (simp add: flip: limitin_canonical_iff)
      apply (transfer fixing: P F)
      using P0 by simp
    moreover have \<open>((\<lambda>x. 0) \<longlongrightarrow> 0) F\<close>
      by simp
    ultimately have \<open>Abs_cblinfun_sot A = 0\<close>
      using \<open>F \<noteq> \<bottom>\<close> tendsto_unique by blast
    then have \<open>A = 0\<close>
      by (metis Abs_cblinfun_sot_inverse cstrong_operator_topology_topspace lim_PA limitin_def zero_cblinfun_sot.rep_eq)
    with P0 show ?thesis
      by simp
  qed
  have \<open>B > 0\<close>
  proof -
    from P_leq_B[of undefined] have \<open>B \<ge> 0\<close>
      by (smt (verit, del_insts) norm_ge_zero)
    with \<open>B \<noteq> 0\<close>
    show ?thesis
      by simp
  qed

  show ?thesis
  proof (rule metric_space_class.tendstoI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    define \<delta> \<gamma> T where \<open>\<delta> = \<epsilon>/4\<close> and \<open>\<gamma> = min \<delta> (\<delta>/B)\<close> and \<open>T x = P x o\<^sub>C\<^sub>L A\<close> for x
    then have \<open>\<delta> > 0\<close>
      using \<open>\<epsilon> > 0\<close> by simp
    then have \<open>\<gamma> > 0\<close>
      using \<open>B > 0\<close> by (simp add: \<gamma>_def)
    from \<open>compact_op A\<close> have \<open>Met_TC.mtotally_bounded (A ` cball 0 1)\<close>
      apply (subst Met_TC.mtotally_bounded_eq_compact_closure_of)
      by (auto intro!: simp: compact_op_def2 Met_TC.mtotally_bounded_eq_compact_closure_of)
    then obtain K where \<open>finite K\<close> and K_T: \<open>K \<subseteq> A ` cball 0 1\<close> and 
      AK: \<open>A ` cball 0 1 \<subseteq> (\<Union>k\<in>K. Met_TC.mball k \<gamma>)\<close> 
      apply atomize_elim unfolding Met_TC.mtotally_bounded_def using \<open>\<gamma> > 0\<close>
      by blast
    from \<open>finite K\<close> and K_T obtain H where \<open>finite H\<close> and \<open>H \<subseteq> cball 0 1\<close>
      and KAH: \<open>K = A ` H\<close>
      by (meson finite_subset_image)
    from AK have AH: \<open>A ` cball 0 1 \<subseteq> (\<Union>h\<in>H. ball (A *\<^sub>V h) \<gamma>)\<close>
      by (simp add: KAH)
    have \<open>\<forall>\<^sub>F x in F. \<forall>h\<in>H. dist (T x h) (A h) < \<delta>\<close>
      using lim_PA \<open>\<delta> > 0\<close>
      by (auto intro!: eventually_ball_finite \<open>finite H\<close>
          simp: limitin_cstrong_operator_topology T_def metric_space_class.tendsto_iff)
    then show \<open>\<forall>\<^sub>F x in F. dist (T x) A < \<epsilon>\<close>
    proof (rule eventually_mono)
      fix x
      assume asm: \<open>\<forall>h\<in>H. dist (T x *\<^sub>V h) (A *\<^sub>V h) < \<delta>\<close>
      have \<open>dist (T x l) (A l) \<le> 3 * \<delta>\<close> if \<open>norm l = 1\<close> for l
      proof -
        from that have \<open>A l \<in> A ` cball 0 1\<close>
          by auto
        with AH obtain h where \<open>h \<in> H\<close> and Al\<gamma>: \<open>A l \<in> ball (A h) \<gamma>\<close>
          by blast
        then have dist_Alh: \<open>dist (A l) (A h) < \<gamma>\<close>
          by (simp add: dist_commute)
        have \<open>dist (A l) (A h) < \<delta>\<close>
          using dist_Alh by (simp add: \<gamma>_def)
        moreover from asm have \<open>dist (A h) (T x h) < \<delta>\<close>
          by (simp add: \<open>h \<in> H\<close> dist_commute)
        moreover have \<open>dist (T x h) (T x l) < \<delta>\<close>
        proof -
          have \<open>dist (T x h) (T x l) \<le> norm (P x) * dist (A h) (A l)\<close>
            by (metis T_def cblinfun.real.diff_right cblinfun_apply_cblinfun_compose dist_norm norm_cblinfun)
          also from Al\<gamma> P_leq_B have \<open>\<dots> < B * \<gamma>\<close>
            by (smt (verit, ccfv_SIG) \<open>B \<noteq> 0\<close> linordered_semiring_strict_class.mult_le_less_imp_less linordered_semiring_strict_class.mult_strict_mono' mem_ball norm_ge_zero zero_le_dist)
          also have \<open>\<dots> \<le> B * (\<delta> / B)\<close>
            by (smt (verit, best) \<gamma>_def \<open>0 < B\<close> mult_left_mono)
          also have \<open>\<dots> \<le> \<delta>\<close>
            by (simp add: \<open>B \<noteq> 0\<close>)
          finally show ?thesis
            by -
        qed
        ultimately show ?thesis
          by (smt (verit) dist_commute dist_triangle2)
      qed
      then have \<open>dist (T x) A \<le> 3 * \<delta>\<close>
        unfolding dist_norm
        apply (auto intro!: norm_cblinfun_bound_unit simp: cblinfun.diff_left)
        using \<open>0 < \<delta>\<close> by linarith
      then show \<open>dist (T x) A < \<epsilon>\<close>
        apply (rule order.strict_trans1)
        using \<open>\<epsilon> > 0\<close> by (simp add: \<delta>_def)
    qed
  qed
qed

(* TODO move *)
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

lemma compact_op_finite_rank: 
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  shows \<open>compact_op A \<longleftrightarrow> A \<in> closure (Collect finite_rank)\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.4.4 (c)\<close>
proof (rule iffI)
  assume \<open>A \<in> closure (Collect finite_rank)\<close>
  then have \<open>A \<in> closure (Collect compact_op)\<close>
    by (metis closure_sequential finite_rank_compact_op mem_Collect_eq)
  also have \<open>\<dots> = Collect compact_op\<close>
    by (simp add: closed_compact_op)
  finally show \<open>compact_op A\<close>
    by simp
next
  assume \<open>compact_op A\<close>
  then have \<open>compact (closure (A ` cball 0 1))\<close>
    using compact_op_def2 by blast
  then have sep_A_ball: \<open>separable (closure (A ` cball 0 1))\<close>
    using compact_imp_separable by blast
  define L where \<open>L = closure (range A)\<close>
  obtain B :: \<open>nat \<Rightarrow> _\<close> where \<open>L \<subseteq> closure (range B)\<close>
  proof atomize_elim
    from sep_A_ball obtain B0 where \<open>countable B0\<close>
      and A_B0: \<open>A ` cball 0 1 \<subseteq> closure B0\<close>
      by (meson closure_subset order_trans separable_def)
    define B1 where \<open>B1 = (\<Union>n::nat. scaleR n ` B0)\<close>
    from \<open>countable B0\<close> have \<open>countable B1\<close>
      by (auto intro!: countable_UN countable_image simp: B1_def)
    have \<open>range A = (\<Union>n::nat. A ` scaleR n ` cball (0::'a) 1)\<close>
    proof -
      have \<open>UNIV = (\<Union>n::nat. scaleR n ` cball (0::'a) 1)\<close>
      proof (intro antisym subsetI UNIV_I)
        fix x :: 'a
        have \<open>x \<in> scaleR (nat (ceiling (norm x)) + 1) ` cball (0::'a) 1\<close>
          apply (rule image_eqI[where x=\<open>x /\<^sub>R (nat (ceiling (norm x)) + 1)\<close>])
           apply (auto intro!: simp: )
          by (smt (verit, ccfv_threshold) left_inverse mult_minus_left mult_mono' norm_ge_zero of_nat_ceiling)
        then show \<open>x \<in> (\<Union>x::nat. (*\<^sub>R) (real x) ` cball 0 1)\<close>
          by blast
      qed
      then show ?thesis
        by fastforce
    qed
    also have \<open>\<dots> = (\<Union>n::nat. scaleR n ` A ` cball 0 1)\<close>
      by (auto intro!: ext simp: cblinfun.scaleR_right image_comp)
    also have \<open>\<dots> \<subseteq> (\<Union>n::nat. scaleR n ` closure B0)\<close>
      using A_B0 by fastforce
    also have \<open>\<dots> \<subseteq> closure (\<Union>n::nat. scaleR n ` B0)\<close>
      by (metis (mono_tags, lifting) SUP_le_iff closure_closure closure_mono closure_scaleR closure_subset)
    also have \<open>\<dots> = closure B1\<close>
      using B1_def by fastforce
    finally have \<open>L \<subseteq> closure B1\<close>
      by (simp add: L_def closure_minimal)
    with \<open>countable B1\<close>
    show \<open>\<exists>B :: nat \<Rightarrow> _. L \<subseteq> closure (range B)\<close>
      by (metis L_def closure_eq_empty empty_not_UNIV image_is_empty range_from_nat_into subset_empty)
  qed
  define P T where \<open>P n = Proj (ccspan (B ` {..n}))\<close> 
    and \<open>T n = P n o\<^sub>C\<^sub>L A\<close> for n
  have \<open>limitin cstrong_operator_topology T A sequentially\<close>
  proof (intro limitin_cstrong_operator_topology[THEN iffD2, rule_format] metric_LIMSEQ_I)
(* Idea: Every point in L is close to some point B n.
   Then it must be even closer to ccspan (B ` {..n}).
   Then the proj must be close to that, too. *)
    fix h and \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    define Ah where \<open>Ah = A h\<close>
    have \<open>Ah \<in> closure (range B)\<close>
      by (metis L_def Ah_def \<open>L \<subseteq> closure (range B)\<close> cblinfun_apply_in_image cblinfun_image.rep_eq subsetD top_ccsubspace.rep_eq)
    then obtain x where \<open>x \<in> range B\<close> and \<open>dist x Ah < \<epsilon>\<close>
      apply atomize_elim
      using \<open>\<epsilon> > 0\<close> by (simp add: closure_approachable)
    then obtain n0 where x_n0: \<open>x = B n0\<close>
      by blast
    have \<open>dist (P n *\<^sub>V Ah) Ah < \<epsilon>\<close> if \<open>n \<ge> n0\<close> for n
    proof -
      have \<open>x \<in> space_as_set (P n *\<^sub>S \<top>)\<close>
        using \<open>n \<ge> n0\<close>
        by (auto intro!: ccspan_superset' simp: P_def x_n0)
      from Proj_nearest[OF this, of Ah]
      have \<open>dist (P n *\<^sub>V Ah) Ah \<le> dist x Ah\<close>
        by (simp add: P_def)
      with \<open>dist x Ah < \<epsilon>\<close> show ?thesis
        by auto
    qed  
    then show \<open>\<exists>n0. \<forall>n\<ge>n0. dist (T n *\<^sub>V h) (A *\<^sub>V h) < \<epsilon>\<close>
      unfolding T_def Ah_def by auto
  qed
  then have \<open>((\<lambda>x. P x o\<^sub>C\<^sub>L A) \<longlongrightarrow> A) sequentially\<close>
    unfolding T_def
    by (auto intro!: bounded_products_sot_lim_imp_lim[where B=1] \<open>compact_op A\<close> norm_is_Proj
        simp: P_def)
  moreover have \<open>finite_rank (P x o\<^sub>C\<^sub>L A)\<close> for x
    by (auto intro!: finite_rank_compose_right finite_rank_Proj_finite simp: P_def)
  ultimately show \<open>A \<in> closure (Collect finite_rank)\<close>
    using closure_sequential by force
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
  by (simp add: finite_rank_compact_op)

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
    by (auto simp: compact_op_finite_rank[abs_def])

  have FG0: \<open>finite_rank a \<Longrightarrow> (FG o Abs_compact_op) a = 0\<close> for a
    by (metis (no_types, lifting) Abs_compact_op_inverse FG_def assms(1) closure_subset comp_apply compact_op_finite_rank eq_iff_diff_eq_0 mem_Collect_eq subset_eq)

  have \<open>(FG o Abs_compact_op) a = 0\<close> if \<open>compact_op a\<close> for a
    using contFG FG0
    apply (rule continuous_constant_on_closure)
    using that by (auto simp: compact_op_finite_rank)

  then have \<open>FG a = 0\<close> for a
    by (metis Abs_compact_op_cases comp_apply mem_Collect_eq)

  then show \<open>F = G\<close>
    by (auto intro!: ext simp: FG_def[abs_def])
qed

lemma Proj_0_compl: \<open>Proj S x = 0\<close> if \<open>x \<in> space_as_set (-S)\<close>
  by (simp add: kernel_memberD that)

lemma trunc_ell2_as_Proj: \<open>trunc_ell2 S \<psi> = Proj (ccspan (ket ` S)) \<psi>\<close>
proof (rule cinner_ket_eqI)
  fix x
  have *: \<open>Proj (ccspan (ket ` S)) (ket x) = 0\<close> if \<open>x \<notin> S\<close>
    by (auto intro!: Proj_0_compl mem_ortho_ccspanI simp: that)
  have \<open>ket x \<bullet>\<^sub>C trunc_ell2 S \<psi> = of_bool (x\<in>S) * (ket x \<bullet>\<^sub>C \<psi>)\<close>
    by (simp add: cinner_ket_left trunc_ell2.rep_eq)
  also have \<open>\<dots> = Proj (ccspan (ket ` S)) (ket x) \<bullet>\<^sub>C \<psi>\<close>
    apply (cases \<open>x \<in> S\<close>)
     apply (subst Proj_fixes_image)
    by (auto simp add: * ccspan_superset')
  also have \<open>\<dots> = ket x \<bullet>\<^sub>C (Proj (ccspan (ket ` S)) *\<^sub>V \<psi>)\<close>
    by (simp add: adj_Proj flip: cinner_adj_left)
  finally show \<open>ket x \<bullet>\<^sub>C trunc_ell2 S \<psi> = ket x \<bullet>\<^sub>C (Proj (ccspan (ket ` S)) *\<^sub>V \<psi>)\<close>
    by -
qed


lemma unitary_between_bij_betw:
  assumes \<open>is_onb A\<close> \<open>is_onb B\<close>
  shows \<open>bij_betw ((*\<^sub>V) (unitary_between A B)) A B\<close>
  using bij_between_bases_bij[OF assms]
  apply (rule bij_betw_cong[THEN iffD1, rotated])
  by (simp add: assms(1) assms(2) unitary_between_apply)

lemma tendsto_finite_subsets_at_top_image:
  assumes \<open>inj_on g X\<close>
  shows \<open>(f \<longlongrightarrow> x) (finite_subsets_at_top (g ` X)) \<longleftrightarrow> ((\<lambda>S. f (g ` S)) \<longlongrightarrow> x) (finite_subsets_at_top X)\<close>
  by (simp add: filterlim_def assms o_def
      flip: filtermap_image_finite_subsets_at_top filtermap_compose)


(* TODO move *)
lemma Proj_onb_limit:
  shows \<open>is_onb A \<Longrightarrow> ((\<lambda>S. Proj (ccspan S) \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top A)\<close>
proof -
  have main: \<open>((\<lambda>S. Proj (ccspan S) \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top A)\<close> if \<open>is_onb A\<close>
    for \<psi> :: \<open>'b::{chilbert_space,not_singleton}\<close> and A
  proof -
    define U where \<open>U = unitary_between (ell2_to_hilbert* ` A) (range ket)\<close>
    have [simp]: \<open>unitary U\<close>
      by (simp add: U_def that unitary_between_unitary unitary_image_onb)
    have lim1: \<open>((\<lambda>S. trunc_ell2 S (U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi>)) \<longlongrightarrow> U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi>) (finite_subsets_at_top UNIV)\<close>
      by (rule trunc_ell2_lim_at_UNIV)
    have lim2: \<open>((\<lambda>S. ell2_to_hilbert *\<^sub>V U* *\<^sub>V trunc_ell2 S (U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi>)) \<longlongrightarrow> ell2_to_hilbert *\<^sub>V U* *\<^sub>V U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi>) (finite_subsets_at_top UNIV)\<close>
      apply (rule_tac cblinfun.tendsto, simp)
      apply (rule_tac cblinfun.tendsto, simp)
      by (fact lim1)
    have *: \<open>ell2_to_hilbert *\<^sub>V U* *\<^sub>V trunc_ell2 S (U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi>) 
            = Proj (ccspan ((ell2_to_hilbert o U* o ket) ` S)) \<psi>\<close> (is \<open>?lhs = ?rhs\<close>) for S
    proof -
      have \<open>?lhs = (sandwich ell2_to_hilbert *\<^sub>V sandwich (U*) *\<^sub>V Proj (ccspan (ket ` S))) *\<^sub>V \<psi>\<close>
        by (simp add: trunc_ell2_as_Proj sandwich_apply)
      also have \<open>\<dots> = Proj (ell2_to_hilbert *\<^sub>S U* *\<^sub>S ccspan (ket ` S)) *\<^sub>V \<psi>\<close>
        by (simp add: Proj_sandwich)
      also have \<open>\<dots> = Proj (ccspan (ell2_to_hilbert ` U* ` ket ` S)) *\<^sub>V \<psi>\<close>
        by (simp add: cblinfun_image_ccspan)
      also have \<open>\<dots> = ?rhs\<close>
        by (simp add: image_comp)
      finally show ?thesis
        by -
    qed
    have **: \<open>ell2_to_hilbert *\<^sub>V U* *\<^sub>V U *\<^sub>V ell2_to_hilbert* *\<^sub>V \<psi> = \<psi>\<close>
      by (simp add: lift_cblinfun_comp[OF unitaryD1] lift_cblinfun_comp[OF unitaryD2])
    have ***: \<open>range (ell2_to_hilbert o U* o ket) = A\<close> (is \<open>?lhs = _\<close>)
    proof -
      have \<open>bij_betw U (ell2_to_hilbert* ` A) (range ket)\<close>
        by (auto intro!: unitary_between_bij_betw that unitary_image_onb simp add: U_def)
      then have bijUadj: \<open>bij_betw (U*) (range ket) (ell2_to_hilbert* ` A)\<close>
        by (metis \<open>unitary U\<close> bij_betw_imp_surj_on inj_imp_bij_betw_inv unitary_adj_inv unitary_inj)
      have \<open>?lhs = ell2_to_hilbert ` U* ` range ket\<close>
        by (simp add: image_comp)
      also with bijUadj have \<open>\<dots> = ell2_to_hilbert ` (ell2_to_hilbert* ` A)\<close>
        by (metis bij_betw_imp_surj_on)
      also have \<open>\<dots> = A\<close>
        by (metis image_inv_f_f unitary_adj unitary_adj_inv unitary_ell2_to_hilbert unitary_inj)
      finally show ?thesis
        by -
    qed
    from lim2 have lim3: \<open>((\<lambda>S. Proj (ccspan ((ell2_to_hilbert o U* o ket) ` S)) \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
      unfolding * ** by -
    then have lim4: \<open>((\<lambda>S. Proj (ccspan S) \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top (range (ell2_to_hilbert o U* o ket)))\<close>
      apply (rule tendsto_finite_subsets_at_top_image[THEN iffD2, rotated])
      by (intro inj_compose unitary_inj unitary_ell2_to_hilbert unitary_adj[THEN iffD2] \<open>unitary U\<close> inj_ket)
    then show ?thesis
      unfolding *** by -
  qed
  assume \<open>is_onb A\<close>
  show ?thesis
  proof (cases \<open>class.not_singleton TYPE('a)\<close>)
    case True
    show ?thesis
      using chilbert_space_class.chilbert_space_axioms True \<open>is_onb A\<close>
      by (rule main[internalize_sort' 'b2])
  next
    case False
    then have \<open>\<psi> = 0\<close>
      by (rule not_not_singleton_zero)
    then show ?thesis
      by simp
  qed
qed

lemma finite_rank_dense_compact:
  fixes A :: \<open>'a::chilbert_space set\<close> and B :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))) = Collect compact_op\<close>
proof (rule Set.equalityI)
  show \<open>closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))) \<subseteq> Collect compact_op\<close>
  proof -
    have \<open>closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))) \<subseteq> closure (Collect finite_rank)\<close>
      apply (auto intro!: closure_mono simp: case_prod_beta)
      by (metis (mono_tags, lifting) complex_vector.span_minimal complex_vector.subspace_span finite_rank_butterfly finite_rank_def image_iff subset_iff)
    also have \<open>\<dots> = Collect compact_op\<close>
      by (simp add: Set.set_eqI compact_op_finite_rank)
    finally show ?thesis
      by -
  qed
  show \<open>Collect compact_op \<subseteq> closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
  proof -
    have \<open>Collect (compact_op :: 'b\<Rightarrow>\<^sub>C\<^sub>L'a \<Rightarrow> _) = closure (cspan (Collect rank1))\<close>
      by (simp add: compact_op_finite_rank[abs_def] finite_rank_def[abs_def])
    also have \<open>\<dots> \<subseteq> closure (cspan (closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))))\<close>
    proof (rule closure_mono, rule complex_vector.span_mono, rule subsetI)
      fix x :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> assume \<open>x \<in> Collect rank1\<close>
      then obtain a b where xab: \<open>x = butterfly a b\<close>
        using rank1_iff_butterfly by fastforce
      define f where \<open>f F G = butterfly (Proj (ccspan F) a) (Proj (ccspan G) b)\<close> for F G
      have lim: \<open>(case_prod f \<longlongrightarrow> x) (finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B)\<close>
      proof (rule tendstoI, subst dist_norm)
        fix e :: real assume \<open>e > 0\<close>
        define d where \<open>d = (if norm a = 0 \<and> norm b = 0 then 1 
                                  else e / (max (norm a) (norm b)) / 4)\<close>
        have d: \<open>norm a * d + norm a * d + norm b * d < e\<close>
        proof -
          have \<open>norm a * d \<le> e/4\<close>
            using \<open>e > 0\<close> apply (auto simp: d_def)
             apply (simp add: divide_le_eq)
            by (smt (z3) Extra_Ordered_Fields.mult_sign_intros(3) \<open>0 < e\<close> antisym_conv divide_le_eq less_imp_le linordered_field_class.mult_imp_div_pos_le mult_left_mono nice_ordered_field_class.dense_le nice_ordered_field_class.divide_nonneg_neg nice_ordered_field_class.divide_nonpos_pos nle_le nonzero_mult_div_cancel_left norm_imp_pos_and_ge ordered_field_class.sign_simps(5) split_mult_pos_le)
          moreover have \<open>norm b * d \<le> e/4\<close>
            using \<open>e > 0\<close> apply (auto simp: d_def)
             apply (simp add: divide_le_eq)
            by (smt (verit) linordered_field_class.mult_imp_div_pos_le mult_left_mono norm_le_zero_iff ordered_field_class.sign_simps(5))
          ultimately have \<open>norm a * d + norm a * d + norm b * d \<le> 3 * e / 4\<close>
            by linarith
          also have \<open>\<dots> < e\<close>
            by (simp add: \<open>0 < e\<close>)
          finally show ?thesis
            by -
        qed
        have [simp]: \<open>d > 0\<close>
          using \<open>e > 0\<close> apply (auto simp: d_def)
           apply (smt (verit, best) nice_ordered_field_class.divide_pos_pos norm_eq_zero norm_not_less_zero)
          by (smt (verit) linordered_field_class.divide_pos_pos zero_less_norm_iff)
        from Proj_onb_limit[where \<psi>=a, OF assms(1)]
        have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. norm (Proj (ccspan F) a - a) < d\<close>
          by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
        moreover from Proj_onb_limit[where \<psi>=b, OF assms(2)]
        have \<open>\<forall>\<^sub>F G in finite_subsets_at_top B. norm (Proj (ccspan G) b - b) < d\<close>
          by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
        ultimately have FG_close: \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              norm (Proj (ccspan F) a - a) < d \<and> norm (Proj (ccspan G) b - b) < d\<close>
          unfolding case_prod_beta
          by (rule eventually_prodI)
        have fFG_dist: \<open>norm (f F G - x) < e\<close> 
          if \<open>norm (Proj (ccspan F) a - a) < d\<close> and \<open>norm (Proj (ccspan G) b - b) < d\<close>
            and \<open>F \<subseteq> A\<close> and \<open>G \<subseteq> B\<close> for F G
        proof -
          have a_split: \<open>a = Proj (ccspan F) a + Proj (ccspan (A-F)) a\<close>
            using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
            apply (subst Proj_orthog_ccspan_union[symmetric])
             apply (metis DiffD1 DiffD2 in_mono that(3))
            using \<open>F \<subseteq> A\<close> by (auto intro!: simp: Un_absorb1)
          have b_split: \<open>b = Proj (ccspan G) b + Proj (ccspan (B-G)) b\<close>
                      using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
            apply (subst Proj_orthog_ccspan_union[symmetric])
             apply (metis DiffD1 DiffD2 in_mono that(4))
            using \<open>G \<subseteq> B\<close> by (auto intro!: simp: Un_absorb1)
          have n1: \<open>norm (f F (B-G)) \<le> norm a * d\<close> for F
          proof -
            have \<open>norm (f F (B-G)) \<le> norm a * norm (Proj (ccspan (B-G)) b)\<close>
              by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_butterfly)
            also have \<open>\<dots> \<le> norm a * norm (Proj (ccspan G) b - b)\<close>
              by (metis add_diff_cancel_left' b_split less_eq_real_def norm_minus_commute)
            also have \<open>\<dots> \<le> norm a * d\<close>
              by (meson less_eq_real_def mult_left_mono norm_ge_zero that(2))
            finally show ?thesis
              by -
          qed
          have n2: \<open>norm (f (A-F) G) \<le> norm b * d\<close> for G
          proof -
            have \<open>norm (f (A-F) G) \<le> norm b * norm (Proj (ccspan (A-F)) a)\<close>
              by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_butterfly mult.commute)
            also have \<open>\<dots> \<le> norm b * norm (Proj (ccspan F) a - a)\<close>
              by (smt (verit, best) a_split add_diff_cancel_left' minus_diff_eq norm_minus_cancel)
            also have \<open>\<dots> \<le> norm b * d\<close>
              by (meson less_eq_real_def mult_left_mono norm_ge_zero that(1))
            finally show ?thesis
              by -
          qed
          have \<open>norm (f F G - x) = norm (- f F (B-G) - f (A-F) (B-G) - f (A-F) G)\<close>
            unfolding xab
            apply (subst a_split, subst b_split)
            by (simp add: f_def butterfly_add_right butterfly_add_left)
          also have \<open>\<dots> \<le> norm (f F (B-G)) + norm (f (A-F) (B-G)) + norm (f (A-F) G)\<close>
            by (smt (verit, best) norm_minus_cancel norm_triangle_ineq4)
          also have \<open>\<dots> \<le> norm a * d + norm a * d + norm b * d\<close>
            using n1 n2
            by (meson add_mono_thms_linordered_semiring(1))
          also have \<open>\<dots> < e\<close>
            by (fact d)
          finally show ?thesis
            by -
        qed
        show \<open>\<forall>\<^sub>F FG in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. norm (case_prod f FG - x) < e\<close>
          apply (rule eventually_elim2)
            apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
             apply auto[2]
           apply (rule FG_close)
          using fFG_dist by fastforce
      qed
      have nontriv: \<open>finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B \<noteq> \<bottom>\<close>
        by (simp add: prod_filter_eq_bot)
      have inside: \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              case_prod f x \<in> cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
      proof (rule eventually_mp[where P=\<open>\<lambda>(F,G). finite F \<and> finite G\<close>])
        show \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. finite F \<and> finite G\<close>
          by (smt (verit) case_prod_conv eventually_finite_subsets_at_top_weakI eventually_prod_filter)
        have f_in_span: \<open>f F G \<in> cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))\<close> if [simp]: \<open>finite F\<close> \<open>finite G\<close> and \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> for F G
        proof -
          have \<open>Proj (ccspan F) a \<in> cspan F\<close>
            by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(1))
          then obtain r where ProjFsum: \<open>Proj (ccspan F) a = (\<Sum>x\<in>F. r x *\<^sub>C x)\<close>
            apply atomize_elim
            using complex_vector.span_finite[OF \<open>finite F\<close>]
            by auto
          have \<open>Proj (ccspan G) b \<in> cspan G\<close>
            by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(2))
          then obtain s where ProjGsum: \<open>Proj (ccspan G) b = (\<Sum>x\<in>G. s x *\<^sub>C x)\<close>
            apply atomize_elim
            using complex_vector.span_finite[OF \<open>finite G\<close>]
            by auto
          have \<open>butterfly \<xi> \<eta> \<in> (\<lambda>(\<xi>, \<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)\<close>
            if \<open>\<eta> \<in> G\<close> and \<open>\<xi> \<in> F\<close> for \<eta> \<xi>
            using \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> that by (auto intro!: pair_imageI)
          then show ?thesis
            by (auto intro!: complex_vector.span_sum complex_vector.span_scale
                complex_vector.span_base[where a=\<open>butterfly _ _\<close>]
                simp add: f_def ProjFsum ProjGsum butterfly_sum_left butterfly_sum_right)
        qed
        show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B.
                      (case x of (F, G) \<Rightarrow> finite F \<and> finite G) \<longrightarrow> (case x of (F, G) \<Rightarrow> f F G) \<in> cspan ((\<lambda>(\<xi>, \<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
          apply (rule eventually_mono)
           apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
          by (auto intro!: f_in_span)
      qed
      show \<open>x \<in> closure (cspan ((\<lambda>(\<xi>, \<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
        using lim nontriv inside by (rule limit_in_closure)
    qed
    also have \<open>\<dots> = closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
      by (simp add: complex_vector.span_eq_iff[THEN iffD2])
    finally show ?thesis
      by -
  qed
qed

subsection \<open>Spectral decomposition\<close>

(* TODO. Currently in Unsorted_HSTP.thy *)

end
