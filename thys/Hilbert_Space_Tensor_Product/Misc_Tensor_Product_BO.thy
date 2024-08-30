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

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma sandwich_unitary_commutant: 
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>sandwich U ` commutant X = commutant (sandwich U ` X)\<close>
proof (rule Set.set_eqI)
  fix x
  let ?comm = \<open>\<lambda>a b. a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close>
  have \<open>x \<in> sandwich U ` commutant X \<longleftrightarrow> sandwich (U*) x \<in> commutant X\<close>
    apply (subst inj_image_mem_iff[symmetric, where f=\<open>sandwich (U*)\<close>])
    by (auto intro!: inj_sandwich_isometry simp: image_image
        simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm (sandwich (U*) x) y)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm x (sandwich U y))\<close>
    apply (rule ball_cong, simp)
    apply (simp add: sandwich_apply)
    by (smt (verit) assms cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD1 unitaryD2)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>sandwich U ` X. ?comm x y)\<close>
  by fast
  also have \<open>\<dots> \<longleftrightarrow> x \<in> commutant (sandwich U ` X)\<close>
    by (simp add: commutant_def)
  finally show \<open>(x \<in> (*\<^sub>V) (sandwich U) ` commutant X) \<longleftrightarrow> (x \<in> commutant ((*\<^sub>V) (sandwich U) ` X))\<close>
    by -
qed

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


end
