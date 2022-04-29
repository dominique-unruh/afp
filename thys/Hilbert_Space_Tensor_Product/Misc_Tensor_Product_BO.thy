section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

lemma norm_cblinfun_bound_dense:
  assumes \<open>0 \<le> b\<close>
  assumes S: \<open>closure S = UNIV\<close>
  assumes bound: \<open>\<And>x. x\<in>S \<Longrightarrow> norm (cblinfun_apply f x) \<le> b * norm x\<close>
  shows \<open>norm f \<le> b\<close>
proof -
  have 1: \<open>continuous_on UNIV (\<lambda>a. norm (f *\<^sub>V a))\<close>
    apply (intro continuous_on_norm linear_continuous_on)
    by (simp add: Complex_Vector_Spaces.bounded_clinear.bounded_linear cblinfun.bounded_clinear_right)
  have 2: \<open>continuous_on UNIV (\<lambda>a. b * norm a)\<close>
    using continuous_on_mult_left continuous_on_norm_id by blast
  have \<open>norm (cblinfun_apply f x) \<le> b * norm x\<close> for x
    apply (rule on_closure_leI[where x=x and S=S])
    using S bound 1 2 by auto
  then show \<open>norm f \<le> b\<close>
    apply (rule_tac norm_cblinfun_bound)
    using \<open>0 \<le> b\<close> by auto
qed

lemma orthogonal_complement_of_cspan: \<open>orthogonal_complement A = orthogonal_complement (cspan A)\<close>
  by (metis (no_types, opaque_lifting) closed_csubspace.subspace complex_vector.span_minimal complex_vector.span_superset double_orthogonal_complement_increasing orthogonal_complement_antimono orthogonal_complement_closed_subspace subset_antisym)

lemma orthogonal_complement_orthogonal_complement_closure_cspan:
  \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close> for S :: \<open>'a::chilbert_space set\<close>
proof -
  have \<open>orthogonal_complement (orthogonal_complement S) = orthogonal_complement (orthogonal_complement (closure (cspan S)))\<close>
    by (simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  also have \<open>\<dots> = closure (cspan S)\<close>
    by simp
  finally show \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close>
    by -
qed

lemma dense_span_separating: \<open>closure (cspan S) = UNIV \<Longrightarrow> bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
proof -
  fix F G :: \<open>'a \<Rightarrow> 'b\<close>
  assume dense: \<open>closure (cspan S) = UNIV\<close>
  assume [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
  assume \<open>\<forall>x\<in>S. F x = G x\<close>
  then have \<open>F x = G x\<close> if \<open>x \<in> cspan S\<close> for x
    apply (rule_tac complex_vector.linear_eq_on[of F G _ S])
    using that by (auto simp: bounded_clinear.clinear)
  then show \<open>F = G\<close>
    apply (rule_tac ext)
    apply (rule on_closure_eqI[of \<open>cspan S\<close> F G])
    using dense by (auto intro!: continuous_at_imp_continuous_on clinear_continuous_at)
qed

lemma separating_dense_span: 
  assumes \<open>\<And>F G :: 'a::chilbert_space \<Rightarrow> 'b::{complex_normed_vector,not_singleton}. 
           bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
  shows \<open>closure (cspan S) = UNIV\<close>
proof -
  have \<open>\<psi> = 0\<close> if \<open>\<psi> \<in> orthogonal_complement S\<close> for \<psi>
  proof -
    obtain \<phi> :: 'b where \<open>\<phi> \<noteq> 0\<close>
      by fastforce
    have \<open>(\<lambda>x. cinner \<psi> x *\<^sub>C \<phi>) = (\<lambda>_. 0)\<close> 
      apply (rule assms[rule_format])
      using orthogonal_complement_orthoI that
      by (auto simp add: bounded_clinear_cinner_right bounded_clinear_scaleC_const)
    then have \<open>cinner \<psi> \<psi> = 0\<close>
      by (meson \<open>\<phi> \<noteq> 0\<close> scaleC_eq_0_iff)
    then show \<open>\<psi> = 0\<close>
      by auto
  qed
  then have \<open>orthogonal_complement (orthogonal_complement S) = UNIV\<close>
    by (metis UNIV_eq_I cinner_zero_right orthogonal_complementI)
  then show \<open>closure (cspan S) = UNIV\<close>
    by (simp add: orthogonal_complement_orthogonal_complement_closure_cspan)
qed


lemma ortho_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> closure (cspan B) = UNIV\<close>
proof -
  define on where \<open>on B \<longleftrightarrow> B \<supseteq> S \<and> is_ortho_set B\<close> for B :: \<open>'a set\<close>
  have \<open>\<exists>B\<in>Collect on. \<forall>B'\<in>Collect on. B \<subseteq> B' \<longrightarrow> B' = B\<close>
  proof (rule subset_Zorn_nonempty; simp)
    show \<open>\<exists>S. on S\<close>
      apply (rule exI[of _ S])
      using assms on_def by fastforce
  next
    fix C :: \<open>'a set set\<close>
    assume \<open>C \<noteq> {}\<close>
    assume \<open>subset.chain (Collect on) C\<close>
    then have C_on: \<open>B \<in> C \<Longrightarrow> on B\<close> and C_order: \<open>B \<in> C \<Longrightarrow> B' \<in> C \<Longrightarrow> B \<subseteq> B' \<or> B' \<subseteq> B\<close> for B B'
      by (auto simp: subset.chain_def)
    have \<open>is_orthogonal x y\<close> if \<open>x\<in>\<Union>C\<close> \<open>y\<in>\<Union>C\<close> \<open>x \<noteq> y\<close> for x y
      by (smt (verit) UnionE C_order C_on on_def is_ortho_set_def subsetD that(1) that(2) that(3))
    moreover have \<open>0 \<notin> \<Union> C\<close>
      by (meson UnionE C_on is_ortho_set_def on_def)
    moreover have \<open>\<Union>C \<supseteq> S\<close>
      using C_on \<open>C \<noteq> {}\<close> on_def by blast
    ultimately show \<open>on (\<Union> C)\<close>
      unfolding on_def is_ortho_set_def by simp
  qed
  then obtain B where \<open>on B\<close> and B_max: \<open>B' \<supseteq> B \<Longrightarrow> on B' \<Longrightarrow> B=B'\<close> for B'
    by auto
  have \<open>\<psi> = 0\<close> if \<psi>ortho: \<open>\<forall>b\<in>B. is_orthogonal \<psi> b\<close> for \<psi> :: 'a
  proof (rule ccontr)
    assume \<open>\<psi> \<noteq> 0\<close>
    define \<phi> B' where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close> and \<open>B' = B \<union> {\<phi>}\<close>
    have [simp]: \<open>norm \<phi> = 1\<close>
      using \<open>\<psi> \<noteq> 0\<close> by (auto simp: \<phi>_def)
    have \<phi>ortho: \<open>is_orthogonal \<phi> b\<close> if \<open>b \<in> B\<close> for b
      using \<psi>ortho that \<phi>_def  apply auto
      by (simp add: scaleR_scaleC)
    have orthoB': \<open>is_orthogonal x y\<close> if \<open>x\<in>B'\<close> \<open>y\<in>B'\<close> \<open>x \<noteq> y\<close> for x y
      using that \<open>on B\<close> \<phi>ortho \<phi>ortho[THEN is_orthogonal_sym[THEN iffD1]]
      by (auto simp: B'_def on_def is_ortho_set_def)
    have B'0: \<open>0 \<notin> B'\<close>
      using B'_def \<open>norm \<phi> = 1\<close> \<open>on B\<close> is_ortho_set_def on_def by fastforce
    have \<open>S \<subseteq> B'\<close>
      using B'_def \<open>on B\<close> on_def by auto
    from orthoB' B'0 \<open>S \<subseteq> B'\<close> have \<open>on B'\<close>
      by (simp add: on_def is_ortho_set_def)
    with B_max have \<open>B = B'\<close>
      by (metis B'_def Un_upper1)
    then have \<open>\<phi> \<in> B\<close>
      using B'_def by blast
    then have \<open>is_orthogonal \<phi> \<phi>\<close>
      using \<phi>ortho by blast
    then show False
      using B'0 \<open>B = B'\<close> \<open>\<phi> \<in> B\<close> by fastforce
  qed 
  then have \<open>orthogonal_complement B = {0}\<close>
    by (auto simp: orthogonal_complement_def)
  then have \<open>UNIV = orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (closure (cspan B)))\<close>
    by (metis (mono_tags, opaque_lifting) \<open>orthogonal_complement B = {0}\<close> cinner_zero_left complex_vector.span_superset empty_iff insert_iff orthogonal_complementI orthogonal_complement_antimono orthogonal_complement_of_closure subsetI subset_antisym)
  also have \<open>\<dots> = closure (cspan B)\<close>
    apply (rule double_orthogonal_complement_id)
    by simp
  finally have \<open>closure (cspan B) = UNIV\<close>
    by simp
  with \<open>on B\<close> show ?thesis
    by (auto simp: on_def)
qed

(* TODO: replace vector_space.span_image_scale *)
lemma (in vector_space) span_image_scale:
  assumes nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
  shows "span ((\<lambda>x. c x *s x) ` S) = span S"
proof
  have \<open>((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (metis (mono_tags, lifting) image_subsetI in_mono local.span_superset local.subspace_scale local.subspace_span)
  then show \<open>span ((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (simp add: local.span_minimal)
next
  have \<open>x \<in> span ((\<lambda>x. c x *s x) ` S)\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>x = inverse (c x) *s c x *s x\<close>
      by (simp add: nz that)
    moreover have \<open>c x *s x \<in> (\<lambda>x. c x *s x) ` S\<close>
      using that by blast
    ultimately show ?thesis
      by (metis local.span_base local.span_scale)
  qed
  then show \<open>span S \<subseteq> span ((\<lambda>x. c x *s x) ` S)\<close>
    by (simp add: local.span_minimal subsetI)
qed

definition is_onb where \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> ccspan E = \<top>\<close>

lemma orthonormal_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_onb B\<close>
proof -
  from \<open>is_ortho_set S\<close>
  obtain B where \<open>is_ortho_set B\<close> and \<open>B \<supseteq> S\<close> and \<open>closure (cspan B) = UNIV\<close>
    using ortho_basis_exists by blast
  define B' where \<open>B' = (\<lambda>x. x /\<^sub>R norm x) ` B\<close>
  have \<open>S = (\<lambda>x. x /\<^sub>R norm x) ` S\<close>
    by (simp add: assms(2))
  then have \<open>B' \<supseteq> S\<close>
    using B'_def \<open>S \<subseteq> B\<close> by blast
  moreover 
  have \<open>ccspan B' = \<top>\<close>
    apply (transfer fixing: B')
    apply (simp add: B'_def scaleR_scaleC)
    apply (subst complex_vector.span_image_scale)
    using \<open>is_ortho_set B\<close> \<open>closure (cspan B) = UNIV\<close> is_ortho_set_def by auto
  moreover have \<open>is_ortho_set B'\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis cinner_simps(5) is_orthogonal_sym mult_zero_right scaleR_scaleC)
  moreover have \<open>\<forall>b\<in>B'. norm b = 1\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis field_class.field_inverse norm_eq_zero)
  ultimately show ?thesis
    by (auto simp: is_onb_def)
qed


lemma bounded_clinear_equal_ket:
  fixes f g :: \<open>'a ell2 \<Rightarrow> _\<close>
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>bounded_clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule bounded_clinear_eq_on[of f g \<open>range ket\<close>])
  using assms by auto

lemma bounded_antilinear_equal_ket:
  fixes f g :: \<open>'a ell2 \<Rightarrow> _\<close>
  assumes \<open>bounded_antilinear f\<close>
  assumes \<open>bounded_antilinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule bounded_antilinear_eq_on[of f g \<open>range ket\<close>])
  using assms by auto

lemma cspan_eqI:
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> a\<in>cspan B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> b\<in>cspan A\<close>
  shows \<open>cspan A = cspan B\<close>
  apply (rule complex_vector.span_subspace[rotated])
    apply (rule complex_vector.span_minimal)
  using assms by auto

(* TODO: bounded_linear is enough *)
lemma infsum_bounded_clinear:
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  apply (rule infsum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right
  by (auto simp: clinear_continuous_within)

(* TODO: bounded_linear is enough *)
lemma has_sum_bounded_clinear: 
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close>
  apply (rule has_sum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right apply auto
  using clinear_continuous_within isCont_def by fastforce

(* TODO: bounded_linear is enough *)
lemma abs_summable_on_bounded_clinear:
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(f o g) abs_summable_on S\<close>
proof -
  have bound: \<open>norm (f (g x)) \<le> onorm f * norm (g x)\<close> for x
    apply (rule onorm)
    by (simp add: bounded_clinear.bounded_linear assms(1))

  from assms(2) have \<open>(\<lambda>x. onorm f *\<^sub>C g x) abs_summable_on S\<close>
    by (auto simp: norm_scaleC intro!: summable_on_cmult_right)
  then have \<open>(\<lambda>x. f (g x)) abs_summable_on S\<close>
    apply (rule abs_summable_on_comparison_test)
    using bound by (auto simp: bounded_clinear.bounded_linear assms(1) onorm_pos_le)
  then show ?thesis
    by auto
qed

lemma infsum_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
  apply (rule infsum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma has_sum_cblinfun_apply:
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (\<lambda>x. A *\<^sub>V g x) S (A *\<^sub>V x)\<close>
  apply (rule has_sum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma abs_summable_on_cblinfun_apply:
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) abs_summable_on S\<close>
  using cblinfun.bounded_clinear_right assms
  by (rule abs_summable_on_bounded_clinear[unfolded o_def])

lemma trunc_ell2_UNIV[simp]: \<open>trunc_ell2 UNIV \<psi> = \<psi>\<close>
  apply transfer by simp

lemma ell2_norm_square: \<open>(ell2_norm x)\<^sup>2 = (\<Sum>\<^sub>\<infinity>i. (cmod (x i))\<^sup>2)\<close>
  unfolding ell2_norm_def
  apply (subst real_sqrt_pow2)
   apply (meson Extra_General.infsum_nonneg zero_le_power2)
  by simp

lemma trunc_ell2_norm_mono: \<open>M \<subseteq> N \<Longrightarrow> norm (trunc_ell2 M \<psi>) \<le> norm (trunc_ell2 N \<psi>)\<close>
proof (rule power2_le_imp_le[rotated], force, transfer)
  fix M N :: \<open>'a set\<close> and \<psi> :: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>M \<subseteq> N\<close> and \<open>has_ell2_norm \<psi>\<close>
  have \<open>(ell2_norm (\<lambda>i. if i \<in> M then \<psi> i else 0))\<^sup>2 = (\<Sum>\<^sub>\<infinity>i\<in>M. (cmod (\<psi> i))\<^sup>2)\<close>
    unfolding ell2_norm_square
    apply (rule infsum_cong_neutral)
    by auto
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>N. (cmod (\<psi> i))\<^sup>2)\<close>
    apply (rule infsum_mono2)
    using \<open>has_ell2_norm \<psi>\<close> \<open>M \<subseteq> N\<close>
    by (auto simp add: ell2_norm_square has_ell2_norm_def simp flip: norm_power intro: summable_on_subset_banach)
  also have \<open>\<dots> = (ell2_norm (\<lambda>i. if i \<in> N then \<psi> i else 0))\<^sup>2\<close>
    unfolding ell2_norm_square
    apply (rule infsum_cong_neutral)
    by auto
  finally show \<open>(ell2_norm (\<lambda>i. if i \<in> M then \<psi> i else 0))\<^sup>2 \<le> (ell2_norm (\<lambda>i. if i \<in> N then \<psi> i else 0))\<^sup>2\<close>
    by -
qed

lemma trunc_ell2_twice[simp]: \<open>trunc_ell2 M (trunc_ell2 N \<psi>) = trunc_ell2 (M\<inter>N) \<psi>\<close>
  apply transfer by auto

lemma trunc_ell2_union: \<open>trunc_ell2 (M \<union> N) \<psi> = trunc_ell2 M \<psi> + trunc_ell2 N \<psi> - trunc_ell2 (M\<inter>N) \<psi>\<close>
  apply transfer by auto

lemma trunc_ell2_union_disjoint: \<open>M\<inter>N = {} \<Longrightarrow> trunc_ell2 (M \<union> N) \<psi> = trunc_ell2 M \<psi> + trunc_ell2 N \<psi>\<close>
  by (simp add: trunc_ell2_union)

lemma trunc_ell2_union_Diff: \<open>M \<subseteq> N \<Longrightarrow> trunc_ell2 (N-M) \<psi> = trunc_ell2 N \<psi> - trunc_ell2 M \<psi>\<close>
  using trunc_ell2_union_disjoint[where M=\<open>N-M\<close> and N=M and \<psi>=\<psi>]
  by (simp add: Un_commute inf.commute le_iff_sup)


(* TODO replace existing lemma (strengthening) *)
thm finite_subsets_at_top_inter
lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) = finite_subsets_at_top A"
proof (subst filter_eq_iff, intro allI iffI)
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (finite_subsets_at_top A)"
  then show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
next
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
  then obtain X where \<open>finite X\<close> \<open>X \<subseteq> B\<close> and P: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> P (Y \<inter> A)\<close> for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by metis
  have *: \<open>finite Y \<Longrightarrow> X \<inter> A \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P Y\<close> for Y
    using P[where Y=\<open>Y \<union> (B-A)\<close>]
    apply (subgoal_tac \<open>(Y \<union> (B - A)) \<inter> A = Y\<close>)
    apply (smt (verit, best) Int_Un_distrib2 Int_Un_eq(4) P Un_subset_iff \<open>X \<subseteq> B\<close> \<open>finite X\<close> assms finite_UnI inf.orderE sup_ge2)
    by auto
  show "eventually P (finite_subsets_at_top A)"
    unfolding eventually_finite_subsets_at_top
    apply (rule exI[of _ \<open>X\<inter>A\<close>])
    by (auto simp: \<open>finite X\<close> intro!: *)
qed


lemma trunc_ell2_lim: \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top M)\<close>
proof -
  have \<open>((\<lambda>S. trunc_ell2 S (trunc_ell2 M \<psi>)) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top UNIV)\<close>
    using trunc_ell2_lim_at_UNIV by blast
  then have \<open>((\<lambda>S. trunc_ell2 (S\<inter>M) \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top UNIV)\<close>
    by simp
  then show \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top M)\<close>
    unfolding filterlim_def
    apply (subst (asm) filtermap_filtermap[where g=\<open>\<lambda>S. S\<inter>M\<close>, symmetric])
    apply (subst (asm) finite_subsets_at_top_inter[where A=M and B=UNIV])
    by auto
qed

lemma trunc_ell2_lim_general:
  assumes big: \<open>\<And>G. finite G \<Longrightarrow> G \<subseteq> M \<Longrightarrow> (\<forall>\<^sub>F H in F. H \<supseteq> G)\<close>
  assumes small: \<open>\<forall>\<^sub>F H in F. H \<subseteq> M\<close>
  shows \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) F\<close>
proof (rule tendstoI)
  fix e :: real assume \<open>e > 0\<close>
  from trunc_ell2_lim[THEN tendsto_iff[THEN iffD1], rule_format, OF \<open>e > 0\<close>, where M=M and \<psi>=\<psi>]
  obtain G where \<open>finite G\<close> and \<open>G \<subseteq> M\<close> and 
    close: \<open>dist (trunc_ell2 G \<psi>) (trunc_ell2 M \<psi>) < e\<close>
    apply atomize_elim
    unfolding eventually_finite_subsets_at_top
    by blast
  from \<open>finite G\<close> \<open>G \<subseteq> M\<close> and big
  have \<open>\<forall>\<^sub>F H in F. H \<supseteq> G\<close>
    by -
  with small have \<open>\<forall>\<^sub>F H in F. H \<subseteq> M \<and> H \<supseteq> G\<close>
    by (simp add: eventually_conj_iff)
  then show \<open>\<forall>\<^sub>F H in F. dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) < e\<close>
  proof (rule eventually_mono)
    fix H assume GHM: \<open>H \<subseteq> M \<and> H \<supseteq> G\<close>
    have \<open>dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) = norm (trunc_ell2 (M-H) \<psi>)\<close>
      by (simp add: GHM dist_ell2_def norm_minus_commute trunc_ell2_union_Diff)
    also have \<open>\<dots> \<le> norm (trunc_ell2 (M-G) \<psi>)\<close>
      by (simp add: Diff_mono GHM trunc_ell2_norm_mono)
    also have \<open>\<dots>  = dist (trunc_ell2 G \<psi>) (trunc_ell2 M \<psi>)\<close>
      by (simp add: \<open>G \<subseteq> M\<close> dist_ell2_def norm_minus_commute trunc_ell2_union_Diff)
    also have \<open>\<dots> < e\<close>
      using close by simp
    finally show \<open>dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) < e\<close>
      by -
  qed
qed

lemma ket_CARD_1_is_1: \<open>ket x = 1\<close> for x :: \<open>'a::CARD_1\<close>
  apply transfer by simp


(* TODO replace *) thm adjoint_eqI
lemma adjoint_eqI:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>\<And>x y. \<langle>(cblinfun_apply F) x, y\<rangle> = \<langle>x, (cblinfun_apply G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using cadjoint_eqI by auto

lemma adj_uminus: \<open>(-A)* = - (A*)\<close>
  apply (rule adjoint_eqI[symmetric])
  by (simp add: cblinfun.minus_left cinner_adj_left)

lemma cblinfun_compose_sum_left: \<open>(\<Sum>i\<in>S. g i) o\<^sub>C\<^sub>L x = (\<Sum>i\<in>S. g i o\<^sub>C\<^sub>L x)\<close>
  apply (induction S rule:infinite_finite_induct)
  by (auto simp: cblinfun_compose_add_left)

lemma cblinfun_compose_sum_right: \<open>x o\<^sub>C\<^sub>L (\<Sum>i\<in>S. g i) = (\<Sum>i\<in>S. x o\<^sub>C\<^sub>L g i)\<close>
  apply (induction S rule:infinite_finite_induct)
  by (auto simp: cblinfun_compose_add_right)


lemma sum_adj: \<open>(sum a F)* = sum (\<lambda>i. (a i)*) F\<close>
  apply (induction rule:infinite_finite_induct)
  by (auto simp add: adj_plus)


lemma is_ortho_set_singleton[simp]: \<open>is_ortho_set {x} \<longleftrightarrow> x \<noteq> 0\<close>
  by (simp add: is_ortho_set_def)


lemma ccspan_one_dim[simp]: \<open>x \<noteq> 0 \<Longrightarrow> ccspan {x} = \<top>\<close> for x :: \<open>_ :: one_dim\<close>
  by (metis (mono_tags, opaque_lifting) cblinfun_image_id ccspan_singleton_scaleC id_cblinfun_eq_1
      image_vector_to_cblinfun of_complex_def of_complex_one_dim_iso one_dim_iso_def 
      one_dim_iso_of_one one_dim_iso_of_zero one_dim_iso_scaleC one_dim_scaleC_1 
      vector_to_cblinfun_adj_apply vector_to_cblinfun_adj_comp_vector_to_cblinfun
      vector_to_cblinfun_cblinfun_apply)

lemma is_onb_one_dim[simp]: \<open>norm x = 1 \<Longrightarrow> is_onb {x}\<close> for x :: \<open>_ :: one_dim\<close>
  by (auto simp: is_onb_def intro!: ccspan_one_dim)

lemma norm_Proj_leq1: \<open>norm (Proj M) \<le> 1\<close>
  apply transfer
  by (metis (no_types, opaque_lifting) mult.left_neutral onorm_bound projection_reduces_norm zero_less_one_class.zero_le_one)

lemma Proj_orthog_ccspan_insert:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan (insert x Y)) = proj x + Proj (ccspan Y)\<close>
  apply (subst asm_rl[of \<open>insert x Y = {x} \<union> Y\<close>], simp)
  apply (rule Proj_orthog_ccspan_union)
  using assms by auto

lemma space_as_set_bot[simp]: \<open>space_as_set \<bottom> = {0}\<close>
  by (rule bot_ccsubspace.rep_eq)


(* TODO following conway functional, Prop 4.14 *)
lemma all_onbs_same_card:
  fixes E F :: \<open>'a::chilbert_space set\<close>
    (* TODO: ortho basis is sufficient *)
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>\<exists>f. bij_betw f E F\<close>
proof -
  have \<open>|F| \<le>o |E|\<close> if \<open>infinite E\<close> and \<open>is_onb E\<close> and \<open>is_onb F\<close> for E F :: \<open>'a set\<close>
  proof -
    define F' where \<open>F' e = {f\<in>F. \<not> is_orthogonal f e}\<close> for e
    have \<open>\<exists>e\<in>E. f \<bullet>\<^sub>C e \<noteq> 0\<close> if \<open>f \<in> F\<close> for f
    proof (rule ccontr, simp)
      assume \<open>\<forall>e\<in>E. is_orthogonal f e\<close>
      then have \<open>f \<in> orthogonal_complement E\<close>
        by (simp add: orthogonal_complementI)
      also have \<open>\<dots> = orthogonal_complement (closure (cspan E))\<close>
        using orthogonal_complement_of_closure orthogonal_complement_of_cspan by blast
      also have \<open>\<dots> = space_as_set (- ccspan E)\<close>
        apply transfer by simp
      also have \<open>\<dots> = space_as_set (- \<top>)\<close>
        by (metis \<open>is_onb E\<close> is_onb_def)
      also have \<open>\<dots> = {0}\<close>
        by auto
      finally have \<open>f = 0\<close>
        by simp
      with \<open>f \<in> F\<close> \<open>is_onb F\<close> show False
        by (simp add: is_onb_def is_ortho_set_def)
    qed
    then have F'_union: \<open>F = (\<Union>e\<in>E. F' e)\<close>
      unfolding F'_def by auto
    have \<open>countable (F' e)\<close> for e
    proof -
      have \<open>(\<Sum>f\<in>M. (cmod (f \<bullet>\<^sub>C e))\<^sup>2) \<le> (norm e)\<^sup>2\<close> if \<open>finite M\<close> and \<open>M \<subseteq> F\<close> for M
      proof -
        have [simp]: \<open>is_ortho_set M\<close>
          by (meson \<open>is_onb F\<close> is_onb_def is_ortho_set_antimono that(2))
        have [simp]: \<open>norm x = 1\<close> if \<open>x \<in> M\<close> for x
          using \<open>M \<subseteq> F\<close> \<open>is_onb F\<close> is_onb_def that by blast
        have \<open>(\<Sum>f\<in>M. (cmod (f \<bullet>\<^sub>C e))\<^sup>2) = (\<Sum>f\<in>M. (norm ((f \<bullet>\<^sub>C e) *\<^sub>C f))\<^sup>2)\<close>
          apply (rule sum.cong[OF refl])
          by simp
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. ((f \<bullet>\<^sub>C e) *\<^sub>C f)))\<^sup>2\<close>
          apply (rule pythagorean_theorem_sum[symmetric])
          using that apply auto
          by (metis \<open>is_ortho_set M\<close> is_ortho_set_def)
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. proj f e))\<^sup>2\<close>
          by (metis (mono_tags, lifting) \<open>is_onb F\<close> butterfly_apply butterfly_eq_proj is_onb_def subset_eq sum.cong that(2))
        also have \<open>\<dots> = (norm (Proj (ccspan M) e))\<^sup>2\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. (norm x)\<^sup>2\<close>])
          using \<open>finite M\<close> \<open>is_ortho_set M\<close> apply induction
           apply simp
          by (smt (verit, ccfv_threshold) Proj_orthog_ccspan_insert insertCI is_ortho_set_def plus_cblinfun.rep_eq sum.insert)
        also have \<open>\<dots> \<le> (norm (Proj (ccspan M)) * norm e)\<^sup>2\<close>
          by (auto simp: norm_cblinfun intro!: power_mono)
        also have \<open>\<dots> \<le> (norm e)\<^sup>2\<close>
          apply (rule power_mono)
           apply (metis norm_Proj_leq1 mult_left_le_one_le norm_ge_zero)
          by simp
        finally show ?thesis
          by -
      qed
      then have \<open>(\<lambda>f. (cmod (cinner f e))\<^sup>2) abs_summable_on F\<close>
        apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
        by auto
      then have \<open>countable {x \<in> F. (cmod (x \<bullet>\<^sub>C e))\<^sup>2 \<noteq> 0}\<close>
        by (rule abs_summable_countable)
      then show ?thesis
        unfolding F'_def
        by (smt (verit, ccfv_SIG) Collect_cong norm_eq_zero power_not_zero zero_power2)
    qed
    then have F'_leq: \<open>|F' e| \<le>o natLeq\<close> for e
      using countable_leq_natLeq by auto

    from F'_union have \<open>|F| \<le>o |Sigma E F'|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      using card_of_UNION_Sigma by blast
    also have \<open>\<dots> \<le>o |E \<times> (UNIV::nat set)|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      apply (rule card_of_Sigma_mono1)
      using F'_leq
      using card_of_nat ordIso_symmetric ordLeq_ordIso_trans by blast
    also have \<open>\<dots> =o |E| *c natLeq\<close> (is \<open>_ =o \<dots>\<close>)
      by (metis Field_card_of Field_natLeq card_of_ordIso_subst cprod_def)
    also have \<open>\<dots> =o |E|\<close>
      apply (rule card_prod_omega)
      using that by (simp add: cinfinite_def)
    finally show \<open>|F| \<le>o |E|\<close>
      by -
  qed
  then have infinite: \<open>|E| =o |F|\<close> if \<open>infinite E\<close> and \<open>infinite F\<close>
    by (simp add: assms(1) assms(2) ordIso_iff_ordLeq that(1) that(2))

  have \<open>|E| =o |F|\<close> if \<open>finite E\<close> and \<open>is_onb E\<close> and \<open>is_onb F\<close> for E F :: \<open>'a set\<close>
  proof -
    have \<open>card E = card F\<close>
      using that 
      by (metis bij_betw_same_card ccspan.rep_eq closure_finite_cspan complex_vector.bij_if_span_eq_span_bases 
          complex_vector.independent_span_bound is_onb_def is_ortho_set_cindependent top_ccsubspace.rep_eq top_greatest)
    with \<open>finite E\<close> have \<open>finite F\<close>
      by (metis ccspan.rep_eq closure_finite_cspan complex_vector.independent_span_bound is_onb_def is_ortho_set_cindependent that(2) that(3) top_ccsubspace.rep_eq top_greatest)
    with \<open>card E = card F\<close> that show ?thesis
      apply (rule_tac finite_card_of_iff_card[THEN iffD2])
      by auto
  qed

  with infinite assms have \<open>|E| =o |F|\<close>
    by (meson ordIso_symmetric)

  then show ?thesis
    by (simp add: card_of_ordIso)
qed


definition bij_between_bases where \<open>bij_between_bases E F = (SOME f. bij_betw f E F)\<close> for E F :: \<open>'a::chilbert_space set\<close>

lemma
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows bij_between_bases_bij: \<open>bij_betw (bij_between_bases E F) E F\<close>
  using all_onbs_same_card
  by (metis assms(1) assms(2) bij_between_bases_def someI)

definition unitary_between where \<open>unitary_between E F = cblinfun_extension E (bij_between_bases E F)\<close>

lemma unitary_between_apply:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close> \<open>e \<in> E\<close>
  shows \<open>unitary_between E F *\<^sub>V e = bij_between_bases E F e\<close>
proof -
  from \<open>is_onb E\<close> \<open>is_onb F\<close>
  have EF: \<open>bij_between_bases E F e \<in> F\<close> if \<open>e \<in> E\<close> for e
    by (meson bij_betwE bij_between_bases_bij that)
  have ortho: \<open>is_orthogonal (bij_between_bases E F x) (bij_between_bases E F y)\<close> if \<open>x \<noteq> y\<close> and \<open>x \<in> E\<close> and \<open>y \<in> E\<close> for x y
    by (smt (verit, del_insts) assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij is_onb_def is_ortho_set_def that(1) that(2) that(3))
  have spanE: \<open>closure (cspan E) = UNIV\<close>
    by (metis assms(1) ccspan.rep_eq is_onb_def top_ccsubspace.rep_eq)
  show ?thesis
    unfolding unitary_between_def
    apply (rule cblinfun_extension_apply)
     apply (rule cblinfun_extension_exists_ortho[where B=1])
    using assms EF ortho spanE
    by (auto simp: is_onb_def)
qed


lemma unitary_between_unitary:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>unitary (unitary_between E F)\<close>
proof -
  have \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = b \<bullet>\<^sub>C c\<close> if \<open>b \<in> E\<close> and \<open>c \<in> E\<close> for b c
  proof (cases \<open>b = c\<close>)
    case True
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C b = 1\<close>
      using cnorm_eq_1 is_onb_def by blast
    from that have \<open>unitary_between E F *\<^sub>V b \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)
    with \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V b) = 1\<close>
      by (simp add: cnorm_eq_1 is_onb_def)
    from 1 2 True show ?thesis
      by simp
  next
    case False
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C c = 0\<close>
      by (simp add: False is_onb_def is_ortho_set_def)
    from that have inF: \<open>unitary_between E F *\<^sub>V b \<in> F\<close> \<open>unitary_between E F *\<^sub>V c \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)+
    have neq: \<open>unitary_between E F *\<^sub>V b \<noteq> unitary_between E F *\<^sub>V c\<close>
      by (metis (no_types, lifting) False assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij that(1) that(2) unitary_between_apply)
    from inF neq \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = 0\<close>
      by (simp add: is_onb_def is_ortho_set_def)
    from 1 2 show ?thesis
      by simp
  qed
  then have iso: \<open>isometry (unitary_between E F)\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=E])
    using assms(1) is_onb_def by auto
  have \<open>unitary_between E F *\<^sub>S \<top> = unitary_between E F *\<^sub>S ccspan E\<close>
    by (metis assms(1) is_onb_def)
  also have \<open>\<dots> \<ge> ccspan (unitary_between E F ` E)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (simp add: cblinfun_image_ccspan)
  also have \<open>\<dots> = ccspan (bij_between_bases E F ` E)\<close>
    by (metis assms(1) assms(2) image_cong unitary_between_apply)
  also have \<open>\<dots> = ccspan F\<close>
    by (metis assms(1) assms(2) bij_betw_imp_surj_on bij_between_bases_bij)
  also have \<open>\<dots> = \<top>\<close>
    using assms(2) is_onb_def by blast
  finally have surj: \<open>unitary_between E F *\<^sub>S \<top> = \<top>\<close>
    by (simp add: top.extremum_unique)
  from iso surj show ?thesis
    by (rule surj_isometry_is_unitary)
qed

lemma is_onb_ket[simp]: \<open>is_onb (range ket)\<close>
  by (auto simp: is_onb_def)

lemma isometry_preserves_norm: \<open>isometry U \<Longrightarrow> norm (U *\<^sub>V \<psi>) = norm \<psi>\<close>
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply cinner_adj_right cnorm_eq isometryD)


lemma space_as_set_image_commute:
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close> and VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close> (* TODO: I think only one of them is needed *)
  shows \<open>(*\<^sub>V) U ` space_as_set T = space_as_set (U *\<^sub>S T)\<close>
proof -
  have \<open>space_as_set (U *\<^sub>S T) = U ` V ` space_as_set (U *\<^sub>S T)\<close>
    by (simp add: image_image UV flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<subseteq> U ` space_as_set (V *\<^sub>S U *\<^sub>S T)\<close>
    by (metis cblinfun_image.rep_eq closure_subset image_mono)
  also have \<open>\<dots> = U ` space_as_set T\<close>
    by (simp add: VU cblinfun_assoc_left(2))
  finally have 1: \<open>space_as_set (U *\<^sub>S T) \<subseteq> U ` space_as_set T\<close>
    by -
  have 2: \<open>U ` space_as_set T \<subseteq> space_as_set (U *\<^sub>S T)\<close>
    by (simp add: cblinfun_image.rep_eq closure_subset)
  from 1 2 show ?thesis
    by simp
qed


definition \<open>rel_ccsubspace R x y = rel_set R (space_as_set x) (space_as_set y)\<close>


lemma left_unique_rel_ccsubspace[transfer_rule]: \<open>left_unique (rel_ccsubspace R)\<close> if \<open>left_unique R\<close>
proof (rule left_uniqueI)
  fix S T :: \<open>'a ccsubspace\<close> and U
  assume assms: \<open>rel_ccsubspace R S U\<close> \<open>rel_ccsubspace R T U\<close>
  have \<open>space_as_set S = space_as_set T\<close>
    apply (rule left_uniqueD)
      using that apply (rule left_unique_rel_set)
    using assms unfolding rel_ccsubspace_def by auto
  then show \<open>S = T\<close>
    by (simp add: space_as_set_inject)
qed

lemma right_unique_rel_ccsubspace[transfer_rule]: \<open>right_unique (rel_ccsubspace R)\<close> if \<open>right_unique R\<close>
  by (metis rel_ccsubspace_def right_unique_def right_unique_rel_set space_as_set_inject that)

lemma bi_unique_rel_ccsubspace[transfer_rule]: \<open>bi_unique (rel_ccsubspace R)\<close> if \<open>bi_unique R\<close>
  by (metis (no_types, lifting) bi_unique_def bi_unique_rel_set rel_ccsubspace_def space_as_set_inject that)

lemma right_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> x = U *\<^sub>V y\<close>
  shows \<open>right_total (rel_ccsubspace R)\<close>
proof (rule right_totalI)
  fix T :: \<open>'b ccsubspace\<close>
  show \<open>\<exists>S. rel_ccsubspace R S T\<close>
    apply (rule exI[of _ \<open>U *\<^sub>S T\<close>])
    using UV VU by (auto simp add: rel_ccsubspace_def R_def rel_set_def simp flip: space_as_set_image_commute)
qed

lemma converse_rel_ccsubspace: \<open>conversep (rel_ccsubspace R) = rel_ccsubspace (conversep R)\<close>
  by (auto simp: rel_ccsubspace_def[abs_def])

lemma left_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> y = U *\<^sub>V x\<close>
  shows \<open>left_total (rel_ccsubspace R)\<close>
proof -
  have \<open>right_total (rel_ccsubspace (conversep R))\<close>
    apply (rule right_total_rel_ccsubspace)
    using assms by auto
  then show ?thesis
    by (auto intro!: right_total_conversep[THEN iffD1] simp: converse_rel_ccsubspace)
qed

lemma [simp]: \<open>space_as_set \<top> = UNIV\<close>
  by (rule top_ccsubspace.rep_eq)

(* Better: add "interpretation cinner: bounded_sesquilinear cinner", but needs fixing local bounded_sesquilinear first *)
lemma cinner_scaleR_left [simp]: "cinner (scaleR r x) y = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

lemma cinner_scaleR_right [simp]: "cinner x (scaleR r y) = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

lemma cblinfun_leI:
  assumes \<open>\<And>x. norm x = 1 \<Longrightarrow> x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close>
  shows \<open>A \<le> B\<close>
proof (unfold less_eq_cblinfun_def, intro allI, case_tac \<open>\<psi> = 0\<close>)
  fix \<psi> :: 'a assume \<open>\<psi> = 0\<close>
  then show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>)\<close>
    by simp
next
  fix \<psi> :: 'a assume \<open>\<psi> \<noteq> 0\<close>
  define \<phi> where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close>
  have \<open>\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>) \<le> \<phi> \<bullet>\<^sub>C (B *\<^sub>V \<phi>)\<close>
    apply (rule assms)
    unfolding \<phi>_def
    by (simp add: \<open>\<psi> \<noteq> 0\<close>)
  with \<open>\<psi> \<noteq> 0\<close> show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>)\<close>
    unfolding \<phi>_def
    by (smt (verit) cinner_adj_left cinner_scaleR_left cinner_simps(6) complex_of_real_nn_iff mult_cancel_right1 mult_left_mono norm_eq_zero norm_ge_zero of_real_1 right_inverse scaleR_scaleC scaleR_scaleR)
qed

(* TODO move *)
lemma cblinfun_compose_minus_right: \<open>a o\<^sub>C\<^sub>L (b - c) = (a o\<^sub>C\<^sub>L b) - (a o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.diff_right bounded_cbilinear_cblinfun_compose)
lemma cblinfun_compose_minus_left: \<open>(a - b) o\<^sub>C\<^sub>L c = (a o\<^sub>C\<^sub>L c) - (b o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.diff_left bounded_cbilinear_cblinfun_compose)

lemma sum_cinner:
  fixes f :: "'a \<Rightarrow> 'b::complex_inner"
  shows "sum f A \<bullet>\<^sub>C sum g B = (\<Sum>i\<in>A. \<Sum>j\<in>B. f i \<bullet>\<^sub>C g j)"
  by (simp add: cinner_sum_right cinner_sum_left) (rule sum.swap)

(* A copy of Series.Cauchy_product_sums with * replaced by \<bullet>\<^sub>C *)
lemma Cauchy_cinner_product_sums:
  fixes a b :: "nat \<Rightarrow> 'a::chilbert_space"
  assumes a: "summable (\<lambda>k. norm (a k))"
    and b: "summable (\<lambda>k. norm (b k))"
  shows "(\<lambda>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) sums ((\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k))"
proof -
  let ?S1 = "\<lambda>n::nat. {..<n} \<times> {..<n}"
  let ?S2 = "\<lambda>n::nat. {(i,j). i + j < n}"
  have S1_mono: "\<And>m n. m \<le> n \<Longrightarrow> ?S1 m \<subseteq> ?S1 n" by auto
  have S2_le_S1: "\<And>n. ?S2 n \<subseteq> ?S1 n" by auto
  have S1_le_S2: "\<And>n. ?S1 (n div 2) \<subseteq> ?S2 n" by auto
  have finite_S1: "\<And>n. finite (?S1 n)" by simp
  with S2_le_S1 have finite_S2: "\<And>n. finite (?S2 n)" by (rule finite_subset)

  let ?g = "\<lambda>(i,j). a i \<bullet>\<^sub>C b j"
  let ?f = "\<lambda>(i,j). norm (a i) * norm (b j)"
  have f_nonneg: "\<And>x. 0 \<le> ?f x" by auto
  then have norm_sum_f: "\<And>A. norm (sum ?f A) = sum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg sum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k<n. a k) \<bullet>\<^sub>C (\<Sum>k<n. b k)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (simp add: a b summable_LIMSEQ summable_norm_cancel tendsto_cinner)
  then have 1: "(\<lambda>n. sum ?g (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (simp only: sum_cinner sum.Sigma [rule_format] finite_lessThan)

  have "(\<lambda>n. (\<Sum>k<n. norm (a k)) * (\<Sum>k<n. norm (b k))) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (simp add: summable_LIMSEQ tendsto_mult)
  then have "(\<lambda>n. sum ?f (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: sum_product sum.Sigma [rule_format] finite_lessThan)
  then have "convergent (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergentI)
  then have Cauchy: "Cauchy (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergent_Cauchy)
  have "Zfun (\<lambda>n. sum ?f (?S1 n - ?S2 n)) sequentially"
  proof (rule ZfunI, simp only: eventually_sequentially norm_sum_f)
    fix r :: real
    assume r: "0 < r"
    from CauchyD [OF Cauchy r] obtain N
      where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (sum ?f (?S1 m) - sum ?f (?S1 n)) < r" ..
    then have "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> norm (sum ?f (?S1 m - ?S1 n)) < r"
      by (simp only: sum_diff finite_S1 S1_mono)
    then have N: "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> sum ?f (?S1 m - ?S1 n) < r"
      by (simp only: norm_sum_f)
    show "\<exists>N. \<forall>n\<ge>N. sum ?f (?S1 n - ?S2 n) < r"
    proof (intro exI allI impI)
      fix n
      assume "2 * N \<le> n"
      then have n: "N \<le> n div 2" by simp
      have "sum ?f (?S1 n - ?S2 n) \<le> sum ?f (?S1 n - ?S1 (n div 2))"
        by (intro sum_mono2 finite_Diff finite_S1 f_nonneg Diff_mono subset_refl S1_le_S2)
      also have "\<dots> < r"
        using n div_le_dividend by (rule N)
      finally show "sum ?f (?S1 n - ?S2 n) < r" .
    qed
  qed
  then have "Zfun (\<lambda>n. sum ?g (?S1 n - ?S2 n)) sequentially"
    apply (rule Zfun_le [rule_format])
    apply (simp only: norm_sum_f)
    apply (rule order_trans [OF norm_sum sum_mono])
    by (auto simp add: norm_mult_ineq complex_inner_class.Cauchy_Schwarz_ineq2)
  then have 2: "(\<lambda>n. sum ?g (?S1 n) - sum ?g (?S2 n)) \<longlonglongrightarrow> 0"
    unfolding tendsto_Zfun_iff diff_0_right
    by (simp only: sum_diff finite_S1 S2_le_S1)
  with 1 have "(\<lambda>n. sum ?g (?S2 n)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (rule Lim_transform2)
  then show ?thesis
    by (simp only: sums_def sum.triangle_reindex)
qed


lemma has_sum_cinner_left:
  assumes \<open>has_sum f I x\<close>
  shows \<open>has_sum (\<lambda>i. a \<bullet>\<^sub>C f i) I (a \<bullet>\<^sub>C x)\<close>
  by (metis assms cblinfun_cinner_right.rep_eq has_sum_cblinfun_apply)


lemma infsum_cinner_left:
  assumes \<open>\<phi> summable_on I\<close>
  shows \<open>\<psi> \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i) = (\<Sum>\<^sub>\<infinity>i\<in>I. \<psi> \<bullet>\<^sub>C \<phi> i)\<close>
  by (metis assms has_sum_cinner_left has_sum_infsum infsumI)


lift_definition cblinfun_power :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> is
  \<open>\<lambda>(a::'a\<Rightarrow>'a) n. a ^^ n\<close>
  apply (rename_tac f n, induct_tac n, auto simp: Nat.funpow_code_def)
  by (simp add: bounded_clinear_compose)

lemma cblinfun_power_0[simp]: \<open>cblinfun_power A 0 = id_cblinfun\<close> 
  apply transfer by auto

lemma cblinfun_power_Suc': \<open>cblinfun_power A (Suc n) = A o\<^sub>C\<^sub>L cblinfun_power A n\<close> 
  apply transfer by auto

lemma cblinfun_power_Suc: \<open>cblinfun_power A (Suc n) = cblinfun_power A n o\<^sub>C\<^sub>L A\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc' simp flip:  cblinfun_compose_assoc)

lemma cblinfun_compose_uminus_left: \<open>(- a) o\<^sub>C\<^sub>L b = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_uminus_right: \<open>a o\<^sub>C\<^sub>L (- b) = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemmas (in bounded_cbilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_cbilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]


lemma one_dim_iso_cblinfun_comp: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = of_complex (cinner (a* *\<^sub>V 1) (b *\<^sub>V 1))\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::one_dim\<close> and b :: \<open>'c::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  by (simp add: cinner_adj_left cinner_cblinfun_def one_dim_iso_def)

lemma op_square_nondegenerate: \<open>a = 0\<close> if \<open>a* o\<^sub>C\<^sub>L a = 0\<close>
proof (rule cblinfun_eq_0_on_UNIV_span[where basis=UNIV]; simp)
  fix s
  from that have \<open>s \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V s) = 0\<close>
    by simp
  then have \<open>(a *\<^sub>V s) \<bullet>\<^sub>C (a *\<^sub>V s) = 0\<close>
    by (simp add: cinner_adj_right)
  then show \<open>a *\<^sub>V s = 0\<close>
    by simp
qed

(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"

unbundle no_cblinfun_notation

end
