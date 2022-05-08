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

lemma infsum_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
  apply (rule infsum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma has_sum_cblinfun_apply:
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (\<lambda>x. A *\<^sub>V g x) S (A *\<^sub>V x)\<close>
  apply (rule has_sum_bounded_linear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_clinear.bounded_linear cblinfun.bounded_clinear_right)

lemma abs_summable_on_cblinfun_apply:
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) abs_summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_right] assms
  by (rule abs_summable_on_bounded_linear[unfolded o_def])

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

lemma has_sum_cinner_left:
  assumes \<open>has_sum f I x\<close>
  shows \<open>has_sum (\<lambda>i. a \<bullet>\<^sub>C f i) I (a \<bullet>\<^sub>C x)\<close>
  by (metis assms cblinfun_cinner_right.rep_eq has_sum_cblinfun_apply)


lemma summable_on_cinner_left:
  assumes \<open>f summable_on I\<close>
  shows \<open>(\<lambda>i. a \<bullet>\<^sub>C f i) summable_on I\<close>
  by (metis assms has_sum_cinner_left summable_on_def)


lemma infsum_cinner_left:
  assumes \<open>\<phi> summable_on I\<close>
  shows \<open>\<psi> \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i) = (\<Sum>\<^sub>\<infinity>i\<in>I. \<psi> \<bullet>\<^sub>C \<phi> i)\<close>
  by (metis assms has_sum_cinner_left has_sum_infsum infsumI)

lemma has_sum_adj:
  assumes \<open>has_sum f I x\<close>
  shows \<open>has_sum (\<lambda>x. adj (f x)) I (adj x)\<close>
  apply (rule has_sum_comm_additive[where f=adj, unfolded o_def])
  apply (simp add: antilinear.axioms(1))
  apply (metis (no_types, lifting) LIM_eq adj_plus adj_uminus norm_adj uminus_add_conv_diff)
  by (simp add: assms)

lemma has_sum_cinner_right:
  assumes \<open>has_sum f I x\<close>
  shows \<open>has_sum (\<lambda>i. f i \<bullet>\<^sub>C a) I (x \<bullet>\<^sub>C a)\<close>
  apply (rule has_sum_bounded_linear[where f=\<open>\<lambda>x. x \<bullet>\<^sub>C a\<close>, unfolded o_def])
  using assms by (simp_all add: bounded_antilinear.bounded_linear bounded_antilinear_cinner_left)

lemma summable_on_cinner_right:
  assumes \<open>f summable_on I\<close>
  shows \<open>(\<lambda>i. f i \<bullet>\<^sub>C a) summable_on I\<close>
  by (metis assms has_sum_cinner_right summable_on_def)

lemma infsum_cinner_right:
  assumes \<open>\<phi> summable_on I\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i) \<bullet>\<^sub>C \<psi> = (\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i \<bullet>\<^sub>C \<psi>)\<close>
  by (metis assms has_sum_cinner_right has_sum_infsum infsumI)


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


(* Should be in misc but depends on Complex_Vector_Spaces.finite_span_closed *)
lemma summable_on_scaleR_left_converse:
  fixes f :: \<open>'b \<Rightarrow> real\<close>
    and c :: \<open>'a :: real_normed_vector\<close>
  assumes \<open>c \<noteq> 0\<close>
  assumes \<open>(\<lambda>x. f x *\<^sub>R c) summable_on A\<close>
  shows \<open>f summable_on A\<close>
proof -
  define fromR toR T where \<open>fromR x = x *\<^sub>R c\<close> and \<open>toR = inv fromR\<close> and \<open>T = range fromR\<close> for x :: real
  have \<open>additive fromR\<close>
    by (simp add: fromR_def additive.intro scaleR_left_distrib)
  have \<open>inj fromR\<close>
    by (simp add: fromR_def \<open>c \<noteq> 0\<close> inj_def)
  have toR_fromR: \<open>toR (fromR x) = x\<close> for x
    by (simp add: \<open>inj fromR\<close> toR_def)
  have fromR_toR: \<open>fromR (toR x) = x\<close> if \<open>x \<in> T\<close> for x
    by (metis T_def f_inv_into_f that toR_def)

  have 1: \<open>sum (toR \<circ> (fromR \<circ> f)) F = toR (sum (fromR \<circ> f) F)\<close> if \<open>finite F\<close> for F
    by (simp add: o_def additive.sum[OF \<open>additive fromR\<close>, symmetric] toR_fromR)
  have 2: \<open>sum (fromR \<circ> f) F \<in> T\<close> if \<open>finite F\<close> for F
    by (simp add: o_def additive.sum[OF \<open>additive fromR\<close>, symmetric] T_def)
  have 3: \<open>(toR \<longlongrightarrow> toR x) (at x within T)\<close> for x
  proof (cases \<open>x \<in> T\<close>)
    case True
    have \<open>dist (toR y) (toR x) < e\<close> if \<open>y\<in>T\<close> \<open>e>0\<close> \<open>dist y x < e * norm c\<close> for e y
    proof -
      obtain x' y' where x: \<open>x = fromR x'\<close> and y: \<open>y = fromR y'\<close>
        using T_def True \<open>y \<in> T\<close> by blast
      have \<open>dist (toR y) (toR x) = dist (fromR (toR y)) (fromR (toR x)) / norm c\<close>
        by (auto simp: dist_real_def fromR_def \<open>c \<noteq> 0\<close>)
      also have \<open>\<dots> = dist y x / norm c\<close>
        using \<open>x\<in>T\<close> \<open>y\<in>T\<close> by (simp add: fromR_toR)
      also have \<open>\<dots> < e\<close>
        using \<open>dist y x < e * norm c\<close>
        by (simp add: divide_less_eq that(2))
      finally show ?thesis
        by (simp add: x y toR_fromR)
    qed
    then show ?thesis
      apply (auto simp: tendsto_iff at_within_def eventually_inf_principal eventually_nhds_metric)
      by (metis assms(1) div_0 divide_less_eq zero_less_norm_iff)
  next
    case False
    have \<open>T = span {c}\<close>
      by (simp add: T_def fromR_def span_singleton)
    then have \<open>closed T\<close>
      by simp
    with False have \<open>x \<notin> closure T\<close>
      by simp
    then have \<open>(at x within T) = bot\<close>
      by (rule not_in_closure_trivial_limitI)
    then show ?thesis
      by simp
  qed
  have 4: \<open>(fromR \<circ> f) summable_on A\<close>
    by (simp add: assms(2) fromR_def summable_on_cong)

  have \<open>(toR o (fromR o f)) summable_on A\<close>
    using 1 2 3 4 
    by (rule summable_on_comm_additive_general[where T=T])
  with toR_fromR
  show ?thesis
    by (auto simp: o_def)
qed


(* strengthening of original *)
(* Should be in misc but depends on Complex_Vector_Spaces.finite_span_closed *)
thm infsum_scaleR_left
lemma infsum_scaleR_left:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  shows "infsum (\<lambda>x. f x *\<^sub>R c) A = infsum f A *\<^sub>R c"
proof (cases \<open>f summable_on A\<close>)
  case True
  then show ?thesis 
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using True by (auto simp add: scaleR_left.additive_axioms)
next
  case False
  then have \<open>\<not> (\<lambda>x. f x *\<^sub>R c) summable_on A\<close> if \<open>c \<noteq> 0\<close>
    using summable_on_scaleR_left_converse[where A=A and f=f and c=c]
    using that by auto
  with False show ?thesis
    apply (cases \<open>c = 0\<close>)
    by (auto simp add: infsum_not_exists)
qed


(* Should be in misc but depends on Complex_Vector_Spaces.finite_span_closed *)
lemma infsum_of_real: 
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>A. of_real (f x) :: 'b::{real_normed_vector, real_algebra_1}) = of_real (\<Sum>\<^sub>\<infinity>x\<in>A. f x)\<close>
  unfolding of_real_def
  by (rule infsum_scaleR_left)

(* TODO: Replace original positive_cblinfunI with this *)
lemma positive_cblinfunI: \<open>A \<ge> 0\<close> if \<open>\<And>x. norm x = 1 \<Longrightarrow> cinner x (A *\<^sub>V x) \<ge> 0\<close>
  apply (rule cblinfun_leI)
  using that by simp

definition partial_isometry where
  \<open>partial_isometry A \<longleftrightarrow> (\<forall>h \<in> space_as_set (- kernel A). norm (A h) = norm h)\<close>

lemma partial_isometryI: 
  assumes \<open>\<And>h. h \<in> space_as_set (- kernel A) \<Longrightarrow> norm (A h) = norm h\<close>
  shows \<open>partial_isometry A\<close>
  using assms partial_isometry_def by blast

lemma ccsubspace_eqI: 
  assumes \<open>\<And>x. x \<in> space_as_set S \<longleftrightarrow> x \<in> space_as_set T\<close>
  shows \<open>S = T\<close>
  by (metis Abs_clinear_space_cases Abs_clinear_space_inverse antisym assms subsetI)

lemma cancel_apply_Proj:
  assumes \<open>\<psi> \<in> space_as_set S\<close>
  shows \<open>Proj S *\<^sub>V \<psi> = \<psi>\<close>
  by (metis Proj_idempotent Proj_range assms cblinfun_fixes_range)

lemma kernel_Proj[simp]: \<open>kernel (Proj S) = - S\<close>
  apply transfer
  apply auto
  apply (metis diff_0_right is_projection_on_iff_orthog projection_is_projection_on')
  by (simp add: complex_vector.subspace_0 projection_eqI)

lemma Proj_partial_isometry: \<open>partial_isometry (Proj S)\<close>
  apply (rule partial_isometryI)
  by (simp add: cancel_apply_Proj)

lemma is_Proj_partial_isometry: \<open>is_Proj P \<Longrightarrow> partial_isometry P\<close>
  by (metis Proj_on_own_range Proj_partial_isometry)

lemma isometry_partial_isometry: \<open>isometry P \<Longrightarrow> partial_isometry P\<close>
  by (simp add: isometry_preserves_norm partial_isometry_def)

lemma unitary_partial_isometry: \<open>unitary P \<Longrightarrow> partial_isometry P\<close>
  using isometry_partial_isometry unitary_isometry by blast

(* lemma minus_zero_ccsubspace[simp]: \<open>- 0 = (\<top> :: _ ccsubspace)\<close>
  by auto *)

lemma norm_partial_isometry:
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>partial_isometry A\<close> and \<open>A \<noteq> 0\<close>
  shows \<open>norm A = 1\<close> 
proof -
  from \<open>A \<noteq> 0\<close>
  have \<open>- (kernel A) \<noteq> 0\<close>
    by (metis cblinfun_eqI diff_zero id_cblinfun_apply kernel_id kernel_memberD ortho_involution orthog_proj_exists orthogonal_complement_closed_subspace uminus_ccsubspace.rep_eq zero_cblinfun.rep_eq)
  then obtain h where \<open>h \<in> space_as_set (- kernel A)\<close> and \<open>h \<noteq> 0\<close>
    by (metis cblinfun_id_cblinfun_apply ccsubspace_eqI closed_csubspace.subspace complex_vector.subspace_0 kernel_id kernel_memberD kernel_memberI orthogonal_complement_closed_subspace uminus_ccsubspace.rep_eq)
  with \<open>partial_isometry A\<close>
  have \<open>norm (A h) = norm h\<close>
    using partial_isometry_def by blast
  then have \<open>norm A \<ge> 1\<close>
    by (smt (verit) \<open>h \<noteq> 0\<close> mult_cancel_right1 mult_left_le_one_le norm_cblinfun norm_eq_zero norm_ge_zero)

  have \<open>norm A \<le> 1\<close>
  proof (rule norm_cblinfun_bound)
    show \<open>0 \<le> (1::real)\<close>
      by simp
    fix \<psi> :: 'a
    define g h where \<open>g = Proj (kernel A) \<psi>\<close> and \<open>h = Proj (- kernel A) \<psi>\<close>
    have \<open>A g = 0\<close>
      by (metis Proj_range cblinfun_apply_in_image g_def kernel_memberD)
    moreover from \<open>partial_isometry A\<close>
    have \<open>norm (A h) = norm h\<close>
      by (metis Proj_range cblinfun_apply_in_image h_def partial_isometry_def)
    ultimately have \<open>norm (A \<psi>) = norm h\<close>
      by (simp add: Proj_ortho_compl cblinfun.diff_left cblinfun.diff_right g_def h_def)
    also have \<open>norm h \<le> norm \<psi>\<close>
      by (smt (verit, del_insts) h_def mult_left_le_one_le norm_Proj_leq1 norm_cblinfun norm_ge_zero)
    finally show \<open>norm (A *\<^sub>V \<psi>) \<le> 1 * norm \<psi>\<close>
      by simp
  qed

  from \<open>norm A \<le> 1\<close> and \<open>norm A \<ge> 1\<close>
  show \<open>norm A = 1\<close>
    by auto
qed

lemma summable_on_product_finite_left:
  fixes f :: \<open>'a\<times>'b \<Rightarrow> 'c::{topological_comm_monoid_add}\<close>
  assumes sum: \<open>\<And>x. x\<in>X \<Longrightarrow> (\<lambda>y. f(x,y)) summable_on Y\<close>
  assumes \<open>finite X\<close>
  shows \<open>f summable_on (X\<times>Y)\<close>
  using \<open>finite X\<close> subset_refl[of X]
proof (induction rule: finite_subset_induct')
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  have *: \<open>bij_betw (Pair x) Y ({x} \<times> Y)\<close>
    apply (rule bij_betwI')
    by auto
  from sum[of x]
  have \<open>f summable_on {x} \<times> Y\<close>
    apply (rule summable_on_reindex_bij_betw[THEN iffD1, rotated])
    by (simp_all add: * insert.hyps(2))
  then have \<open>f summable_on {x} \<times> Y \<union> F \<times> Y\<close>
    apply (rule summable_on_Un_disjoint)
    using insert by auto
  then show ?case
    by (metis Sigma_Un_distrib1 insert_is_Un)
qed

lemma summable_on_product_finite_right:
  fixes f :: \<open>'a\<times>'b \<Rightarrow> 'c::{topological_comm_monoid_add}\<close>
  assumes sum: \<open>\<And>y. y\<in>Y \<Longrightarrow> (\<lambda>x. f(x,y)) summable_on X\<close>
  assumes \<open>finite Y\<close>
  shows \<open>f summable_on (X\<times>Y)\<close>
proof -
  have \<open>(\<lambda>(y,x). f(x,y)) summable_on (Y\<times>X)\<close>
    apply (rule summable_on_product_finite_left)
    using assms by auto
  then show ?thesis
    apply (subst summable_on_reindex_bij_betw[where g=prod.swap and A=\<open>Y\<times>X\<close>, symmetric])
    apply (simp add: bij_betw_def product_swap)
    by (metis (mono_tags, lifting) case_prod_unfold prod.swap_def summable_on_cong)
qed

lemma Cauchy_cinner_product_summable:
  assumes asum: \<open>a summable_on UNIV\<close>
  assumes bsum: \<open>b summable_on UNIV\<close>
  assumes \<open>finite X\<close> \<open>finite Y\<close>
  assumes pos: \<open>\<And>x y. x \<notin> X \<Longrightarrow> y \<notin> Y \<Longrightarrow> a x \<bullet>\<^sub>C b y \<ge> 0\<close>
  shows absum: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on UNIV\<close>
proof -
  have \<open>(\<Sum>(x,y)\<in>F. norm (a x \<bullet>\<^sub>C b y)) \<le> norm (infsum a (-X) \<bullet>\<^sub>C infsum b (-Y)) + norm (infsum a (-X)) + norm (infsum b (-Y)) + 1\<close> 
    if \<open>finite F\<close> and \<open>F \<subseteq> (-X)\<times>(-Y)\<close> for F
  proof -
    from asum \<open>finite X\<close>
    have \<open>a summable_on (-X)\<close>
      by (simp add: Compl_eq_Diff_UNIV summable_on_cofin_subset)
    then obtain MA where \<open>finite MA\<close> and \<open>MA \<subseteq> -X\<close>
      and MA: \<open>G \<supseteq> MA \<Longrightarrow> G \<subseteq> -X \<Longrightarrow> finite G \<Longrightarrow> norm (sum a G - infsum a (-X)) \<le> 1\<close> for G
      apply (simp add: summable_iff_has_sum_infsum has_sum_metric dist_norm)
      by (meson less_eq_real_def zero_less_one)
    
    from bsum \<open>finite Y\<close>
    have \<open>b summable_on (-Y)\<close>
      by (simp add: Compl_eq_Diff_UNIV summable_on_cofin_subset)
    then obtain MB where \<open>finite MB\<close> and \<open>MB \<subseteq> -Y\<close>
      and MB: \<open>G \<supseteq> MB \<Longrightarrow> G \<subseteq> -Y \<Longrightarrow> finite G \<Longrightarrow> norm (sum b G - infsum b (-Y)) \<le> 1\<close> for G
      apply (simp add: summable_iff_has_sum_infsum has_sum_metric dist_norm)
      by (meson less_eq_real_def zero_less_one)

    define F1 F2 where \<open>F1 = fst ` F \<union> MA\<close> and \<open>F2 = snd ` F \<union> MB\<close>
    define t1 t2 where \<open>t1 = sum a F1 - infsum a (-X)\<close> and \<open>t2 = sum b F2 - infsum b (-Y)\<close>
  
    have [simp]: \<open>finite F1\<close> \<open>finite F2\<close>
      using F1_def F2_def \<open>finite MA\<close> \<open>finite MB\<close> that by auto
    have [simp]: \<open>F1 \<subseteq> -X\<close> \<open>F2 \<subseteq> -Y\<close>
      using \<open>F \<subseteq> (-X)\<times>(-Y)\<close> \<open>MA \<subseteq> -X\<close> \<open>MB \<subseteq> -Y\<close>
      by (auto simp: F1_def F2_def)
    from MA[OF _ \<open>F1 \<subseteq> -X\<close> \<open>finite F1\<close>] have \<open>norm t1 \<le> 1\<close> 
      by (auto simp: t1_def F1_def)
    from MB[OF _ \<open>F2 \<subseteq> -Y\<close> \<open>finite F2\<close>] have \<open>norm t2 \<le> 1\<close> 
      by (auto simp: t2_def F2_def)
    have [simp]: \<open>F \<subseteq> F1 \<times> F2\<close>
      apply (auto simp: F1_def F2_def image_def)
      by force+
    have \<open>(\<Sum>(x,y)\<in>F. norm (a x \<bullet>\<^sub>C b y)) \<le> (\<Sum>(x,y)\<in>F1\<times>F2. norm (a x \<bullet>\<^sub>C b y))\<close>
      apply (rule sum_mono2)
      by auto
    also from pos have \<open>\<dots> = norm (\<Sum>(x,y)\<in>F1\<times>F2. a x \<bullet>\<^sub>C b y)\<close>
      apply (auto intro!: of_real_eq_iff[THEN iffD1] simp: case_prod_beta)
      apply (subst abs_complex_def[unfolded o_def, symmetric, THEN fun_cong])+
      apply (subst (2) abs_pos)
       apply (rule sum_nonneg)
       apply (metis Compl_eq_Diff_UNIV Diff_iff SigmaE \<open>F1 \<subseteq> - X\<close> \<open>F2 \<subseteq> - Y\<close> fst_conv prod.sel(2) subsetD)
      apply (rule sum.cong)
      apply simp
      by (metis Compl_iff SigmaE \<open>F1 \<subseteq> - X\<close> \<open>F2 \<subseteq> - Y\<close> abs_pos fst_conv prod.sel(2) subset_eq)
    also have \<open>\<dots> = norm (sum a F1 \<bullet>\<^sub>C sum b F2)\<close>
      by (simp add: sum.cartesian_product sum_cinner)
    also have \<open>\<dots> = norm ((infsum a (-X) + t1) \<bullet>\<^sub>C (infsum b (-Y) + t2))\<close>
      by (simp add: t1_def t2_def)
    also have \<open>\<dots> \<le> norm (infsum a (-X) \<bullet>\<^sub>C infsum b (-Y)) + norm (infsum a (-X)) * norm t2 + norm t1 * norm (infsum b (-Y)) + norm t1 * norm t2\<close>
      apply (simp add: cinner_add_right cinner_add_left)
      by (smt (verit, del_insts) complex_inner_class.Cauchy_Schwarz_ineq2 norm_triangle_ineq)
    also from \<open>norm t1 \<le> 1\<close> \<open>norm t2 \<le> 1\<close>
    have \<open>\<dots> \<le> norm (infsum a (-X) \<bullet>\<^sub>C infsum b (-Y)) + norm (infsum a (-X)) + norm (infsum b (-Y)) + 1\<close>
      by (auto intro!: add_mono mult_left_le mult_left_le_one_le mult_le_one)
    finally show ?thesis
      by -
  qed

  then have \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) abs_summable_on (-X)\<times>(-Y)\<close>
    apply (rule_tac abs_summable_bdd_above[THEN iffD2])
    apply (rule bdd_aboveI2)
    by (auto simp: case_prod_unfold)
  then have 1: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on (-X)\<times>(-Y)\<close>
    using abs_summable_summable by blast

  from bsum
  have \<open>(\<lambda>y. b y) summable_on (-Y)\<close>
    by (simp add: Compl_eq_Diff_UNIV assms(4) summable_on_cofin_subset)
  then have \<open>(\<lambda>y. a x \<bullet>\<^sub>C b y) summable_on (-Y)\<close> for x
    using summable_on_cinner_left by blast
  with \<open>finite X\<close> have 2: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on X\<times>(-Y)\<close>
    apply (rule_tac summable_on_product_finite_left)
    by auto

  from asum
  have \<open>(\<lambda>x. a x) summable_on (-X)\<close>
    by (simp add: Compl_eq_Diff_UNIV assms(3) summable_on_cofin_subset)
  then have \<open>(\<lambda>x. a x \<bullet>\<^sub>C b y) summable_on (-X)\<close> for y
    using summable_on_cinner_right by blast
  with \<open>finite Y\<close> have 3: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on (-X)\<times>Y\<close>
    apply (rule_tac summable_on_product_finite_right)
    by auto

  have 4: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on X\<times>Y\<close>
    by (simp add: \<open>finite X\<close> \<open>finite Y\<close>)

  show ?thesis
    apply (subst asm_rl[of \<open>UNIV = (-X)\<times>(-Y) \<union> X\<times>(-Y) \<union> (-X)\<times>Y \<union> X\<times>Y\<close>])
    using 1 2 3 4 by (auto intro!: summable_on_Un_disjoint)
qed

lemma Cauchy_cinner_product_summable':
  fixes a b :: "nat \<Rightarrow> 'a::complex_inner"
  shows \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on UNIV \<longleftrightarrow> (\<lambda>(x, y). a y \<bullet>\<^sub>C b (x - y)) summable_on {(k, i). i \<le> k}\<close>
proof -
  have img: \<open>(\<lambda>(k::nat, i). (i, k - i)) ` {(k, i). i \<le> k} = UNIV\<close>
    apply (auto simp: image_def)
    by (metis add.commute add_diff_cancel_right' diff_le_self)
  have inj: \<open>inj_on (\<lambda>(k::nat, i). (i, k - i)) {(k, i). i \<le> k}\<close>
    by (smt (verit, del_insts) Pair_inject case_prodE case_prod_conv eq_diff_iff inj_onI mem_Collect_eq)

  have \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on UNIV \<longleftrightarrow> (\<lambda>(k, l). a k \<bullet>\<^sub>C b l) summable_on (\<lambda>(k, i). (i, k - i)) ` {(k, i). i \<le> k}\<close>
    by (simp only: img)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(k, l). a k \<bullet>\<^sub>C b l) \<circ> (\<lambda>(k, i). (i, k - i))) summable_on {(k, i). i \<le> k}\<close>
    using inj by (rule summable_on_reindex)
  also have \<open>\<dots> \<longleftrightarrow> (\<lambda>(x, y). a y \<bullet>\<^sub>C b (x - y)) summable_on {(k, i). i \<le> k}\<close>
    by (simp add: o_def case_prod_unfold)
  finally show ?thesis
    by -
qed




text \<open>A variant of @{thm [source] Series.Cauchy_product_sums} with \<^term>\<open>(*)\<close> replaced by \<^term>\<open>(\<bullet>\<^sub>C)\<close>.
   Differently from @{thm [source] Series.Cauchy_product_sums}, we do not require absolute summability
   of \<^term>\<open>a\<close> and \<^term>\<open>b\<close> individually but only unconditional summability of \<^term>\<open>a\<close>, \<^term>\<open>b\<close>, and their product.
   While on, e.g., reals, unconditional summability is equivalent to absolute summability, in
   general unconditional summability is a weaker requirement.\<close>
lemma 
  fixes a b :: "nat \<Rightarrow> 'a::complex_inner"
  assumes asum: \<open>a summable_on UNIV\<close>
  assumes bsum: \<open>b summable_on UNIV\<close>
  assumes absum: \<open>(\<lambda>(x, y). a x \<bullet>\<^sub>C b y) summable_on UNIV\<close>
    \<comment> \<open>See @{thm [source] Cauchy_cinner_product_summable} or @{thm [source] Cauchy_cinner_product_summable'} for a way to rewrite this premise.\<close>
  shows Cauchy_cinner_product_infsum: \<open>(\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) = (\<Sum>\<^sub>\<infinity>k. a k) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>k. b k)\<close>
    and Cauchy_cinner_product_infsum_exists: \<open>(\<lambda>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) summable_on UNIV\<close>
(* TODO: Thm showing existence of the lhs *)
proof -
  have img: \<open>(\<lambda>(k::nat, i). (i, k - i)) ` {(k, i). i \<le> k} = UNIV\<close>
    apply (auto simp: image_def)
    by (metis add.commute add_diff_cancel_right' diff_le_self)
  have inj: \<open>inj_on (\<lambda>(k::nat, i). (i, k - i)) {(k, i). i \<le> k}\<close>
    by (smt (verit, del_insts) Pair_inject case_prodE case_prod_conv eq_diff_iff inj_onI mem_Collect_eq)
  have sigma: \<open>(SIGMA k:UNIV. {i. i \<le> k}) = {(k, i). i \<le> k}\<close>
    by auto

  from absum
  have \<open>(\<lambda>(x, y). a y \<bullet>\<^sub>C b (x - y)) summable_on {(k, i). i \<le> k}\<close>
    by (rule Cauchy_cinner_product_summable'[THEN iffD1])
  then have \<open>(\<lambda>k. \<Sum>\<^sub>\<infinity>i|i\<le>k. a i \<bullet>\<^sub>C b (k-i)) summable_on UNIV\<close>
    by (metis (mono_tags, lifting) sigma summable_on_Sigma_banach summable_on_cong)
  then show \<open>(\<lambda>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) summable_on UNIV\<close>
    by (metis (mono_tags, lifting) atMost_def finite_Collect_le_nat infsum_finite summable_on_cong)

  have \<open>(\<Sum>\<^sub>\<infinity>k. a k) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>k. b k) = (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>l. a k \<bullet>\<^sub>C b l)\<close>
    apply (subst infsum_cinner_right)
     apply (rule asum)
    apply (subst infsum_cinner_left)
     apply (rule bsum)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k,l). a k \<bullet>\<^sub>C b l)\<close>
    apply (subst infsum_Sigma'_banach)
    using absum by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k, l)\<in>(\<lambda>(k, i). (i, k - i)) ` {(k, i). i \<le> k}. a k \<bullet>\<^sub>C b l)\<close>
    by (simp only: img)
  also have \<open>\<dots> = infsum ((\<lambda>(k, l). a k \<bullet>\<^sub>C b l) \<circ> (\<lambda>(k, i). (i, k - i))) {(k, i). i \<le> k}\<close>
    using inj by (rule infsum_reindex)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k,i)|i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>i|i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    apply (subst infsum_Sigma'_banach)
    using absum by (auto simp: sigma Cauchy_cinner_product_summable')
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    apply (subst infsum_finite[symmetric])
    by (auto simp add: atMost_def)
  finally show \<open>(\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) = (\<Sum>\<^sub>\<infinity>k. a k) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>k. b k)\<close>
    by simp
qed

(* (* A copy of Series.Cauchy_product_sums with * replaced by \<bullet>\<^sub>C *)
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
qed *)


lemma summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)


lemma summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_right.additive_axioms)

lemma infsum_scaleC_left:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>C c) A = infsum f A *\<^sub>C c"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)

lemma infsum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>C f x) A = c *\<^sub>C infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
      apply (rule infsum_comm_additive)
      using summable by (auto simp add: scaleC_right.additive_axioms)
  next
    case c0
    then show ?thesis by auto
  next
    case not_summable
    have \<open>\<not> (\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
    proof (rule notI)
      assume \<open>(\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
      then have \<open>(\<lambda>x. inverse c *\<^sub>C c *\<^sub>C f x) summable_on A\<close>
        using summable_on_scaleC_right by blast
      then have \<open>f summable_on A\<close>
        using not_summable by auto
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed

lemma cblinfun_power_compose[simp]: \<open>cblinfun_power A n o\<^sub>C\<^sub>L cblinfun_power A m = cblinfun_power A (n+m)\<close>
  apply (induction n)
  apply (auto simp: cblinfun_power_Suc')
  by (metis cblinfun_assoc_left(1))


lemma cblinfun_power_scaleC: \<open>cblinfun_power (c *\<^sub>C a) n = c^n *\<^sub>C cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_scaleR: \<open>cblinfun_power (c *\<^sub>R a) n = c^n *\<^sub>R cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_uminus: \<open>cblinfun_power (-a) n = (-1)^n *\<^sub>R cblinfun_power a n\<close>
  apply (subst asm_rl[of \<open>-a = (-1) *\<^sub>R a\<close>])
   apply simp
  by (rule cblinfun_power_scaleR)


lemma cblinfun_power_adj: \<open>(cblinfun_power S n)* = cblinfun_power (S*) n\<close>
  apply (induction n)
   apply simp
  apply (subst cblinfun_power_Suc)
  apply (subst cblinfun_power_Suc')
  by auto

lemma adj_minus: \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis add_implies_diff adj_plus diff_add_cancel)

lemma complex_of_real_leq_1_iff[iff]: \<open>complex_of_real x \<le> 1 \<longleftrightarrow> x \<le> 1\<close>
  by (metis complex_of_real_mono_iff of_real_1)

lemma cinner_hermitian_real: \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close> if \<open>A* = A\<close>
  by (metis Reals_cnj_iff cinner_adj_right cinner_commute' that)

lemma x_cnj_x: \<open>c * cnj c = (abs c)\<^sup>2\<close>
  by (metis cnj_x_x mult.commute)

unbundle no_cblinfun_notation

end
