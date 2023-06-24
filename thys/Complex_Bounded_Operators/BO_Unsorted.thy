text \<open>Files in this directory are intended to be added to other theory files when the next AFP 
      release is near. The reason why they are currently held in a separate file is that this will
      lessen the severity of merge conflicts due to changes made to the Complex_Bounded_Operators
      session in the development branch of the AFP by the AFP maintainers.\<close>

theory BO_Unsorted
  imports Cblinfun_Code
begin

unbundle cblinfun_notation
unbundle jnf_notation
unbundle lattice_syntax
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Order.top
hide_const (open) Coset.kernel
no_notation Order.top ("\<top>\<index>") 

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
(* abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> canonical_basis_length TYPE('a)\<close> *)


(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"





lemma mem_ortho_ccspanI:
  assumes \<open>\<And>y. y \<in> S \<Longrightarrow> is_orthogonal x y\<close>
  shows \<open>x \<in> space_as_set (- ccspan S)\<close>
proof -
  have \<open>x \<in> space_as_set (ccspan {x})\<close>
    using ccspan_superset by blast
  also have \<open>\<dots> \<subseteq> space_as_set (- ccspan S)\<close>
    apply (simp add: flip: less_eq_ccsubspace.rep_eq)
    apply (rule ccspan_leq_ortho_ccspan)
    using assms by auto
  finally show ?thesis
    by -
qed

lemma trunc_ell2_uminus: \<open>trunc_ell2 (-M) \<psi> = \<psi> - trunc_ell2 M \<psi>\<close>
  by (metis Int_UNIV_left boolean_algebra_class.diff_eq subset_UNIV trunc_ell2_UNIV trunc_ell2_union_Diff)

lemma cblinfun_same_on_image: \<open>A \<psi> = B \<psi>\<close> if eq: \<open>A o\<^sub>C\<^sub>L C = B o\<^sub>C\<^sub>L C\<close> and mem: \<open>\<psi> \<in> space_as_set (C *\<^sub>S \<top>)\<close>
proof -
  have \<open>A \<psi> = B \<psi>\<close> if \<open>\<psi> \<in> range C\<close> for \<psi>
    by (metis (no_types, lifting) eq cblinfun_apply_cblinfun_compose image_iff that)
  moreover have \<open>\<psi> \<in> closure (range C)\<close>
    by (metis cblinfun_image.rep_eq mem top_ccsubspace.rep_eq)
  ultimately show ?thesis
    apply (rule on_closure_eqI)
    by (auto simp: continuous_on_eq_continuous_at)
qed

lemma lift_cblinfun_comp:
  assumes \<open>a o\<^sub>C\<^sub>L b = c\<close>
  shows \<open>a o\<^sub>C\<^sub>L b = c\<close>
    and \<open>a o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L d) = c o\<^sub>C\<^sub>L d\<close>
    and \<open>a *\<^sub>S (b *\<^sub>S S) = c *\<^sub>S S\<close>
    and \<open>a *\<^sub>V (b *\<^sub>V x) = c *\<^sub>V x\<close>
     apply (fact assms)
    apply (simp add: assms cblinfun_assoc_left(1))
  using assms cblinfun_assoc_left(2) apply force
  using assms by force

lemma SUP_ccspan: \<open>(SUP x\<in>X. ccspan (S x)) = ccspan (\<Union>x\<in>X. S x)\<close>
proof (rule SUP_eqI)
  show \<open>ccspan (S x) \<le> ccspan (\<Union>x\<in>X. S x)\<close> if \<open>x \<in> X\<close> for x
    apply (rule ccspan_mono)
    using that by auto
  show \<open>ccspan (\<Union>x\<in>X. S x) \<le> y\<close> if \<open>\<And>x. x \<in> X \<Longrightarrow> ccspan (S x) \<le> y\<close> for y
    apply (intro ccspan_leqI UN_least)
    using that ccspan_superset by (auto simp: less_eq_ccsubspace.rep_eq)
qed

lemma has_sumI_metric:
  fixes l :: \<open>'a :: {metric_space, comm_monoid_add}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) l < e)\<close>
  shows \<open>(f has_sum l) A\<close>
  unfolding has_sum_metric using assms by simp

lemma basis_projections_reconstruct_has_sum:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<psi>B: \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>((\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) has_sum \<psi>) B\<close>
proof (rule has_sumI_metric)
  fix e :: real assume \<open>e > 0\<close>
  define e2 where \<open>e2 = e/2\<close>
  have [simp]: \<open>e2 > 0\<close>
    by (simp add: \<open>0 < e\<close> e2_def)
  define bb where \<open>bb \<phi> b = (b \<bullet>\<^sub>C \<phi>) *\<^sub>C b\<close> for \<phi> and b :: 'a
  have linear_bb: \<open>clinear (\<lambda>\<phi>. bb \<phi> b)\<close> for b
    by (simp add: bb_def cinner_add_right clinear_iff scaleC_left.add)
  from \<psi>B obtain \<phi> where dist\<phi>\<psi>: \<open>dist \<phi> \<psi> < e2\<close> and \<phi>B: \<open>\<phi> \<in> cspan B\<close>
    apply atomize_elim apply (simp add: ccspan.rep_eq closure_approachable)
    using \<open>0 < e2\<close> by blast
  from \<phi>B obtain F where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and \<phi>F: \<open>\<phi> \<in> cspan F\<close>
    by (meson vector_finitely_spanned)
  have \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close> 
    if \<open>finite G\<close> and \<open>F \<subseteq> G\<close> and \<open>G \<subseteq> B\<close> for G
  proof -
    have sum\<phi>: \<open>sum (bb \<phi>) G = \<phi>\<close>
    proof -
      from \<phi>F \<open>F \<subseteq> G\<close> have \<phi>G: \<open>\<phi> \<in> cspan G\<close>
        using complex_vector.span_mono by blast
      then obtain f where \<phi>sum: \<open>\<phi> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        using complex_vector.span_finite[OF \<open>finite G\<close>] 
        by auto
      have \<open>sum (bb \<phi>) G = (\<Sum>c\<in>G. \<Sum>b\<in>G. bb (f b *\<^sub>C b) c)\<close>
        apply (simp add: \<phi>sum)
        apply (rule sum.cong, simp)
        apply (rule complex_vector.linear_sum[where f=\<open>\<lambda>x. bb x _\<close>])
        by (rule linear_bb)
      also have \<open>\<dots> = (\<Sum>(c,b)\<in>G\<times>G. bb (f b *\<^sub>C b) c)\<close>
        by (simp add: sum.cartesian_product)
      also have \<open>\<dots> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        apply (rule sym)
        apply (rule sum.reindex_bij_witness_not_neutral
            [where j=\<open>\<lambda>b. (b,b)\<close> and i=fst and T'=\<open>G\<times>G - (\<lambda>b. (b,b)) ` G\<close> and S'=\<open>{}\<close>])
        using \<open>finite G\<close> apply (auto simp: bb_def)
         apply (metis (no_types, lifting) assms(1) imageI is_ortho_set_antimono is_ortho_set_def that(3))
        using normB \<open>G \<subseteq> B\<close> cnorm_eq_1 by blast
      also have \<open>\<dots> = \<phi>\<close>
        by (simp flip: \<phi>sum)
      finally show ?thesis
        by -
    qed
    have \<open>dist (sum (bb \<phi>) G) (sum (bb \<psi>) G) < e2\<close>
    proof -
      define \<gamma> where \<open>\<gamma> = \<phi> - \<psi>\<close>
      have \<open>(dist (sum (bb \<phi>) G) (sum (bb \<psi>) G))\<^sup>2 = (norm (sum (bb \<gamma>) G))\<^sup>2\<close>
        by (simp add: dist_norm \<gamma>_def complex_vector.linear_diff[OF linear_bb] sum_subtractf)
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G))\<^sup>2 + (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G + (\<gamma> - sum (bb \<gamma>) G)))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
      proof -
        have \<open>(\<Sum>b\<in>G. bb \<gamma> b \<bullet>\<^sub>C bb \<gamma> c) = bb \<gamma> c \<bullet>\<^sub>C \<gamma>\<close> if \<open>c \<in> G\<close> for c
          apply (subst sum_single[where i=c])
          using that apply (auto intro!: \<open>finite G\<close> simp: bb_def)
           apply (metis \<open>G \<subseteq> B\<close> \<open>is_ortho_set B\<close> is_ortho_set_antimono is_ortho_set_def)
          using \<open>G \<subseteq> B\<close> normB cnorm_eq_1 by blast
        then have \<open>is_orthogonal (sum (bb \<gamma>) G) (\<gamma> - sum (bb \<gamma>) G)\<close>
          by (simp add: cinner_sum_left cinner_diff_right cinner_sum_right)
        then show ?thesis
          apply (rule_tac arg_cong[where f=\<open>\<lambda>x. x - _\<close>])
          by (rule pythagorean_theorem[symmetric])
      qed
      also have \<open>\<dots> = (norm \<gamma>)\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> \<le> (norm \<gamma>)\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (dist \<phi> \<psi>)\<^sup>2\<close>
        by (simp add: \<gamma>_def dist_norm)
      also have \<open>\<dots> < e2\<^sup>2\<close>
        using dist\<phi>\<psi> apply (rule power_strict_mono)
        by auto
      finally show ?thesis
        by (smt (verit) \<open>0 < e2\<close> power_mono)
    qed
    with sum\<phi> dist\<phi>\<psi> show \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close>
      apply (rule_tac dist_triangle_lt[where z=\<phi>])
      by (simp add: e2_def dist_commute)
  qed
  with \<open>finite F\<close> and \<open>F \<subseteq> B\<close> 
  show \<open>\<exists>F. finite F \<and>
             F \<subseteq> B \<and> (\<forall>G. finite G \<and> F \<subseteq> G \<and> G \<subseteq> B \<longrightarrow> dist (sum (bb \<psi>) G) \<psi> < e)\<close>
    by (auto intro!: exI[of _ F])
qed

lemma basis_projections_reconstruct:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = \<psi>\<close>
  using assms basis_projections_reconstruct_has_sum infsumI by blast

lemma basis_projections_reconstruct_summable:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) summable_on B\<close>
  by (simp add: assms basis_projections_reconstruct basis_projections_reconstruct_has_sum summable_iff_has_sum_infsum)

(* TODO move (this replaces Trace_Class.parseval_infsum) *)
lemma has_sum_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>((\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) has_sum (norm \<psi>)\<^sup>2) B\<close>
proof -
  have *: \<open>(\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)\<close> if \<open>finite F\<close> and \<open>F \<subseteq> B\<close> for F
    apply (subst pythagorean_theorem_sum)
    using \<open>is_ortho_set B\<close> normB that
      apply (auto intro!: sum.cong[OF refl] simp: is_ortho_set_def)
    by blast
  
  from assms have \<open>((\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) has_sum \<psi>) B\<close>
    by (simp add: basis_projections_reconstruct_has_sum)
  then have \<open>((\<lambda>F. \<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) \<longlongrightarrow> \<psi>) (finite_subsets_at_top B)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. (\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule isCont_tendsto_compose[rotated])
    by simp
  then have \<open>((\<lambda>F. (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule tendsto_cong[THEN iffD2, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by (simp add: *)
  then show \<open>((\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) has_sum (norm \<psi>)\<^sup>2) B\<close>
    by (simp add: has_sum_def)
qed

lemma summable_onI:
  assumes \<open>(f has_sum s) A\<close>
  shows \<open>f summable_on A\<close>
  using assms summable_on_def by blast

lemma summable_on_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) summable_on B\<close>
  using has_sum_norm_on_basis[OF assms] summable_onI by blast

lemma infsum_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) = (norm \<psi>)\<^sup>2\<close>
  using has_sum_norm_on_basis[OF assms]
  using infsumI by blast

lemma ccspan_superset': \<open>x \<in> X \<Longrightarrow> x \<in> space_as_set (ccspan X)\<close>
  using ccspan_superset by auto

lemma kernel_apply_self: \<open>A *\<^sub>S kernel A = 0\<close>
proof transfer
  fix A :: \<open>'b \<Rightarrow> 'a\<close>
  assume \<open>bounded_clinear A\<close>
  then have \<open>A 0 = 0\<close>
    by (simp add: bounded_clinear_def complex_vector.linear_0)
  then have \<open>A ` A -` {0} = {0}\<close>
    by fastforce
  then show \<open>closure (A ` A -` {0}) = {0}\<close>
    by auto
qed

lemma leq_kernel_iff: 
  shows \<open>A \<le> kernel B \<longleftrightarrow> B *\<^sub>S A = 0\<close>
proof (rule iffI)
  assume \<open>A \<le> kernel B\<close>
  then have \<open>B *\<^sub>S A \<le> B *\<^sub>S kernel B\<close>
    by (simp add: cblinfun_image_mono)
  also have \<open>\<dots> = 0\<close>
    by (simp add: kernel_apply_self)
  finally show \<open>B *\<^sub>S A = 0\<close>
    by (simp add: bot.extremum_unique)
next
  assume \<open>B *\<^sub>S A = 0\<close>
  then show \<open>A \<le> kernel B\<close>
    apply transfer
    by (metis closure_subset image_subset_iff_subset_vimage)
qed

lemma cblinfun_image_kernel:
  assumes \<open>C *\<^sub>S A *\<^sub>S kernel B \<le> kernel B\<close>
  assumes \<open>A o\<^sub>C\<^sub>L C = id_cblinfun\<close>
  shows \<open>A *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L C)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S kernel B \<le> kernel (B o\<^sub>C\<^sub>L C)\<close>
    using assms(1) by (simp add: leq_kernel_iff cblinfun_compose_image)
  show \<open>kernel (B o\<^sub>C\<^sub>L C) \<le> A *\<^sub>S kernel B\<close>
  proof (insert assms(2), transfer, intro subsetI)
    fix A :: \<open>'a \<Rightarrow> 'b\<close> and B :: \<open>'a \<Rightarrow> 'c\<close> and C :: \<open>'b \<Rightarrow> 'a\<close> and x
    assume \<open>x \<in> (B \<circ> C) -` {0}\<close>
    then have BCx: \<open>B (C x) = 0\<close>
      by simp
    assume \<open>A \<circ> C = (\<lambda>x. x)\<close>
    then have \<open>x = A (C x)\<close>
      apply (simp add: o_def)
      by metis
    then show \<open>x \<in> closure (A ` B -` {0})\<close>
      using \<open>B (C x) = 0\<close> closure_subset by fastforce
  qed
qed

lemma cblinfun_image_kernel_unitary:
  assumes \<open>unitary U\<close>
  shows \<open>U *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L U*)\<close>
  apply (rule cblinfun_image_kernel)
  using assms by (auto simp flip: cblinfun_compose_image)

lemma kernel_cblinfun_compose:
  assumes \<open>kernel B = 0\<close>
  shows \<open>kernel A = kernel (B o\<^sub>C\<^sub>L A)\<close>
  using assms apply transfer by auto


lemma eigenspace_0[simp]: \<open>eigenspace 0 A = kernel A\<close>
  by (simp add: eigenspace_def)

lemma kernel_isometry: \<open>kernel U = 0\<close> if \<open>isometry U\<close>
  by (simp add: kernel_compl_adj_range range_adjoint_isometry that)

lemma cblinfun_image_def2: \<open>A *\<^sub>S S = ccspan ((*\<^sub>V) A ` space_as_set S)\<close>
  apply (simp add: flip: cblinfun_image_ccspan)
  by (metis ccspan_leqI ccspan_superset less_eq_ccsubspace.rep_eq order_class.order_eq_iff)

lemma ccspan_UNIV[simp]: \<open>ccspan UNIV = \<top>\<close>
  by (simp add: ccspan.abs_eq top_ccsubspace_def)


lemma cblinfun_image_eigenspace_isometry:
  assumes [simp]: \<open>isometry A\<close> and \<open>c \<noteq> 0\<close>
  shows \<open>A *\<^sub>S eigenspace c B = eigenspace c (sandwich A B)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S eigenspace c B \<le> eigenspace c (sandwich A B)\<close>
  proof (unfold cblinfun_image_def2, rule ccspan_leqI, rule subsetI)
    fix x assume \<open>x \<in> (*\<^sub>V) A ` space_as_set (eigenspace c B)\<close>
    then obtain y where x_def: \<open>x = A y\<close> and \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by auto
    then have \<open>B y = c *\<^sub>C y\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>sandwich A B x = c *\<^sub>C x\<close>
      apply (simp add: sandwich_apply x_def cblinfun_compose_assoc 
          flip: cblinfun_apply_cblinfun_compose)
      by (simp add: cblinfun.scaleC_right)
    then show \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
      by (simp add: eigenspace_memberI)
  qed
  show \<open>eigenspace c (sandwich A *\<^sub>V B) \<le> A *\<^sub>S eigenspace c B\<close>
  proof (rule ccsubspace_leI_unit)
    fix x
    assume \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
    then have *: \<open>sandwich A B x = c *\<^sub>C x\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>c *\<^sub>C x \<in> range A\<close>
      apply (simp add: sandwich_apply)
      by (metis rangeI)
    then have \<open>(inverse c * c) *\<^sub>C x \<in> range A\<close>
      apply (simp flip: scaleC_scaleC)
      by (metis (no_types, lifting) cblinfun.scaleC_right rangeE rangeI)
    with \<open>c \<noteq> 0\<close> have \<open>x \<in> range A\<close>
      by simp
    then obtain y where x_def: \<open>x = A y\<close>
      by auto
    have \<open>B *\<^sub>V y = A* *\<^sub>V sandwich A B x\<close>
      apply (simp add: sandwich_apply x_def)
      by (metis assms cblinfun_apply_cblinfun_compose id_cblinfun.rep_eq isometryD)
    also have \<open>\<dots> = c *\<^sub>C y\<close>
      apply (simp add: * cblinfun.scaleC_right)
      apply (simp add: x_def)
      by (metis assms(1) cblinfun_apply_cblinfun_compose id_cblinfun_apply isometry_def)
    finally have \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by (simp add: eigenspace_memberI)
    then show \<open>x \<in> space_as_set (A *\<^sub>S eigenspace c B) \<close>
      by (simp add: x_def cblinfun_apply_in_image')
  qed
qed

lemma cblinfun_image_eigenspace_unitary:
  assumes [simp]: \<open>unitary A\<close>
  shows \<open>A *\<^sub>S eigenspace c B = eigenspace c (sandwich A B)\<close>
  apply (cases \<open>c = 0\<close>)
   apply (simp add: sandwich_apply cblinfun_image_kernel_unitary kernel_isometry cblinfun_compose_assoc
    flip: kernel_cblinfun_compose)
  by (simp add: cblinfun_image_eigenspace_isometry)

lemma unitary_image_ortho_compl: 
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>U *\<^sub>S (- A) = - (U *\<^sub>S A)\<close>
proof -
  have \<open>Proj (U *\<^sub>S (- A)) = sandwich U (Proj (- A))\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = sandwich U (id_cblinfun - Proj A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = id_cblinfun - sandwich U (Proj A)\<close>
    by (metis assms cblinfun.diff_right sandwich_isometry_id unitary_twosided_isometry)
  also have \<open>\<dots> = id_cblinfun - Proj (U *\<^sub>S A)\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = Proj (- (U *\<^sub>S A))\<close>
    by (simp add: Proj_ortho_compl)
  finally show ?thesis
    by (simp add: Proj_inj)
qed

lemma summable_on_bounded_linear:
  assumes \<open>bounded_linear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (metis assms(1) assms(2) has_sum_bounded_linear infsum_bounded_linear summable_iff_has_sum_infsum)

lemma infsum_cblinfun_apply_isometry:
  assumes \<open>isometry A\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
proof -
  consider (summable) \<open>g summable_on S\<close> | (summable') \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    | (not_summable) \<open>\<not> g summable_on S\<close> \<open>\<not> (\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case summable'
    then have \<open>(\<lambda>x. A* *\<^sub>V A *\<^sub>V g x) summable_on S\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. A* *\<^sub>V x\<close>, rotated])
      by (intro bounded_linear_intros)
    with \<open>isometry A\<close> have \<open>g summable_on S\<close>
      by (simp add: flip: cblinfun_apply_cblinfun_compose)
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case not_summable
    then show ?thesis 
      by (simp add: infsum_not_exists)
  qed
qed

lemma infsum_in_closed_csubspaceI:
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x \<in> A\<close>
  assumes \<open>closed_csubspace A\<close>
  shows \<open>infsum f X \<in> A\<close>
proof (cases \<open>f summable_on X\<close>)
  case True
  then have lim: \<open>(sum f \<longlongrightarrow> infsum f X) (finite_subsets_at_top X)\<close>
    by (simp add: infsum_tendsto)
  have sumA: \<open>sum f F \<in> A\<close> if \<open>finite F\<close> and \<open>F \<subseteq> X\<close> for F
    apply (rule complex_vector.subspace_sum)
    using that assms by auto
  from lim show \<open>infsum f X \<in> A\<close>
    apply (rule Lim_in_closed_set[rotated -1])
    using assms sumA by (auto intro!: closed_csubspace.closed eventually_finite_subsets_at_top_weakI)
next
  case False
  then show ?thesis
    using assms by (auto intro!: closed_csubspace.closed complex_vector.subspace_0 simp add: infsum_not_exists)
qed

lemma closed_csubspace_space_as_set[simp]: \<open>closed_csubspace (space_as_set X)\<close>
  using space_as_set by simp

lemma unitary_nonzero[simp]: \<open>\<not> unitary (0 :: 'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  by (simp add: unitary_def)

lemma kernel_member_iff: \<open>x \<in> space_as_set (kernel A) \<longleftrightarrow> A *\<^sub>V x = 0\<close>
  using kernel_memberD kernel_memberI by blast

(* TODO move next to *) thm abs_summable_on_cblinfun_apply
lemma summable_on_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_right] assms
  by (rule summable_on_bounded_linear[unfolded o_def])

(* TODO move next to *) thm abs_summable_on_cblinfun_apply
lemma summable_on_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule summable_on_bounded_linear[unfolded o_def])
lemma abs_summable_on_cblinfun_apply_left:
  assumes \<open>A abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) abs_summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule abs_summable_on_bounded_linear[unfolded o_def])
lemma infsum_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A x *\<^sub>V g) S = (infsum A S) *\<^sub>V g\<close>
  apply (rule infsum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms 
  by (auto simp add: bounded_clinear.bounded_linear bounded_cbilinear_cblinfun_apply)
lemma has_sum_cblinfun_apply_left:
  assumes \<open>(A has_sum x) S\<close>
  shows \<open>((\<lambda>x. A x *\<^sub>V g) has_sum (x *\<^sub>V g)) S\<close>
  apply (rule has_sum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms by (auto simp add: bounded_clinear.bounded_linear cblinfun.bounded_clinear_left)

lemma clinear_scaleR[simp]: \<open>clinear (scaleR x)\<close>
  by (simp add: complex_vector.linear_scale_self scaleR_scaleC)

lemma continuous_cstrong_operator_topology_plus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x + g x)\<close>
  using assms
  by (auto intro!: continuous_map_add
      simp: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.add_left)

lemma continuous_cstrong_operator_topology_uminus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. - f x)\<close>
  using assms
  by (auto simp add: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.minus_left)

lemma continuous_cstrong_operator_topology_minus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro continuous_intros assms)


lemma is_Proj_id[simp]: \<open>is_Proj id_cblinfun\<close>
  apply transfer
  by (auto intro!: exI[of _ UNIV] simp: is_projection_on_def is_arg_min_def)

lemma choice2: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y\<close>
  by (meson that)

lemma choice3: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y\<close>
  by (meson that)

lemma choice4: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x)) \<and> (\<forall>x. Q4 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y \<and> Q4 x y\<close>
  by (meson that)

lemma limitin_pullback_topology: 
  \<open>limitin (pullback_topology A g T) f l F \<longleftrightarrow> l\<in>A \<and> (\<forall>\<^sub>F x in F. f x \<in> A) \<and> limitin T (g o f) (g l) F\<close>
  apply (simp add: topspace_pullback_topology limitin_def openin_pullback_topology imp_ex flip: ex_simps(1))
  apply rule
   apply simp
   apply safe
  using eventually_mono apply fastforce
   apply (simp add: eventually_conj_iff)
  by (simp add: eventually_conj_iff)

lemma tendsto_coordinatewise: \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
proof (intro iffI allI)
  assume asm: \<open>(f \<longlongrightarrow> l) F\<close>
  then show \<open>((\<lambda>i. f i x) \<longlongrightarrow> l x) F\<close> for x
    apply (rule continuous_on_tendsto_compose[where s=UNIV, rotated])
    by auto
next
  assume asm: \<open>(\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
  show \<open>(f \<longlongrightarrow> l) F\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
    from product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>l \<in> S\<close>]
    obtain U where lU: \<open>l \<in> Pi UNIV U\<close> and openU: \<open>\<And>x. open (U x)\<close> and finiteD: \<open>finite {x. U x \<noteq> UNIV}\<close> and US: \<open>Pi UNIV U \<subseteq> S\<close>
      by (auto simp add: PiE_UNIV_domain)

    define D where \<open>D = {x. U x \<noteq> UNIV}\<close>
    with finiteD have finiteD: \<open>finite D\<close>
      by simp
    have PiUNIV: \<open>t \<in> Pi UNIV U \<longleftrightarrow> (\<forall>x\<in>D. t x \<in> U x)\<close> for t
      using D_def by blast

    have f_Ui: \<open>\<forall>\<^sub>F i in F. f i x \<in> U x\<close> for x
      using asm[rule_format, of x] openU[of x]
      using lU topological_tendstoD by fastforce

    have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>D. f x i \<in> U i\<close>
      using finiteD
    proof induction
      case empty
      then show ?case
        by simp
    next
      case (insert x F)
      with f_Ui show ?case
        by (simp add: eventually_conj_iff)
    qed

    then show \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
      using US by (simp add: PiUNIV eventually_mono in_mono)
  qed
qed

lemma limitin_cstrong_operator_topology:
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> (\<forall>i. ((\<lambda>j. f j *\<^sub>V i) \<longlongrightarrow> l *\<^sub>V i) F)\<close>
  by (simp add: cstrong_operator_topology_def limitin_pullback_topology 
      tendsto_coordinatewise)

lemma limitin_closure_of:
  assumes limit: \<open>limitin T f c F\<close>
  assumes in_S: \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
  assumes nontrivial: \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
proof (intro in_closure_of[THEN iffD2] conjI impI allI)
  from limit show \<open>c \<in> topspace T\<close>
    by (simp add: limitin_topspace)
  fix U
  assume \<open>c \<in> U \<and> openin T U\<close>
  with limit have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    by (simp add: limitin_def)
  with in_S have \<open>\<forall>\<^sub>F x in F. f x \<in> U \<and> f x \<in> S\<close>
    by (simp add: eventually_frequently_simps)
  with nontrivial
  show \<open>\<exists>y. y \<in> S \<and> y \<in> U\<close>
    using eventually_happens' by blast
qed


(* lemma limitin_closure_of:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) eventually_happens' in_closure_of limitin_def rangeI subsetD)
 *)

(* TODO: can be generalized for more pullback topologies, I think *)
lemma cstrong_operator_topology_in_closureI:
  assumes \<open>\<And>M \<epsilon>. \<epsilon> > 0 \<Longrightarrow> finite M \<Longrightarrow> \<exists>a\<in>A. \<forall>v\<in>M. norm ((b-a) *\<^sub>V v) \<le> \<epsilon>\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof -
  define F :: \<open>('a set \<times> real) filter\<close> where \<open>F = finite_subsets_at_top UNIV \<times>\<^sub>F at_right 0\<close>
  obtain f where fA: \<open>f M \<epsilon> \<in> A\<close> and f: \<open>v \<in> M \<Longrightarrow> norm ((f M \<epsilon> - b) *\<^sub>V v) \<le> \<epsilon>\<close> if \<open>finite M\<close> and \<open>\<epsilon> > 0\<close> for M \<epsilon> v
    apply atomize_elim
    apply (intro allI choice2)
    using assms
    by (metis cblinfun.diff_left norm_minus_commute)
  have F_props: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. finite M \<and> \<epsilon> > 0\<close>
    apply (auto intro!: eventually_prodI simp: F_def case_prod_unfold)
    by (simp add: eventually_at_right_less)
  then have inA: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. f M \<epsilon> \<in> A\<close>
    apply (rule eventually_rev_mp)
    using fA by (auto intro!: always_eventually)
  have \<open>limitin cstrong_operator_topology (case_prod f) b F\<close>
  proof -
    have \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>e > 0\<close> for e v
    proof -
      have 1: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. (finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close>
        apply (unfold F_def case_prod_unfold, rule eventually_prodI)
        using eventually_at_right that
        by (auto simp add: eventually_finite_subsets_at_top)
      have 2: \<open>norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>(finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close> for M \<epsilon>
        by (smt (verit) cblinfun.diff_left f that)
      show ?thesis
        using 1 apply (rule eventually_mono)
        using 2 by auto
    qed
    then have \<open>((\<lambda>(M,\<epsilon>). f M \<epsilon> *\<^sub>V v) \<longlongrightarrow> b *\<^sub>V v) F\<close> for v
      by (simp add: tendsto_iff dist_norm case_prod_unfold)
    then show ?thesis
      by (simp add: case_prod_unfold limitin_cstrong_operator_topology)
  qed
  then show ?thesis
    apply (rule limitin_closure_of)
    using inA by (auto simp: F_def case_prod_unfold prod_filter_eq_bot)
qed



lemma sandwich_arg_compose:
  assumes \<open>isometry U\<close>
  shows \<open>sandwich U x o\<^sub>C\<^sub>L sandwich U y = sandwich U (x o\<^sub>C\<^sub>L y)\<close>
  apply (simp add: sandwich_apply)
  by (metis (no_types, lifting) lift_cblinfun_comp(2) assms cblinfun_compose_id_right isometryD)



lemma isometry_inj:
  assumes \<open>isometry U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule inj_on_inverseI[where g=\<open>U*\<close>])
  using assms by (simp flip: cblinfun_apply_cblinfun_compose)

lemma unitary_inj:
  assumes \<open>unitary U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule isometry_inj)
  using assms by simp

lemma unitary_adj_inv: \<open>unitary U \<Longrightarrow> cblinfun_apply (U*) = inv (cblinfun_apply U)\<close>
  apply (rule inj_imp_inv_eq[symmetric])
   apply (simp add: unitary_inj)
  unfolding unitary_def
  by (simp flip: cblinfun_apply_cblinfun_compose)

lemma isometry_cinner_both_sides:
  assumes \<open>isometry U\<close>
  shows \<open>cinner (U x) (U y) = cinner x y\<close>
  using assms by (simp add: flip: cinner_adj_right cblinfun_apply_cblinfun_compose)

lemma isometry_image_is_ortho_set:
  assumes \<open>is_ortho_set A\<close>
  assumes \<open>isometry U\<close>
  shows \<open>is_ortho_set (U ` A)\<close>
  using assms apply (auto simp add: is_ortho_set_def isometry_cinner_both_sides)
  by (metis cinner_eq_zero_iff isometry_cinner_both_sides)

lemma unitary_image_onb:
  assumes \<open>is_onb A\<close>
  assumes \<open>unitary U\<close>
  shows \<open>is_onb (U ` A)\<close>
  using assms
  by (auto simp add: is_onb_def isometry_image_is_ortho_set isometry_preserves_norm
      simp flip: cblinfun_image_ccspan)

lemma cspan_compose_closed:
  assumes \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L b \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close> and \<open>b \<in> cspan A\<close>
  shows \<open>a o\<^sub>C\<^sub>L b \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  from \<open>b \<in> cspan A\<close>
  obtain G g where \<open>finite G\<close> and \<open>G \<subseteq> A\<close> and b_def: \<open>b = (\<Sum>x\<in>G. g x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  have \<open>a o\<^sub>C\<^sub>L b = (\<Sum>(x,y)\<in>F\<times>G. (f x *\<^sub>C x) o\<^sub>C\<^sub>L (g y *\<^sub>C y))\<close>
    apply (simp add: a_def b_def cblinfun_compose_sum_left)
    by (auto intro!: sum.cong simp add: cblinfun_compose_sum_right scaleC_sum_right sum.cartesian_product case_prod_beta)
  also have \<open>\<dots> = (\<Sum>(x,y)\<in>F\<times>G. (f x * g y) *\<^sub>C (x o\<^sub>C\<^sub>L y))\<close>
    by (metis (no_types, opaque_lifting) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_scaleC)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>G \<subseteq> A\<close> \<open>F \<subseteq> A\<close>
    apply (auto intro!: complex_vector.span_sum complex_vector.span_scale 
        simp: complex_vector.span_clauses)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

lemma cspan_adj_closed:
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close>
  shows \<open>a* \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>a* = (\<Sum>x\<in>F. cnj (f x) *\<^sub>C x*)\<close>
    by (auto simp: sum_adj)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>F \<subseteq> A\<close>
    by (auto intro!: complex_vector.span_sum complex_vector.span_scale simp: complex_vector.span_clauses)
  finally show ?thesis
    by -
qed

lemma kernel_square[simp]: \<open>kernel (A* o\<^sub>C\<^sub>L A) = kernel A\<close>
proof (intro ccsubspace_eqI iffI)
  fix x
  assume \<open>x \<in> space_as_set (kernel A)\<close>
  then show \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
    by (simp add: kernel.rep_eq)
next
  fix x
  assume \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
  then have \<open>A* *\<^sub>V A *\<^sub>V x = 0\<close>
    by (simp add: kernel.rep_eq)
  then have \<open>(A *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x) = 0\<close>
    by (metis cinner_adj_right cinner_zero_right)
  then have \<open>A *\<^sub>V x = 0\<close>
    by auto
  then show \<open>x \<in> space_as_set (kernel A)\<close>
    by (simp add: kernel.rep_eq)
qed

lemma Proj_on_image [simp]: \<open>Proj S *\<^sub>S S = S\<close>
  by (metis Proj_idempotent Proj_range cblinfun_compose_image)

lemma not_not_singleton_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::zero\<close>
  using that unfolding class.not_singleton_def by auto

lemma not_not_singleton_cblinfun_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  apply (rule cblinfun_eqI)
  apply (subst not_not_singleton_zero[OF that])
  by simp

lemma cblinfun_norm_approx_witness':
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using complex_normed_vector_axioms True assms
    by (rule cblinfun_norm_approx_witness[internalize_sort' 'a])
  then have \<open>norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
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

lemma any_norm_exists:
  assumes \<open>n \<ge> 0\<close>
  shows \<open>\<exists>\<psi>::'a::{real_normed_vector,not_singleton}. norm \<psi> = n\<close>
proof -
  obtain \<psi> :: 'a where \<open>\<psi> \<noteq> 0\<close>
    using not_singleton_card
    by force
  then have \<open>norm (n *\<^sub>R sgn \<psi>) = n\<close>
    using assms by (auto simp: sgn_div_norm abs_mult)
  then show ?thesis
    by blast
qed




lemma sot_weaker_than_norm_limitin: \<open>limitin cstrong_operator_topology a A F\<close> if \<open>(a \<longlongrightarrow> A) F\<close>
proof -
  from that have \<open>((\<lambda>x. a x *\<^sub>V \<psi>) \<longlongrightarrow> A \<psi>) F\<close> for \<psi>
    by (auto intro!: cblinfun.tendsto)
  then show ?thesis
    by (simp add: limitin_cstrong_operator_topology)
qed

instance cblinfun :: (chilbert_space, chilbert_space) ordered_complex_vector
  by intro_classes

lemma less_eq_scaled_id_norm: 
  assumes \<open>norm A \<le> c\<close> and \<open>A = A*\<close>
  shows \<open>A \<le> complex_of_real c *\<^sub>C id_cblinfun\<close>
proof -
  have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> complex_of_real c\<close> if \<open>norm x = 1\<close> for x
  proof -
    have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> norm (A *\<^sub>V x)\<close>
      by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right1 that)
    also have \<open>\<dots> \<le> norm A\<close>
      by (metis more_arith_simps(6) norm_cblinfun that)
    also have \<open>\<dots> \<le> c\<close>
      by (rule assms)
    finally have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> c\<close>
      by -
    moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close>
      by (metis assms(2) cinner_hermitian_real)
    ultimately show ?thesis
      by (metis cnorm_le_square complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff dual_order.trans reals_zero_comparable)
  qed
  then show ?thesis
    by (smt (verit) cblinfun.scaleC_left cblinfun_id_cblinfun_apply cblinfun_leI cinner_scaleC_right cnorm_eq_1 mult_cancel_left2)
qed

lemma abs_summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp: norm_scaleC)

lemma abs_summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms simp: norm_scaleC)


lemma abs_summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp flip: real_norm_def)

lemma abs_summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms)



unbundle
  no_cblinfun_notation
  no_jnf_notation
  no_lattice_syntax

end
