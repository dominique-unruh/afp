text \<open>Files in this directory are intended to be added to other theory files when the next AFP 
      release is near. The reason why they are currently held in a separate file is that this will
      lessen the severity of merge conflicts due to changes made to the Complex_Bounded_Operators
      session in the development branch of the AFP by the AFP maintainers.\<close>

theory BO_Unsorted
  imports Cblinfun_Code
begin

unbundle cblinfun_notation
unbundle jnf_notation
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Order.top
hide_const (open) Coset.kernel

lemma bounded_clinear_Rep_ell2[simp, bounded_clinear]: \<open>bounded_clinear (\<lambda>\<psi>. Rep_ell2 \<psi> x)\<close>
  apply (subst asm_rl[of \<open>(\<lambda>\<psi>. Rep_ell2 \<psi> x) = (\<lambda>\<psi>. ket x \<bullet>\<^sub>C \<psi>)\<close>])
   apply (auto simp: cinner_ket_left) 
  by (simp add: bounded_clinear_cinner_right)

lemma norm_is_Proj_nonzero: \<open>norm P = 1\<close> if \<open>is_Proj P\<close> and \<open>P \<noteq> 0\<close> for P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof (rule antisym)
  show \<open>norm P \<le> 1\<close>
    by (simp add: norm_is_Proj that(1))
  from \<open>P \<noteq> 0\<close>
  have \<open>range P \<noteq> 0\<close>
    by (metis cblinfun_eq_0_on_UNIV_span complex_vector.span_UNIV rangeI set_zero singletonD)
  then obtain \<psi> where \<open>\<psi> \<in> range P\<close> and \<open>\<psi> \<noteq> 0\<close>
    by force
  then have \<open>P \<psi> = \<psi>\<close>
    using is_Proj.rep_eq is_projection_on_fixes_image is_projection_on_image that(1) by blast
  then show \<open>norm P \<ge> 1\<close>
    apply (rule_tac cblinfun_norm_geqI[of _ _ \<psi>])
    using \<open>\<psi> \<noteq> 0\<close> by simp
qed

declare cindependent_ket[simp]

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

definition explicit_cblinfun_exists :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> bool\<close> where
  \<open>explicit_cblinfun_exists m \<longleftrightarrow> 
    (\<forall>a. has_ell2_norm (\<lambda>j. m j a)) \<and> 
      cblinfun_extension_exists (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma cblinfun_extension_exists_restrict:
  assumes \<open>B \<subseteq> A\<close>
  assumes \<open>\<And>x. x\<in>B \<Longrightarrow> f x = g x\<close>
  assumes \<open>cblinfun_extension_exists A f\<close>
  shows \<open>cblinfun_extension_exists B g\<close>
  by (metis assms cblinfun_extension_exists_def subset_eq)

lemma norm_ell2_bound_trunc:
  assumes \<open>\<And>M. finite M \<Longrightarrow> norm (trunc_ell2 M \<psi>) \<le> B\<close>
  shows \<open>norm \<psi> \<le> B\<close>
proof -
  note trunc_ell2_lim_at_UNIV[of \<psi>]
  then have \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    using tendsto_norm by auto
  then show \<open>norm \<psi> \<le> B\<close>
    apply (rule tendsto_upperbound)
    using assms apply (rule eventually_finite_subsets_at_top_weakI)
    by auto
qed

lemma clinear_Rep_ell2[simp]: \<open>clinear (\<lambda>\<psi>. Rep_ell2 \<psi> i)\<close>
  by (simp add: clinearI plus_ell2.rep_eq scaleC_ell2.rep_eq)

lemma explicit_cblinfun_exists_bounded:
  fixes B :: real
  assumes \<open>\<And>S T \<psi>. finite S \<Longrightarrow> finite T \<Longrightarrow> (\<And>a. a\<notin>T \<Longrightarrow> \<psi> a = 0) \<Longrightarrow>
            (\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C m b a))\<^sup>2) \<le> B * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close>
  shows \<open>explicit_cblinfun_exists m\<close>
proof -
  define F f where \<open>F = complex_vector.construct (range ket) f\<close>
    and \<open>f = (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>
  from assms[where S=\<open>{}\<close> and T=\<open>{undefined}\<close> and \<psi>=\<open>\<lambda>x. of_bool (x=undefined)\<close>]
  have \<open>B \<ge> 0\<close>
    by auto
  have has_norm: \<open>has_ell2_norm (\<lambda>b. m b a)\<close> for a
  proof (unfold has_ell2_norm_def, intro nonneg_bdd_above_summable_on bdd_aboveI)
    show \<open>0 \<le> cmod ((m x a)\<^sup>2)\<close> for x
      by simp
    fix B'
    assume \<open>B' \<in> sum (\<lambda>x. cmod ((m x a)\<^sup>2)) ` {F. F \<subseteq> UNIV \<and> finite F}\<close>
    then obtain S where [simp]: \<open>finite S\<close> and B'_def: \<open>B' = (\<Sum>x\<in>S. cmod ((m x a)\<^sup>2))\<close>
      by blast
    from assms[where S=S and T=\<open>{a}\<close> and \<psi>=\<open>\<lambda>x. of_bool (x=a)\<close>]
    show \<open>B' \<le> B\<close>
      by (simp add: norm_power B'_def)
  qed
  have \<open>clinear F\<close>
    by (auto intro!: complex_vector.linear_construct simp: F_def)
  have F_B: \<open>norm (F \<psi>) \<le> (sqrt B) * norm \<psi>\<close> if \<psi>_range_ket: \<open>\<psi> \<in> cspan (range ket)\<close> for \<psi>
  proof -
    from that
    obtain T' where \<open>finite T'\<close> and \<open>T' \<subseteq> range ket\<close> and \<psi>T': \<open>\<psi> \<in> cspan T'\<close>
      by (meson vector_finitely_spanned)
        (*   from that
    obtain T' r where \<open>finite T'\<close> and \<open>T' \<subseteq> range ket\<close> and
      \<psi>T': \<open>\<psi> = (\<Sum>v\<in>T'. r v *\<^sub>C v)\<close>
      unfolding complex_vector.span_explicit
      by blast *)
    then obtain T where T'_def: \<open>T' = ket ` T\<close>
      by (meson subset_image_iff)
    have \<open>finite T\<close>
      by (metis T'_def \<open>finite T'\<close> finite_image_iff inj_ket inj_on_subset subset_UNIV)
    have \<psi>T: \<open>\<psi> \<in> cspan (ket ` T)\<close>
      using T'_def \<psi>T' by blast
    have Rep_\<psi>: \<open>Rep_ell2 \<psi> x = 0\<close> if \<open>x \<notin> T\<close> for x
      using _ _ \<psi>T apply (rule complex_vector.linear_eq_0_on_span)
       apply auto
      by (metis ket.rep_eq that)
    have \<open>norm (trunc_ell2 S (F \<psi>)) \<le> sqrt B * norm \<psi>\<close> if \<open>finite S\<close> for S
    proof -
      have *: \<open>cconstruct (range ket) f \<psi> = (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C f (ket x))\<close>
      proof (rule complex_vector.linear_eq_on[where x=\<psi> and B=\<open>ket ` T\<close>])
        show \<open>clinear (cconstruct (range ket) f)\<close>
          using F_def \<open>clinear F\<close> by blast
        show \<open>clinear (\<lambda>a. \<Sum>x\<in>T. Rep_ell2 a x *\<^sub>C f (ket x))\<close>
          by (auto intro!: clinear_compose[unfolded o_def, OF clinear_Rep_ell2] complex_vector.linear_compose_sum)
        show \<open>\<psi> \<in> cspan (ket ` T)\<close>
          by (simp add: \<psi>T)
        have \<open>f b = (\<Sum>x\<in>T. Rep_ell2 b x *\<^sub>C f (ket x))\<close> 
          if \<open>b \<in> ket ` T\<close> for b
        proof -
          define b' where \<open>b' = inv ket b\<close>
          have bb': \<open>b = ket b'\<close>
            using b'_def that by force
          show ?thesis
            apply (subst sum_single[where i=b'])
            using that by (auto simp add: \<open>finite T\<close> bb' ket.rep_eq)
        qed
        then show \<open>cconstruct (range ket) f b = (\<Sum>x\<in>T. Rep_ell2 b x *\<^sub>C f (ket x))\<close>
          if \<open>b \<in> ket ` T\<close> for b
          apply (subst complex_vector.construct_basis)
          using that by auto
      qed
      have \<open>(norm (trunc_ell2 S (F \<psi>)))\<^sup>2 = (norm (trunc_ell2 S (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C f (ket x))))\<^sup>2\<close>
        apply (rule arg_cong[where f=\<open>\<lambda>x. (norm (trunc_ell2 _ x))\<^sup>2\<close>])
        by (simp add: F_def * )
      also have \<open>\<dots> = (norm (trunc_ell2 S (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Abs_ell2 (\<lambda>b. m b x))))\<^sup>2\<close>
        by (simp add: f_def)
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (Rep_ell2 (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Abs_ell2 (\<lambda>b. m b x)) i))\<^sup>2)\<close>
        by (simp add: that norm_trunc_ell2_finite real_sqrt_pow2 sum_nonneg)
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Rep_ell2 (Abs_ell2 (\<lambda>b. m b x)) i))\<^sup>2)\<close>
        by (simp add: complex_vector.linear_sum[OF clinear_Rep_ell2]
            clinear.scaleC[OF clinear_Rep_ell2])
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C m i x))\<^sup>2)\<close>
        using has_norm by (simp add: Abs_ell2_inverse)
      also have \<open>\<dots> \<le> B * (\<Sum>x\<in>T. (cmod (Rep_ell2 \<psi> x))\<^sup>2)\<close>
        using \<open>finite S\<close> \<open>finite T\<close> Rep_\<psi> by (rule assms)
      also have \<open>\<dots> = B * ((norm (trunc_ell2 T \<psi>))\<^sup>2)\<close>
        by (simp add: \<open>finite T\<close> norm_trunc_ell2_finite sum_nonneg)
      also have \<open>\<dots> \<le> B * (norm \<psi>)\<^sup>2\<close>
        by (simp add: mult_left_mono \<open>B \<ge> 0\<close> trunc_ell2_reduces_norm)
      finally show ?thesis
        apply (rule_tac power2_le_imp_le)
        by (simp_all add: \<open>0 \<le> B\<close> power_mult_distrib)
    qed
    then show ?thesis
      by (rule norm_ell2_bound_trunc)
  qed
  then have \<open>cblinfun_extension_exists (cspan (range ket)) F\<close>
    apply (rule cblinfun_extension_exists_hilbert[rotated -1])
    by (auto intro: \<open>clinear F\<close> complex_vector.linear_add complex_vector.linear_scale)
  then have ex: \<open>cblinfun_extension_exists (range ket) f\<close>
    apply (rule cblinfun_extension_exists_restrict[rotated -1])
    by (simp_all add: F_def complex_vector.span_superset complex_vector.construct_basis)
  from ex has_norm
  show ?thesis
    using explicit_cblinfun_exists_def f_def by blast
qed

lemma explicit_cblinfun_exists_finite_dim[simp]: \<open>explicit_cblinfun_exists m\<close> for m :: "_::finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: explicit_cblinfun_exists_def cblinfun_extension_exists_finite_dim)

lemma explicit_cblinfun_ket: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> if \<open>explicit_cblinfun_exists m\<close>
  using that by (auto simp: explicit_cblinfun_exists_def explicit_cblinfun_def cblinfun_extension_apply)

lemma Rep_ell2_explicit_cblinfun_ket[simp]: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> if \<open>explicit_cblinfun_exists m\<close>
  using that apply (simp add: explicit_cblinfun_ket)
  by (simp add: Abs_ell2_inverse explicit_cblinfun_exists_def)

(* Original enum_idx_bound should say this, and be [simp] *)
lemma enum_idx_bound'[simp]: "enum_idx x < CARD('a)" for x :: "'a::enum"
  using enum_idx_bound unfolding card_UNIV_length_enum by auto

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> length (canonical_basis :: 'a list)\<close>

lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

lemma cblinfun_of_mat_invalid: 
  assumes \<open>M \<notin> carrier_mat (cdimension TYPE('b::{basis_enum,complex_normed_vector})) (cdimension TYPE('a::{basis_enum,complex_normed_vector}))\<close>
  shows \<open>(cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = 0\<close>
  apply (transfer fixing: M)
  using assms by simp


lemma trunc_ell2_singleton: \<open>trunc_ell2 {x} \<psi> = Rep_ell2 \<psi> x *\<^sub>C ket x\<close>
  apply transfer by auto

lemma trunc_ell2_insert: \<open>trunc_ell2 (insert x M) \<phi> = Rep_ell2 \<phi> x *\<^sub>C ket x + trunc_ell2 M \<phi>\<close>
  if \<open>x \<notin> M\<close>
  using trunc_ell2_union_disjoint[where M=\<open>{x}\<close> and N=M]
  using that by (auto simp: trunc_ell2_singleton)


lemma ell2_decompose_has_sum: \<open>has_sum (\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) UNIV \<phi>\<close>
proof (unfold has_sum_def)
  have *: \<open>trunc_ell2 M \<phi> = (\<Sum>x\<in>M. Rep_ell2 \<phi> x *\<^sub>C ket x)\<close> if \<open>finite M\<close> for M
    using that apply induction
    by (auto simp: trunc_ell2_insert)
  show \<open>(sum (\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) \<longlongrightarrow> \<phi>) (finite_subsets_at_top UNIV)\<close>
    apply (rule Lim_transform_eventually)
     apply (rule trunc_ell2_lim_at_UNIV)
    using * by (rule eventually_finite_subsets_at_top_weakI)
qed

lemma ell2_decompose_infsum: \<open>\<phi> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x *\<^sub>C ket x)\<close>
  by (metis ell2_decompose_has_sum infsumI)

lemma ell2_decompose_summable: \<open>(\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) summable_on UNIV\<close>
  using ell2_decompose_has_sum summable_on_def by blast

lemma Rep_ell2_cblinfun_apply_sum: \<open>Rep_ell2 (A *\<^sub>V \<phi>) y = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x * Rep_ell2 (A *\<^sub>V ket x) y)\<close>
proof -
  have 1: \<open>bounded_linear (\<lambda>z. Rep_ell2 (A *\<^sub>V z) y)\<close>
    by (auto intro!: bounded_clinear_compose[unfolded o_def, OF bounded_clinear_Rep_ell2]
        cblinfun.bounded_clinear_right bounded_clinear.bounded_linear)
  have 2: \<open>(\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) summable_on UNIV\<close>
    by (simp add: ell2_decompose_summable)
  have \<open>Rep_ell2 (A *\<^sub>V \<phi>) y = Rep_ell2 (A *\<^sub>V (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x *\<^sub>C ket x)) y\<close>
    by (simp flip: ell2_decompose_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 (A *\<^sub>V (Rep_ell2 \<phi> x *\<^sub>C ket x)) y)\<close>
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>z. Rep_ell2 (A *\<^sub>V z) y\<close>])
    using 1 2 by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x * Rep_ell2 (A *\<^sub>V ket x) y)\<close>
    by (simp add: cblinfun.scaleC_right scaleC_ell2.rep_eq)
  finally show ?thesis
    by -
qed

(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"

lemma butterfly_sum_left: \<open>butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. butterfly (\<psi> i) \<phi>)\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_left)

lemma butterfly_sum_right: \<open>butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. butterfly \<psi> (\<phi> i))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_right)

lemma trunc_ell2_finite_sum: \<open>trunc_ell2 M \<psi> = (\<Sum>i\<in>M. Rep_ell2 \<psi> i *\<^sub>C ket i)\<close> if \<open>finite M\<close>
  using that apply induction by (auto simp: trunc_ell2_insert)

lemma bounded_clinear_cblinfun_compose_left: \<open>bounded_clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose)
lemma bounded_clinear_cblinfun_compose_right: \<open>bounded_clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose)
lemma clinear_cblinfun_compose_left: \<open>clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose bounded_clinear.clinear)
lemma clinear_cblinfun_compose_right: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_clinear.clinear bounded_clinear_cblinfun_compose_right)

(* TODO: rename \<rightarrow> norm_isometry_compose' *)
lemma norm_isometry_o': \<open>norm (A o\<^sub>C\<^sub>L U) = norm A\<close> if \<open>isometry (U*)\<close>
  by (smt (verit, ccfv_threshold) adj_0 cblinfun_assoc_right(1) cblinfun_compose_id_right cblinfun_compose_zero_right double_adj isometryD isometry_partial_isometry mult_cancel_left2 norm_adj norm_cblinfun_compose norm_partial_isometry norm_zero that)




unbundle no_cblinfun_notation

end
