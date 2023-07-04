text \<open>Files in this directory are intended to be added to other theory files when the next AFP 
      release is near. The reason why they are currently held in a separate file is that this will
      lessen the severity of merge conflicts due to changes made to the Complex_Bounded_Operators
      session in the development branch of the AFP by the AFP maintainers.\<close>

theory BO_Unsorted
  imports Complex_Bounded_Operators.Cblinfun_Code
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

lemma is_orthogonal_trunc_ell2: \<open>is_orthogonal (trunc_ell2 M \<psi>) (trunc_ell2 N \<phi>)\<close> if \<open>M \<inter> N = {}\<close>
proof -
  have *: \<open>cnj (if i \<in> M then a else 0) * (if i \<in> N then b else 0) = 0\<close> for a b i
    using that by auto
  show ?thesis
    apply (transfer fixing: M N)
    by (simp add: * )
qed

(* TODO replace existing cblinfun_image_INF_leq *)
lemma cblinfun_image_INF_leq[simp]:
  fixes U :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::cbanach"
    and V :: "'a \<Rightarrow> 'b ccsubspace"
  shows \<open>U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S (V i))\<close>
  apply transfer
  by (simp add: INT_greatest Inter_lower closure_mono image_mono)

(* TODO replace existing cblinfun_image_INF_eq_general *)
lemma cblinfun_image_INF_eq_general:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L'c::chilbert_space"
    and Uinv :: "'c \<Rightarrow>\<^sub>C\<^sub>L'b"
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv" and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
    \<comment> \<open>Meaning: \<^term>\<open>Uinv\<close> is a Pseudoinverse of \<^term>\<open>U\<close>\<close>
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
    and \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S V i)"
    by (rule cblinfun_image_INF_leq)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where INFUV_def: "INFUV = (INF i\<in>X. U *\<^sub>S V i)" and INFV_def: "INFV = (INF i\<in>X. V i)"
  from assms have "V i \<le> rangeUinv"
    for i
    unfolding rangeUinv_def by simp
  moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv"
    for \<psi>
    using UinvUUinv cblinfun_fixes_range rangeUinv_def that by fastforce
  ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)"
    for \<psi> i
    using less_eq_ccsubspace.rep_eq that by blast
  hence d1: "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
  proof (transfer fixing: i)
    fix V :: "'a \<Rightarrow> 'b set"
      and Uinv :: "'c \<Rightarrow> 'b"
      and U :: "'b \<Rightarrow> 'c"
    assume "pred_fun \<top> closed_csubspace V"
      and "bounded_clinear Uinv"
      and "bounded_clinear U"
      and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> (Uinv \<circ> U) \<psi> = \<psi>"
    then show "closure ((Uinv \<circ> U) ` V i) = V i"
    proof auto
      fix x
      from \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> V i"
        if "x \<in> closure (V i)" 
        using that apply simp
        by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
      with \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> closure (V i)"
        if "x \<in> V i"
        using that
        using setdist_eq_0_sing_1 setdist_sing_in_set
        by blast
    qed
  qed
  have "U *\<^sub>S V i \<le> rangeU" for i
    by (simp add: cblinfun_image_mono rangeU_def)
  hence "INFUV \<le> rangeU"
    unfolding INFUV_def using \<open>X \<noteq> {}\<close>
    by (metis INF_eq_const INF_lower2)
  moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
    using UUinvU cblinfun_fixes_range rangeU_def that by fastforce
  ultimately have x: "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
    by (simp add: in_mono less_eq_ccsubspace.rep_eq that)

  have "closure ((U \<circ> Uinv) ` INFUV) = INFUV"
    if "closed_csubspace INFUV"
      and "bounded_clinear U"
      and "bounded_clinear Uinv"
      and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> (U \<circ> Uinv) \<psi> = \<psi>"
    for INFUV :: "'c set"
    using that
  proof auto
    fix x
    show "x \<in> INFUV" if "x \<in> closure INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
    show "x \<in> closure INFUV"
      if "x \<in> INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      using setdist_eq_0_sing_1 setdist_sing_in_set
      by (simp add: closed_csubspace.closed)
  qed
  hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
    by (metis (mono_tags, opaque_lifting) x cblinfun_image.rep_eq cblinfun_image_id id_cblinfun_apply image_cong
        space_as_set_inject)
  hence "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
    by (simp add: cblinfun_compose_image)
  also have "\<dots> \<le> U *\<^sub>S (INF i\<in>X. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    by (metis cblinfun_image_mono cblinfun_image_INF_leq)
  also have "\<dots> = U *\<^sub>S INFV"
    using d1
    by (metis (no_types, lifting) INFV_def cblinfun_assoc_left(2) image_cong)
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

(* TODO replace existing cblinfun_image_INF_eq *)
lemma cblinfun_image_INF_eq[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space"
  assumes \<open>isometry U\<close> \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: cblinfun_compose_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    using \<open>X \<noteq> {}\<close> by (rule cblinfun_image_INF_eq_general)
qed

lemma ccspan_closure[simp]: \<open>ccspan (closure X) = ccspan X\<close>
  by (simp add: basic_trans_rules(24) ccspan.rep_eq ccspan_leqI ccspan_mono closure_mono closure_subset complex_vector.span_superset)


lemma sandwich_isometry_id: \<open>isometry (U*) \<Longrightarrow> sandwich U id_cblinfun = id_cblinfun\<close>
  by (simp add: sandwich_apply isometry_def)


lemma ccspan_finite: \<open>space_as_set (ccspan X) = cspan X\<close> if \<open>finite X\<close>
  by (simp add: ccspan.rep_eq that)

lemma cblinfun_apply_in_image': "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S S)" if \<open>\<psi> \<in> space_as_set S\<close>
  by (metis cblinfun_image.rep_eq closure_subset image_subset_iff that)

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
  shows \<open>has_sum f A l\<close>
  unfolding has_sum_metric using assms by simp

lemma basis_projections_reconstruct_has_sum:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<psi>B: \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>has_sum (\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) B \<psi>\<close>
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
  shows \<open>has_sum (\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) B ((norm \<psi>)\<^sup>2)\<close>
proof -
  have *: \<open>(\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)\<close> if \<open>finite F\<close> and \<open>F \<subseteq> B\<close> for F
    apply (subst pythagorean_theorem_sum)
    using \<open>is_ortho_set B\<close> normB that
      apply (auto intro!: sum.cong[OF refl] simp: is_ortho_set_def)
    by blast
  
  from assms have \<open>has_sum (\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) B \<psi>\<close>
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
  then show \<open>has_sum (\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) B ((norm \<psi>)\<^sup>2)\<close>
    by (simp add: has_sum_def)
qed

lemma summable_onI:
  assumes \<open>has_sum f A s\<close>
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
  assumes \<open>has_sum A S x\<close>
  shows \<open>has_sum (\<lambda>x. A x *\<^sub>V g) S (x *\<^sub>V g)\<close>
  apply (rule has_sum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms by (auto simp add: bounded_clinear.bounded_linear cblinfun.bounded_clinear_left)

lemma clinear_scaleR[simp]: \<open>clinear (scaleR x)\<close>
  by (simp add: complex_vector.linear_scale_self scaleR_scaleC)

lemma additive_cblinfun_compose_left[simp]: \<open>Modules.additive (\<lambda>x. x o\<^sub>C\<^sub>L a)\<close>
  by (simp add: Modules.additive_def cblinfun_compose_add_left)
lemma additive_cblinfun_compose_right[simp]: \<open>Modules.additive (\<lambda>x. a o\<^sub>C\<^sub>L x)\<close>
  by (simp add: Modules.additive_def cblinfun_compose_add_right)
lemma isCont_cblinfun_compose_left: \<open>isCont (\<lambda>x. x o\<^sub>C\<^sub>L a) y\<close>
  apply (rule clinear_continuous_at)
  by (rule bounded_clinear_cblinfun_compose_left)
lemma isCont_cblinfun_compose_right: \<open>isCont (\<lambda>x. a o\<^sub>C\<^sub>L x) y\<close>
  apply (rule clinear_continuous_at)
  by (rule bounded_clinear_cblinfun_compose_right)



unbundle
  no_cblinfun_notation
  no_jnf_notation
  no_lattice_syntax

end
