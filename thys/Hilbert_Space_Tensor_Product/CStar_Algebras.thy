theory CStar_Algebras
imports Positive_Operators
begin

(* TODO: Discard this file? *)


definition cstar_algebra where \<open>cstar_algebra A \<longleftrightarrow> csubspace A \<and> (\<forall>x\<in>A. \<forall>y\<in>A. x o\<^sub>C\<^sub>L y \<in> A) \<and> (\<forall>x\<in>A. x* \<in> A) \<and> closed A\<close>

lemma sqrt_op_in_cstar_algebra:
  assumes \<open>cstar_algebra A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>a \<in> A\<close>
  shows \<open>sqrt_op a \<in> A\<close>
proof -
  have *: \<open>cblinfun_power a n \<in> A\<close> for n
    apply (induction n)
    using assms by (auto simp: cblinfun_power_Suc cstar_algebra_def)
  have \<open>sqrt_op a \<in> closure (cspan (range (cblinfun_power a)))\<close>
    by (rule sqrt_op_in_closure)
  also have \<open>\<dots> \<subseteq> closure (cspan A)\<close>
    apply (intro closure_mono complex_vector.span_mono)
    by (auto intro!: * )
  also have \<open>\<dots> = closure A\<close>
    using \<open>cstar_algebra A\<close>
    apply (simp add: cstar_algebra_def)
    by (metis closure_closed complex_vector.span_eq_iff)
  also have \<open>\<dots> = A\<close>
    using \<open>cstar_algebra A\<close>
    by (simp add: cstar_algebra_def)
  finally show \<open>sqrt_op a \<in> A\<close>
    by -
qed

lemma cstar_decompose_four_unitaries:
  \<comment> \<open>\<^cite>\<open>takesaki\<close>, Proposition I.4.9\<close>
  fixes M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close>
  assumes \<open>cstar_algebra M\<close>
  assumes [simp]: \<open>id_cblinfun \<in> M\<close>
  assumes \<open>x \<in> M\<close>
  shows \<open>\<exists>a1 a2 a3 a4 u1 u2 u3 u4. u1 \<in> M \<and> u2 \<in> M \<and> u3 \<in> M \<and> u4 \<in> M
              \<and> unitary u1 \<and> unitary u2 \<and> unitary u3 \<and> unitary u4
              \<and> x = a1 *\<^sub>C u1 + a2 *\<^sub>C u2 + a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
proof -
  have herm: \<open>\<exists>u1 u2 a1 a2. u1 \<in> M \<and> u2 \<in> M \<and> unitary u1 \<and> unitary u2 \<and> h = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close> 
    if \<open>h \<in> M\<close> and \<open>h* = h\<close> for h
  proof (cases \<open>h = 0\<close>)
    case True
    show ?thesis 
      apply (rule exI[of _ id_cblinfun]; rule exI[of _  id_cblinfun])
      apply (rule exI[of _ 0]; rule exI[of _ 0])
      by (simp add: True)
  next
    case False
    define h' where \<open>h' = sgn h\<close>
    from False have [simp]: \<open>h' \<in> M\<close> and [simp]: \<open>h'* = h'\<close> and \<open>norm h' = 1\<close>
        using \<open>cstar_algebra M\<close>
        by (auto simp: h'_def sgn_cblinfun_def complex_vector.subspace_scale norm_inverse that
            cstar_algebra_def)
    define u where \<open>u = h' + imaginary_unit *\<^sub>C sqrt_op (id_cblinfun - (h' o\<^sub>C\<^sub>L h'))\<close>
    have [simp]: \<open>u \<in> M\<close>
    proof -
      have \<open>id_cblinfun - h' o\<^sub>C\<^sub>L h' \<in> M\<close>
        using \<open>cstar_algebra M\<close>
        by (simp add: complex_vector.subspace_diff cstar_algebra_def)
      then have \<open>sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') \<in> M\<close>
        apply (rule sqrt_op_in_cstar_algebra[rotated -1])
        using \<open>cstar_algebra M\<close> by auto
      then show ?thesis
        using \<open>cstar_algebra M\<close>
        by (auto simp: u_def cstar_algebra_def intro!: complex_vector.subspace_add complex_vector.subspace_scale)
    qed
    then have [simp]: \<open>u* \<in> M\<close>
      using \<open>cstar_algebra M\<close>
      by (simp add: cstar_algebra_def)
    have *: \<open>h' o\<^sub>C\<^sub>L h' \<le> id_cblinfun\<close>
    proof (rule cblinfun_leI)
      fix x :: 'a assume \<open>norm x = 1\<close>
      have \<open>x \<bullet>\<^sub>C ((h' o\<^sub>C\<^sub>L h') *\<^sub>V x) = (norm (h' *\<^sub>V x))\<^sup>2\<close>
        by (metis \<open>h'* = h'\<close> cblinfun_apply_cblinfun_compose cdot_square_norm cinner_adj_right)
      also have \<open>\<dots> \<le> (norm h')\<^sup>2\<close>
        by (metis \<open>norm h' = 1\<close> \<open>norm x = 1\<close> cnorm_eq_square cnorm_le_square norm_cblinfun one_power2 power2_eq_square)
      also have \<open>\<dots> \<le> 1\<close>
        by (simp add: \<open>norm h' = 1\<close>)
      also have \<open>\<dots> = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V x)\<close>
        using \<open>norm x = 1\<close> cnorm_eq_1 by auto
      finally show \<open>x \<bullet>\<^sub>C ((h' o\<^sub>C\<^sub>L h') *\<^sub>V x) \<le> x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V x)\<close>
        by -
    qed
    have **: \<open>h' o\<^sub>C\<^sub>L sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') = sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') o\<^sub>C\<^sub>L h'\<close>
      apply (rule sqrt_op_commute[symmetric])
      by (auto simp: * cblinfun_compose_minus_right cblinfun_compose_minus_left cblinfun_compose_assoc)
    have [simp]: \<open>unitary u\<close>
      by (auto intro!: unitary_def[THEN iffD2] simp: * ** u_def cblinfun_compose_add_right
          cblinfun_compose_add_left adj_plus cblinfun_compose_minus_left cblinfun_compose_minus_right
          positive_hermitianI sqrt_op_pos scaleC_diff_right scaleC_add_right)
    have [simp]: \<open>u + u* = h' + h'\<close>
      by (simp add: * u_def adj_plus positive_hermitianI[symmetric] sqrt_op_pos)
    show ?thesis
      apply (rule exI[of _ u]; rule exI[of _ \<open>u*\<close>])
      apply (rule exI[of _ \<open>of_real (norm h) / 2\<close>]; rule exI[of _ \<open>of_real (norm h) / 2\<close>])
      by (auto simp flip: scaleC_add_right scaleC_2 simp: h'_def)
  qed
  obtain a1 a2 u1 u2 where \<open>u1 \<in> M\<close> and \<open>u2 \<in> M\<close> and \<open>unitary u1\<close> and \<open>unitary u2\<close> and decomp1: \<open>x + x* = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> complex_vector.subspace_add adj_plus cstar_algebra_def)
  obtain a3 a4 u3 u4 where \<open>u3 \<in> M\<close> and \<open>u4 \<in> M\<close> and \<open>unitary u3\<close> and \<open>unitary u4\<close> 
    and decomp2: \<open>\<i> *\<^sub>C (x - x*) = a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> adj_minus complex_vector.subspace_diff complex_vector.subspace_scale cstar_algebra_def flip: scaleC_minus_right)
  have \<open>x = (1/2) *\<^sub>C (x + x*) + (-\<i>/2) *\<^sub>C (\<i> *\<^sub>C (x - x*))\<close>
    by (simp add: scaleC_add_right scaleC_diff_right flip: scaleC_add_left)
  also have \<open>\<dots> = (a1 / 2) *\<^sub>C u1 + (a2 / 2) *\<^sub>C u2 + (- \<i> * a3 / 2) *\<^sub>C u3 + (- \<i> * a4 / 2) *\<^sub>C u4\<close>
    apply (simp only: decomp1 decomp2)
    by (simp add: scaleC_add_right scaleC_diff_right)
  finally show ?thesis
    using \<open>u1 \<in> M\<close> \<open>u2 \<in> M\<close> \<open>u3 \<in> M\<close> \<open>u4 \<in> M\<close>
      \<open>unitary u1\<close> \<open>unitary u2\<close> \<open>unitary u3\<close> \<open>unitary u4\<close>
    by blast
qed


end
