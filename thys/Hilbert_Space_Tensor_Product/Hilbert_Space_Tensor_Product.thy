section \<open>\<open>Hilbert_Space_Tensor_Product\<close> -- Tensor product of Hilbert Spaces\<close>

theory Hilbert_Space_Tensor_Product
  imports Complex_Bounded_Operators.Complex_L2 (* Registers.Misc *) Misc_Tensor_Product
    Strong_Operator_Topology Polynomial_Interpolation.Ring_Hom

    (* TODO: Consider moving things that depend on these elsewhere? *)
    Positive_Operators Trace_Class Weak_Star_Topology
begin

unbundle cblinfun_notation
(* no_notation Group.m_inv ("inv\<index> _" [81] 80) *)
(* no_notation Congruence.eq_closure_of ("closure'_of\<index>") *)
(* no_notation Order.bottom ("\<bottom>\<index>") *)

subsection \<open>Tensor product on \<^typ>\<open>_ ell2\<close>\<close>

lift_definition tensor_ell2 :: \<open>'a ell2 \<Rightarrow> 'b ell2 \<Rightarrow> ('a\<times>'b) ell2\<close> (infixr "\<otimes>\<^sub>s" 70) is
  \<open>\<lambda>\<psi> \<phi> (i,j). \<psi> i * \<phi> j\<close>
proof -
  fix \<psi> :: \<open>'a \<Rightarrow> complex\<close> and \<phi> :: \<open>'b \<Rightarrow> complex\<close>
  assume \<open>has_ell2_norm \<psi>\<close> \<open>has_ell2_norm \<phi>\<close>
  from \<open>has_ell2_norm \<phi>\<close> have \<phi>_sum: \<open>(\<lambda>j. (\<psi> i * \<phi> j)\<^sup>2) abs_summable_on UNIV\<close> for i
    by (metis ell2_norm_smult(1) has_ell2_norm_def)
  have double_sum: \<open>(\<lambda>i. \<Sum>\<^sub>\<infinity>j. cmod ((\<psi> i * \<phi> j)\<^sup>2)) abs_summable_on UNIV\<close>
    apply (simp add: norm_mult power_mult_distrib infsum_cmult_right' del: real_norm_def)
    apply (rule summable_on_cmult_left)
    using \<open>has_ell2_norm \<psi>\<close> has_ell2_norm_def by auto
  have \<open>(\<lambda>(i,j). (\<psi> i * \<phi> j)\<^sup>2) abs_summable_on UNIV \<times> UNIV\<close>
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
    using \<phi>_sum double_sum by auto
  then show \<open>has_ell2_norm (\<lambda>(i, j). \<psi> i * \<phi> j)\<close>
    by (auto simp add: has_ell2_norm_def case_prod_beta)
qed

lemma tensor_ell2_add1: \<open>tensor_ell2 (a + b) c = tensor_ell2 a c + tensor_ell2 b c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (simp add: vector_space_over_itself.scale_left_distrib)

lemma tensor_ell2_add2: \<open>tensor_ell2 a (b + c) = tensor_ell2 a b + tensor_ell2 a c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (meson algebra_simps)

lemma tensor_ell2_scaleC1: \<open>tensor_ell2 (c *\<^sub>C a) b = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_scaleC2: \<open>tensor_ell2 a (c *\<^sub>C b) = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_diff1: \<open>tensor_ell2 (a - b) c = tensor_ell2 a c - tensor_ell2 b c\<close>
  apply transfer apply (rule ext) 
  by (auto simp: case_prod_beta ordered_field_class.sign_simps)

lemma tensor_ell2_diff2: \<open>tensor_ell2 a (b - c) = tensor_ell2 a b - tensor_ell2 a c\<close>
  apply transfer apply (rule ext) 
  by (auto simp: case_prod_beta ordered_field_class.sign_simps)

lemma tensor_ell2_inner_prod[simp]: \<open>tensor_ell2 a b \<bullet>\<^sub>C tensor_ell2 c d = (a \<bullet>\<^sub>C c) * (b \<bullet>\<^sub>C d)\<close>
  apply (rule local_defE[where y=\<open>tensor_ell2 a b\<close>], rename_tac ab)
  apply (rule local_defE[where y=\<open>tensor_ell2 c d\<close>], rename_tac cd)
proof (transfer, hypsubst_thin)
  fix a c :: \<open>'a \<Rightarrow> complex\<close> and b d :: \<open>'b \<Rightarrow> complex\<close>

  assume \<open>has_ell2_norm (\<lambda>(i, j). a i * b j)\<close> and \<open>has_ell2_norm (\<lambda>(i, j). c i * d j)\<close>

  then have *: \<open>(\<lambda>xy. cnj (a (fst xy) * b (snd xy)) * (c (fst xy) * d (snd xy))) abs_summable_on UNIV\<close>
    apply (rule_tac abs_summable_product)
    apply (metis (mono_tags, lifting) complex_mod_cnj complex_mod_mult_cnj has_ell2_norm_def norm_mult norm_power split_def summable_on_cong)
    by (metis (mono_tags, lifting) case_prod_unfold has_ell2_norm_def power2_eq_square summable_on_cong)

  then have *: \<open>(\<lambda>(x, y). cnj (a x * b y) * (c x * d y)) summable_on UNIV \<times> UNIV\<close>
    apply (rule_tac abs_summable_summable)
    by (simp add: case_prod_unfold)

  have \<open>(\<Sum>\<^sub>\<infinity>i. cnj (case i of (i, j) \<Rightarrow> a i * b j) * (case i of (i, j) \<Rightarrow> c i * d j))
     = (\<Sum>\<^sub>\<infinity>(i,j)\<in>UNIV\<times>UNIV. cnj (a i * b j) * (c i * d j))\<close> (is \<open>?lhs = _\<close>)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. cnj (a i * b j) * (c i * d j))\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using * by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. cnj (a i) * c i) * (\<Sum>\<^sub>\<infinity>j. cnj (b j) * (d j))\<close> (is \<open>_ = ?rhs\<close>)
    apply (subst infsum_cmult_left'[symmetric])
    by (auto intro!: infsum_cong simp flip: infsum_cmult_right')
  finally show \<open>?lhs = ?rhs\<close>
    by -
qed

lemma tensor_ell2_norm: \<open>norm (a \<otimes>\<^sub>s b) = norm a * norm b\<close>
  by (simp add: norm_eq_sqrt_cinner[where 'a=\<open>(_::type) ell2\<close>] norm_mult real_sqrt_mult)

lemma clinear_tensor_ell21: "clinear (\<lambda>b. a \<otimes>\<^sub>s b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: cond_case_prod_eta algebra_simps)

lemma bounded_clinear_tensor_ell21: "bounded_clinear (\<lambda>b. a \<otimes>\<^sub>s b)"
  apply (auto intro!: bounded_clinear.intro clinear_tensor_ell21
      simp: bounded_clinear_axioms_def tensor_ell2_norm)
  using mult.commute order_eq_refl by blast

lemma clinear_tensor_ell22: "clinear (\<lambda>a. a \<otimes>\<^sub>s b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: case_prod_beta' algebra_simps)

lemma bounded_clinear_tensor_ell22: "bounded_clinear (\<lambda>a. tensor_ell2 a b)"
  by (auto intro!: bounded_clinear.intro clinear_tensor_ell22
      simp: bounded_clinear_axioms_def tensor_ell2_norm)

lemma tensor_ell2_ket: "tensor_ell2 (ket i) (ket j) = ket (i,j)"
  apply transfer by auto

lemma tensor_ell2_0_left[simp]: \<open>0 \<otimes>\<^sub>s x = 0\<close>
  apply transfer by auto

lemma tensor_ell2_0_right[simp]: \<open>x \<otimes>\<^sub>s 0 = 0\<close>
  apply transfer by auto

lemma tensor_ell2_sum_left: \<open>(\<Sum>x\<in>X. a x) \<otimes>\<^sub>s b = (\<Sum>x\<in>X. a x \<otimes>\<^sub>s b)\<close>
  apply (induction X rule:infinite_finite_induct)
  by (auto simp: tensor_ell2_add1)

lemma tensor_ell2_sum_right: \<open>a \<otimes>\<^sub>s (\<Sum>x\<in>X. b x) = (\<Sum>x\<in>X. a \<otimes>\<^sub>s b x)\<close>
  apply (induction X rule:infinite_finite_induct)
  by (auto simp: tensor_ell2_add2)

(* TODO: duplicated *) thm tensor_ell2_norm (* Use name norm_tensor_ell2 *)
lemma norm_tensor_ell2: \<open>norm (a \<otimes>\<^sub>s b) = norm a * norm b\<close>
proof transfer
  fix a :: \<open>'a \<Rightarrow> complex\<close> and b :: \<open>'b \<Rightarrow> complex\<close>
  assume \<open>has_ell2_norm a\<close> \<open>has_ell2_norm b\<close>
  have 1: \<open>(\<lambda>j. (a i * b j)\<^sup>2) abs_summable_on UNIV\<close> for i
    using \<open>has_ell2_norm b\<close>
    by (auto simp add: power_mult_distrib norm_mult has_ell2_norm_def
        intro!: summable_on_cmult_right)
  have 2: \<open>(\<lambda>i. cmod (\<Sum>\<^sub>\<infinity>j. cmod ((a i * b j)\<^sup>2))) summable_on UNIV\<close>
    using \<open>has_ell2_norm a\<close>
    by (auto simp add: power_mult_distrib norm_mult has_ell2_norm_def infsum_cmult_right'
        intro!: summable_on_cmult_left)
  have 3: \<open>(\<lambda>p. (a (fst p) * b (snd p))\<^sup>2) abs_summable_on UNIV \<times> UNIV\<close>
    using 1 2 by (auto intro!: abs_summable_on_Sigma_iff[THEN iffD2] simp flip: UNIV_Times_UNIV)

  have \<open>(ell2_norm (\<lambda>(i, j). a i * b j))\<^sup>2 = (\<Sum>\<^sub>\<infinity>(i,j). (cmod (a i * b j))\<^sup>2)\<close>
    by (simp add: ell2_norm_def case_prod_unfold infsum_nonneg)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(i,j). cmod ((a i * b j)\<^sup>2))\<close>
    by (simp add: norm_power)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. cmod ((a i * b j)\<^sup>2))\<close>
    using 3 by (simp add: infsum_Sigma'_banach case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. (cmod (a i))\<^sup>2 * (cmod (b j))\<^sup>2)\<close>
    by (simp add: norm_power power_mult_distrib norm_mult)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (a i))\<^sup>2 * (\<Sum>\<^sub>\<infinity>j. (cmod (b j))\<^sup>2))\<close>
    by (simp add: infsum_cmult_right')
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (a i))\<^sup>2) * (\<Sum>\<^sub>\<infinity>j. (cmod (b j))\<^sup>2)\<close>
    by (simp add: infsum_cmult_left')
  also have \<open>\<dots> = (ell2_norm a)\<^sup>2 * (ell2_norm b)\<^sup>2\<close>
    by (metis (mono_tags, lifting) ell2_norm_def ell2_norm_geq0 real_sqrt_ge_0_iff real_sqrt_pow2_iff)
  finally show \<open>ell2_norm (\<lambda>(i, j). a i * b j) = ell2_norm a * ell2_norm b\<close>
    by (metis ell2_norm_geq0 mult_nonneg_nonneg power2_eq_imp_eq power_mult_distrib)
qed

lemma tensor_ell2_dense:
  fixes S :: \<open>'a ell2 set\<close> and T :: \<open>'b ell2 set\<close>
  assumes \<open>closure (cspan S) = UNIV\<close> and \<open>closure (cspan T) = UNIV\<close>
  shows \<open>closure (cspan {a\<otimes>\<^sub>sb | a b. a\<in>S \<and> b\<in>T}) = UNIV\<close>
proof -
  define ST where \<open>ST = {a\<otimes>\<^sub>sb | a b. a\<in>S \<and> b\<in>T}\<close>
  from assms have 1: \<open>bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close> for F G :: \<open>'a ell2 \<Rightarrow> complex\<close>
    using dense_span_separating[of S F G] by auto
  from assms have 2: \<open>bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>T. F x = G x) \<Longrightarrow> F = G\<close> for F G :: \<open>'b ell2 \<Rightarrow> complex\<close>
    using dense_span_separating[of T F G] by auto
  have \<open>F = G\<close> 
    if [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close> and eq: \<open>\<forall>x\<in>ST. F x = G x\<close>
    for F G :: \<open>('a\<times>'b) ell2 \<Rightarrow> complex\<close>
  proof -
    from eq have eq': \<open>F (s \<otimes>\<^sub>s t) = G (s \<otimes>\<^sub>s t)\<close> if \<open>s \<in> S\<close> and \<open>t \<in> T\<close> for s t
      using ST_def that by blast
    then have \<open>F (s \<otimes>\<^sub>s ket t) = G (s \<otimes>\<^sub>s ket t)\<close> if \<open>s \<in> S\<close> for s t
      apply (rule_tac fun_cong[where x=\<open>ket t\<close>])
      apply (rule 2)
      using that by (auto simp add: bounded_clinear_compose bounded_clinear_tensor_ell21)
    then have \<open>F (ket s \<otimes>\<^sub>s ket t) = G (ket s \<otimes>\<^sub>s ket t)\<close> for s t
      apply (rule_tac fun_cong[where x=\<open>ket s\<close>])
      apply (rule 1)
      apply (auto simp add: bounded_clinear_compose bounded_clinear_tensor_ell21)
      using that bounded_clinear_compose bounded_clinear_tensor_ell22 that by blast+
    then show "F = G"
      apply (rule_tac bounded_clinear_equal_ket)
      by (auto simp: tensor_ell2_ket)
  qed
  then show \<open>closure (cspan ST) = UNIV\<close>
    using separating_dense_span by blast
qed

definition assoc_ell2 :: \<open>(('a\<times>'b)\<times>'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>('b\<times>'c)) ell2\<close> where
  \<open>assoc_ell2 = classical_operator (Some o (\<lambda>((a,b),c). (a,(b,c))))\<close>

lemma unitary_assoc_ell2[simp]: \<open>unitary assoc_ell2\<close>
  unfolding assoc_ell2_def
  apply (rule unitary_classical_operator)
  apply (rule o_bij[of \<open>(\<lambda>(a,(b,c)). ((a,b),c))\<close>])
  by auto

lemma assoc_ell2_tensor: \<open>assoc_ell2 *\<^sub>V ((a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close>
proof -
  note [simp] = bounded_clinear_compose[OF bounded_clinear_tensor_ell21]
    bounded_clinear_compose[OF bounded_clinear_tensor_ell22]
    bounded_clinear_cblinfun_apply
  have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s ket b) \<otimes>\<^sub>s ket c) = (ket a \<otimes>\<^sub>s (ket b \<otimes>\<^sub>s ket c))\<close> for a :: 'a and b :: 'b and c :: 'c
    by (simp add: inj_def assoc_ell2_def classical_operator_ket classical_operator_exists_inj tensor_ell2_ket)
  then have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s ket b) \<otimes>\<^sub>s c) = (ket a \<otimes>\<^sub>s (ket b \<otimes>\<^sub>s c))\<close> for a :: 'a and b :: 'b
    apply (rule_tac fun_cong[where x=c])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (ket a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close> for a :: 'a
    apply (rule_tac fun_cong[where x=b])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then show \<open>assoc_ell2 *\<^sub>V ((a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close>
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
qed

lemma assoc_ell2'_tensor: \<open>assoc_ell2* *\<^sub>V tensor_ell2 a (tensor_ell2 b c) = tensor_ell2 (tensor_ell2 a b) c\<close>
  by (metis (no_types, opaque_lifting) assoc_ell2_tensor cblinfun_apply_cblinfun_compose id_cblinfun.rep_eq unitaryD1 unitary_assoc_ell2)

definition swap_ell2 :: \<open>('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'a) ell2\<close> where
  \<open>swap_ell2 = classical_operator (Some o prod.swap)\<close>

lemma unitary_swap_ell2[simp]: \<open>unitary swap_ell2\<close>
  unfolding swap_ell2_def
  apply (rule unitary_classical_operator)
  by auto

lemma swap_ell2_tensor[simp]: \<open>swap_ell2 *\<^sub>V (a \<otimes>\<^sub>s b) = b \<otimes>\<^sub>s a\<close> for a :: \<open>'a ell2\<close> and b :: \<open>'b ell2\<close>
proof -
  note [simp] = bounded_clinear_compose[OF bounded_clinear_tensor_ell21]
    bounded_clinear_compose[OF bounded_clinear_tensor_ell22]
    bounded_clinear_cblinfun_apply
  have \<open>swap_ell2 *\<^sub>V (ket a \<otimes>\<^sub>s ket b) = (ket b \<otimes>\<^sub>s ket a)\<close> for a :: 'a and b :: 'b
    by (simp add: inj_def swap_ell2_def classical_operator_ket classical_operator_exists_inj tensor_ell2_ket)
  then have \<open>swap_ell2 *\<^sub>V (ket a \<otimes>\<^sub>s b) = (b \<otimes>\<^sub>s ket a)\<close> for a :: 'a
    apply (rule_tac fun_cong[where x=b])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then show \<open>swap_ell2 *\<^sub>V (a \<otimes>\<^sub>s b) = (b \<otimes>\<^sub>s a)\<close>
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
qed

lemma swap_ell2_ket[simp]: \<open>(swap_ell2 :: ('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)*\<^sub>V ket (x,y) = ket (y,x)\<close>
  by (metis swap_ell2_tensor tensor_ell2_ket)

lemma adjoint_swap_ell2[simp]: \<open>swap_ell2* = swap_ell2\<close>
  by (simp add: swap_ell2_def inv_map_total)

lemma tensor_ell2_extensionality:
  assumes "(\<And>s t. a *\<^sub>V (s \<otimes>\<^sub>s t) = b *\<^sub>V (s \<otimes>\<^sub>s t))"
  shows "a = b"
  apply (rule equal_ket, case_tac x, hypsubst_thin)
  by (simp add: assms flip: tensor_ell2_ket)

lemma tensor_ell2_nonzero: \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close> if \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  apply (use that in transfer)
  apply auto
  by (metis mult_eq_0_iff old.prod.case)

lemma swap_ell2_selfinv[simp]: \<open>swap_ell2 o\<^sub>C\<^sub>L swap_ell2 = id_cblinfun\<close>
  by (metis adjoint_swap_ell2 unitary_def unitary_swap_ell2)

lemma bounded_cbilinear_tensor_ell2[bounded_cbilinear]: \<open>bounded_cbilinear (\<otimes>\<^sub>s)\<close>
proof standard
  fix a a' :: "'a ell2" and b b' :: "'b ell2" and r :: complex
  show \<open>tensor_ell2 (a + a') b = tensor_ell2 a b + tensor_ell2 a' b\<close>
    by (meson tensor_ell2_add1)
  show \<open>tensor_ell2 a (b + b') = tensor_ell2 a b + tensor_ell2 a b'\<close>
    by (simp add: tensor_ell2_add2)  
  show \<open>tensor_ell2 (r *\<^sub>C a) b = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC1)
  show \<open>tensor_ell2 a (r *\<^sub>C b) = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC2)
  show \<open>\<exists>K. \<forall>a b. norm (tensor_ell2 a b) \<le> norm a * norm b * K \<close>
    apply (rule exI[of _ 1])
    by (simp add: norm_tensor_ell2)
qed

lemma ket_pair_split: \<open>ket x = tensor_ell2 (ket (fst x)) (ket (snd x))\<close>
  by (simp add: tensor_ell2_ket)



lemma tensor_ell2_is_ortho_set:
  assumes \<open>is_ortho_set A\<close> \<open>is_ortho_set B\<close>
  shows \<open>is_ortho_set {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B}\<close>
  using assms unfolding is_ortho_set_def
  apply auto
   apply fast
  by (metis tensor_ell2_nonzero)

lemma tensor_ell2_dense': \<open>ccspan {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B} = \<top>\<close> if \<open>ccspan A = \<top>\<close> and \<open>ccspan B = \<top>\<close>
proof -
  from that have Adense: \<open>closure (cspan A) = UNIV\<close>
    apply (transfer' fixing: A)
    by simp
  from that have Bdense: \<open>closure (cspan B) = UNIV\<close>
    apply (transfer' fixing: B)
    by simp
  show \<open>ccspan {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B} = \<top>\<close>
    apply (transfer fixing: A B)
    using Adense Bdense by (rule tensor_ell2_dense)
qed

lemma tensor_ell2_is_onb:
  assumes \<open>is_onb A\<close> \<open>is_onb B\<close>
  shows \<open>is_onb {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B}\<close>
proof (subst is_onb_def, intro conjI ballI)
  show \<open>is_ortho_set {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B}\<close>
    apply (rule tensor_ell2_is_ortho_set)
    using assms by (auto simp: is_onb_def)
  show \<open>ccspan {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B} = \<top>\<close>
    apply (rule tensor_ell2_dense')
    using \<open>is_onb A\<close> \<open>is_onb B\<close> by (simp_all add: is_onb_def)
  show \<open>ab \<in> {a \<otimes>\<^sub>s b |a b. a \<in> A \<and> b \<in> B} \<Longrightarrow> norm ab = 1\<close> for ab
    using \<open>is_onb A\<close> \<open>is_onb B\<close> by (auto simp: is_onb_def norm_tensor_ell2)
qed

lemma continuous_tensor_ell2: \<open>continuous_on UNIV (\<lambda>(x::'a ell2, y::'b ell2). x \<otimes>\<^sub>s y)\<close>
proof -
  have cont: \<open>continuous_on UNIV (\<lambda>t. t \<otimes>\<^sub>s x)\<close> for x :: \<open>'b ell2\<close>
    by (intro linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_tensor_ell22)
  have lip: \<open>local_lipschitz (UNIV :: 'a ell2 set) (UNIV :: 'b ell2 set) (\<otimes>\<^sub>s)\<close>
  proof (rule local_lipschitzI)
    fix t :: \<open>'a ell2\<close> and x :: \<open>'b ell2\<close>
    define u L :: real where \<open>u = 1\<close> and \<open>L = norm t + u\<close>
    have \<open>u > 0\<close>
      by (simp add: u_def)
    have [simp]: \<open>L \<ge> 0\<close>
      by (simp add: L_def u_def)
    have *: \<open>norm s \<le> L\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      using that
      apply (simp add: L_def dist_norm)
      by (smt (verit) norm_minus_commute norm_triangle_sub)
    have \<open>L-lipschitz_on (cball x u) ((\<otimes>\<^sub>s) s)\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      apply (rule lipschitz_onI)
      by (auto intro!: mult_right_mono *[OF that]
          simp add: dist_norm norm_tensor_ell2 simp flip: tensor_ell2_diff2)
    with \<open>u > 0\<close> show \<open>\<exists>u>0. \<exists>L. \<forall>s\<in>cball t u \<inter> UNIV. L-lipschitz_on (cball x u \<inter> UNIV) ((\<otimes>\<^sub>s) s)\<close>
      by force
  qed
  show ?thesis
    apply (subst UNIV_Times_UNIV[symmetric])
    using lip cont by (rule Lipschitz.continuous_on_TimesI)
qed

lemma summable_on_tensor_ell2_right: \<open>\<phi> summable_on A \<Longrightarrow> (\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
  apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. \<psi> \<otimes>\<^sub>s x\<close>])
  by (intro bounded_linear_intros)

lemma summable_on_tensor_ell2_left: \<open>\<phi> summable_on A \<Longrightarrow> (\<lambda>x. \<phi> x \<otimes>\<^sub>s \<psi>) summable_on A\<close>
  apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. x \<otimes>\<^sub>s \<psi>\<close>])
  by (intro bounded_linear_intros)

lift_definition tensor_ell2_left :: \<open>'a ell2 \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b) ell2)\<close> is
  \<open>\<lambda>\<psi> \<phi>. \<psi> \<otimes>\<^sub>s \<phi>\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_tensor_ell2)

lemma tensor_ell2_left_apply[simp]: \<open>tensor_ell2_left \<psi> *\<^sub>V \<phi> = \<psi> \<otimes>\<^sub>s \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>) by simp

lift_definition tensor_ell2_right :: \<open>'a ell2 \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'a) ell2)\<close> is
  \<open>\<lambda>\<psi> \<phi>. \<phi> \<otimes>\<^sub>s \<psi>\<close>
  by (simp add: bounded_clinear_tensor_ell22)

lemma tensor_ell2_right_apply[simp]: \<open>tensor_ell2_right \<psi> *\<^sub>V \<phi> = \<phi> \<otimes>\<^sub>s \<psi>\<close>
  apply (transfer fixing: \<psi> \<phi>) by simp

lemma isometry_tensor_ell2_right: \<open>isometry (tensor_ell2_right \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_right_apply norm_tensor_ell2 that)

lemma isometry_tensor_ell2_left: \<open>isometry (tensor_ell2_left \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_left_apply norm_tensor_ell2 that)

lemma tensor_ell2_right_scale: \<open>tensor_ell2_right (a *\<^sub>C \<psi>) = a *\<^sub>C tensor_ell2_right \<psi>\<close>
  apply transfer by (auto intro!: ext simp: tensor_ell2_scaleC2)
lemma tensor_ell2_left_scale: \<open>tensor_ell2_left (a *\<^sub>C \<psi>) = a *\<^sub>C tensor_ell2_left \<psi>\<close>
  apply transfer by (auto intro!: ext simp: tensor_ell2_scaleC1)

lemma tensor_ell2_right_0[simp]: \<open>tensor_ell2_right 0 = 0\<close>
  by (auto intro!: cblinfun_eqI simp: tensor_ell2_right_apply)
lemma tensor_ell2_left_0[simp]: \<open>tensor_ell2_left 0 = 0\<close>
  by (auto intro!: cblinfun_eqI simp: tensor_ell2_left_apply)

lemma tensor_ell2_right_adj_apply[simp]: \<open>(tensor_ell2_right \<psi>*) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<beta>) = (\<psi> \<bullet>\<^sub>C \<beta>) *\<^sub>C \<alpha>\<close>
  apply (rule cinner_extensionality)
  by (simp add: cinner_adj_right tensor_ell2_right_apply)
lemma tensor_ell2_left_adj_apply[simp]: \<open>(tensor_ell2_left \<psi>*) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<beta>) = (\<psi> \<bullet>\<^sub>C \<alpha>) *\<^sub>C \<beta>\<close>
  apply (rule cinner_extensionality)
  by (simp add: cinner_adj_right tensor_ell2_right_apply)


lemma infsum_tensor_ell2_right: \<open>\<psi> \<otimes>\<^sub>s (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<psi> \<otimes>\<^sub>s \<phi> x)\<close>
proof -
  consider (summable) \<open>\<phi> summable_on A\<close> | (summable') \<open>\<psi> \<noteq> 0\<close> \<open>(\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
    | (\<psi>0) \<open>\<psi> = 0\<close>
    | (not_summable) \<open>\<not> \<phi> summable_on A\<close> \<open>\<not> (\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (rule infsum_bounded_linear[symmetric, unfolded o_def, rotated])
      by (intro bounded_linear_intros)
  next
    case summable'
    then have *: \<open>(\<psi> /\<^sub>R (norm \<psi>)\<^sup>2) \<bullet>\<^sub>C \<psi> = 1\<close>
      by (simp add: scaleR_scaleC cdot_square_norm)
    from summable'(2) have \<open>(\<lambda>x. (tensor_ell2_left (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2))* *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi> x)) summable_on A\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, rotated])
      by (intro bounded_linear_intros)
    with * have \<open>\<phi> summable_on A\<close>
      by (simp add: tensor_ell2_left_adj_apply)
    then show ?thesis
      apply (rule infsum_bounded_linear[symmetric, unfolded o_def, rotated])
      by (intro bounded_linear_intros)
  next
    case \<psi>0
    then show ?thesis
      by simp
  next
    case not_summable
    then show ?thesis 
      by (simp add: infsum_not_exists)
  qed
qed

lemma infsum_tensor_ell2_left: \<open>(\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x) \<otimes>\<^sub>s \<psi> = (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x \<otimes>\<^sub>s \<psi>)\<close>
proof -
  from infsum_tensor_ell2_right
  have \<open>swap_ell2 *\<^sub>V (\<psi> \<otimes>\<^sub>s (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x)) = swap_ell2 *\<^sub>V (\<Sum>\<^sub>\<infinity>x\<in>A. \<psi> \<otimes>\<^sub>s \<phi> x)\<close>
    by metis
  then show ?thesis
    by (simp add: flip: infsum_cblinfun_apply_isometry)
qed


subsection \<open>Tensor product of operators on \<^typ>\<open>_ ell2\<close>\<close>

definition tensor_op :: \<open>('a ell2, 'b ell2) cblinfun \<Rightarrow> ('c ell2, 'd ell2) cblinfun
      \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) cblinfun\<close> (infixr "\<otimes>\<^sub>o" 70) where
  \<open>tensor_op M N = cblinfun_extension (range ket) (\<lambda>k. case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (M *\<^sub>V ket x) (N *\<^sub>V ket y))\<close>

(* Vaguely following Takesaki, Section IV.1 *) (* TODO bibtex *)
lemma  
  fixes a :: \<open>'a\<close> and b :: \<open>'b\<close> and c :: \<open>'c\<close> and d :: \<open>'d\<close> and M :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> and N :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  shows tensor_op_ell2: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close>
  and tensor_op_norm: \<open>norm (M \<otimes>\<^sub>o N) = norm M * norm N\<close>
proof -
  define S1 :: \<open>('a\<times>'d) ell2 set\<close> and f1 g1 extg1 
    where \<open>S1 = range ket\<close> 
      and \<open>f1 k = (case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (M *\<^sub>V ket x) (ket y))\<close>
      and \<open>g1 = cconstruct S1 f1\<close> and \<open>extg1 = cblinfun_extension (cspan S1) g1\<close>
    for k
  define S2 :: \<open>('a\<times>'c) ell2 set\<close> and f2 g2 extg2
    where \<open>S2 = range ket\<close> 
      and \<open>f2 k = (case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (ket x) (N *\<^sub>V ket y))\<close>
      and \<open>g2 = cconstruct S2 f2\<close> and \<open>extg2 = cblinfun_extension (cspan S2) g2\<close>
    for k
  define tensorMN where \<open>tensorMN = extg1 o\<^sub>C\<^sub>L extg2\<close>

  have extg1_ket: \<open>extg1 *\<^sub>V ket (x,y) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close>
    and norm_extg1: \<open>norm extg1 \<le> norm M\<close> for x y
  proof -
    have [simp]: \<open>cindependent S1\<close>
      using S1_def cindependent_ket by blast
    have [simp]: \<open>closure (cspan S1) = UNIV\<close>
      by (simp add: S1_def)
    have [simp]: \<open>ket (x, y) \<in> cspan S1\<close> for x y
      by (simp add: S1_def complex_vector.span_base)
    have g1_f1: \<open>g1 (ket (x,y)) = f1 (ket (x,y))\<close> for x y
      by (metis S1_def \<open>cindependent S1\<close> complex_vector.construct_basis g1_def rangeI)
    have [simp]: \<open>clinear g1\<close>
      unfolding g1_def using \<open>cindependent S1\<close> by (rule complex_vector.linear_construct)
    then have g1_add: \<open>g1 (x + y) = g1 x + g1 y\<close> if \<open>x \<in> cspan S1\<close> and \<open>y \<in> cspan S1\<close> for x y
      using clinear_iff by blast
    from \<open>clinear g1\<close> have g1_scale: \<open>g1 (c *\<^sub>C x) = c *\<^sub>C g1 x\<close> if \<open>x \<in> cspan S1\<close> for x c
      by (simp add: complex_vector.linear_scale)

    have g1_bounded: \<open>norm (g1 \<psi>) \<le> norm M * norm \<psi>\<close> if \<open>\<psi> \<in> cspan S1\<close> for \<psi>
    proof -
      from that obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range ket\<close> and \<psi>_tr: \<open>\<psi> = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by (smt (verit) complex_vector.span_explicit mem_Collect_eq S1_def)
      define X Y where \<open>X = fst ` inv ket ` t\<close> and \<open>Y = snd ` inv ket ` t\<close>
      have g1_ket: \<open>g1 (ket (x,y)) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close> for x y
        apply (simp add: g1_def S1_def)
        apply (subst complex_vector.construct_basis)
        by (auto simp add: f1_def cindependent_ket)
      define \<xi> where \<open>\<xi> y = (\<Sum>x\<in>X. if (ket (x,y) \<in> t) then r (ket (x,y)) *\<^sub>C ket x else 0)\<close> for y
      have \<psi>\<xi>: \<open>\<psi> = (\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y)\<close>
      proof -
        have \<open>(\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y) = (\<Sum>xy\<in>X \<times> Y. if ket xy \<in> t then r (ket xy) *\<^sub>C ket xy else 0)\<close>
          apply (simp add: \<xi>_def tensor_ell2_sum_left)
          apply (subst sum.swap)
          by (auto simp: sum.cartesian_product tensor_ell2_scaleC1 tensor_ell2_ket intro!: sum.cong)
        also have \<open>\<dots> = (\<Sum>xy\<in>ket ` (X \<times> Y). if xy \<in> t then r xy *\<^sub>C xy else 0)\<close>
          apply (subst sum.reindex)
          by (auto simp add: inj_on_def)
        also have \<open>\<dots> = \<psi>\<close>
          unfolding \<psi>_tr
          apply (rule sum.mono_neutral_cong_right)
             apply (auto simp add: X_def Y_def \<open>finite t\<close>)
          by (smt (verit, ccfv_SIG) Sigma_cong Y_def \<open>t \<subseteq> range ket\<close> f_inv_into_f image_eqI subsetD subset_fst_snd)
        finally show ?thesis
          by simp
      qed
      have \<open>(norm (g1 \<psi>))\<^sup>2 = (norm (\<Sum>y\<in>Y. (M *\<^sub>V \<xi> y) \<otimes>\<^sub>s ket y))\<^sup>2\<close>
        by (auto simp: \<psi>\<xi> complex_vector.linear_sum \<xi>_def tensor_ell2_sum_left 
            complex_vector.linear_scale g1_ket tensor_ell2_scaleC1
            complex_vector.linear_0 tensor_ell2_ket
            intro!: sum.cong arg_cong[where f=norm])
      also have \<open>\<dots> = (\<Sum>y\<in>Y. (norm ((M *\<^sub>V \<xi> y) \<otimes>\<^sub>s ket y))\<^sup>2)\<close>
        apply (rule pythagorean_theorem_sum)
        using Y_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (\<Sum>y\<in>Y. (norm (M *\<^sub>V \<xi> y))\<^sup>2)\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> \<le> (\<Sum>y\<in>Y. (norm M * norm (\<xi> y))\<^sup>2)\<close>
        by (meson norm_cblinfun norm_ge_zero power_mono sum_mono)
      also have \<open>\<dots> = (norm M)\<^sup>2 * (\<Sum>y\<in>Y. (norm (\<xi> y \<otimes>\<^sub>s ket y))\<^sup>2)\<close>
        by (simp add: power_mult_distrib norm_tensor_ell2 flip: sum_distrib_left)
      also have \<open>\<dots> = (norm M)\<^sup>2 * (norm (\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y))\<^sup>2\<close>
        apply (subst pythagorean_theorem_sum)
        using Y_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (norm M)\<^sup>2 * (norm \<psi>)\<^sup>2\<close>
        using \<psi>\<xi> by fastforce
      finally show \<open>norm (g1 \<psi>) \<le> norm M * norm \<psi>\<close>
        by (metis mult_nonneg_nonneg norm_ge_zero power2_le_imp_le power_mult_distrib)
    qed

    from g1_add g1_scale g1_bounded
    have extg1_exists: \<open>cblinfun_extension_exists (cspan S1) g1\<close>
      apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=\<open>norm M\<close>])
      by auto

    then show \<open>extg1 *\<^sub>V ket (x,y) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close> for x y
      by (simp add: extg1_def cblinfun_extension_apply g1_f1 f1_def)

    from g1_add g1_scale g1_bounded
    show \<open>norm extg1 \<le> norm M\<close>
      by (auto simp: extg1_def intro!: cblinfun_extension_norm_bounded_dense)
  qed

  have extg1_apply: \<open>extg1 *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s \<phi>\<close> for \<psi> \<phi>
  proof -
    have 1: \<open>bounded_clinear (\<lambda>a. extg1 *\<^sub>V (a \<otimes>\<^sub>s ket y))\<close> for y
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell22)
    have 2: \<open>bounded_clinear (\<lambda>a. (M *\<^sub>V a) \<otimes>\<^sub>s ket y)\<close> for y :: 'd
      by (auto intro!: bounded_clinear_tensor_ell22[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)
    have 3: \<open>bounded_clinear (\<lambda>a. extg1 *\<^sub>V (\<psi> \<otimes>\<^sub>s a))\<close>
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell21)
    have 4: \<open>bounded_clinear ((\<otimes>\<^sub>s) (M *\<^sub>V \<psi>))\<close>
      by (auto intro!: bounded_clinear_tensor_ell21[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)

    have eq_ket: \<open>extg1 *\<^sub>V tensor_ell2 \<psi> (ket y) = tensor_ell2 (M *\<^sub>V \<psi>) (ket y)\<close> for y
      apply (rule bounded_clinear_eq_on[where t=\<psi> and G=\<open>range ket\<close>])
      using 1 2 extg1_ket by (auto simp: tensor_ell2_ket)
    show ?thesis 
      apply (rule bounded_clinear_eq_on[where t=\<phi> and G=\<open>range ket\<close>])
      using 3 4 eq_ket by auto
  qed

  have extg2_ket: \<open>extg2 *\<^sub>V ket (x,y) = ket x \<otimes>\<^sub>s (N *\<^sub>V ket y)\<close>
    and norm_extg2: \<open>norm extg2 \<le> norm N\<close> for x y
  proof -
    have [simp]: \<open>cindependent S2\<close>
      using S2_def cindependent_ket by blast
    have [simp]: \<open>closure (cspan S2) = UNIV\<close>
      by (simp add: S2_def)
    have [simp]: \<open>ket (x, y) \<in> cspan S2\<close> for x y
      by (simp add: S2_def complex_vector.span_base)
    have g2_f2: \<open>g2 (ket (x,y)) = f2 (ket (x,y))\<close> for x y
      by (metis S2_def \<open>cindependent S2\<close> complex_vector.construct_basis g2_def rangeI)
    have [simp]: \<open>clinear g2\<close>
      unfolding g2_def using \<open>cindependent S2\<close> by (rule complex_vector.linear_construct)
    then have g2_add: \<open>g2 (x + y) = g2 x + g2 y\<close> if \<open>x \<in> cspan S2\<close> and \<open>y \<in> cspan S2\<close> for x y
      using clinear_iff by blast
    from \<open>clinear g2\<close> have g2_scale: \<open>g2 (c *\<^sub>C x) = c *\<^sub>C g2 x\<close> if \<open>x \<in> cspan S2\<close> for x c
      by (simp add: complex_vector.linear_scale)

    have g2_bounded: \<open>norm (g2 \<psi>) \<le> norm N * norm \<psi>\<close> if \<open>\<psi> \<in> cspan S2\<close> for \<psi>
    proof -
      from that obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range ket\<close> and \<psi>_tr: \<open>\<psi> = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by (smt (verit) complex_vector.span_explicit mem_Collect_eq S2_def)
      define X Y where \<open>X = fst ` inv ket ` t\<close> and \<open>Y = snd ` inv ket ` t\<close>
      have g2_ket: \<open>g2 (ket (x,y)) = ket x \<otimes>\<^sub>s (N *\<^sub>V ket y)\<close> for x y
        apply (simp add: g2_def S2_def)
        apply (subst complex_vector.construct_basis)
        by (auto simp add: f2_def cindependent_ket)
      define \<xi> where \<open>\<xi> x = (\<Sum>y\<in>Y. if (ket (x,y) \<in> t) then r (ket (x,y)) *\<^sub>C ket y else 0)\<close> for x
      have \<psi>\<xi>: \<open>\<psi> = (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x)\<close>
      proof -
        have \<open>(\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x) = (\<Sum>xy\<in>X \<times> Y. if ket xy \<in> t then r (ket xy) *\<^sub>C ket xy else 0)\<close>
          apply (simp add: \<xi>_def tensor_ell2_sum_right)
          by (auto simp: sum.cartesian_product tensor_ell2_scaleC2 tensor_ell2_ket intro!: sum.cong)
        also have \<open>\<dots> = (\<Sum>xy\<in>ket ` (X \<times> Y). if xy \<in> t then r xy *\<^sub>C xy else 0)\<close>
          apply (subst sum.reindex)
          by (auto simp add: inj_on_def)
        also have \<open>\<dots> = \<psi>\<close>
          unfolding \<psi>_tr
          apply (rule sum.mono_neutral_cong_right)
             apply (auto simp add: X_def Y_def \<open>finite t\<close>)
          by (smt (verit, ccfv_SIG) Sigma_cong Y_def \<open>t \<subseteq> range ket\<close> f_inv_into_f image_eqI subsetD subset_fst_snd)
        finally show ?thesis
          by simp
      qed
      have \<open>(norm (g2 \<psi>))\<^sup>2 = (norm (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s (N *\<^sub>V \<xi> x)))\<^sup>2\<close>
        by (auto simp: \<psi>\<xi> complex_vector.linear_sum \<xi>_def tensor_ell2_sum_right
            complex_vector.linear_scale g2_ket tensor_ell2_scaleC2
            complex_vector.linear_0 tensor_ell2_ket
            intro!: sum.cong arg_cong[where f=norm])
      also have \<open>\<dots> = (\<Sum>x\<in>X. (norm (ket x \<otimes>\<^sub>s (N *\<^sub>V \<xi> x)))\<^sup>2)\<close>
        apply (rule pythagorean_theorem_sum)
        using X_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (\<Sum>x\<in>X. (norm (N *\<^sub>V \<xi> x))\<^sup>2)\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> \<le> (\<Sum>x\<in>X. (norm N * norm (\<xi> x))\<^sup>2)\<close>
        by (meson norm_cblinfun norm_ge_zero power_mono sum_mono)
      also have \<open>\<dots> = (norm N)\<^sup>2 * (\<Sum>x\<in>X. (norm (ket x \<otimes>\<^sub>s \<xi> x))\<^sup>2)\<close>
        by (simp add: power_mult_distrib norm_tensor_ell2 flip: sum_distrib_left)
      also have \<open>\<dots> = (norm N)\<^sup>2 * (norm (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x))\<^sup>2\<close>
        apply (subst pythagorean_theorem_sum)
        using X_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (norm N)\<^sup>2 * (norm \<psi>)\<^sup>2\<close>
        using \<psi>\<xi> by fastforce
      finally show \<open>norm (g2 \<psi>) \<le> norm N * norm \<psi>\<close>
        by (metis mult_nonneg_nonneg norm_ge_zero power2_le_imp_le power_mult_distrib)
    qed

    from g2_add g2_scale g2_bounded
    have extg2_exists: \<open>cblinfun_extension_exists (cspan S2) g2\<close>
      apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=\<open>norm N\<close>])
      by auto

    then show \<open>extg2 *\<^sub>V ket (x,y) = ket x \<otimes>\<^sub>s N *\<^sub>V ket y\<close> for x y
      by (simp add: extg2_def cblinfun_extension_apply g2_f2 f2_def)

    from g2_add g2_scale g2_bounded
    show \<open>norm extg2 \<le> norm N\<close>
      by (auto simp: extg2_def intro!: cblinfun_extension_norm_bounded_dense)
  qed

  have extg2_apply: \<open>extg2 *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = \<psi> \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
  proof -
    have 1: \<open>bounded_clinear (\<lambda>a. extg2 *\<^sub>V (ket x \<otimes>\<^sub>s a))\<close> for x
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell21)
    have 2: \<open>bounded_clinear (\<lambda>a. ket x \<otimes>\<^sub>s (N *\<^sub>V a))\<close> for x :: 'a
      by (auto intro!: bounded_clinear_tensor_ell21[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)
    have 3: \<open>bounded_clinear (\<lambda>a. extg2 *\<^sub>V (a \<otimes>\<^sub>s \<phi>))\<close>
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell22)
    have 4: \<open> bounded_clinear (\<lambda>a. a \<otimes>\<^sub>s (N *\<^sub>V \<phi>))\<close>
      by (auto intro!: bounded_clinear_tensor_ell22[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)

    have eq_ket: \<open>extg2 *\<^sub>V (ket x \<otimes>\<^sub>s \<phi>) = ket x \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for x
      apply (rule bounded_clinear_eq_on[where t=\<phi> and G=\<open>range ket\<close>])
      using 1 2 extg2_ket by (auto simp: tensor_ell2_ket)
    show ?thesis 
      apply (rule bounded_clinear_eq_on[where t=\<psi> and G=\<open>range ket\<close>])
      using 3 4 eq_ket by auto
  qed

  have tensorMN_apply: \<open>tensorMN *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
    by (simp add: extg1_apply extg2_apply tensorMN_def)

  have \<open>cblinfun_extension_exists (range ket) (\<lambda>k. case inv ket k of (x, y) \<Rightarrow> (M *\<^sub>V ket x) \<otimes>\<^sub>s (N *\<^sub>V ket y))\<close>
    apply (rule cblinfun_extension_existsI[where B=tensorMN])
    using tensorMN_apply[of \<open>ket _\<close> \<open>ket _\<close>] by (auto simp: tensor_ell2_ket)

  then have otimes_ket: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (ket (a,c)) = (M *\<^sub>V ket a) \<otimes>\<^sub>s (N *\<^sub>V ket c)\<close> for a c
    by (simp add: tensor_op_def cblinfun_extension_apply)

  have tensorMN_otimes: \<open>M \<otimes>\<^sub>o N = tensorMN\<close>
    apply (rule_tac equal_ket) 
    using tensorMN_apply[of \<open>ket _\<close> \<open>ket _\<close>] 
    by (auto simp: otimes_ket tensor_ell2_ket)

  show otimes_apply: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
    by (simp add: tensorMN_apply tensorMN_otimes)

  show \<open>norm (M \<otimes>\<^sub>o N) = norm M * norm N\<close>
  proof (rule order.antisym)
    show \<open>norm (M \<otimes>\<^sub>o N) \<le> norm M * norm N\<close>
      apply (simp add: tensorMN_otimes tensorMN_def)
      by (smt (verit, best) mult_mono norm_cblinfun_compose norm_extg1 norm_extg2 norm_ge_zero)
    have \<open>norm (M \<otimes>\<^sub>o N) \<ge> norm M * norm N * \<epsilon>\<close> if \<open>\<epsilon> < 1\<close> and \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof -
      obtain \<psi>a where 1: \<open>norm (M *\<^sub>V \<psi>a) \<ge> norm M * sqrt \<epsilon>\<close> and \<open>norm \<psi>a = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_mult[where \<epsilon>=\<open>sqrt \<epsilon>\<close> and A=M])
        using \<open>\<epsilon> < 1\<close> by auto
      obtain \<psi>b where 2: \<open>norm (N *\<^sub>V \<psi>b) \<ge> norm N * sqrt \<epsilon>\<close> and \<open>norm \<psi>b = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_mult[where \<epsilon>=\<open>sqrt \<epsilon>\<close> and A=N])
        using \<open>\<epsilon> < 1\<close> by auto
      have \<open>norm ((M \<otimes>\<^sub>o N) *\<^sub>V (\<psi>a \<otimes>\<^sub>s \<psi>b)) / norm (\<psi>a \<otimes>\<^sub>s \<psi>b) = norm ((M \<otimes>\<^sub>o N) *\<^sub>V (\<psi>a \<otimes>\<^sub>s \<psi>b))\<close>
        using \<open>norm \<psi>a = 1\<close> \<open>norm \<psi>b = 1\<close>
        by (simp add: norm_tensor_ell2) 
      also have \<open>\<dots> = norm (M *\<^sub>V \<psi>a) * norm (N *\<^sub>V \<psi>b)\<close>
        by (simp add: norm_tensor_ell2 otimes_apply)
      also from 1 2 have \<open>\<dots> \<ge> (norm M * sqrt \<epsilon>) * (norm N * sqrt \<epsilon>)\<close> (is \<open>_ \<ge> \<dots>\<close>)
        apply (rule mult_mono')
        using \<open>\<epsilon> > 0\<close> by auto
      also have \<open>\<dots> = norm M * norm N * \<epsilon>\<close>
        using \<open>\<epsilon> > 0\<close> by force
      finally show ?thesis
        using cblinfun_norm_geqI by blast
    qed
    then show \<open>norm (M \<otimes>\<^sub>o N) \<ge> norm M * norm N\<close>
      by (metis field_le_mult_one_interval mult.commute)
  qed
qed

lemma tensor_op_ket: \<open>tensor_op M N *\<^sub>V (ket (a,c)) = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c)\<close>
  by (metis tensor_ell2_ket tensor_op_ell2)

lemma comp_tensor_op: "(tensor_op a b) o\<^sub>C\<^sub>L (tensor_op c d) = tensor_op (a o\<^sub>C\<^sub>L c) (b o\<^sub>C\<^sub>L d)"
  for a :: "'e ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2" and b :: "'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2" and
      c :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2" and d :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'f ell2"
  apply (rule equal_ket)
  apply (rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_op_left_add: \<open>(x + y) \<otimes>\<^sub>o b = x \<otimes>\<^sub>o b + y \<otimes>\<^sub>o b\<close>
  for x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add1 tensor_op_ket)

lemma tensor_op_right_add: \<open>b \<otimes>\<^sub>o (x + y) = b \<otimes>\<^sub>o x + b \<otimes>\<^sub>o y\<close>
  for x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add2 tensor_op_ket)

lemma tensor_op_scaleC_left: \<open>(c *\<^sub>C x) \<otimes>\<^sub>o b = c *\<^sub>C (x \<otimes>\<^sub>o b)\<close>
  for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  by (auto intro!: equal_ket simp: tensor_op_ket tensor_ell2_scaleC1)

lemma tensor_op_scaleC_right: \<open>b \<otimes>\<^sub>o (c *\<^sub>C x) = c *\<^sub>C (b \<otimes>\<^sub>o x)\<close>
  for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  by (auto intro!: equal_ket simp: tensor_op_ket tensor_ell2_scaleC2)

lemma tensor_op_bounded_cbilinear[simp]: \<open>bounded_cbilinear tensor_op\<close>
  by (auto intro!: bounded_cbilinear.intro exI[of _ 1]
      simp: tensor_op_left_add tensor_op_right_add tensor_op_scaleC_left tensor_op_scaleC_right tensor_op_norm)

lemma tensor_op_cbilinear[simp]: \<open>cbilinear tensor_op\<close>
  by (simp add: bounded_cbilinear.add_left bounded_cbilinear.add_right cbilinear_def clinearI tensor_op_scaleC_left tensor_op_scaleC_right)

lemma tensor_butter: \<open>butterket i j \<otimes>\<^sub>o butterket k l = butterket (i,k) (j,l)\<close>
  apply (rule equal_ket, rename_tac x, case_tac x)
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2 butterfly_def)
  by (auto simp: tensor_ell2_scaleC1 tensor_ell2_scaleC2)

lemma cspan_tensor_op_butter: \<open>cspan {tensor_op (butterket i j) (butterket k l)| (i::_::finite) (j::_::finite) (k::_::finite) (l::_::finite). True} = UNIV\<close>
  unfolding tensor_butter
  apply (subst cspan_butterfly_ket[symmetric])
  by (metis surj_pair)

lemma cindependent_tensor_op_butter: \<open>cindependent {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close>
  unfolding tensor_butter
  using cindependent_butterfly_ket
  by (smt (z3) Collect_mono_iff complex_vector.independent_mono)

lift_definition right_amplification :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow>\<^sub>C\<^sub>L (('a\<times>'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'c) ell2)\<close> is
  \<open>\<lambda>a. a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left)

lift_definition left_amplification :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c\<times>'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c\<times>'b) ell2)\<close> is
  \<open>\<lambda>a. id_cblinfun \<otimes>\<^sub>o a\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right)



lemma sandwich_tensor_ell2_right: \<open>sandwich (tensor_ell2_right \<psi>*) *\<^sub>V a \<otimes>\<^sub>o b = (\<psi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) *\<^sub>C a\<close>
  apply (rule cblinfun_eqI)
  by (simp add: sandwich_apply tensor_ell2_right_apply tensor_op_ell2)
lemma sandwich_tensor_ell2_left: \<open>sandwich (tensor_ell2_left \<psi>*) *\<^sub>V a \<otimes>\<^sub>o b = (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>)) *\<^sub>C b\<close>
  apply (rule cblinfun_eqI)
  by (simp add: sandwich_apply tensor_ell2_left_apply tensor_op_ell2)

lemma tensor_op_adjoint: \<open>(tensor_op a b)* = tensor_op (a*) (b*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)
  by (simp add: cinner_adj_left)

lemma has_sum_id_tensor_butterfly_ket: \<open>has_sum (\<lambda>i. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>) UNIV \<psi>\<close>
proof -
  have *: \<open>(\<Sum>i\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>) = trunc_ell2 (UNIV \<times> F) \<psi>\<close> if \<open>finite F\<close> for F
  proof (rule Rep_ell2_inject[THEN iffD1], rule ext, rename_tac xy)
    fix xy :: \<open>'b \<times> 'a\<close>
    obtain x y where xy: \<open>xy = (x,y)\<close>
      by fastforce
    have \<open>Rep_ell2 (\<Sum>i\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>) xy
       = ket xy \<bullet>\<^sub>C (\<Sum>i\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>)\<close>
      by (simp add: cinner_ket_left)
    also have \<open>... = (\<Sum>i\<in>F. ket xy \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>))\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum>i\<in>F. ket xy \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket i)* *\<^sub>V \<psi>))\<close>
      by (simp add: tensor_op_adjoint)
    also have \<open>\<dots> = (\<Sum>i\<in>F. ((id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V ket xy) \<bullet>\<^sub>C \<psi>)\<close>
      by (meson cinner_adj_right)
    also have \<open>\<dots> = of_bool (y\<in>F) * (ket xy \<bullet>\<^sub>C \<psi>)\<close>
      apply (subst sum_single[where i=y])
      by (auto simp: xy tensor_op_ell2 cinner_ket that simp flip: tensor_ell2_ket)
    also have \<open>\<dots> = of_bool (y\<in>F) * (Rep_ell2 \<psi> xy)\<close>
      by (simp add: cinner_ket_left)
    also have \<open>\<dots> = Rep_ell2 (trunc_ell2 (UNIV \<times> F) \<psi>) xy\<close>
      by (simp add: trunc_ell2.rep_eq xy)
    finally show \<open>Rep_ell2 (\<Sum>i\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>) xy = \<dots>\<close>
      by -
  qed

  have \<open>((\<lambda>F. trunc_ell2 F \<psi>) \<longlongrightarrow> trunc_ell2 UNIV \<psi>) (filtermap ((\<times>)UNIV) (finite_subsets_at_top UNIV))\<close>
    apply (rule trunc_ell2_lim_general)
    by (auto simp add: filterlim_def le_filter_def eventually_finite_subsets_at_top
        eventually_filtermap intro!: exI[where x=\<open>snd ` _\<close>])
  then have \<open>((\<lambda>F. trunc_ell2 (UNIV\<times>F) \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
    apply (simp add: filterlim_def filtermap_filtermap)
    by -
  then have \<open>((\<lambda>F. (\<Sum>i\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>)) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
    apply (rule Lim_transform_eventually)
    by (simp add: * eventually_finite_subsets_at_top_weakI)
  then show ?thesis
    by (simp add: has_sum_def)
qed


(* TODO: make proper comment. With bibtex
Takesaki, p.185, (10) basically is this, I think.
*)
lemma tensor_op_dense: \<open>cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. True}) = UNIV\<close>
proof (intro order.antisym subset_UNIV subsetI)
  fix c :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
  define c' where \<open>c' i j = (tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close> for i j
  define AB :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2) set\<close> where
    \<open>AB = cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. True})\<close>

  have [simp]: \<open>closedin cstrong_operator_topology AB\<close>
    by (simp add: AB_def)
  have [simp]: \<open>csubspace AB\<close>
    using AB_def sot_closure_is_csubspace' by blast

  have *: \<open>c' i j \<otimes>\<^sub>o butterket i j = (id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)\<close> for i j
  proof (rule equal_ket, rule cinner_ket_eqI, rename_tac a b)
    fix a :: \<open>'a \<times> 'b\<close> and b :: \<open>'c \<times> 'd\<close>
    obtain bi bj ai aj where b: \<open>b = (bi,bj)\<close> and a: \<open>a = (ai,aj)\<close>
      by (meson surj_pair)
    have \<open>ket b \<bullet>\<^sub>C ((c' i j \<otimes>\<^sub>o butterket i j) *\<^sub>V ket a) = of_bool (j = aj \<and> bj = i) * ((ket bi \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V ket ai \<otimes>\<^sub>s ket aj))\<close>
      by (auto simp add: a b tensor_op_ell2 cinner_ket c'_def tensor_ell2_right_apply cinner_adj_right
          simp flip: tensor_ell2_ket)
    also have \<open>\<dots> = ket b \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket i o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L id_cblinfun \<otimes>\<^sub>o selfbutterket j) *\<^sub>V ket a)\<close>
      apply (subst asm_rl[of \<open>id_cblinfun \<otimes>\<^sub>o selfbutterket i = (id_cblinfun \<otimes>\<^sub>o selfbutterket i)*\<close>])
       apply (simp add: tensor_op_adjoint)
      by (auto simp: a b tensor_op_ell2 cinner_adj_right cinner_ket
          simp flip: tensor_ell2_ket)
    finally show \<open>ket b \<bullet>\<^sub>C ((c' i j \<otimes>\<^sub>o butterket i j) *\<^sub>V ket a) =
           ket b \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket i o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L id_cblinfun \<otimes>\<^sub>o selfbutterket j) *\<^sub>V ket a)\<close>
      by -
  qed

  have \<open>c' i j \<otimes>\<^sub>o butterket i j \<in> AB\<close> for i j
  proof -
    have \<open>c' i j \<otimes>\<^sub>o butterket i j \<in> {a \<otimes>\<^sub>o b | a b. True}\<close>
      by auto
    also have \<open>\<dots> \<subseteq> cspan \<dots>\<close>
      by (simp add: complex_vector.span_superset)
    also have \<open>\<dots> \<subseteq> cstrong_operator_topology closure_of \<dots>\<close>
      apply (rule closure_of_subset)
      by (simp add: cstrong_operator_topology_topspace)
    also have \<open>\<dots> = AB\<close>
      by (simp add: AB_def)
    finally show ?thesis
      by simp
  qed
  with * have AB1: \<open>(id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j) \<in> AB\<close> for i j
    by simp
  have \<open>has_sum (\<lambda>i. ((id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>)
            UNIV ((c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>)\<close> for j \<psi>
    apply simp by (rule has_sum_id_tensor_butterfly_ket)
  then have AB2: \<open>(c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) \<in> AB\<close> for j
    apply (rule has_sum_closed_cstrong_operator_topology[rotated -1])
    using AB1 by auto

  have \<open>has_sum (\<lambda>j. (c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>) UNIV (c *\<^sub>V \<psi>)\<close> for \<psi>
    apply simp
    apply (rule has_sum_cblinfun_apply)
    by (rule has_sum_id_tensor_butterfly_ket)
  then show AB3: \<open>c \<in> AB\<close>
    apply (rule has_sum_closed_cstrong_operator_topology[rotated -1])
    using AB2 by auto
qed

(* TODO this one, too? *)
(* lemma tensor_op_dense:
  fixes S :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2) set\<close> and T :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2) set\<close>
  assumes \<open>cstrong_operator_topology closure_of (cspan S) = UNIV\<close> and \<open>cstrong_operator_topology closure_of (cspan T) = UNIV\<close>
  shows \<open>cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. a\<in>S \<and> b\<in>T}) = UNIV\<close> *)


(* TODO analog lemma, infinite.
(Works for SOT-continuous linear F,G. Any alternative (simpler?) useful characterization?) *)
lemma tensor_extensionality_finite:
  fixes F G :: \<open>((('a::finite \<times> 'b::finite) ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c::finite \<times> 'd::finite) ell2)) \<Rightarrow> 'e::complex_vector\<close>
  assumes [simp]: "clinear F" "clinear G"
  assumes tensor_eq: "(\<And>a b. F (tensor_op a b) = G (tensor_op a b))"
  shows "F = G"
proof (rule ext, rule complex_vector.linear_eq_on_span[where f=F and g=G])
  show \<open>clinear F\<close> and \<open>clinear G\<close>
    using assms by (simp_all add: cbilinear_def)
  show \<open>x \<in> cspan  {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close> 
    for x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
    using cspan_tensor_op_butter by auto
  show \<open>F x = G x\<close> if \<open>x \<in> {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close> for x
    using that by (auto simp: tensor_eq)
qed

lemma tensor_id[simp]: \<open>tensor_op id_cblinfun id_cblinfun = id_cblinfun\<close>
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_butterfly[simp]: "tensor_op (butterfly \<psi> \<psi>') (butterfly \<phi> \<phi>') = butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 butterfly_def
      cblinfun_apply_cblinfun_compose tensor_ell2_scaleC1 tensor_ell2_scaleC2)

definition tensor_lift :: \<open>(('a1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a2::finite ell2) \<Rightarrow> ('b1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2::finite ell2) \<Rightarrow> 'c)
                        \<Rightarrow> ((('a1\<times>'b1) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a2\<times>'b2) ell2) \<Rightarrow> 'c::complex_normed_vector)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b))"
(* TODO use cblinfun_extension? *)
(* TODO the same for tensor_ell2 *)

lemma 
  fixes F2 :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
            \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2
            \<Rightarrow> 'e::complex_normed_vector"
  assumes "cbilinear F2"
  shows tensor_lift_clinear: "clinear (tensor_lift F2)"
    and tensor_lift_correct:  \<open>(\<lambda>a b. tensor_lift F2 (a \<otimes>\<^sub>o b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_op (butterket i j) (butterket k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butterket i j) (butterket k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: t4_def x tensor_op_ell2 butterfly_def cinner_ket simp flip: tensor_ell2_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: t4_def x y tensor_op_ell2 butterfly_def cblinfun_apply_cblinfun_compose cinner_ket
               simp flip: tensor_ell2_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_op (butterket i j) (butterket k l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_op (butterket i j) (butterket k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    thm cblinfun_extension_exists_finite_dim[where \<phi>=\<phi>]
    apply (rule cblinfun_extension_exists_finite_dim)
     apply auto unfolding * 
    using cindependent_tensor_op_butter cspan_tensor_op_butter by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_op (butterket i j) (butterket k l) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_op a (butterket k l) = F2 a (butterket k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto intro!: clinear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_op a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
     apply (metis cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_op a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto simp: cblinfun.add_right clinearI
                        intro!: clinear_compose[unfolded o_def, where f=\<open>tensor_op a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast

  have \<open>clinear F2' \<and> (\<forall>a b. F2' (tensor_op a b) = F2 a b)\<close>
    unfolding F2'_def tensor_lift_def 
    apply (rule someI[where x=\<open>(*\<^sub>V) G\<close> and P=\<open>\<lambda>G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b)\<close>])
    using G_F2 by (simp add: cblinfun.add_right clinearI)

  then show \<open>clinear F2'\<close> and \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
    unfolding F2'_def by auto
qed


lemma tensor_op_nonzero:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  assumes \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>a *\<^sub>V ket i \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from \<open>b \<noteq> 0\<close> obtain j where j: \<open>b *\<^sub>V ket j \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from i j have ijneq0: \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  have \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) = (a \<otimes>\<^sub>o b) *\<^sub>V ket (i,j)\<close>
    by (simp add: tensor_op_ket)
  with ijneq0 show \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by force
qed

lemma inj_tensor_ell2_left: \<open>inj (\<lambda>a::'a ell2. a \<otimes>\<^sub>s b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>s b = y \<otimes>\<^sub>s b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>x \<otimes>\<^sub>s b \<noteq> y \<otimes>\<^sub>s b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add1)
  with eq show False
    by auto
qed

lemma inj_tensor_ell2_right: \<open>inj (\<lambda>b::'b ell2. a \<otimes>\<^sub>s b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>s x = a \<otimes>\<^sub>s y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>a \<otimes>\<^sub>s x \<noteq> a \<otimes>\<^sub>s y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add2)
  with eq show False
    by auto
qed

lemma inj_tensor_left: \<open>inj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. a \<otimes>\<^sub>o b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>o b = y \<otimes>\<^sub>o b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>x \<otimes>\<^sub>o b \<noteq> y \<otimes>\<^sub>o b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_left_add) 
  with eq show False
    by auto
qed

lemma inj_tensor_right: \<open>inj (\<lambda>b::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. a \<otimes>\<^sub>o b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>o x = a \<otimes>\<^sub>o y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>a \<otimes>\<^sub>o x \<noteq> a \<otimes>\<^sub>o y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_right_add) 
  with eq show False
    by auto
qed

lemma tensor_ell2_almost_injective:
  assumes \<open>tensor_ell2 a b = tensor_ell2 c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>cinner (ket i) a \<noteq> 0\<close>
    by (metis cinner_eq_zero_iff cinner_ket_left ell2_pointwise_ortho)
  have \<open>cinner (ket i \<otimes>\<^sub>s ket j) (a \<otimes>\<^sub>s b) = cinner (ket i \<otimes>\<^sub>s ket j) (c \<otimes>\<^sub>s d)\<close> for j
    using assms by simp
  then have eq2: \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) c) * (cinner (ket j) d)\<close> for j
    by (metis tensor_ell2_inner_prod)
  then obtain \<gamma> where \<open>cinner (ket i) c = \<gamma> * cinner (ket i) a\<close>
    by (metis i eq_divide_eq)
  with eq2 have \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) a) * (\<gamma> * cinner (ket j) d)\<close> for j
    by simp
  then have \<open>cinner (ket j) b = cinner (ket j) (\<gamma> *\<^sub>C d)\<close> for j
    using i by force
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cinner_ket_eqI)
  then show ?thesis
    by auto
qed


lemma tensor_op_almost_injective:
  fixes a c :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    and b d :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  assumes \<open>tensor_op a b = tensor_op c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof (cases \<open>d = 0\<close>)
  case False
  from \<open>a \<noteq> 0\<close> obtain \<psi> where \<psi>: \<open>a *\<^sub>V \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  have \<open>(a \<otimes>\<^sub>o b) (\<psi> \<otimes>\<^sub>s \<phi>) = (c \<otimes>\<^sub>o d) (\<psi> \<otimes>\<^sub>s \<phi>)\<close> for \<phi>
    using assms by simp
  then have eq2: \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (c \<psi>) \<otimes>\<^sub>s (d \<phi>)\<close> for \<phi>
    by (simp add: tensor_op_ell2)
  then have eq2': \<open>(d \<phi>) \<otimes>\<^sub>s (c \<psi>) = (b \<phi>) \<otimes>\<^sub>s (a \<psi>)\<close> for \<phi>
    by (metis swap_ell2_tensor)
  from False obtain \<phi>0 where \<phi>0: \<open>d \<phi>0 \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  obtain \<gamma> where \<open>c \<psi> = \<gamma> *\<^sub>C a \<psi>\<close>
    apply atomize_elim
    using eq2' \<phi>0 by (rule tensor_ell2_almost_injective)
  with eq2 have \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (a \<psi>) \<otimes>\<^sub>s (\<gamma> *\<^sub>C d \<phi>)\<close> for \<phi>
    by (simp add: tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  then have \<open>b \<phi> = \<gamma> *\<^sub>C d \<phi>\<close> for \<phi>
    by (smt (verit, best) \<psi> complex_vector.scale_cancel_right tensor_ell2_almost_injective tensor_ell2_nonzero tensor_ell2_scaleC2)
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cblinfun_eqI)
  then show ?thesis
    by auto
next
  case True
  then have \<open>c \<otimes>\<^sub>o d = 0\<close>
    by (metis add_cancel_right_left tensor_op_right_add)
  then have \<open>a \<otimes>\<^sub>o b = 0\<close>
    using assms(1) by presburger
  with \<open>a \<noteq> 0\<close> have \<open>b = 0\<close>
    by (meson tensor_op_nonzero)
  then show ?thesis
    by auto
qed

lemma clinear_tensor_left[simp]: \<open>clinear (\<lambda>a. a \<otimes>\<^sub>o b :: _ ell2 \<Rightarrow>\<^sub>C\<^sub>L _ ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_left_add)
  by (rule tensor_op_scaleC_left)

lemma clinear_tensor_right[simp]: \<open>clinear (\<lambda>b. a \<otimes>\<^sub>o b :: _ ell2 \<Rightarrow>\<^sub>C\<^sub>L _ ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_right_add)
  by (rule tensor_op_scaleC_right)

lemma tensor_op_0_left[simp]: \<open>tensor_op 0 x = (0 :: ('a*'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c*'d) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma tensor_op_0_right[simp]: \<open>tensor_op x 0 = (0 :: ('a*'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c*'d) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma bij_tensor_ell2_one_dim_left:
  assumes \<open>\<psi> \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
proof (rule bijI)
  show \<open>inj (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    using assms by (rule inj_tensor_ell2_right)
  have \<open>\<exists>x. \<psi> \<otimes>\<^sub>s x = \<phi>\<close> for \<phi> :: \<open>('a*'b) ell2\<close>
  proof (use assms in transfer)
    fix \<psi> :: \<open>'a \<Rightarrow> complex\<close> and \<phi> :: \<open>'a*'b \<Rightarrow> complex\<close>
    assume \<open>has_ell2_norm \<phi>\<close> and \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close>
    define c where \<open>c = \<psi> undefined\<close>
    then have \<open>\<psi> a = c\<close> for a 
      apply (subst everything_the_same[of _ undefined])
      by simp
    with \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close> have \<open>c \<noteq> 0\<close>
      by auto

    define x where \<open>x j = \<phi> (undefined, j) / c\<close> for j
    have \<open>(\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (auto intro!: ext simp: x_def \<open>\<psi> _ = c\<close> \<open>c \<noteq> 0\<close>)
      apply (subst (2) everything_the_same[of _ undefined])
      by simp
    moreover have \<open>has_ell2_norm x\<close>
    proof -
      have \<open>(\<lambda>(i,j). (\<phi> (i,j))\<^sup>2) abs_summable_on UNIV\<close>
        using \<open>has_ell2_norm \<phi>\<close> has_ell2_norm_def by auto
      then have \<open>(\<lambda>(i,j). (\<phi> (i,j))\<^sup>2) abs_summable_on Pair undefined ` UNIV\<close>
        using summable_on_subset_banach by blast
      then have \<open>(\<lambda>j. (\<phi> (undefined,j))\<^sup>2) abs_summable_on UNIV\<close>
        apply (subst (asm) summable_on_reindex)
        by (auto simp: o_def inj_def)
      then have \<open>(\<lambda>j. (\<phi> (undefined,j) / c)\<^sup>2) abs_summable_on UNIV\<close>
        by (simp add: divide_inverse power_mult_distrib norm_mult summable_on_cmult_left)
      then have \<open>(\<lambda>j. (x j)\<^sup>2) abs_summable_on UNIV\<close>
        by (simp add: x_def)
      then show ?thesis
        using has_ell2_norm_def by blast
    qed
    ultimately show \<open>\<exists>x\<in>Collect has_ell2_norm. (\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (rule_tac bexI[where x=x])
      by auto
  qed

  then show \<open>surj (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    by (metis surj_def)
qed

lemma bij_tensor_op_one_dim_left:
  fixes a :: \<open>'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. a \<otimes>\<^sub>o x)\<close>
proof -
  have [simp]: \<open>bij (Pair (undefined::'a))\<close>
    apply (rule o_bij[of snd]) by auto
  have [simp]: \<open>bij (Pair (undefined::'b))\<close>
    apply (rule o_bij[of snd]) by auto
  define t where \<open>t x = a \<otimes>\<^sub>o x\<close> for x :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  define u :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'c) ell2\<close> where \<open>u = classical_operator (Some o Pair undefined)\<close>
  define v :: \<open>'d ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'d) ell2\<close> where \<open>v = classical_operator (Some o Pair undefined)\<close>
  have [simp]: \<open>unitary u\<close> \<open>unitary v\<close>
    by (simp_all add: u_def v_def)
  have u_ket[simp]: \<open>u *\<^sub>V ket x = ket (undefined, x)\<close> for x
    by (simp add: u_def classical_operator_ket classical_operator_exists_inj inj_def)
  have uadj_ket[simp]: \<open>u* *\<^sub>V ket (z, x) = ket x\<close> for x z
    apply (subst everything_the_same[of _ undefined])
    by (metis (no_types, opaque_lifting) u_ket cinner_adj_right cinner_ket_eqI cinner_ket_same orthogonal_ket prod.inject)
  have v_ket[simp]: \<open>v *\<^sub>V ket x = ket (undefined, x)\<close> for x
    by (simp add: v_def classical_operator_ket classical_operator_exists_inj inj_def)
  then have [simp]: \<open>v *\<^sub>V x = ket undefined \<otimes>\<^sub>s x\<close> for x
    apply (rule_tac fun_cong[where x=x])
    apply (rule bounded_clinear_equal_ket)
    by (auto simp add: bounded_clinear_tensor_ell21 cblinfun.bounded_clinear_right tensor_ell2_ket)
  define a' :: complex where \<open>a' = one_dim_iso a\<close>
  from assms have \<open>a' \<noteq> 0\<close>
    using a'_def one_dim_iso_of_zero' by auto
  have a_a': \<open>a = of_complex a'\<close>
    by (simp add: a'_def) 
  have \<open>t x *\<^sub>V ket (i,j) = (a' *\<^sub>C v o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L u*) *\<^sub>V ket (i,j)\<close> for x i j
    apply (simp add: t_def)
    apply (simp add: ket_CARD_1_is_1 tensor_op_ell2 flip: tensor_ell2_ket)
    by (metis a'_def one_cblinfun_apply_one one_dim_scaleC_1 scaleC_cblinfun.rep_eq tensor_ell2_scaleC1) 
  then have t: \<open>t x = (a' *\<^sub>C v o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L u*)\<close> for x
    apply (rule_tac equal_ket)
    by auto
  define s where \<open>s y = (inverse a' *\<^sub>C (v)* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L u)\<close> for y
  have \<open>s (t x) = (a' * inverse a') *\<^sub>C (((v)* o\<^sub>C\<^sub>L v) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L (u* o\<^sub>C\<^sub>L u))\<close> for x
    apply (simp add: s_def t cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  also have \<open>\<dots> x = x\<close> for x
    using \<open>a' \<noteq> 0\<close> by simp
  finally have \<open>s o t = id\<close>
    by auto
  have \<open>t (s y) = (a' * inverse a') *\<^sub>C ((v o\<^sub>C\<^sub>L (v)*) o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L (u o\<^sub>C\<^sub>L u*))\<close> for y
    apply (simp add: s_def t cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  also have \<open>\<dots> y = y\<close> for y
    using \<open>a' \<noteq> 0\<close> by simp
  finally have \<open>t o s = id\<close>
    by auto
  from \<open>s o t = id\<close> \<open>t o s = id\<close>
  show \<open>bij t\<close>
    using o_bij by blast
qed

lemma bij_tensor_op_one_dim_right:
  assumes \<open>b \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. x \<otimes>\<^sub>o (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2))\<close>
    (is \<open>bij ?f\<close>)
proof -
  let ?sf = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L (?f x) o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?s = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?g = \<open>(\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2) \<otimes>\<^sub>o x)\<close>
  have \<open>?sf = ?g\<close>
    by (auto intro!: ext tensor_ell2_extensionality simp add: swap_ell2_tensor tensor_op_ell2)
  have \<open>bij ?g\<close>
    using assms by (rule bij_tensor_op_one_dim_left)
  have \<open>?s o ?sf = ?f\<close>
    apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  also have \<open>bij ?s\<close>
    apply (rule o_bij[where g=\<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>])
     apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  show \<open>bij ?f\<close>
    apply (subst \<open>?s o ?sf = ?f\<close>[symmetric], subst \<open>?sf = ?g\<close>)
    using \<open>bij ?g\<close> \<open>bij ?s\<close> by (rule bij_comp)
qed

lemma overlapping_tensor:
  fixes a23 :: \<open>('a2*'a3) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b2*'b3) ell2\<close>
    and b12 :: \<open>('a1*'a2) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b1*'b2) ell2\<close>
  assumes eq: \<open>butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = assoc_ell2 o\<^sub>C\<^sub>L (b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>') o\<^sub>C\<^sub>L assoc_ell2*\<close>
  assumes \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close>
  shows \<open>\<exists>c. butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
proof -
  let ?id1 = \<open>id_cblinfun :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2\<close>
  note id_cblinfun_eq_1[simp del]
  define d where \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>

  define \<psi>\<^sub>n \<psi>\<^sub>n' a23\<^sub>n where \<open>\<psi>\<^sub>n = \<psi> /\<^sub>C norm \<psi>\<close> and \<open>\<psi>\<^sub>n' = \<psi>' /\<^sub>C norm \<psi>'\<close> and \<open>a23\<^sub>n = norm \<psi> *\<^sub>C norm \<psi>' *\<^sub>C a23\<close>
  have [simp]: \<open>norm \<psi>\<^sub>n = 1\<close> \<open>norm \<psi>\<^sub>n' = 1\<close>
    using \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> by (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def norm_inverse)
  have n1: \<open>butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o a23\<^sub>n = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>
    apply (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def a23\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(2) assms(3) inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_eq_0_iff right_inverse scaleC_one)

  define \<phi>\<^sub>n \<phi>\<^sub>n' b12\<^sub>n where \<open>\<phi>\<^sub>n = \<phi> /\<^sub>C norm \<phi>\<close> and \<open>\<phi>\<^sub>n' = \<phi>' /\<^sub>C norm \<phi>'\<close> and \<open>b12\<^sub>n = norm \<phi> *\<^sub>C norm \<phi>' *\<^sub>C b12\<close>
  have [simp]: \<open>norm \<phi>\<^sub>n = 1\<close> \<open>norm \<phi>\<^sub>n' = 1\<close>
    using \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close> by (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def norm_inverse)
  have n2: \<open>b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n' = b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    apply (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def b12\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(4) assms(5) field_class.field_inverse inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_hom.hom_0 scaleC_one)

  define c' :: \<open>(unit*'a2*unit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (unit*'b2*unit) ell2\<close> 
    where \<open>c' = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)* o\<^sub>C\<^sub>L d
            o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')\<close>

  define c'' :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c'' = inv (\<lambda>c''. id_cblinfun \<otimes>\<^sub>o c'' \<otimes>\<^sub>o id_cblinfun) c'\<close>

  have *: \<open>bij (\<lambda>c''::'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2. ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1)\<close>
    apply (subst asm_rl[of \<open>_ = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) o (\<lambda>c''. c'' \<otimes>\<^sub>o id_cblinfun)\<close>])
    using [[show_consts]]
    by (auto intro!: bij_comp bij_tensor_op_one_dim_left bij_tensor_op_one_dim_right)

  have c'_c'': \<open>c' = ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1\<close>
    unfolding c''_def 
    apply (rule surj_f_inv_f[where y=c', symmetric])
    using * by (rule bij_is_surj)

  define c :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c = c'' /\<^sub>C norm \<psi> /\<^sub>C norm \<psi>' /\<^sub>C norm \<phi> /\<^sub>C norm \<phi>'\<close>

  have aux: \<open>assoc_ell2* o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L assoc_ell2*) o\<^sub>C\<^sub>L assoc_ell2 = x\<close> for x
    apply (simp add: cblinfun_assoc_left)
    by (simp add: cblinfun_assoc_right)
  have aux2: \<open>(assoc_ell2 o\<^sub>C\<^sub>L ((x \<otimes>\<^sub>o y) \<otimes>\<^sub>o z) o\<^sub>C\<^sub>L assoc_ell2*) = x \<otimes>\<^sub>o (y \<otimes>\<^sub>o z)\<close> for x y z
    apply (rule equal_ket, rename_tac xyz)
    apply (case_tac xyz, hypsubst_thin)
    by (simp flip: tensor_ell2_ket add: assoc_ell2'_tensor assoc_ell2_tensor tensor_op_ell2)

  have \<open>d = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n1[symmetric] comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n')
                  o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def eq n2 cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n') o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (assoc_ell2* o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L assoc_ell2) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n2 eq aux)
  also have \<open>\<dots> = ((butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L assoc_ell2*))
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L ((assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n') o\<^sub>C\<^sub>L assoc_ell2*) o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: sandwich_def cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n')\<close>
    apply (simp only: tensor_id[symmetric] comp_tensor_op aux2)
    by (simp add: cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L c' o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')*\<close>
    apply (simp add: c'_def butterfly_def_one_dim[where 'c="unit ell2"] cblinfun_assoc_left comp_tensor_op
                      tensor_op_adjoint cnorm_eq_1[THEN iffD1])
    by (simp add: cblinfun_assoc_right comp_tensor_op)
  also have \<open>\<dots> = butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o c'' \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n'\<close>
    by (simp add: c'_c'' comp_tensor_op tensor_op_adjoint butterfly_def_one_dim[symmetric])
  also have \<open>\<dots> = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by (simp add: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def \<phi>\<^sub>n_def \<phi>\<^sub>n'_def c_def tensor_op_scaleC_left tensor_op_scaleC_right)
  finally have d_c: \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by -
  then show ?thesis
    by (auto simp: d_def)
qed


(* TODO cite [register paper], Lemma 17 *)
lemma tensor_op_pos: \<open>a \<otimes>\<^sub>o b \<ge> 0\<close> if [simp]: \<open>a \<ge> 0\<close> \<open>b \<ge> 0\<close>
  for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
proof -
  have \<open>(sqrt_op a \<otimes>\<^sub>o sqrt_op b)* o\<^sub>C\<^sub>L (sqrt_op a \<otimes>\<^sub>o sqrt_op b) = a \<otimes>\<^sub>o b\<close>
    by (simp add: tensor_op_adjoint comp_tensor_op flip: positive_hermitianI)
  then show \<open>a \<otimes>\<^sub>o b \<ge> 0\<close>
    by (metis positive_cblinfun_squareI)
qed

(* TODO cite [register paper], Lemma 17 *)
lemma abs_op_tensor: \<open>abs_op (a \<otimes>\<^sub>o b) = abs_op a \<otimes>\<^sub>o abs_op b\<close>
proof -
  have \<open>(abs_op a \<otimes>\<^sub>o abs_op b)* o\<^sub>C\<^sub>L (abs_op a \<otimes>\<^sub>o abs_op b) = (a \<otimes>\<^sub>o b)* o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b)\<close>
    by (simp add: tensor_op_adjoint comp_tensor_op abs_op_def positive_cblinfun_squareI flip: positive_hermitianI)
  then show ?thesis
    by (metis abs_opI abs_op_pos tensor_op_pos)
qed

(* TODO cite [register paper], Lemma 31 *)
lemma trace_class_tensor: \<open>trace_class (a \<otimes>\<^sub>o b)\<close> if \<open>trace_class a\<close> and \<open>trace_class b\<close>
proof -
  from \<open>trace_class a\<close>
  have a: \<open>(\<lambda>x. ket x \<bullet>\<^sub>C (abs_op a *\<^sub>V ket x)) abs_summable_on UNIV\<close>
    by (auto simp add: trace_class_iff_summable[OF is_onb_ket] summable_on_reindex o_def)
  from \<open>trace_class b\<close>
  have b: \<open>(\<lambda>y. ket y \<bullet>\<^sub>C (abs_op b *\<^sub>V ket y)) abs_summable_on UNIV\<close>
    by (auto simp add: trace_class_iff_summable[OF is_onb_ket] summable_on_reindex o_def)
  from a b have \<open>(\<lambda>(x,y). (ket x \<bullet>\<^sub>C (abs_op a *\<^sub>V ket x)) * (ket y \<bullet>\<^sub>C (abs_op b *\<^sub>V ket y))) abs_summable_on UNIV \<times> UNIV\<close>
    by (rule abs_summable_times)
  then have \<open>(\<lambda>(x,y). (ket x \<otimes>\<^sub>s ket y) \<bullet>\<^sub>C ((abs_op a \<otimes>\<^sub>o abs_op b) *\<^sub>V (ket x \<otimes>\<^sub>s ket y))) abs_summable_on UNIV \<times> UNIV\<close>
    by (simp add: tensor_op_ell2 case_prod_unfold flip: tensor_ell2_ket)
  then have \<open>(\<lambda>xy. ket xy \<bullet>\<^sub>C ((abs_op a \<otimes>\<^sub>o abs_op b) *\<^sub>V ket xy)) abs_summable_on UNIV\<close>
    by (simp add: case_prod_beta tensor_ell2_ket)
  then have \<open>(\<lambda>xy. ket xy \<bullet>\<^sub>C (abs_op (a \<otimes>\<^sub>o b) *\<^sub>V ket xy)) abs_summable_on UNIV\<close>
    by (simp add: abs_op_tensor)
  then show \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
    by (auto simp add: trace_class_iff_summable[OF is_onb_ket] summable_on_reindex o_def)
qed

lemma swap_tensor_op[simp]: \<open>swap_ell2 o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L swap_ell2 = b \<otimes>\<^sub>o a\<close>
  by (auto intro!: equal_ket simp add: tensor_op_ell2 simp flip: tensor_ell2_ket)

lemma swap_tensor_op_sandwich[simp]: \<open>sandwich swap_ell2 (a \<otimes>\<^sub>o b) = b \<otimes>\<^sub>o a\<close>
  by (simp add: sandwich_apply swap_tensor_op)

lemma swap_ell2_commute_tensor_op: 
  \<open>swap_ell2 o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) = (b \<otimes>\<^sub>o a) o\<^sub>C\<^sub>L swap_ell2\<close>
  by (auto intro!: tensor_ell2_extensionality simp: tensor_op_ell2)

lemma trace_class_tensor_op_swap: \<open>trace_class (a \<otimes>\<^sub>o b) \<longleftrightarrow> trace_class (b \<otimes>\<^sub>o a)\<close>
proof (rule iffI)
  assume \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
  then have \<open>trace_class (swap_ell2 o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L swap_ell2)\<close>
    using trace_class_comp_left trace_class_comp_right by blast
  then show \<open>trace_class (b \<otimes>\<^sub>o a)\<close>
    by simp
next
  assume \<open>trace_class (b \<otimes>\<^sub>o a)\<close>
  then have \<open>trace_class (swap_ell2 o\<^sub>C\<^sub>L (b \<otimes>\<^sub>o a) o\<^sub>C\<^sub>L swap_ell2)\<close>
    using trace_class_comp_left trace_class_comp_right by blast
  then show \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
    by simp
qed


lemma trace_class_tensor_iff: \<open>trace_class (a \<otimes>\<^sub>o b) \<longleftrightarrow> (trace_class a \<and> trace_class b) \<or> a = 0 \<or> b = 0\<close>
proof (intro iffI)
  show \<open>trace_class a \<and> trace_class b \<or> a = 0 \<or> b = 0 \<Longrightarrow> trace_class (a \<otimes>\<^sub>o b)\<close>
    by (auto simp add: trace_class_tensor)
  show \<open>trace_class a \<and> trace_class b \<or> a = 0 \<or> b = 0\<close> if \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
  proof (cases \<open>a = 0 \<or> b = 0\<close>)
    case True
    then show ?thesis
      by simp
  next
    case False
    then have \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
      by auto
    have *: \<open>trace_class a\<close> if \<open>trace_class (a \<otimes>\<^sub>o b)\<close> and \<open>b \<noteq> 0\<close> for a :: \<open>'e ell2 \<Rightarrow>\<^sub>C\<^sub>L 'g ell2\<close> and b :: \<open>'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'h ell2\<close>
    proof -
      from \<open>b \<noteq> 0\<close> have \<open>abs_op b \<noteq> 0\<close>
        using abs_op_nondegenerate by blast
      then obtain \<psi>0 where \<psi>0: \<open>\<psi>0 \<bullet>\<^sub>C (abs_op b *\<^sub>V \<psi>0) \<noteq> 0\<close>
        by (metis cblinfun.zero_left cblinfun_cinner_eqI cinner_zero_right)
      define \<psi> where \<open>\<psi> = sgn \<psi>0\<close>
      with \<psi>0 have \<open>\<psi> \<bullet>\<^sub>C (abs_op b *\<^sub>V \<psi>) \<noteq> 0\<close> and \<open>norm \<psi> = 1\<close>
         apply (auto simp add: \<psi>_def norm_sgn)
        by (simp add: sgn_div_norm cblinfun.scaleR_right)
      then have \<open>\<exists>B. {\<psi>} \<subseteq> B \<and> is_onb B\<close>
        apply (rule_tac orthonormal_basis_exists)
        by auto
      then obtain B where [simp]: \<open>is_onb B\<close> and \<open>\<psi> \<in> B\<close>
        by auto
      define A :: \<open>'e ell2 set\<close> where \<open>A = range ket\<close>      
      then have [simp]: \<open>is_onb A\<close> by simp
      with \<open>is_onb B\<close> have \<open>is_onb {\<alpha> \<otimes>\<^sub>s \<beta> |\<alpha> \<beta>. \<alpha> \<in> A \<and> \<beta> \<in> B}\<close>
        by (simp add: tensor_ell2_is_onb)
      with \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
      have \<open>(\<lambda>\<gamma>. \<gamma> \<bullet>\<^sub>C (abs_op (a \<otimes>\<^sub>o b) *\<^sub>V \<gamma>)) abs_summable_on {\<alpha> \<otimes>\<^sub>s \<beta> |\<alpha> \<beta>. \<alpha> \<in> A \<and> \<beta> \<in> B}\<close>
        using trace_class_iff_summable by auto
      then have \<open>(\<lambda>\<gamma>. \<gamma> \<bullet>\<^sub>C (abs_op (a \<otimes>\<^sub>o b) *\<^sub>V \<gamma>)) abs_summable_on (\<lambda>\<alpha>. \<alpha> \<otimes>\<^sub>s \<psi>) ` A\<close>
        apply (rule summable_on_subset_banach)
        using \<open>\<psi> \<in> B\<close> by blast
      then have \<open>(\<lambda>\<alpha>. (\<alpha> \<otimes>\<^sub>s \<psi>) \<bullet>\<^sub>C (abs_op (a \<otimes>\<^sub>o b) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<psi>))) abs_summable_on A\<close>
        apply (subst (asm) summable_on_reindex)
         apply (metis UNIV_I \<open>norm \<psi> = 1\<close> inj_on_subset inj_tensor_ell2_left norm_le_zero_iff not_one_le_zero subset_iff)
        by (simp add: o_def)
      then have \<open>(\<lambda>\<alpha>. norm (\<alpha> \<bullet>\<^sub>C (abs_op a *\<^sub>V \<alpha>)) * norm (\<psi> \<bullet>\<^sub>C (abs_op b *\<^sub>V \<psi>))) summable_on A\<close>
        by (simp add: abs_op_tensor tensor_op_ell2 norm_mult)
      then have \<open>(\<lambda>\<alpha>. \<alpha> \<bullet>\<^sub>C (abs_op a *\<^sub>V \<alpha>)) abs_summable_on A\<close>
        apply (rule summable_on_cmult_left'[THEN iffD1, rotated])
        using \<open>\<psi> \<bullet>\<^sub>C (abs_op b *\<^sub>V \<psi>) \<noteq> 0\<close> norm_eq_zero by blast
      then show \<open>trace_class a\<close>
        using \<open>is_onb A\<close> trace_classI by blast
    qed
    from *[of a b] \<open>b \<noteq> 0\<close> \<open>trace_class (a \<otimes>\<^sub>o b)\<close> have \<open>trace_class a\<close>
      by simp
    have \<open>trace_class (b \<otimes>\<^sub>o a)\<close>
      using that trace_class_tensor_op_swap by blast
    from *[of b a] \<open>a \<noteq> 0\<close> \<open>trace_class (b \<otimes>\<^sub>o a)\<close> have \<open>trace_class b\<close>
      by simp
    from \<open>trace_class a\<close> \<open>trace_class b\<close> show ?thesis
      by simp
  qed
qed


(* TODO cite [register paper], Lemma 31 *)
lemma trace_tensor: \<open>trace (a \<otimes>\<^sub>o b) = trace a * trace b\<close>
(* TODO nice candidate for wlog demo *)
proof -
  consider (tc) \<open>trace_class a\<close> \<open>trace_class b\<close> | (zero) \<open>a = 0 \<or> b = 0\<close> | (nota) \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>\<not> trace_class a\<close> | (notb) \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>\<not> trace_class b\<close>
    by blast
  then show ?thesis
  proof cases
    case tc
    then have *: \<open>trace_class (a \<otimes>\<^sub>o b)\<close>
      by (simp add: trace_class_tensor)
    have sum: \<open>(\<lambda>(x, y). ket (x, y) \<bullet>\<^sub>C ((a \<otimes>\<^sub>o b) *\<^sub>V ket (x, y))) summable_on UNIV\<close>
      using trace_exists[OF is_onb_ket *]
      by (simp_all add: o_def case_prod_unfold summable_on_reindex)

    have \<open>trace a * trace b = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. ket x \<bullet>\<^sub>C (a *\<^sub>V ket x) * (ket y \<bullet>\<^sub>C (b *\<^sub>V ket y)))\<close>
      apply (simp add: trace_ket_sum tc flip: infsum_cmult_left')
      by (simp flip: infsum_cmult_right')
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. ket (x,y) \<bullet>\<^sub>C ((a \<otimes>\<^sub>o b) *\<^sub>V ket (x,y)))\<close>
      by (simp add: tensor_op_ell2 flip: tensor_ell2_ket)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>xy\<in>UNIV. ket xy \<bullet>\<^sub>C ((a \<otimes>\<^sub>o b) *\<^sub>V ket xy))\<close>
      apply (simp add: sum infsum_Sigma'_banach)
      by (simp add: case_prod_unfold)
    also have \<open>\<dots> = trace (a \<otimes>\<^sub>o b)\<close>
      by (simp add: "*" trace_ket_sum)
    finally show ?thesis 
      by simp
  next
    case zero
    then show ?thesis by auto
  next
    case nota
    then have [simp]: \<open>trace a = 0\<close>
      unfolding trace_def by simp
    from nota have \<open>\<not> trace_class (a \<otimes>\<^sub>o b)\<close>
      by (simp add: trace_class_tensor_iff)
    then have [simp]: \<open>trace (a \<otimes>\<^sub>o b) = 0\<close>
      unfolding trace_def by simp
    show ?thesis 
      by simp
  next
    case notb
    then have [simp]: \<open>trace b = 0\<close>
      unfolding trace_def by simp
    from notb have \<open>\<not> trace_class (a \<otimes>\<^sub>o b)\<close>
      by (simp add: trace_class_tensor_iff)
    then have [simp]: \<open>trace (a \<otimes>\<^sub>o b) = 0\<close>
      unfolding trace_def by simp
    show ?thesis 
      by simp
  qed
qed

lemma isometry_tensor_op: \<open>isometry (U \<otimes>\<^sub>o V)\<close> if \<open>isometry U\<close> and \<open>isometry V\<close>
  unfolding isometry_def using that by (simp add: tensor_op_adjoint comp_tensor_op)

lemma is_Proj_tensor_op: \<open>is_Proj a \<Longrightarrow> is_Proj b \<Longrightarrow> is_Proj (a \<otimes>\<^sub>o b)\<close>
  by (simp add: comp_tensor_op is_Proj_algebraic tensor_op_adjoint)

lemma isometry_tensor_id_right[simp]:
  fixes U :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  shows \<open>isometry (U \<otimes>\<^sub>o (id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) \<longleftrightarrow> isometry U\<close>
proof (rule iffI)
  assume \<open>isometry U\<close>
  then show \<open>isometry (U \<otimes>\<^sub>o id_cblinfun)\<close>
    unfolding isometry_def
    by (auto simp add: tensor_op_adjoint comp_tensor_op)
next
  let ?id = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  assume asm: \<open>isometry (U \<otimes>\<^sub>o ?id)\<close>
  then have \<open>(U* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o ?id = id_cblinfun \<otimes>\<^sub>o ?id\<close>
    by (simp add: isometry_def tensor_op_adjoint comp_tensor_op)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    apply (rule inj_tensor_left[of ?id, unfolded inj_def, rule_format, rotated])
    by simp
  then show \<open>isometry U\<close>
    by (simp add: isometry_def)
qed

lemma isometry_tensor_id_left[simp]: 
  fixes U :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  shows \<open>isometry ((id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _) \<otimes>\<^sub>o U) \<longleftrightarrow> isometry U\<close>
proof (rule iffI)
  assume \<open>isometry U\<close>
  then show \<open>isometry (id_cblinfun \<otimes>\<^sub>o U)\<close>
    unfolding isometry_def
    by (auto simp add: tensor_op_adjoint comp_tensor_op)
next
  let ?id = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  assume asm: \<open>isometry (?id \<otimes>\<^sub>o U)\<close>
  then have \<open>?id \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L U) = ?id \<otimes>\<^sub>o id_cblinfun\<close>
    by (simp add: isometry_def tensor_op_adjoint comp_tensor_op)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    apply (rule inj_tensor_right[of ?id, unfolded inj_def, rule_format, rotated])
    by simp
  then show \<open>isometry U\<close>
    by (simp add: isometry_def)
qed

lemma unitary_tensor_id_right[simp]: \<open>unitary (U \<otimes>\<^sub>o id_cblinfun) \<longleftrightarrow> unitary U\<close>
  unfolding unitary_twosided_isometry
  by (simp add: tensor_op_adjoint)

lemma unitary_tensor_id_left[simp]: \<open>unitary (id_cblinfun \<otimes>\<^sub>o U) \<longleftrightarrow> unitary U\<close>
  unfolding unitary_twosided_isometry
  by (simp add: tensor_op_adjoint)


subsection \<open>Tensor product of subspaces\<close>

definition tensor_ccsubspace (infixr "\<otimes>\<^sub>S" 70) where
  \<open>tensor_ccsubspace A B = ccspan {\<psi> \<otimes>\<^sub>s \<phi> | \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}\<close>

lemma tensor_ccsubspace_via_Proj: \<open>A \<otimes>\<^sub>S B = (Proj A \<otimes>\<^sub>o Proj B) *\<^sub>S \<top>\<close>
proof (rule antisym)
  have \<open>\<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set ((Proj A \<otimes>\<^sub>o Proj B) *\<^sub>S \<top>)\<close> if \<open>\<psi> \<in> space_as_set A\<close> and \<open>\<phi> \<in> space_as_set B\<close> for \<psi> \<phi>
    by (metis Proj_fixes_image cblinfun_apply_in_image tensor_op_ell2 that(1) that(2))
  then show \<open>A \<otimes>\<^sub>S B \<le> (Proj A \<otimes>\<^sub>o Proj B) *\<^sub>S \<top>\<close>
    by (auto intro!: ccspan_leqI simp: tensor_ccsubspace_def)
  have *: \<open>ccspan {\<psi> \<otimes>\<^sub>s \<phi> | (\<psi>::'a ell2) (\<phi>::'b ell2). True} = \<top>\<close>
    using tensor_ell2_dense'[where A=\<open>UNIV :: 'a ell2 set\<close> and B=\<open>UNIV :: 'b ell2 set\<close>]
    by auto
  have \<open>(Proj A \<otimes>\<^sub>o Proj B) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set (A \<otimes>\<^sub>S B)\<close> for \<psi> \<phi>
    apply (simp add: tensor_op_ell2 tensor_ccsubspace_def)
     by (smt (verit) Proj_range cblinfun_apply_in_image ccspan_superset mem_Collect_eq subsetD)
  then show \<open>(Proj A \<otimes>\<^sub>o Proj B) *\<^sub>S \<top> \<le> A \<otimes>\<^sub>S B\<close>
    by (auto intro!: ccspan_leqI simp: cblinfun_image_ccspan simp flip: *)
qed

lemma tensor_ccsubspace_top[simp]: \<open>\<top> \<otimes>\<^sub>S \<top> = \<top>\<close>
  by (simp add: tensor_ccsubspace_via_Proj)

lemma tensor_ccsubspace_0_left[simp]: \<open>0 \<otimes>\<^sub>S X = 0\<close>
  by (simp add: tensor_ccsubspace_via_Proj)

lemma tensor_ccsubspace_0_right[simp]: \<open>X \<otimes>\<^sub>S 0 = 0\<close>
  by (simp add: tensor_ccsubspace_via_Proj)


lemma tensor_ccsubspace_image: \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
proof -
  have \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set (A *\<^sub>S T) \<times> space_as_set (B *\<^sub>S U)))\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect ccspan.rep_eq)
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` closure ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by (simp add: cblinfun_image.rep_eq closure_Times)
  also have \<open>\<dots> = ccspan (closure ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U))))\<close>
    apply (subst closure_image_closure[symmetric])
    using continuous_on_subset continuous_tensor_ell2 by auto
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by simp
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set T \<times> space_as_set U))\<close>
    by (simp add: cblinfun_image_ccspan image_image tensor_op_ell2 case_prod_beta
        flip: map_prod_image)
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect)
  finally show ?thesis
    by -
qed

lemma tensor_ccsubspace_bot_left[simp]: \<open>\<bottom> \<otimes>\<^sub>S S = \<bottom>\<close>
  by (simp add: tensor_ccsubspace_via_Proj)
lemma tensor_ccsubspace_bot_right[simp]: \<open>S \<otimes>\<^sub>S \<bottom> = \<bottom>\<close>
  by (simp add: tensor_ccsubspace_via_Proj)

lemma swap_ell2_tensor_ccsubspace: \<open>swap_ell2 *\<^sub>S (S \<otimes>\<^sub>S T) = T \<otimes>\<^sub>S S\<close>
  apply (auto intro!: arg_cong[where f=ccspan] 
      simp add: tensor_ccsubspace_def cblinfun_image_ccspan image_image set_compr_2_image_collect)
  by force

lemma tensor_ccsubspace_right1dim_member:
  assumes \<open>\<psi> \<in> space_as_set (S \<otimes>\<^sub>S ccspan{\<phi>})\<close>
  shows \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
proof (cases \<open>\<phi> = 0\<close>)
  case True
  with assms show ?thesis 
    by simp
next
  case False
  have \<open>{\<psi> \<otimes>\<^sub>s \<phi>' |\<psi> \<phi>'. \<psi> \<in> space_as_set S \<and> \<phi>' \<in> space_as_set (ccspan {\<phi>})}
    = {\<psi> \<otimes>\<^sub>s \<phi> | \<psi>. \<psi> \<in> space_as_set S}\<close>
  proof -
    have \<open>\<psi> \<in> space_as_set S \<Longrightarrow> \<exists>\<psi>'. \<psi> \<otimes>\<^sub>s c *\<^sub>C \<phi> = \<psi>' \<otimes>\<^sub>s \<phi> \<and> \<psi>' \<in> space_as_set S\<close> for c \<psi>
      apply (rule exI[where x=\<open>c *\<^sub>C \<psi>\<close>])
      by (auto simp: tensor_ell2_scaleC2 tensor_ell2_scaleC1
          complex_vector.subspace_scale)
    moreover have \<open>\<psi> \<in> space_as_set S \<Longrightarrow>
         \<exists>\<psi>' \<phi>'. \<psi> \<otimes>\<^sub>s \<phi> = \<psi>' \<otimes>\<^sub>s \<phi>' \<and> \<psi>' \<in> space_as_set S \<and> \<phi>' \<in> range (\<lambda>k. k *\<^sub>C \<phi>)\<close> for \<psi>
      apply (rule exI[where x=\<psi>], rule exI[where x=\<phi>])
      by (auto intro!: range_eqI[where x=\<open>1::complex\<close>])
    ultimately show ?thesis
      by (auto simp: ccspan_finite complex_vector.span_singleton)
  qed
  moreover have \<open>csubspace {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
  proof (rule complex_vector.subspaceI)
    show \<open>0 \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
      by (auto intro!: exI[where x=0])
    show \<open>x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow>
           y \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow> x + y \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> for x y
      apply (auto simp flip: tensor_ell2_add1)
      apply (rename_tac \<psi> \<psi>', rule_tac x=\<open>\<psi> + \<psi>'\<close> in exI)
      by (auto simp: complex_vector.subspace_add)
    show \<open>x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow> c *\<^sub>C x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> for c x
      apply (auto simp flip: tensor_ell2_scaleC1)
      apply (rename_tac \<psi>, rule_tac x=\<open>c *\<^sub>C \<psi>\<close> in exI)
      by (auto simp: complex_vector.subspace_scale tensor_ell2_scaleC2 tensor_ell2_scaleC1)
  qed
  moreover have \<open>closed {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
  proof (rule closed_sequential_limits[THEN iffD2, rule_format])
    fix x l
    assume asm: \<open>(\<forall>n. x n \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}) \<and> x \<longlonglongrightarrow> l\<close>
    then obtain \<psi>' where x_def: \<open>x n = \<psi>' n \<otimes>\<^sub>s \<phi>\<close> and \<psi>'_S: \<open>\<psi>' n \<in> space_as_set S\<close> for n
      apply atomize_elim apply auto by metis
    from asm have \<open>x \<longlonglongrightarrow> l\<close>
      by simp
    have \<open>Cauchy \<psi>'\<close>
    proof (rule CauchyI)
      fix e :: real assume \<open>e > 0\<close>
      define d where \<open>d = e * norm \<phi>\<close>
      with False \<open>e > 0\<close> have \<open>d > 0\<close>
        by auto
      from \<open>x \<longlonglongrightarrow> l\<close>
      have \<open>Cauchy x\<close>
        using LIMSEQ_imp_Cauchy by blast
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. norm (x m - x n) < d\<close>
        using Cauchy_iff \<open>0 < d\<close> by blast
      then show \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (\<psi>' m - \<psi>' n) < e\<close>
        apply (rule_tac exI[of _ M])
        using False by (auto simp add: x_def norm_tensor_ell2 d_def simp flip: tensor_ell2_diff1)
    qed
    then obtain l' where \<open>\<psi>' \<longlonglongrightarrow> l'\<close>
      using convergent_eq_Cauchy by blast
    with \<psi>'_S have l'_S: \<open>l' \<in> space_as_set S\<close>
      by (metis \<open>Cauchy \<psi>'\<close> completeE complete_space_as_set limI)
    from \<open>\<psi>' \<longlonglongrightarrow> l'\<close> have \<open>x \<longlonglongrightarrow> l' \<otimes>\<^sub>s \<phi>\<close>
      by (auto intro: tendsto_eq_intros simp: x_def[abs_def])
    with \<open>x \<longlonglongrightarrow> l\<close> have \<open>l = l' \<otimes>\<^sub>s \<phi>\<close>
      using LIMSEQ_unique by blast
    then show \<open>l \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
      using l'_S by auto
  qed
  ultimately have \<open>space_as_set (ccspan {\<psi> \<otimes>\<^sub>s \<phi>' |\<psi> \<phi>'. \<psi> \<in> space_as_set S \<and> \<phi>' \<in> space_as_set (ccspan {\<phi>})})
      = {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> 
    by (simp add: ccspan.rep_eq complex_vector.span_eq_iff[THEN iffD2])
  with assms have \<open>\<psi> \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
    by (simp add: tensor_ccsubspace_def)
  then show \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    by auto
qed

lemma tensor_ccsubspace_left1dim_member:
  assumes \<open>\<psi> \<in> space_as_set (ccspan{\<phi>} \<otimes>\<^sub>S S)\<close>
  shows \<open>\<exists>\<psi>'. \<psi> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
proof -
  from assms 
  have \<open>swap_ell2 *\<^sub>V \<psi> \<in> space_as_set (swap_ell2 *\<^sub>S (ccspan {\<phi>} \<otimes>\<^sub>S S))\<close>
  by (metis rev_image_eqI space_as_set_image_commute swap_ell2_selfinv)
  then have \<open>swap_ell2 \<psi> \<in> space_as_set (S \<otimes>\<^sub>S ccspan{\<phi>})\<close>
    by (simp add: swap_ell2_tensor_ccsubspace)
  then obtain \<psi>' where \<psi>': \<open>swap_ell2 \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    using tensor_ccsubspace_right1dim_member by blast
  have \<open>\<psi> = swap_ell2 *\<^sub>V swap_ell2 *\<^sub>V \<psi>\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> = swap_ell2 *\<^sub>V (\<psi>' \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: \<psi>')
  also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
    by simp
  finally show ?thesis
    by auto
qed

lemma tensor_ell2_mem_tensor_ccsubspace_left:
  assumes \<open>a \<otimes>\<^sub>s b \<in> space_as_set (S \<otimes>\<^sub>S T)\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<in> space_as_set S\<close>
proof (cases \<open>a = 0\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  have \<open>norm (Proj S a) * norm (Proj T b) = norm ((Proj S a) \<otimes>\<^sub>s (Proj T b))\<close>
    by (simp add: norm_tensor_ell2)
  also have \<open>\<dots> = norm (Proj (S \<otimes>\<^sub>S T) (a \<otimes>\<^sub>s b))\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range is_Proj_tensor_op
        tensor_op_ell2)
  also from assms have \<open>\<dots> = norm (a \<otimes>\<^sub>s b)\<close>
    by (simp add: Proj_fixes_image)
  also have \<open>\<dots> = norm a * norm b\<close>
    by (simp add: norm_tensor_ell2)
  finally have prod_eq: \<open>norm (Proj S *\<^sub>V a) * norm (Proj T *\<^sub>V b) = norm a * norm b\<close>
    by -
  with False \<open>b \<noteq> 0\<close> have Tb_non0: \<open>norm (Proj T *\<^sub>V b) \<noteq> 0\<close>
    by fastforce
  have \<open>norm (Proj S a) = norm a\<close>
  proof (rule ccontr)
    assume asm: \<open>norm (Proj S *\<^sub>V a) \<noteq> norm a\<close>
    have Sa_leq: \<open>norm (Proj S *\<^sub>V a) \<le> norm a\<close>
      by (simp add: is_Proj_reduces_norm)
    have Tb_leq: \<open>norm (Proj T *\<^sub>V b) \<le> norm b\<close>
      by (simp add: is_Proj_reduces_norm)
    from asm Sa_leq have \<open>norm (Proj S *\<^sub>V a) < norm a\<close>
      by simp
    then have \<open>norm (Proj S *\<^sub>V a) * norm (Proj T *\<^sub>V b) < norm a * norm (Proj T *\<^sub>V b)\<close>
      using Tb_non0 by auto
    also from Tb_leq have \<open>\<dots> \<le> norm a * norm b\<close>
      using False by force
    also note prod_eq
    finally show False
      by simp
  qed
  then show \<open>a \<in> space_as_set S\<close>
    using norm_Proj_apply by blast
qed

lemma tensor_ell2_mem_tensor_ccsubspace_right:
  assumes \<open>a \<otimes>\<^sub>s b \<in> space_as_set (S \<otimes>\<^sub>S T)\<close> and \<open>a \<noteq> 0\<close>
  shows \<open>b \<in> space_as_set T\<close>
proof -
  have \<open>swap_ell2 *\<^sub>V (a \<otimes>\<^sub>s b) \<in> space_as_set (swap_ell2 *\<^sub>S (S \<otimes>\<^sub>S T))\<close>
    using assms(1) cblinfun_apply_in_image' by blast
  then have \<open>b \<otimes>\<^sub>s a \<in> space_as_set (T \<otimes>\<^sub>S S)\<close>
    by (simp add: swap_ell2_tensor_ccsubspace)
  then show \<open>b \<in> space_as_set T\<close>
    using \<open>a \<noteq> 0\<close> by (rule tensor_ell2_mem_tensor_ccsubspace_left)
qed

lemma tensor_ell2_in_tensor_ccsubspace: \<open>a \<otimes>\<^sub>s b \<in> space_as_set (A \<otimes>\<^sub>S B)\<close> if \<open>a \<in> space_as_set A\<close> and \<open>b \<in> space_as_set B\<close>
  \<comment> \<open>Converse is @{thm [source] tensor_ell2_mem_tensor_ccsubspace_left} and \<open>\<dots>_right\<close>.\<close>
  using that by (auto intro!: ccspan_superset[THEN subsetD] simp add: tensor_ccsubspace_def)

lemma tensor_ccsubspace_INF_left_top:
  fixes S :: \<open>'a \<Rightarrow> 'b ell2 ccsubspace\<close>
  shows \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S (\<top>::'c ell2 ccsubspace) = (INF x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
proof (rule antisym[rotated])
  let ?top = \<open>\<top> :: 'c ell2 ccsubspace\<close>
  have \<open>\<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    if \<open>\<psi> \<in> space_as_set (\<Sqinter>x\<in>X. S x)\<close> for \<psi> \<phi>
  proof -
    from that(1) have \<open>\<psi> \<in> space_as_set (S x)\<close> if \<open>x \<in> X\<close> for x
      using that by (simp add: Inf_ccsubspace.rep_eq)
    then have \<open>\<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set (S x \<otimes>\<^sub>S \<top>)\<close> if \<open>x \<in> X\<close> for x
      using ccspan_superset that apply (auto simp: tensor_ccsubspace_def)
      by fastforce
    then show ?thesis
      by (simp add: Inf_ccsubspace.rep_eq)
  qed
  then show \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S ?top \<le> (INF x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    apply (subst tensor_ccsubspace_def)
    apply (rule ccspan_leqI)
    by auto

  show \<open>(\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top) \<le> (\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top\<close>
  proof (rule ccsubspace_leI_unit)
    fix \<psi>
    assume asm: \<open>\<psi> \<in> space_as_set (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    obtain \<psi>' where \<psi>'b_b: \<open>\<psi>' b \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close> for b
    proof (atomize_elim, rule choice, intro allI)
      fix b :: 'c
      have \<open>(id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi> \<in> space_as_set (\<top> \<otimes>\<^sub>S ccspan {ket b})\<close>
        by (simp add: butterfly_eq_proj tensor_ccsubspace_via_Proj)
      then show \<open>\<exists>\<psi>'. \<psi>' \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close>
       by (metis tensor_ccsubspace_right1dim_member)
    qed
  
    have \<open>\<psi>' b \<in> space_as_set (S x)\<close> if \<open>x \<in> X\<close> for x b
    proof -
      from asm have \<psi>_ST: \<open>\<psi> \<in> space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by (meson INF_lower Set.basic_monos(7) less_eq_ccsubspace.rep_eq that)
      have \<open>\<psi>' b \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close>
        by (simp add: \<psi>'b_b)
      also from \<psi>_ST
      have \<open>\<dots> \<in> space_as_set (((id_cblinfun \<otimes>\<^sub>o selfbutterket b)) *\<^sub>S (S x \<otimes>\<^sub>S ?top))\<close>
        by (meson cblinfun_apply_in_image')
      also have \<open>\<dots> = space_as_set (((id_cblinfun \<otimes>\<^sub>o selfbutterket b) o\<^sub>C\<^sub>L (Proj (S x) \<otimes>\<^sub>o id_cblinfun)) *\<^sub>S \<top>)\<close>
        by (simp add: cblinfun_compose_image tensor_ccsubspace_via_Proj)
      also have \<open>\<dots> = space_as_set ((Proj (S x) \<otimes>\<^sub>o (selfbutterket b o\<^sub>C\<^sub>L id_cblinfun)) *\<^sub>S \<top>)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> = space_as_set ((Proj (S x) \<otimes>\<^sub>o (id_cblinfun o\<^sub>C\<^sub>L selfbutterket b)) *\<^sub>S \<top>)\<close>
        by simp
      also have \<open>\<dots> = space_as_set (((Proj (S x) \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket b)) *\<^sub>S \<top>)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> \<subseteq> space_as_set ((Proj (S x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>)\<close>
        by (metis cblinfun_compose_image cblinfun_image_mono less_eq_ccsubspace.rep_eq top_greatest)
      also have \<open>\<dots> = space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by (simp add: tensor_ccsubspace_via_Proj)
      finally have \<open>\<psi>' b \<otimes>\<^sub>s ket b \<in> space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by -
      then show \<open>\<psi>' b \<in> space_as_set (S x)\<close>
        using tensor_ell2_mem_tensor_ccsubspace_left
        by (metis ket_nonzero)
    qed

    then have \<open>\<psi>' b \<in> space_as_set (\<Sqinter>x\<in>X. S x)\<close> if \<open>x \<in> X\<close> for x b
      using that by (simp add: Inf_ccsubspace.rep_eq)

    then have *: \<open>\<psi>' b \<otimes>\<^sub>s ket b \<in> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close> for b
      by (auto intro!: ccspan_superset[THEN set_mp] 
          simp add: tensor_ccsubspace_def Inf_ccsubspace.rep_eq)
    
    have \<open>\<psi> \<in> space_as_set (ccspan (range (\<lambda>b. \<psi>' b \<otimes>\<^sub>s ket b)))\<close> (is \<open>\<psi> \<in> ?rhs\<close>)
    proof -
      define \<gamma> where \<open>\<gamma> F = (\<Sum>b\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>)\<close> for F
      have \<gamma>_rhs: \<open>\<gamma> F \<in> ?rhs\<close> for F
        apply (auto intro!: complex_vector.subspace_sum simp add: \<gamma>_def \<psi>'b_b)
        using ccspan_superset by fastforce
      have \<gamma>_trunc: \<open>\<gamma> F = trunc_ell2 (UNIV \<times> F) \<psi>\<close> if \<open>finite F\<close> for F
      proof (rule cinner_ket_eqI)
        fix x :: \<open>'b \<times> 'c\<close> obtain x1 x2 where x_def: \<open>x = (x1,x2)\<close>
          by force
        have *: \<open>ket x \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket j) *\<^sub>V \<psi>) = of_bool (j=x2) * Rep_ell2 \<psi> x\<close> for j
          apply (simp add: x_def tensor_op_ell2 tensor_op_adjoint cinner_ket 
              flip: tensor_ell2_ket cinner_adj_left)
          by (simp add: tensor_ell2_ket cinner_ket_left)
        have \<open>ket x \<bullet>\<^sub>C \<gamma> F = of_bool (x2\<in>F) *\<^sub>C Rep_ell2 \<psi> x\<close>
          using that
          apply (simp add: x_def \<gamma>_def complex_vector.linear_sum[of \<open>cinner _\<close>] bounded_clinear_cinner_right 
              bounded_clinear.clinear sum_single[where i=x2] tensor_op_adjoint tensor_op_ell2 cinner_ket
              flip: tensor_ell2_ket cinner_adj_left)
          by (simp add: tensor_ell2_ket cinner_ket_left)
        moreover have \<open>ket x \<bullet>\<^sub>C trunc_ell2 (UNIV \<times> F) \<psi> = of_bool (x2\<in>F) *\<^sub>C Rep_ell2 \<psi> x\<close>
          by (simp add: trunc_ell2.rep_eq cinner_ket_left x_def)
        ultimately show \<open>ket x \<bullet>\<^sub>C \<gamma> F = ket x \<bullet>\<^sub>C trunc_ell2 (UNIV \<times> F) \<psi>\<close>
          by simp
      qed
      have \<open>(\<gamma> \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
      proof (rule tendsto_iff[THEN iffD2, rule_format])
        fix e :: real assume \<open>e > 0\<close>
        from trunc_ell2_lim_at_UNIV[of \<psi>]
        have \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV. dist (trunc_ell2 F \<psi>) \<psi> < e\<close>
          by (simp add: \<open>0 < e\<close> tendstoD)
        then obtain M where \<open>finite M\<close> and less_e: \<open>finite F \<Longrightarrow> F \<supseteq> M \<Longrightarrow> dist (trunc_ell2 F \<psi>) \<psi> < e\<close> for F
          by (metis (mono_tags, lifting) eventually_finite_subsets_at_top subset_UNIV)
        define M' where \<open>M' = snd ` M\<close>
        have \<open>finite M'\<close>
          using M'_def \<open>finite M\<close> by blast
        have \<open>dist (\<gamma> F') \<psi> < e\<close> if \<open>finite F'\<close> and \<open>F' \<supseteq> M'\<close> for F'
        proof -
          have \<open>dist (\<gamma> F') \<psi> = norm (trunc_ell2 (- (UNIV \<times> F')) \<psi>)\<close>
            using that by (simp only: \<gamma>_trunc dist_norm trunc_ell2_uminus norm_minus_commute)
          also have \<open>\<dots> \<le> norm (trunc_ell2 (- ((fst ` M) \<times> F')) \<psi>)\<close>
            by (meson Compl_anti_mono Set.basic_monos(1) Sigma_mono subset_UNIV trunc_ell2_norm_mono)
          also have \<open>\<dots> = dist (trunc_ell2 ((fst ` M) \<times> F') \<psi>) \<psi>\<close>
            apply (simp add: trunc_ell2_uminus dist_norm)
            using norm_minus_commute by blast
          also have \<open>\<dots> < e\<close>
            apply (rule less_e)
            using \<open>finite F'\<close> \<open>finite M\<close> apply force
            using \<open>F' \<supseteq> M'\<close> M'_def by force
          finally show ?thesis
            by -
        qed
        then show \<open>\<forall>\<^sub>F F' in finite_subsets_at_top UNIV. dist (\<gamma> F') \<psi> < e\<close>
          using \<open>finite M'\<close> by (auto simp add: eventually_finite_subsets_at_top)
      qed
      then show \<open>\<psi> \<in> ?rhs\<close>
        apply (rule Lim_in_closed_set[rotated -1])
        using \<gamma>_rhs by auto 
    qed
    also from * have \<open>\<dots> \<subseteq> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close>
      by (meson ccspan_leqI image_subset_iff less_eq_ccsubspace.rep_eq)
    
    finally show \<open>\<psi> \<in> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close>
      by -
  qed
qed

lemma tensor_ccsubspace_INF_right_top:
  fixes S :: \<open>'a \<Rightarrow> 'b ell2 ccsubspace\<close>
  shows \<open>(\<top>::'c ell2 ccsubspace) \<otimes>\<^sub>S (INF x\<in>X. S x) = (INF x\<in>X. \<top> \<otimes>\<^sub>S S x)\<close>
proof -
  have \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S (\<top>::'c ell2 ccsubspace) = (INF x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
    by (rule tensor_ccsubspace_INF_left_top)
  then have \<open>swap_ell2 *\<^sub>S ((INF x\<in>X. S x) \<otimes>\<^sub>S (\<top>::'c ell2 ccsubspace)) = swap_ell2 *\<^sub>S (INF x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
    by simp
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    by (simp_all add: swap_ell2_tensor_ccsubspace cblinfun_image_INF_eq)
qed

lemma tensor_ccsubspace_INF_left: \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S T = (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close> if \<open>X \<noteq> {}\<close>
proof (cases \<open>T=0\<close>)
  case True
  then show ?thesis 
    using that by simp
next
  case False
  from ccsubspace_as_whole_type[OF False]
  have \<open>\<forall>\<^sub>\<tau> 't::type = some_chilbert_basis_of T.
        (INF x\<in>X. S x) \<otimes>\<^sub>S T = (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close>
  proof (rule with_type_mp)
    fix Rep :: \<open>'t \<Rightarrow> 'c ell2\<close> and Abs
    assume \<open>type_definition Rep Abs (some_chilbert_basis_of T)\<close>
    then interpret type_definition Rep Abs \<open>some_chilbert_basis_of T\<close>
      by simp
    assume \<open>\<exists>U :: 't ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. isometry U \<and> U *\<^sub>S \<top> = T\<close>
    then obtain U :: \<open>'t ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where [simp]: \<open>isometry U\<close> and imU: \<open>U *\<^sub>S \<top> = T\<close>
      by auto
    have \<open>(id_cblinfun \<otimes>\<^sub>o U) *\<^sub>S ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S \<top>) = (id_cblinfun \<otimes>\<^sub>o U) *\<^sub>S (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. _ *\<^sub>S x\<close>])  
      by (rule tensor_ccsubspace_INF_left_top)
    then show \<open>(\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S T = (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S T)\<close>
      using that by (simp add: imU cblinfun_image_INF_eq isometry_tensor_op
          flip: tensor_ccsubspace_image)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma tensor_ccsubspace_INF_right: \<open>(INF x\<in>X. T \<otimes>\<^sub>S S x) = (INF x\<in>X. T \<otimes>\<^sub>S S x)\<close> if \<open>X \<noteq> {}\<close>
proof -
  from that have \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S T = (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close>
    by (rule tensor_ccsubspace_INF_left)
  then have \<open>swap_ell2 *\<^sub>S ((INF x\<in>X. S x) \<otimes>\<^sub>S T) = swap_ell2 *\<^sub>S (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close>
    by simp
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    by (simp_all add: swap_ell2_tensor_ccsubspace cblinfun_image_INF_eq)
qed

lemma tensor_ccsubspace_ccspan: \<open>ccspan X \<otimes>\<^sub>S ccspan Y = ccspan {x \<otimes>\<^sub>s y | x y. x \<in> X \<and> y \<in> Y}\<close>
proof (rule antisym)
  show \<open>ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y} \<le> ccspan X \<otimes>\<^sub>S ccspan Y\<close>
    apply (auto intro!: ccspan_mono Collect_mono ex_mono simp add: tensor_ccsubspace_def)
    using ccspan_superset by auto
next
  have \<open>{\<psi> \<otimes>\<^sub>s \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set (ccspan X) \<and> \<phi> \<in> space_as_set (ccspan Y)}
       \<subseteq> closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
  proof (rule subsetI)
    fix \<gamma>
    assume \<open>\<gamma> \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set (ccspan X) \<and> \<phi> \<in> space_as_set (ccspan Y)}\<close>
    then obtain \<psi> \<phi> where \<psi>: \<open>\<psi> \<in> space_as_set (ccspan X)\<close> and \<phi>: \<open>\<phi> \<in> space_as_set (ccspan Y)\<close> and \<gamma>_def: \<open>\<gamma> = \<psi> \<otimes>\<^sub>s \<phi>\<close>
      by blast
    from \<psi>
    obtain \<psi>' where lim1: \<open>\<psi>' \<longlonglongrightarrow> \<psi>\<close> and \<psi>'X: \<open>\<psi>' n \<in> cspan X\<close> for n
      apply atomize_elim
      apply (auto simp: ccspan.rep_eq)
      using closure_sequential by blast
    from \<phi>
    obtain \<phi>' where lim2: \<open>\<phi>' \<longlonglongrightarrow> \<phi>\<close> and \<phi>'Y: \<open>\<phi>' n \<in> cspan Y\<close> for n
      apply atomize_elim
      apply (auto simp: ccspan.rep_eq)
      using closure_sequential by blast
    interpret tensor: bounded_cbilinear tensor_ell2
      by (rule bounded_cbilinear_tensor_ell2)
    from lim1 lim2 have \<open>(\<lambda>n. \<psi>' n \<otimes>\<^sub>s \<phi>' n) \<longlonglongrightarrow> \<psi> \<otimes>\<^sub>s \<phi>\<close>
      by (rule tensor.tendsto)
    moreover have \<open>\<psi>' n \<otimes>\<^sub>s \<phi>' n \<in> {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close> for n
      using \<psi>'X \<phi>'Y by auto
    ultimately show \<open>\<gamma> \<in> closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
      unfolding \<gamma>_def
      by (meson closure_sequential)
  qed
  also have \<open>closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}
          \<subseteq> closure (cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y})\<close>
  proof (intro closure_mono subsetI)
    fix \<gamma>
    assume \<open>\<gamma> \<in> {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
    then obtain x y where \<gamma>_def: \<open>\<gamma> = x \<otimes>\<^sub>s y\<close> and \<open>x \<in> cspan X\<close> and \<open>y \<in> cspan Y\<close>
      by blast
    from \<open>x \<in> cspan X\<close>
    obtain X' x' where \<open>finite X'\<close> and \<open>X' \<subseteq> X\<close> and x_def: \<open>x = (\<Sum>i\<in>X'. x' i *\<^sub>C i)\<close>
      using complex_vector.span_explicit[of X] apply atomize_elim
      by auto
    from \<open>y \<in> cspan Y\<close>
    obtain Y' y' where \<open>finite Y'\<close> and \<open>Y' \<subseteq> Y\<close> and y_def: \<open>y = (\<Sum>j\<in>Y'. y' j *\<^sub>C j)\<close>
      using complex_vector.span_explicit[of Y] apply atomize_elim
      by auto
    from x_def y_def \<gamma>_def
    have \<open>\<gamma> = (\<Sum>i\<in>X'. x' i *\<^sub>C i) \<otimes>\<^sub>s (\<Sum>j\<in>Y'. y' j *\<^sub>C j)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>X'. \<Sum>j\<in>Y'. (x' i *\<^sub>C i) \<otimes>\<^sub>s (y' j *\<^sub>C j))\<close>
      by (smt (verit) sum.cong tensor_ell2_sum_left tensor_ell2_sum_right)
    also have \<open>\<dots> = (\<Sum>i\<in>X'. \<Sum>j\<in>Y'. (x' i * y' j) *\<^sub>C (i \<otimes>\<^sub>s j))\<close>
      by (metis (no_types, lifting) scaleC_scaleC sum.cong tensor_ell2_scaleC1 tensor_ell2_scaleC2)
    also have \<open>\<dots> \<in> cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
      using \<open>X' \<subseteq> X\<close> \<open>Y' \<subseteq> Y\<close>
      by (auto intro!: complex_vector.span_sum complex_vector.span_scale
          complex_vector.span_base[of \<open>_ \<otimes>\<^sub>s _\<close>])
    finally show \<open>\<gamma> \<in> cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
      by -
  qed
  also have \<open>\<dots> = space_as_set (ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y})\<close>
    using ccspan.rep_eq by blast
  finally show \<open>ccspan X \<otimes>\<^sub>S ccspan Y \<le> ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
    by (auto intro!: ccspan_leqI simp add: tensor_ccsubspace_def)
qed

lemma tensor_ccsubspace_mono: \<open>A \<otimes>\<^sub>S B \<le> C \<otimes>\<^sub>S D\<close> if \<open>A \<le> C\<close> and \<open>B \<le> D\<close>
  apply (auto intro!: ccspan_mono simp add: tensor_ccsubspace_def)
  using that
  by (auto simp add: less_eq_ccsubspace_def)

lemma tensor_ccsubspace_element_as_infsum:
  fixes A :: \<open>'a ell2 ccsubspace\<close> and B :: \<open>'b ell2 ccsubspace\<close>
  assumes \<open>\<psi> \<in> space_as_set (A \<otimes>\<^sub>S B)\<close>
  shows \<open>\<exists>\<phi> \<delta>. (\<forall>n::nat. \<phi> n \<in> space_as_set A) \<and> (\<forall>n. \<delta> n \<in> space_as_set B)
       \<and> has_sum (\<lambda>n. \<phi> n \<otimes>\<^sub>s \<delta> n) UNIV \<psi>\<close>
proof -
  obtain A' where spanA': \<open>ccspan A' = A\<close> and orthoA': \<open>is_ortho_set A'\<close> and normA': \<open>a \<in> A' \<Longrightarrow> norm a = 1\<close> for a
    using some_chilbert_basis_of_ccspan some_chilbert_basis_of_is_ortho_set some_chilbert_basis_of_norm1
    by blast
  obtain B' where spanB': \<open>ccspan B' = B\<close> and orthoB': \<open>is_ortho_set B'\<close> and normB': \<open>b \<in> B' \<Longrightarrow> norm b = 1\<close> for b
    using some_chilbert_basis_of_ccspan some_chilbert_basis_of_is_ortho_set some_chilbert_basis_of_norm1
    by blast
  define AB' where \<open>AB' = {a \<otimes>\<^sub>s b | a b. a \<in> A' \<and> b \<in> B'}\<close>
  define ABnon0 where \<open>ABnon0 = {ab \<in> AB'. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab \<noteq> 0}\<close>
  have ABnon0_def': \<open>ABnon0 = {ab \<in> AB'. (norm (ab \<bullet>\<^sub>C \<psi>))\<^sup>2 \<noteq> 0}\<close>
    by (auto simp: ABnon0_def)
  have \<open>is_ortho_set AB'\<close>
    by (simp add: AB'_def orthoA' orthoB' tensor_ell2_is_ortho_set)
  have normAB': \<open>ab \<in> AB' \<Longrightarrow> norm ab = 1\<close> for ab
    by (auto simp add: AB'_def norm_tensor_ell2 normA' normB')
  have spanAB': \<open>ccspan AB' = A \<otimes>\<^sub>S B\<close>
    by (simp add: tensor_ccsubspace_ccspan AB'_def flip: spanA' spanB')
  have sum1: \<open>has_sum (\<lambda>ab. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab) AB' \<psi>\<close>
    apply (rule basis_projections_reconstruct_has_sum)
    by (simp_all add: spanAB' \<open>is_ortho_set AB'\<close> normAB' assms)
  have \<open>(\<lambda>ab. (norm (ab \<bullet>\<^sub>C \<psi>))\<^sup>2) summable_on AB'\<close>
    apply (rule summable_on_norm_on_basis)
    by (simp_all add: spanAB' \<open>is_ortho_set AB'\<close> normAB' assms)
  then have \<open>countable ABnon0\<close>
    using ABnon0_def' summable_countable_real by blast
  obtain f and N :: \<open>nat set\<close> where bij_f: \<open>bij_betw f N ABnon0\<close>
    using \<open>countable ABnon0\<close> countableE_bij by blast
  then obtain \<phi>0 \<delta>0 where f_def: \<open>f n = \<phi>0 n \<otimes>\<^sub>s \<delta>0 n\<close> and \<phi>0A': \<open>\<phi>0 n \<in> A'\<close> and \<delta>0B': \<open>\<delta>0 n \<in> B'\<close> if \<open>n \<in> N\<close> for n
    apply atomize_elim 
    apply (subst all_conj_distrib[symmetric] choice_iff[symmetric])+
    apply (simp add: bij_betw_def ABnon0_def)
    using AB'_def \<open>bij_betw f N ABnon0\<close> bij_betwE mem_Collect_eq by blast
  define c where \<open>c n = (\<phi>0 n \<otimes>\<^sub>s \<delta>0 n) \<bullet>\<^sub>C \<psi>\<close> for n
  from sum1 have \<open>has_sum (\<lambda>ab. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab) ABnon0 \<psi>\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    by (auto simp: ABnon0_def)
  then have \<open>has_sum (\<lambda>n. (f n \<bullet>\<^sub>C \<psi>) *\<^sub>C f n) N \<psi>\<close>
    by (rule has_sum_reindex_bij_betw[OF bij_f, THEN iffD2])
  then have sum2: \<open>has_sum (\<lambda>n. c n *\<^sub>C (\<phi>0 n \<otimes>\<^sub>s \<delta>0 n)) N \<psi>\<close>
    apply (rule has_sum_cong[THEN iffD1, rotated])
    by (simp add: f_def c_def)
  define \<phi> \<delta> where \<open>\<phi> n = (if n\<in>N then c n *\<^sub>C \<phi>0 n else 0)\<close> and \<open>\<delta> n = (if n\<in>N then \<delta>0 n else 0)\<close> for n
  then have 1: \<open>\<phi> n \<in> space_as_set A\<close> and 2: \<open>\<delta> n \<in> space_as_set B\<close> for n
    using \<phi>0A' \<delta>0B' spanA' spanB' ccspan_superset 
    by (auto intro!: complex_vector.subspace_scale simp: \<phi>_def \<delta>_def)
  from sum2 have sum3: \<open>has_sum (\<lambda>n. \<phi> n \<otimes>\<^sub>s \<delta> n) UNIV \<psi>\<close>
    apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
    by (auto simp: \<phi>_def \<delta>_def tensor_ell2_scaleC1)
  from 1 2 sum3 show ?thesis
    by auto
qed

lemma ortho_tensor_ccsubspace_right: \<open>- (\<top> \<otimes>\<^sub>S A) = \<top> \<otimes>\<^sub>S (- A)\<close>
proof -
  have [simp]: \<open>is_Proj (id_cblinfun \<otimes>\<^sub>o Proj X)\<close> for X
    by (metis Proj_is_Proj Proj_top is_Proj_tensor_op)
  
  have \<open>Proj (- (\<top> \<otimes>\<^sub>S A)) = id_cblinfun - Proj (\<top> \<otimes>\<^sub>S A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = id_cblinfun - (id_cblinfun \<otimes>\<^sub>o Proj A)\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range)
  also have \<open>\<dots> = id_cblinfun \<otimes>\<^sub>o (id_cblinfun - Proj A)\<close>
    by (metis cblinfun.diff_right left_amplification.rep_eq tensor_id)
  also have \<open>\<dots> = Proj \<top> \<otimes>\<^sub>o Proj (- A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = Proj (\<top> \<otimes>\<^sub>S (- A))\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range)
  finally show ?thesis
    using Proj_inj by blast
qed

lemma ortho_tensor_ccsubspace_left: \<open>- (A \<otimes>\<^sub>S \<top>) = (- A) \<otimes>\<^sub>S \<top>\<close>
proof -
  have \<open>- (A \<otimes>\<^sub>S \<top>) = swap_ell2 *\<^sub>S (- (\<top> \<otimes>\<^sub>S A))\<close>
    by (simp add: unitary_image_ortho_compl swap_ell2_tensor_ccsubspace)
  also have \<open>\<dots> = swap_ell2 *\<^sub>S (\<top> \<otimes>\<^sub>S (- A))\<close>
    by (simp add: ortho_tensor_ccsubspace_right)
  also have \<open>\<dots> = (- A) \<otimes>\<^sub>S \<top>\<close>
    by (simp add: swap_ell2_tensor_ccsubspace)
  finally show ?thesis
    by -
qed

lemma kernel_tensor_id_left: \<open>kernel (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S kernel A\<close>
proof -
  have \<open>kernel (id_cblinfun \<otimes>\<^sub>o A) = - ((id_cblinfun \<otimes>\<^sub>o A)* *\<^sub>S \<top>)\<close>
    by (rule kernel_compl_adj_range)
  also have \<open>\<dots> = - (id_cblinfun *\<^sub>S \<top> \<otimes>\<^sub>S A* *\<^sub>S \<top>)\<close>
    by (metis cblinfun_image_id id_cblinfun_adjoint tensor_ccsubspace_image tensor_ccsubspace_top tensor_op_adjoint)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S (- (A* *\<^sub>S \<top>))\<close>
    by (simp add: ortho_tensor_ccsubspace_right)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S kernel A\<close>
    by (simp add: kernel_compl_adj_range)
  finally show ?thesis
    by -
qed

lemma kernel_tensor_id_right: \<open>kernel (A \<otimes>\<^sub>o id_cblinfun) = kernel A \<otimes>\<^sub>S \<top>\<close>
proof -
  have ker_swap: \<open>kernel swap_ell2 = 0\<close>
    by (simp add: kernel_isometry)
  have \<open>kernel (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S kernel A\<close>
    by (rule kernel_tensor_id_left)
  from this[THEN arg_cong, of \<open>cblinfun_image swap_ell2\<close>]
  show ?thesis
    by (simp add: swap_ell2_tensor_ccsubspace cblinfun_image_kernel_unitary
        flip: swap_ell2_commute_tensor_op kernel_cblinfun_compose[OF ker_swap])
qed


lemma eigenspace_tensor_id_left: \<open>eigenspace c (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S eigenspace c A\<close>
proof -
  have \<open>eigenspace c (id_cblinfun \<otimes>\<^sub>o A) = kernel (id_cblinfun \<otimes>\<^sub>o (A - c *\<^sub>C id_cblinfun))\<close>
    apply (simp add: eigenspace_def)
    by (metis (no_types, lifting) complex_vector.scale_minus_left tensor_id tensor_op_right_add tensor_op_scaleC_right uminus_add_conv_diff)
  also have \<open>kernel (id_cblinfun \<otimes>\<^sub>o (A - c *\<^sub>C id_cblinfun)) = \<top> \<otimes>\<^sub>S kernel (A - c *\<^sub>C id_cblinfun)\<close>
    by (simp add: kernel_tensor_id_left)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S eigenspace c A\<close>
    by (simp add: eigenspace_def)
  finally show ?thesis
    by -
qed

lemma eigenspace_tensor_id_right: \<open>eigenspace c (A \<otimes>\<^sub>o id_cblinfun) = eigenspace c A \<otimes>\<^sub>S \<top>\<close>
proof -
  have \<open>eigenspace c (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S eigenspace c A\<close>
    by (rule eigenspace_tensor_id_left)
  from this[THEN arg_cong, of \<open>cblinfun_image swap_ell2\<close>]
  show ?thesis
    by (simp add: swap_ell2_commute_tensor_op cblinfun_image_eigenspace_unitary swap_ell2_tensor_ccsubspace)
qed

end
