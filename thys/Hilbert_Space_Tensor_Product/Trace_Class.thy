section \<open>\<open>Trace_Class\<close> -- Trace-class operators\<close>

theory Trace_Class
  imports Complex_Bounded_Operators.Complex_L2 HS2Ell2
    Weak_Operator_Topology Positive_Operators Compact_Operators
begin

hide_fact (open) Infinite_Set_Sum.abs_summable_on_Sigma_iff
hide_fact (open) Infinite_Set_Sum.abs_summable_on_comparison_test
hide_const (open) Determinants.trace
hide_fact (open) Determinants.trace_def

unbundle cblinfun_notation

subsection \<open>Auxiliary lemmas\<close>

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_abs_summable: \<open>(\<lambda>e. (cmod (e \<bullet>\<^sub>C h))\<^sup>2) abs_summable_on E\<close>
proof (cases \<open>h = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (e \<bullet>\<^sub>C h))\<^sup>2) \<noteq> 0\<close>
    using assms by (simp add: parseval_identity is_onb_def)
  then show ?thesis
    using infsum_not_exists by auto
qed

lemma basis_image_square_has_sum1:
  \<comment> \<open>Half of \<^cite>\<open>\<open>Proposition 18.1\<close> in conway00operator\<close>, other half in \<open>basis_image_square_has_sum1\<close>.\<close>
  fixes E :: \<open>'a::complex_inner set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
proof (rule iffI)
  assume asm: \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    using asm infsumI by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using asm summable_on_def by auto
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    apply (subst sum1)
    apply (rule infsum_cong)
    using assms(2)
    by (simp add: is_onb_def flip: parseval_identity)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) abs_summable_on E\<close>
    using _ abs1 apply (rule summable_on_cong[THEN iffD2])
    apply (subst parseval_identity)
    using assms(2) by (auto simp: is_onb_def)
  have abs3: \<open>(\<lambda>(x, y). (cmod (y \<bullet>\<^sub>C (A *\<^sub>V x)))\<^sup>2) abs_summable_on E \<times> F\<close>
    thm abs_summable_on_Sigma_iff
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2], rule conjI)
    using abs2 apply (auto simp del: real_norm_def)
    using assms(2) parseval_abs_summable apply blast
    by auto
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    apply (subst sum2)
    apply (subst infsum_Sigma'_banach[symmetric])
    using abs3 abs_summable_summable apply blast
    by auto
  then show \<open>((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
    using abs3 abs_summable_summable has_sum_infsum by blast
next
  assume asm: \<open>((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
  have abs3: \<open>(\<lambda>(x, y). (cmod (y \<bullet>\<^sub>C (A *\<^sub>V x)))\<^sup>2) abs_summable_on E \<times> F\<close>
    using asm summable_on_def summable_on_iff_abs_summable_on_real
    by blast
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    using asm infsumI by blast
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    by (metis (mono_tags, lifting) asm infsum_Sigma'_banach infsum_cong sum3 summable_iff_has_sum_infsum)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) abs_summable_on E\<close>
    by (smt (verit, del_insts) abs3 summable_on_Sigma_banach summable_on_cong summable_on_iff_abs_summable_on_real)
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    apply (subst sum2)
    apply (rule infsum_cong)
    using assms(2) parseval_identity is_onb_def
    by fastforce
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using abs2 assms(2) parseval_identity is_onb_def by fastforce
  show \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
    using abs1 sum1 by auto
qed

lemma basis_image_square_has_sum2:
  \<comment> \<open>Half of \<^cite>\<open>\<open>Proposition 18.1\<close> in conway00operator\<close>, other half in @{thm [source] basis_image_square_has_sum1}.\<close>
  fixes E :: \<open>'a::chilbert_space set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
proof -
  have \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
    using basis_image_square_has_sum1 assms by blast
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(e,f). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) has_sum t) (E\<times>F)\<close>
    apply (subst cinner_adj_left)
    by (rule refl)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(f,e). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) has_sum t) (F\<times>E)\<close>
    apply (subst asm_rl[of \<open>F\<times>E = prod.swap ` (E\<times>F)\<close>])
     apply force
    apply (subst has_sum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    apply (subst cinner_commute, subst complex_mod_cnj)
    using basis_image_square_has_sum1 assms
    by blast
  finally show ?thesis
    by -
qed

subsection \<open>Trace-norm and trace-class\<close>

lemma trace_norm_basis_invariance:
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) E \<longleftrightarrow> ((\<lambda>f. cmod (f \<bullet>\<^sub>C (abs_op A *\<^sub>V f))) has_sum t) F\<close>
    \<comment> \<open>@{cite "conway00operator"}, Corollary 18.2\<close>
proof -
  define B where \<open>B = sqrt_op (abs_op A)\<close>
  have \<open>complex_of_real (cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) = (B* *\<^sub>V B*\<^sub>V e) \<bullet>\<^sub>C e\<close> for e
    apply (simp add: B_def positive_hermitianI flip: cblinfun_apply_cblinfun_compose)
    by (metis abs_op_pos abs_pos cinner_commute cinner_pos_if_pos complex_cnj_complex_of_real complex_of_real_cmod)
  also have \<open>\<dots> e = complex_of_real ((norm (B *\<^sub>V e))\<^sup>2)\<close> for e
    apply (subst cdot_square_norm[symmetric])
    apply (subst cinner_adj_left[symmetric])
    by (simp add: B_def)
  finally have *: \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = (norm (B *\<^sub>V e))\<^sup>2\<close> for e
    by (metis Re_complex_of_real)

  have \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) E \<longleftrightarrow> ((\<lambda>e. (norm (B *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
    by (simp add: *)
  also have \<open>\<dots> = ((\<lambda>f. (norm (B* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    apply (subst basis_image_square_has_sum2[where F=F])
    by (simp_all add: assms)
  also have \<open>\<dots> = ((\<lambda>f. (norm (B *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    using basis_image_square_has_sum2 assms(2) by blast
  also have \<open>\<dots> = ((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) F\<close>
    by (simp add: *)
  finally show ?thesis
    by simp
qed

definition trace_class :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> bool\<close> 
  where \<open>trace_class A \<longleftrightarrow> (\<exists>E. is_onb E \<and> (\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E)\<close>

lemma trace_classI:
  assumes \<open>is_onb E\<close> and \<open>(\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E\<close>
  shows \<open>trace_class A\<close>
  using assms(1) assms(2) trace_class_def by blast

lemma trace_class_iff_summable:
  assumes \<open>is_onb E\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E\<close>
  apply (auto intro!: trace_classI assms simp: trace_class_def)
  using assms summable_on_def trace_norm_basis_invariance by blast

lemma trace_class_0[simp]: \<open>trace_class 0\<close>
  unfolding trace_class_def
  by (auto intro!: exI[of _ some_chilbert_basis] simp: is_onb_def is_normal_some_chilbert_basis)

(* lemma polar_polar_abs_op: \<open>(polar_decomposition a)* o\<^sub>C\<^sub>L polar_decomposition a o\<^sub>C\<^sub>L abs_op a = abs_op a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using polar_decomposition_correct[of a] polar_decomposition_correct'[of a]
  by (simp add: cblinfun_compose_assoc) *)

lemma trace_class_uminus: \<open>trace_class t \<Longrightarrow> trace_class (-t)\<close>
  by (auto simp add: trace_class_def)

lemma trace_class_uminus_iff[simp]: \<open>trace_class (-a) = trace_class a\<close>
  by (auto simp add: trace_class_def)

definition trace_norm where \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) else 0)\<close>

definition trace where \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>

lemma trace_0[simp]: \<open>trace 0 = 0\<close>
  unfolding trace_def by simp

lemma trace_class_abs_op[simp]: \<open>trace_class (abs_op A) = trace_class A\<close>
  unfolding trace_class_def
  by simp

lemma trace_abs_op[simp]: \<open>trace (abs_op A) = trace_norm A\<close>
proof (cases \<open>trace_class A\<close>)
  case True
  have pos: \<open>e \<bullet>\<^sub>C (abs_op A *\<^sub>V e) \<ge> 0\<close> for e
    by (simp add: cinner_pos_if_pos)
  then have abs: \<open>e \<bullet>\<^sub>C (abs_op A *\<^sub>V e) = abs (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))\<close> for e
    by (simp add: abs_pos)
  
  have \<open>trace (abs_op A) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))\<close>
    by (simp add: trace_def True)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. complex_of_real (cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))))\<close>
    using pos abs complex_of_real_cmod by presburger
  also have \<open>\<dots> = complex_of_real (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)))\<close>
    by (simp add: infsum_of_real)
  also have \<open>\<dots> = trace_norm A\<close>
    by (simp add: trace_norm_def True)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis 
    by (simp add: trace_def trace_norm_def)
qed

lemma trace_norm_pos: \<open>trace_norm A = trace A\<close> if \<open>A \<ge> 0\<close>
  by (metis abs_op_id_on_pos that trace_abs_op)


lemma trace_norm_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. cmod (e  \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) else 0)\<close>
  by (metis (mono_tags, lifting) assms infsum_eqI' is_onb_some_chilbert_basis trace_norm_basis_invariance trace_norm_def)

lemma trace_class_finite_dim[simp]: \<open>trace_class A\<close> for A :: \<open>'a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  apply (subst trace_class_iff_summable[of some_chilbert_basis])
  by (auto intro!: summable_on_finite)

lemma trace_class_scaleC: \<open>trace_class (c *\<^sub>C a)\<close> if \<open>trace_class a\<close>
proof -
  from that obtain B where \<open>is_onb B\<close> and \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op a *\<^sub>V x)) abs_summable_on B\<close>
    by (auto simp: trace_class_def)
  then show ?thesis
    by (auto intro!: exI[of _ B] summable_on_cmult_right simp: trace_class_def \<open>is_onb B\<close> abs_op_scaleC norm_mult)
qed

lemma trace_scaleC: \<open>trace (c *\<^sub>C a) = c * trace a\<close>
proof -
  consider (trace_class) \<open>trace_class a\<close> | (c0) \<open>c = 0\<close> | (non_trace_class) \<open>\<not> trace_class a\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case trace_class
    then have \<open>trace_class (c *\<^sub>C a)\<close>
      by (rule trace_class_scaleC)
    then have \<open>trace (c *\<^sub>C a) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (c *\<^sub>C a *\<^sub>V e))\<close>
      unfolding trace_def by simp
    also have \<open>\<dots> = c * (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (a *\<^sub>V e))\<close>
      by (auto simp: infsum_cmult_right')
    also from trace_class have \<open>\<dots> = c * trace a\<close>
      by (simp add: Trace_Class.trace_def)
    finally show ?thesis
      by -
  next
    case c0
    then show ?thesis 
      by simp
  next
    case non_trace_class
    then have \<open>\<not> trace_class (c *\<^sub>C a)\<close>
      by (metis divideC_field_simps(2) trace_class_scaleC)
    with non_trace_class show ?thesis
      by (simp add: trace_def)
  qed
qed

lemma trace_uminus: \<open>trace (- a) = - trace a\<close>
  by (metis mult_minus1 scaleC_minus1_left trace_scaleC)

lemma trace_norm_0[simp]: \<open>trace_norm 0 = 0\<close>
  by (auto simp: trace_norm_def)

lemma trace_norm_nneg[simp]: \<open>trace_norm a \<ge> 0\<close>
  apply (cases \<open>trace_class a\<close>)
  by (auto simp: trace_norm_def infsum_nonneg)

lemma trace_norm_scaleC: \<open>trace_norm (c *\<^sub>C a) = norm c * trace_norm a\<close>
proof -
  consider (trace_class) \<open>trace_class a\<close> | (c0) \<open>c = 0\<close> | (non_trace_class) \<open>\<not> trace_class a\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case trace_class
    then have \<open>trace_class (c *\<^sub>C a)\<close>
      by (rule trace_class_scaleC)
    then have \<open>trace_norm (c *\<^sub>C a) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (e \<bullet>\<^sub>C (abs_op (c *\<^sub>C a) *\<^sub>V e)))\<close>
      unfolding trace_norm_def by simp
    also have \<open>\<dots> = norm c * (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close>
      by (auto simp: infsum_cmult_right' abs_op_scaleC norm_mult)
    also from trace_class have \<open>\<dots> = norm c * trace_norm a\<close>
      by (simp add: trace_norm_def)
    finally show ?thesis
      by -
  next
    case c0
    then show ?thesis
      by simp
  next
    case non_trace_class
    then have \<open>\<not> trace_class (c *\<^sub>C a)\<close>
      by (metis divideC_field_simps(2) trace_class_scaleC)
    with non_trace_class show ?thesis
      by (simp add: trace_norm_def)
  qed
qed


lemma trace_norm_nondegenerate: \<open>a = 0\<close> if \<open>trace_class a\<close> and \<open>trace_norm a = 0\<close>
proof (rule ccontr)
  assume \<open>a \<noteq> 0\<close>
  then have \<open>abs_op a \<noteq> 0\<close>
    using abs_op_nondegenerate by blast
  then obtain x where xax: \<open>x \<bullet>\<^sub>C (abs_op a *\<^sub>V x) \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_cinner_eqI cinner_zero_right)
  then have \<open>norm x \<noteq> 0\<close>
    by auto
  then have xax': \<open>sgn x \<bullet>\<^sub>C (abs_op a *\<^sub>V sgn x) \<noteq> 0\<close> and [simp]: \<open>norm (sgn x) = 1\<close>
    unfolding sgn_div_norm using xax by (auto simp: cblinfun.scaleR_right)
  obtain B where sgnx_B: \<open>{sgn x} \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim apply (rule orthonormal_basis_exists)
    using \<open>norm x \<noteq> 0\<close> by (auto simp: is_ortho_set_def sgn_div_norm)

  from \<open>is_onb B\<close> that
  have summable: \<open>(\<lambda>e. e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)) abs_summable_on B\<close>
    using trace_class_iff_summable by fastforce

  from that have \<open>0 = trace_norm a\<close>
    by simp
  also from \<open>is_onb B\<close> have \<open>trace_norm a = (\<Sum>\<^sub>\<infinity>e\<in>B. cmod (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close>
    by (smt (verit, ccfv_SIG) abs_norm_cancel infsum_cong infsum_not_exists real_norm_def trace_class_def trace_norm_alt_def)
  also have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>e\<in>{sgn x}. cmod (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono2)
    using summable sgnx_B by auto
  also from xax' have \<open>\<dots> > 0\<close>
    by (simp add: is_orthogonal_sym xax')
  finally show False
    by simp
qed

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) trace_class = \<open>Collect trace_class :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  morphisms from_trace_class Abs_trace_class
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_trace_class

lemma trace_class_from_trace_class[simp]: \<open>trace_class (from_trace_class t)\<close>
  using from_trace_class by blast

lemma trace_pos: \<open>trace a \<ge> 0\<close> if \<open>a \<ge> 0\<close>
  by (metis abs_op_def complex_of_real_nn_iff sqrt_op_unique that trace_abs_op trace_norm_nneg)

lemma trace_adj_prelim: \<open>trace (a*) = cnj (trace a)\<close> if \<open>trace_class a\<close> and \<open>trace_class (a*)\<close>
  \<comment> \<open>We will later strengthen this as \<open>trace_adj\<close> and then hide this fact.\<close>
  by (simp add: trace_def that flip: cinner_adj_right infsum_cnj)

subsection \<open>Hilbert-Schmidt operators\<close>

definition hilbert_schmidt where \<open>hilbert_schmidt a \<longleftrightarrow> trace_class (a* o\<^sub>C\<^sub>L a)\<close>

definition hilbert_schmidt_norm where \<open>hilbert_schmidt_norm a = sqrt (trace_norm (a* o\<^sub>C\<^sub>L a))\<close>

lemma hilbert_schmidtI: \<open>hilbert_schmidt a\<close> if \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
  using that unfolding hilbert_schmidt_def by simp

lemma hilbert_schmidt_0[simp]: \<open>hilbert_schmidt 0\<close>
  unfolding hilbert_schmidt_def by simp

lemma hilbert_schmidt_norm_pos[simp]: \<open>hilbert_schmidt_norm a \<ge> 0\<close>
  by (auto simp: hilbert_schmidt_norm_def)

lemma has_sum_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) B\<close>
proof -
  from \<open>hilbert_schmidt a\<close>
  have \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
  using hilbert_schmidt_def by blast
  with \<open>is_onb B\<close> have \<open>((\<lambda>x. cmod (x \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V x))) has_sum trace_norm (a* o\<^sub>C\<^sub>L a)) B\<close>
    by (metis (no_types, lifting) abs_op_def has_sum_cong has_sum_infsum positive_cblinfun_squareI sqrt_op_unique trace_class_def trace_norm_alt_def trace_norm_basis_invariance)
  then show ?thesis
    by (auto simp: cinner_adj_right cdot_square_norm of_real_power norm_power hilbert_schmidt_norm_def)
qed

lemma summable_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
  using assms(1) assms(2) has_sum_hilbert_schmidt_norm_square summable_on_def by blast

lemma summable_hilbert_schmidt_norm_square_converse:
  assumes \<open>is_onb B\<close>
  assumes \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
  shows \<open>hilbert_schmidt a\<close>
proof -
  from assms(2)
  have \<open>(\<lambda>x. cmod (x \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V x))) summable_on B\<close>
    by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cinner_adj_right cinner_pos_if_pos cmod_Re positive_cblinfun_squareI power2_norm_eq_cinner' summable_on_cong)
  then have \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
    by (metis (no_types, lifting) abs_op_def assms(1) positive_cblinfun_squareI sqrt_op_unique summable_on_cong trace_class_def)
  then show ?thesis
    using hilbert_schmidtI by blast
qed

lemma infsum_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) = ((hilbert_schmidt_norm a)\<^sup>2)\<close>
    using assms has_sum_hilbert_schmidt_norm_square infsumI by blast


lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  assumes  \<open>hilbert_schmidt b\<close>
  shows hilbert_schmidt_comp_right: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
    and hilbert_schmidt_norm_comp_right: \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * hilbert_schmidt_norm b\<close>
proof -
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  have [simp]: \<open>is_onb B\<close>
    by (simp add: B_def)

  have leq: \<open>(norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2 \<le> (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2\<close> for x
    by (metis cblinfun_apply_cblinfun_compose norm_cblinfun norm_ge_zero power_mono power_mult_distrib)

  have \<open>(\<lambda>x. (norm (b *\<^sub>V x))\<^sup>2) summable_on B\<close>
    using \<open>is_onb B\<close> summable_hilbert_schmidt_norm_square assms by blast
  then have sum2: \<open>(\<lambda>x. (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2) summable_on B\<close>
    using summable_on_cmult_right by blast
  then have \<open>(\<lambda>x. ((norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2)) abs_summable_on B\<close>
    by auto
  then have \<open>(\<lambda>x. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2) abs_summable_on B\<close>
    apply (rule abs_summable_on_comparison_test)
    using leq by force
  then have sum5: \<open>(\<lambda>x. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2) summable_on B\<close>
    by auto
  then show [simp]: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
    using \<open>is_onb B\<close>
    by (rule summable_hilbert_schmidt_norm_square_converse[rotated])

  have \<open>(hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2)\<close>
    apply (rule infsum_hilbert_schmidt_norm_square[symmetric])
    by simp_all
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2)\<close>
    using sum5 sum2 leq by (rule infsum_mono)
  also have \<open>\<dots> = (norm a)\<^sup>2 * (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (b *\<^sub>V x))\<^sup>2)\<close>
    by (simp add: infsum_cmult_right')
  also have \<open>\<dots> = (norm a)\<^sup>2 * (hilbert_schmidt_norm b)\<^sup>2\<close>
    by (simp add: assms infsum_hilbert_schmidt_norm_square)
  finally show \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * hilbert_schmidt_norm b\<close>
    apply (rule_tac power2_le_imp_le)
    by (auto intro!: mult_nonneg_nonneg simp: power_mult_distrib)
qed


lemma hilbert_schmidt_adj[simp]:
  \<comment> \<open>Implicit in \<^cite>\<open>conway00operator\<close>, Proposition 18.6 (b)\<close>
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>hilbert_schmidt (a*)\<close>
proof -
  from assms
  have \<open>(\<lambda>e. (norm (a *\<^sub>V e))\<^sup>2) summable_on some_chilbert_basis\<close>
    using is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square by blast
  then have \<open>(\<lambda>e. (norm (a* *\<^sub>V e))\<^sup>2) summable_on some_chilbert_basis\<close>
    by (metis basis_image_square_has_sum2 is_onb_some_chilbert_basis summable_on_def)
  then show ?thesis
    using is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square_converse by blast
qed

lemma hilbert_schmidt_norm_adj[simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (b)\<close>
  shows \<open>hilbert_schmidt_norm (a*) = hilbert_schmidt_norm a\<close>
proof (cases \<open>hilbert_schmidt a\<close>)
  case True
  then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) some_chilbert_basis\<close>
    by (simp add: has_sum_hilbert_schmidt_norm_square)
  then have 1: \<open>((\<lambda>x. (norm (a* *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) some_chilbert_basis\<close>
    by (metis basis_image_square_has_sum2 is_onb_some_chilbert_basis)

  from True
  have \<open>hilbert_schmidt (a*)\<close>
    by simp
  then have 2: \<open>((\<lambda>x. (norm (a* *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm (a*))\<^sup>2) some_chilbert_basis\<close>
    by (simp add: has_sum_hilbert_schmidt_norm_square)

  from 1 2 show ?thesis
  by (metis abs_of_nonneg hilbert_schmidt_norm_pos infsumI real_sqrt_abs)
next
  case False
  then have \<open>\<not> hilbert_schmidt (a*)\<close>
    using hilbert_schmidt_adj by fastforce

  then show ?thesis
    by (metis False hilbert_schmidt_def hilbert_schmidt_norm_def trace_norm_def)
qed

lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b
  assumes  \<open>hilbert_schmidt a\<close>
  shows hilbert_schmidt_comp_left: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  by (auto intro!: assms hilbert_schmidt_comp_right hilbert_schmidt_adj simp del: adj_cblinfun_compose)

lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b
  assumes  \<open>hilbert_schmidt a\<close>
  shows hilbert_schmidt_norm_comp_left: \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm b * hilbert_schmidt_norm a\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  using hilbert_schmidt_norm_comp_right[of \<open>a*\<close> \<open>b*\<close>]
  by (auto intro!: assms hilbert_schmidt_adj simp del: adj_cblinfun_compose)

lemma hilbert_schmidt_scaleC: \<open>hilbert_schmidt (c *\<^sub>C a)\<close> if \<open>hilbert_schmidt a\<close>
  using hilbert_schmidt_def that trace_class_scaleC by fastforce 

lemma hilbert_schmidt_scaleR: \<open>hilbert_schmidt (r *\<^sub>R a)\<close> if \<open>hilbert_schmidt a\<close>
  by (simp add: hilbert_schmidt_scaleC scaleR_scaleC that) 

lemma hilbert_schmidt_uminus: \<open>hilbert_schmidt (- a)\<close> if \<open>hilbert_schmidt a\<close>
  by (metis hilbert_schmidt_scaleC scaleC_minus1_left that) 

lemma hilbert_schmidt_plus: \<open>hilbert_schmidt (t + u)\<close> if \<open>hilbert_schmidt t\<close> and \<open>hilbert_schmidt u\<close>
  for t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (e).
     We use a different proof than Conway: Our proof of \<open>trace_class_plus\<close> below was easy to adapt to Hilbert-Schmidt operators,
     so we adapted that one. However, Conway's proof would most likely work as well, and possible additionally
     allow us to weaken the sort of \<^typ>\<open>'b\<close> to \<^class>\<open>complex_inner\<close>.\<close>
proof -
  define II :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>II = cblinfun_left + cblinfun_right\<close>
  define JJ :: \<open>('b\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>JJ = cblinfun_left* + cblinfun_right*\<close>
  define t2 u2 where \<open>t2 = t* o\<^sub>C\<^sub>L t\<close> and \<open>u2 = u* o\<^sub>C\<^sub>L u\<close>
  define tu :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'b)\<close> where \<open>tu = (cblinfun_left o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  define tu2 :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>tu2 = (cblinfun_left o\<^sub>C\<^sub>L t2 o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u2 o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  have t_plus_u: \<open>t + u = JJ o\<^sub>C\<^sub>L tu o\<^sub>C\<^sub>L II\<close>
    apply (simp add: II_def JJ_def tu_def cblinfun_compose_add_left cblinfun_compose_add_right cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  have tu_tu2: \<open>tu* o\<^sub>C\<^sub>L tu = tu2\<close>
    by (simp add: tu_def tu2_def t2_def u2_def cblinfun_compose_add_left 
        cblinfun_compose_add_right cblinfun_compose_assoc adj_plus
        isometryD[THEN simp_a_oCL_b] cblinfun_right_left_ortho[THEN simp_a_oCL_b]
        cblinfun_left_right_ortho[THEN simp_a_oCL_b])
  have \<open>trace_class tu2\<close>
  proof (rule trace_classI)
    define BL BR B :: \<open>('a\<times>'a) set\<close> where \<open>BL = some_chilbert_basis \<times> {0}\<close>
      and \<open>BR = {0} \<times> some_chilbert_basis\<close>
      and \<open>B = BL \<union> BR\<close>
    have \<open>BL \<inter> BR = {}\<close>
      using is_ortho_set_some_chilbert_basis
      by (auto simp: BL_def BR_def is_ortho_set_def)
    show \<open>is_onb B\<close>
      by (simp add: BL_def BR_def B_def is_onb_prod)
    have \<open>tu2 \<ge> 0\<close>
      by (auto intro!: positive_cblinfunI simp: t2_def u2_def cinner_adj_right tu2_def cblinfun.add_left cinner_pos_if_pos)
    then have abs_tu2: \<open>abs_op tu2 = tu2\<close>
      by (metis abs_opI)
    have abs_t2: \<open>abs_op t2 = t2\<close>
      by (metis abs_opI positive_cblinfun_squareI t2_def)
    have abs_u2: \<open>abs_op u2 = u2\<close>
      by (metis abs_opI positive_cblinfun_squareI u2_def)

    from that(1)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op t2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: hilbert_schmidt_def t2_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
    then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (t2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: abs_t2)
    then have sum_BL: \<open>(\<lambda>x. x \<bullet>\<^sub>C (tu2 *\<^sub>V x)) abs_summable_on BL\<close>
      apply (subst asm_rl[of \<open>BL = (\<lambda>x. (x,0)) ` some_chilbert_basis\<close>])
      by (auto simp: BL_def summable_on_reindex inj_on_def o_def tu2_def cblinfun.add_left)
    from that(2)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op u2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: hilbert_schmidt_def u2_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
    then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (u2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: abs_u2)
    then have sum_BR: \<open>(\<lambda>x. x \<bullet>\<^sub>C (tu2 *\<^sub>V x)) abs_summable_on BR\<close>
      apply (subst asm_rl[of \<open>BR = (\<lambda>x. (0,x)) ` some_chilbert_basis\<close>])
      by (auto simp: BR_def summable_on_reindex inj_on_def o_def tu2_def cblinfun.add_left)
    from sum_BL sum_BR
    show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu2 *\<^sub>V x)) abs_summable_on B\<close>
      using \<open>BL \<inter> BR = {}\<close>
      by (auto intro!: summable_on_Un_disjoint simp: B_def abs_tu2)
  qed
  then have \<open>hilbert_schmidt tu\<close>
    by (auto simp flip: tu_tu2 intro!: hilbert_schmidtI)
  with t_plus_u
  show \<open>hilbert_schmidt (t + u)\<close>
    by (auto intro: hilbert_schmidt_comp_left hilbert_schmidt_comp_right)
qed

lemma hilbert_schmidt_minus: \<open>hilbert_schmidt (a - b)\<close> if \<open>hilbert_schmidt a\<close> and \<open>hilbert_schmidt b\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using hilbert_schmidt_plus hilbert_schmidt_uminus that(1) that(2) by fastforce

typedef (overloaded) ('a::chilbert_space,'b::complex_inner) hilbert_schmidt = \<open>Collect hilbert_schmidt :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_hilbert_schmidt

instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) 
  "{zero,scaleC,uminus,plus,minus,dist_norm,sgn_div_norm,uniformity_dist,open_uniformity}" begin
lift_definition zero_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt\<close> is 0 by auto
lift_definition norm_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> real\<close> is hilbert_schmidt_norm .
lift_definition scaleC_hilbert_schmidt :: \<open>complex \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is scaleC
  by (simp add: hilbert_schmidt_scaleC)
lift_definition scaleR_hilbert_schmidt :: \<open>real \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is scaleR
  by (simp add: hilbert_schmidt_scaleR)
lift_definition uminus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is uminus
  by (simp add: hilbert_schmidt_uminus)
lift_definition minus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is minus
  by (simp add: hilbert_schmidt_minus)
lift_definition plus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is plus
  by (simp add: hilbert_schmidt_plus)
definition \<open>dist a b = norm (a - b)\<close> for a b :: \<open>('a,'b) hilbert_schmidt\<close>
definition \<open>sgn x = inverse (norm x) *\<^sub>R x\<close> for x :: \<open>('a,'b) hilbert_schmidt\<close>
definition \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) hilbert_schmidt, y). dist x y < e})\<close>
definition \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) hilbert_schmidt set\<close>
instance
proof intro_classes
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: ('a,'b) hilbert_schmidt \<Rightarrow> _)\<close> for r :: real
    apply (rule ext)
    apply transfer
    by (auto simp: scaleR_scaleC)
  show \<open>dist x y = norm (x - y)\<close> for x y :: \<open>('a,'b) hilbert_schmidt\<close>
    by (simp add: dist_hilbert_schmidt_def)
  show \<open>sgn x = inverse (norm x) *\<^sub>R x\<close> for x :: \<open>('a,'b) hilbert_schmidt\<close>
    by (simp add: Trace_Class.sgn_hilbert_schmidt_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) hilbert_schmidt, y). dist x y < e})\<close>
    using Trace_Class.uniformity_hilbert_schmidt_def by blast
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) hilbert_schmidt set\<close>
    by (simp add: uniformity_hilbert_schmidt_def open_hilbert_schmidt_def dist_hilbert_schmidt_def)
qed
end

lift_definition hs_compose :: \<open>('b::chilbert_space,'c::complex_inner) hilbert_schmidt 
                               \<Rightarrow> ('a::chilbert_space,'b) hilbert_schmidt \<Rightarrow> ('a,'c) hilbert_schmidt\<close> is
    cblinfun_compose
  by (simp add: hilbert_schmidt_comp_right)

lemma
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, 18.8 Proposition\<close>
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  shows trace_class_iff_sqrt_hs: \<open>trace_class A \<longleftrightarrow> hilbert_schmidt (sqrt_op (abs_op A))\<close> (is ?thesis1)
    and trace_class_iff_hs_times_hs: \<open>trace_class A \<longleftrightarrow> (\<exists>B (C::'a\<Rightarrow>\<^sub>C\<^sub>L'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C)\<close> (is ?thesis2)
    and trace_class_iff_abs_hs_times_hs: \<open>trace_class A \<longleftrightarrow> (\<exists>B (C::'a\<Rightarrow>\<^sub>C\<^sub>L'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C)\<close> (is ?thesis3)
proof -
  define Sq W where \<open>Sq = sqrt_op (abs_op A)\<close> and \<open>W = polar_decomposition A\<close>
  have trace_class_sqrt_hs: \<open>hilbert_schmidt Sq\<close> if \<open>trace_class A\<close>
  proof (rule hilbert_schmidtI)
    from that
    have \<open>trace_class (abs_op A)\<close>
      by simp
    then show \<open>trace_class (Sq* o\<^sub>C\<^sub>L Sq)\<close>
      by (auto simp: Sq_def positive_hermitianI)
  qed
  have sqrt_hs_hs_times_hs: \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C\<close>
    if \<open>hilbert_schmidt Sq\<close>
  proof -
    have \<open>A = W o\<^sub>C\<^sub>L abs_op A\<close>
      by (simp add: polar_decomposition_correct W_def)
    also have \<open>\<dots> = (W o\<^sub>C\<^sub>L Sq) o\<^sub>C\<^sub>L Sq\<close>
      by (metis Sq_def abs_op_pos cblinfun_compose_assoc positive_hermitianI sqrt_op_pos sqrt_op_square)
    finally have \<open>A = (W o\<^sub>C\<^sub>L Sq) o\<^sub>C\<^sub>L Sq\<close>
      by -
    then show ?thesis
      apply (rule_tac exI[of _ \<open>W o\<^sub>C\<^sub>L Sq\<close>], rule_tac exI[of _ Sq])
      using that by (auto simp add: hilbert_schmidt_comp_right)
  qed
  have hs_times_hs_abs_hs_times_hs: \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C\<close>
    if \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C\<close>
  proof -
    from that obtain B and C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and ABC: \<open>A = B o\<^sub>C\<^sub>L C\<close>
      by auto
    from \<open>hilbert_schmidt B\<close>
    have hs_WB: \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
      by (simp add: hilbert_schmidt_comp_right)
    have \<open>abs_op A = W* o\<^sub>C\<^sub>L A\<close>
      by (simp add: W_def polar_decomposition_correct')
    also have \<open>\<dots> = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
      by (metis ABC cblinfun_compose_assoc)
    finally have \<open>abs_op A = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
      by -
    with hs_WB \<open>hilbert_schmidt C\<close>
    show ?thesis
      by auto
  qed
  have abs_hs_times_hs_trace_class: \<open>trace_class A\<close>
    if \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C\<close>
  proof -
    from that obtain B and C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and ABC: \<open>abs_op A = B o\<^sub>C\<^sub>L C\<close>
      by auto
    from \<open>hilbert_schmidt B\<close>
    have \<open>hilbert_schmidt (B*)\<close>
      by simp
    then have \<open>(\<lambda>e. (norm (B* *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
    moreover 
    from \<open>hilbert_schmidt C\<close>
    have \<open>(\<lambda>e. (norm (C *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
    ultimately have \<open>(\<lambda>e. norm (B* *\<^sub>V e) * norm (C *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
      apply (rule_tac abs_summable_product)
      by (metis (no_types, lifting) power2_eq_square summable_on_cong)+
    then have \<open>(\<lambda>e. cinner e (abs_op A *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    proof (rule Infinite_Sum.abs_summable_on_comparison_test)
      fix e :: 'a assume \<open>e \<in> some_chilbert_basis\<close>
      have \<open>norm (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = norm ((B* *\<^sub>V e) \<bullet>\<^sub>C (C *\<^sub>V e))\<close>
        by (simp add: ABC cinner_adj_left)
      also have \<open>\<dots> \<le> norm (B* *\<^sub>V e) * norm (C *\<^sub>V e)\<close>
        by (rule Cauchy_Schwarz_ineq2)
      also have \<open>\<dots> = norm (norm (B* *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
        by simp
      finally show \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) \<le> norm (norm (B* *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
        by -
    qed
    then show \<open>trace_class A\<close>
      apply (rule trace_classI[rotated]) by simp
  qed
  from trace_class_sqrt_hs sqrt_hs_hs_times_hs hs_times_hs_abs_hs_times_hs abs_hs_times_hs_trace_class
  show ?thesis1 and ?thesis2 and ?thesis3
    unfolding Sq_def by metis+
qed


lemma trace_exists:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.9\<close>
  assumes \<open>is_onb B\<close> and \<open>trace_class A\<close>
  shows \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) summable_on B\<close>
proof -
  obtain b c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt b\<close> \<open>hilbert_schmidt c\<close> and Abc: \<open>A = c* o\<^sub>C\<^sub>L b\<close>
    by (metis abs_op_pos adj_cblinfun_compose assms(2) double_adj hilbert_schmidt_comp_left hilbert_schmidt_comp_right polar_decomposition_correct polar_decomposition_correct' positive_hermitianI trace_class_iff_hs_times_hs)


  have \<open>(\<lambda>e. (norm (b *\<^sub>V e))\<^sup>2) summable_on B\<close>
    using \<open>hilbert_schmidt b\<close> assms(1) summable_hilbert_schmidt_norm_square by auto
  moreover have \<open>(\<lambda>e. (norm (c *\<^sub>V e))\<^sup>2) summable_on B\<close>
    using \<open>hilbert_schmidt c\<close> assms(1) summable_hilbert_schmidt_norm_square by auto
  ultimately have \<open>(\<lambda>e. (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2)) / 2) summable_on B\<close>
    by (auto intro!: summable_on_cdivide summable_on_add)

  then have \<open>(\<lambda>e. (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2)) / 2) abs_summable_on B\<close>
    by simp

  then have \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) abs_summable_on B\<close>
  proof (rule abs_summable_on_comparison_test)
    fix e assume \<open>e \<in> B\<close>
    obtain \<gamma> where \<open>cmod \<gamma> = 1\<close> and \<gamma>: \<open>\<gamma> * ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)) = abs ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e))\<close>
      apply atomize_elim
      apply (cases \<open>(b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e) \<noteq> 0\<close>)
       apply (rule exI[of _ \<open>cnj (sgn ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)))\<close>])
       apply (auto simp add: norm_sgn intro!: norm_one)
      by (metis (no_types, lifting) abs_mult_sgn cblinfun.scaleC_right cblinfun_mult_right.rep_eq cdot_square_norm complex_norm_square complex_scaleC_def mult.comm_neutral norm_one norm_sgn one_cinner_one)

    have \<open>cmod (e \<bullet>\<^sub>C (A *\<^sub>V e)) = Re (abs (e \<bullet>\<^sub>C (A *\<^sub>V e)))\<close>
      by (metis abs_nn cmod_Re norm_abs)
    also have \<open>\<dots> = Re (abs ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)))\<close>
      by (metis (mono_tags, lifting) Abc abs_nn cblinfun_apply_cblinfun_compose cinner_adj_left cinner_commute' complex_mod_cnj complex_of_real_cmod norm_abs)
    also have \<open>\<dots> = Re (((b *\<^sub>V e) \<bullet>\<^sub>C (\<gamma> *\<^sub>C (c *\<^sub>V e))))\<close>
      by (simp add: \<gamma>)
    also have \<open>\<dots> \<le> ((norm (b *\<^sub>V e))\<^sup>2 + (norm (\<gamma> *\<^sub>C (c *\<^sub>V e)))\<^sup>2) / 2\<close>
      by (smt (z3) field_sum_of_halves norm_ge_zero polar_identity_minus zero_le_power_eq_numeral)
    also have \<open>\<dots> = ((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2\<close>
      by (simp add: \<open>cmod \<gamma> = 1\<close>)
    also have \<open>\<dots> \<le> norm (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2)\<close>
      by simp
    finally show \<open>cmod (e \<bullet>\<^sub>C (A *\<^sub>V e)) \<le> norm (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2)\<close>
      by -
  qed

  then show ?thesis
    by (metis abs_summable_summable)
    
qed


lemma trace_plus_prelim: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close> \<open>trace_class (a+b)\<close>
    \<comment> \<open>We will later strengthen this as \<open>trace_plus\<close> and then hide this fact.\<close>
  shows \<open>trace (a + b) = trace a + trace b\<close>
  by (auto simp add: assms infsum_add trace_def cblinfun.add_left cinner_add_right
      intro!: infsum_add trace_exists)

lemma hs_times_hs_trace_class: 
  fixes B :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and C :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close>
  shows \<open>trace_class (B o\<^sub>C\<^sub>L C)\<close>
  \<comment> \<open>Not an immediate consequence of @{thm [source] trace_class_iff_hs_times_hs} because here the types of \<^term>\<open>B\<close>, \<^term>\<open>C\<close> are more general.\<close>
proof -
  define A Sq W where \<open>A = B o\<^sub>C\<^sub>L C\<close> and \<open>Sq = sqrt_op (abs_op A)\<close> and \<open>W = polar_decomposition A\<close>

  from \<open>hilbert_schmidt B\<close>
  have hs_WB: \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
    by (simp add: hilbert_schmidt_comp_right)
  have \<open>abs_op A = W* o\<^sub>C\<^sub>L A\<close>
    by (simp add: W_def polar_decomposition_correct')
  also have \<open>\<dots> = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
    by (metis A_def cblinfun_compose_assoc)
  finally have abs_op_A: \<open>abs_op A = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
    by -
  from \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
  have \<open>hilbert_schmidt (B* o\<^sub>C\<^sub>L W)\<close>
    by (simp add: assms(1) hilbert_schmidt_comp_left)
  then have \<open>(\<lambda>e. (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
  moreover from \<open>hilbert_schmidt C\<close>
  have \<open>(\<lambda>e. (norm (C *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
  ultimately have \<open>(\<lambda>e. norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    apply (rule_tac abs_summable_product)
    by (metis (no_types, lifting) power2_eq_square summable_on_cong)+
  then have \<open>(\<lambda>e. cinner e (abs_op A *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
  proof (rule Infinite_Sum.abs_summable_on_comparison_test)
    fix e :: 'a assume \<open>e \<in> some_chilbert_basis\<close>
    have \<open>norm (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = norm (((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) \<bullet>\<^sub>C (C *\<^sub>V e))\<close>
      by (simp add: abs_op_A cinner_adj_left cinner_adj_right)
    also have \<open>\<dots> \<le> norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e)\<close>
      by (rule Cauchy_Schwarz_ineq2)
    also have \<open>\<dots> = norm (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
      by simp
    finally show \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) \<le> norm (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
      by -
  qed
  then show \<open>trace_class A\<close>
    apply (rule trace_classI[rotated]) by simp
qed

instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) complex_vector begin
instance
proof intro_classes
  fix a b c :: \<open>('a,'b) hilbert_schmidt\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show \<open>r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b\<close> for r :: complex
    apply transfer
    using scaleC_add_right 
    by auto
  show \<open>(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a\<close> for r r' :: complex
    apply transfer
    by (simp add: scaleC_add_left)
  show \<open>r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a\<close> for r r'
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
qed
end (* instantiation hilbert_schmidt :: complex_vector *)


instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) "complex_inner" begin
lift_definition cinner_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> complex\<close> is
  \<open>\<lambda>b c. trace (b* o\<^sub>C\<^sub>L c)\<close> .
instance
proof intro_classes
  fix x y z :: \<open>('a,'b) hilbert_schmidt\<close>
  show \<open>x \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)\<close>
  proof (transfer; simp)
    fix x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume hs_xy: \<open>hilbert_schmidt x\<close> \<open>hilbert_schmidt y\<close>
    then have tc: \<open>trace_class ((y* o\<^sub>C\<^sub>L x)*)\<close> \<open>trace_class (y* o\<^sub>C\<^sub>L x)\<close>
      by (auto intro!: hs_times_hs_trace_class)
    have \<open>trace (x* o\<^sub>C\<^sub>L y) = trace ((y* o\<^sub>C\<^sub>L x)*)\<close>
      by simp
    also have \<open>\<dots> = cnj (trace (y* o\<^sub>C\<^sub>L x))\<close>
      using tc trace_adj_prelim by blast
    finally show \<open>trace (x* o\<^sub>C\<^sub>L y) = cnj (trace (y* o\<^sub>C\<^sub>L x))\<close>
      by -
  qed
  show \<open>(x + y) \<bullet>\<^sub>C z = x \<bullet>\<^sub>C z + y \<bullet>\<^sub>C z\<close>
  proof (transfer; simp) 
    fix x y z :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume [simp]: \<open>hilbert_schmidt x\<close> \<open>hilbert_schmidt y\<close> \<open>hilbert_schmidt z\<close>
    have [simp]: \<open>trace_class ((x + y)* o\<^sub>C\<^sub>L z)\<close> \<open>trace_class (x* o\<^sub>C\<^sub>L z)\<close> \<open>trace_class (y* o\<^sub>C\<^sub>L z)\<close>
      by (auto intro!: hs_times_hs_trace_class hilbert_schmidt_adj hilbert_schmidt_plus)
    then have [simp]: \<open>trace_class ((x* o\<^sub>C\<^sub>L z) + (y* o\<^sub>C\<^sub>L z))\<close>
      by (simp add: adj_plus cblinfun_compose_add_left)
    show \<open>trace ((x + y)* o\<^sub>C\<^sub>L z) = trace (x* o\<^sub>C\<^sub>L z) + trace (y* o\<^sub>C\<^sub>L z)\<close>
      by (simp add: trace_plus_prelim adj_plus cblinfun_compose_add_left hs_times_hs_trace_class)
  qed
  show \<open>r *\<^sub>C x \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)\<close> for r
    apply transfer 
    by (simp add: trace_scaleC)
  show \<open>0 \<le> x \<bullet>\<^sub>C x\<close>
    apply transfer
    by (simp add: positive_cblinfun_squareI trace_pos)
  show \<open>(x \<bullet>\<^sub>C x = 0) = (x = 0)\<close>
  proof (transfer; simp)
    fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume [simp]: \<open>hilbert_schmidt x\<close>
    have \<open>trace (x* o\<^sub>C\<^sub>L x) = 0 \<longleftrightarrow> trace (abs_op (x* o\<^sub>C\<^sub>L x)) = 0\<close>
      by (metis abs_op_def positive_cblinfun_squareI sqrt_op_unique)
    also have \<open>\<dots> \<longleftrightarrow> trace_norm (x* o\<^sub>C\<^sub>L x) = 0\<close>
      by simp
    also have \<open>\<dots> \<longleftrightarrow> x* o\<^sub>C\<^sub>L x = 0\<close>
      by (metis \<open>hilbert_schmidt x\<close> hilbert_schmidt_def trace_norm_0 trace_norm_nondegenerate)
    also have \<open>\<dots> \<longleftrightarrow> x = 0\<close>
      using cblinfun_compose_zero_right op_square_nondegenerate by blast
    finally show \<open>trace (x* o\<^sub>C\<^sub>L x) = 0 \<longleftrightarrow> x = 0\<close>
      by -
  qed
  show \<open>norm x = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
    apply transfer
    apply (auto simp: hilbert_schmidt_norm_def)
    by (metis Re_complex_of_real cmod_Re positive_cblinfun_squareI trace_norm_pos trace_pos)
qed
end

lemma hilbert_schmidt_norm_triangle_ineq:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (e). We do not use their proof but get it as a
  simple corollary of the instantiation of \<open>hilbert_schmidt\<close> as a inner product space.
  The proof by Conway would probably allow us to weaken the sort of \<^typ>\<open>'b\<close> to \<^class>\<open>complex_inner\<close>.\<close>
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>hilbert_schmidt a\<close> \<open>hilbert_schmidt b\<close>
  shows \<open>hilbert_schmidt_norm (a + b) \<le> hilbert_schmidt_norm a + hilbert_schmidt_norm b\<close>
proof -
  define a' b' where \<open>a' = Abs_hilbert_schmidt a\<close> and \<open>b' = Abs_hilbert_schmidt b\<close>
  have [transfer_rule]: \<open>cr_hilbert_schmidt a a'\<close>
    by (simp add: Abs_hilbert_schmidt_inverse a'_def assms(1) cr_hilbert_schmidt_def)
  have [transfer_rule]: \<open>cr_hilbert_schmidt b b'\<close>
    by (simp add: Abs_hilbert_schmidt_inverse assms(2) b'_def cr_hilbert_schmidt_def)
  have \<open>norm (a' + b') \<le> norm a' + norm b'\<close>
    by (rule norm_triangle_ineq)
  then show ?thesis
    apply transfer
    by -
qed

lift_definition adj_hs :: \<open>('a::chilbert_space,'b::chilbert_space) hilbert_schmidt \<Rightarrow> ('b,'a) hilbert_schmidt\<close> is adj
  by auto

lemma adj_hs_plus: \<open>adj_hs (x + y) = adj_hs x + adj_hs y\<close>
  apply transfer 
  by (simp add: adj_plus)

lemma adj_hs_minus: \<open>adj_hs (x - y) = adj_hs x - adj_hs y\<close>
  apply transfer 
  by (simp add: adj_minus)

lemma norm_adj_hs[simp]: \<open>norm (adj_hs x) = norm x\<close>
  apply transfer
  by simp


subsection \<open>Trace-norm and trace-class, continued\<close>

lemma trace_class_comp_left: \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class a\<close> for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  from \<open>trace_class a\<close>
  obtain C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and B where \<open>hilbert_schmidt C\<close> and \<open>hilbert_schmidt B\<close> and aCB: \<open>a = C o\<^sub>C\<^sub>L B\<close>
    by (auto simp: trace_class_iff_hs_times_hs)
  from \<open>hilbert_schmidt B\<close> have \<open>hilbert_schmidt (B o\<^sub>C\<^sub>L b)\<close>
    by (simp add: hilbert_schmidt_comp_left)
  with \<open>hilbert_schmidt C\<close> have \<open>trace_class (C o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b))\<close>
    using hs_times_hs_trace_class by blast
  then show ?thesis
    by (simp flip: aCB cblinfun_compose_assoc) 
qed

lemma trace_class_comp_right: \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class b\<close> for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  from \<open>trace_class b\<close>
  obtain C :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and B where \<open>hilbert_schmidt C\<close> and \<open>hilbert_schmidt B\<close> and aCB: \<open>b = C o\<^sub>C\<^sub>L B\<close>
    by (auto simp: trace_class_iff_hs_times_hs)
  from \<open>hilbert_schmidt C\<close> have \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L C)\<close>
    by (simp add: hilbert_schmidt_comp_right)
  with \<open>hilbert_schmidt B\<close> have \<open>trace_class ((a o\<^sub>C\<^sub>L C) o\<^sub>C\<^sub>L B)\<close>
    using hs_times_hs_trace_class by blast
  then show ?thesis
    by (simp flip: aCB add: cblinfun_compose_assoc) 
qed

lemma 
  fixes B :: \<open>'a::chilbert_space set\<close> and A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and c :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> 
  shows trace_alt_def:
    \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.9\<close>
    \<open>is_onb B \<Longrightarrow> trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
    and trace_hs_times_hs: \<open>hilbert_schmidt c \<Longrightarrow> hilbert_schmidt b \<Longrightarrow> trace (c o\<^sub>C\<^sub>L b) = 
          ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
                      \<i> * (of_real (hilbert_schmidt_norm (((c*) + \<i> *\<^sub>C b))))\<^sup>2 +
                      \<i> * (of_real (hilbert_schmidt_norm (((c*) - \<i> *\<^sub>C b))))\<^sup>2) / 4\<close>
proof -
  have ecbe_has_sum: \<open>((\<lambda>e. e \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L b) *\<^sub>V e)) has_sum
          ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4) B\<close>
    if \<open>is_onb B\<close> and \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close> for B :: \<open>'y::chilbert_space set\<close> and c :: \<open>'x::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'y\<close> and b
    apply (simp flip: cinner_adj_left[of c])
    apply (subst cdot_norm)
    using that by (auto simp add: field_class.field_divide_inverse infsum_cmult_left'
        simp del: Num.inverse_eq_divide_numeral
        simp flip: cblinfun.add_left cblinfun.diff_left cblinfun.scaleC_left of_real_power
        intro!: has_sum_cmult_left has_sum_cmult_right has_sum_add has_sum_diff has_sum_of_real
        has_sum_hilbert_schmidt_norm_square hilbert_schmidt_plus hilbert_schmidt_minus hilbert_schmidt_scaleC)

  then have ecbe_infsum: \<open>(\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L b) *\<^sub>V e)) =
          (((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4)\<close>
    if \<open>is_onb B\<close> and \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close> for B :: \<open>'y::chilbert_space set\<close> and c :: \<open>'x::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'y\<close> and b
    using infsumI that(1) that(2) that(3) by blast

  show \<open>trace (c o\<^sub>C\<^sub>L b) = 
        ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4\<close>
    if \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close>
  proof -
    from that have tc_cb[simp]: \<open>trace_class (c o\<^sub>C\<^sub>L b)\<close>
      by (rule hs_times_hs_trace_class)
    show ?thesis
      using ecbe_infsum[OF is_onb_some_chilbert_basis \<open>hilbert_schmidt c\<close> \<open>hilbert_schmidt b\<close>]
      apply (simp only: trace_def)
      by simp
  qed

  show \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close> if \<open>is_onb B\<close>
  proof (cases \<open>trace_class A\<close>)
    case True
    with that
    obtain b c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where hs_b: \<open>hilbert_schmidt b\<close> and hs_c: \<open>hilbert_schmidt c\<close> and Acb: \<open>A = c o\<^sub>C\<^sub>L b\<close>
      by (metis trace_class_iff_hs_times_hs)
    have [simp]: \<open>trace_class  (c o\<^sub>C\<^sub>L b)\<close>
      using Acb True by auto

    show \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
      using ecbe_infsum[OF is_onb_some_chilbert_basis hs_c hs_b]
      using ecbe_infsum[OF \<open>is_onb B\<close> hs_c hs_b]
      by (simp only: Acb trace_def)
  next
    case False
    then show ?thesis
      by (simp add: trace_def)
  qed
qed

lemma trace_ket_sum:
  fixes A :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes \<open>trace_class A\<close>
  shows \<open>trace A = (\<Sum>\<^sub>\<infinity>e. ket e \<bullet>\<^sub>C (A *\<^sub>V ket e))\<close>
  apply (subst infsum_reindex[where h=ket, unfolded o_def, symmetric])
  by (auto simp: \<open>trace_class A\<close>  trace_alt_def[OF is_onb_ket] is_onb_ket)

lemma trace_one_dim[simp]: \<open>trace A = one_dim_iso A\<close> for A :: \<open>'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof -
  have onb: \<open>is_onb {1 :: 'a}\<close>
    by auto
  have \<open>trace A = 1 \<bullet>\<^sub>C (A *\<^sub>V 1)\<close>
    apply (subst trace_alt_def)
     apply (fact onb)
    by simp
  also have \<open>\<dots> = one_dim_iso A\<close>
    by (simp add: cinner_cblinfun_def one_dim_iso_def)
  finally show ?thesis
    by -
qed


lemma trace_has_sum:
  assumes \<open>is_onb E\<close>
  assumes \<open>trace_class t\<close>
  shows \<open>((\<lambda>e. e \<bullet>\<^sub>C (t *\<^sub>V e)) has_sum trace t) E\<close>
  using assms(1) assms(2) trace_alt_def trace_exists by fastforce


lemma trace_sandwich_isometry[simp]: \<open>trace (sandwich U A) = trace A\<close> if \<open>isometry U\<close>
proof (cases \<open>trace_class A\<close>)
  case True
  note True[simp]
  have \<open>is_ortho_set ((*\<^sub>V) U ` some_chilbert_basis)\<close>
    unfolding is_ortho_set_def
    apply auto
    apply (metis (no_types, opaque_lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply cinner_adj_right is_ortho_set_def is_ortho_set_some_chilbert_basis isometry_def that)
    by (metis is_normal_some_chilbert_basis isometry_preserves_norm norm_zero that zero_neq_one)
  moreover have \<open>x \<in> (*\<^sub>V) U ` some_chilbert_basis \<Longrightarrow> norm x = 1\<close> for x
    using is_normal_some_chilbert_basis isometry_preserves_norm that by fastforce
  ultimately obtain B where BU: \<open>B \<supseteq> U ` some_chilbert_basis\<close> and \<open>is_onb B\<close>
    apply atomize_elim
    by (rule orthonormal_basis_exists)

  have xUy: \<open>x \<bullet>\<^sub>C U y = 0\<close> if xBU: \<open>x \<in> B - U ` some_chilbert_basis\<close> for x y
  proof -
    from that \<open>is_onb B\<close> \<open>isometry U\<close>
    have \<open>x \<bullet>\<^sub>C z = 0\<close> if \<open>z \<in> U ` some_chilbert_basis\<close> for z
      using that by (metis BU Diff_iff in_mono is_onb_def is_ortho_set_def)
    then have \<open>x \<in> orthogonal_complement (closure (cspan (U ` some_chilbert_basis)))\<close>
      by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_of_cspan)
    then have \<open>x \<in> space_as_set (- ccspan (U ` some_chilbert_basis))\<close>
      by (simp add: ccspan.rep_eq uminus_ccsubspace.rep_eq)
    then have \<open>x \<in> space_as_set (- (U *\<^sub>S top))\<close>
      by (metis cblinfun_image_ccspan ccspan_some_chilbert_basis)
    moreover have \<open>U y \<in> space_as_set (U *\<^sub>S top)\<close>
      by simp
    ultimately show ?thesis
      apply (transfer fixing: x y)
      using orthogonal_complement_orthoI by blast
  qed

  have [simp]: \<open>trace_class (sandwich U A)\<close>
    by (simp add: sandwich.rep_eq trace_class_comp_left trace_class_comp_right)
  have \<open>trace (sandwich U A) = (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V e))\<close>
    using \<open>is_onb B\<close> trace_alt_def by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>U ` some_chilbert_basis. e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V e))\<close>
    apply (rule infsum_cong_neutral)
    using BU xUy by (auto simp: sandwich_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. U e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V U e))\<close>
    apply (subst infsum_reindex)
    apply (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply inj_on_inverseI isometry_def that)
    by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C A e)\<close>
    apply (rule infsum_cong)
    apply (simp add: sandwich_apply flip: cinner_adj_right)
    by (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply isometry_def that)
  also have \<open>\<dots> = trace A\<close>
    by (simp add: trace_def)
  finally show ?thesis
    by -
next
  case False
  note False[simp]
  then have [simp]: \<open>\<not> trace_class (sandwich U A)\<close>
    by (smt (verit, ccfv_SIG) cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right isometryD sandwich.rep_eq that trace_class_comp_left trace_class_comp_right)
  show ?thesis
    by (simp add: trace_def)
qed

lemma circularity_of_trace:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    \<comment> \<open>The proof from \<^cite>\<open>conway00operator\<close> only work for square operators, we generalize it\<close>
  assumes \<open>trace_class a\<close>
    \<comment> \<open>Actually, \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b) \<and> trace_class (b o\<^sub>C\<^sub>L a)\<close> is sufficient here,
        see @{cite "mathoverflow-circ-trace2"} but the proof is more involved.
        Only \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> is not sufficient, 
        see @{cite "mathoverflow-circ-trace1"}.\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
proof -
  (* We first make a and b into square operators by padding them because for those the circularity of the trace is easier. *)
  define a' b' :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close> 
    where \<open>a' = cblinfun_right o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L cblinfun_left*\<close>
      and \<open>b' = cblinfun_left o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L cblinfun_right*\<close>

  have \<open>trace_class a'\<close>
    by (simp add: a'_def assms trace_class_comp_left trace_class_comp_right)

  (* Circularity of the trace for square operators *)
  have circ': \<open>trace (a' o\<^sub>C\<^sub>L b') = trace (b' o\<^sub>C\<^sub>L a')\<close>
  proof -
    from \<open>trace_class a'\<close>
    obtain B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and aCB: \<open>a' = C* o\<^sub>C\<^sub>L B\<close>
      by (metis abs_op_pos adj_cblinfun_compose double_adj hilbert_schmidt_comp_left hilbert_schmidt_comp_right polar_decomposition_correct polar_decomposition_correct' positive_hermitianI trace_class_iff_hs_times_hs)
    have hs_iB: \<open>hilbert_schmidt (\<i> *\<^sub>C B)\<close>
      by (metis Abs_hilbert_schmidt_inverse Rep_hilbert_schmidt \<open>hilbert_schmidt B\<close> mem_Collect_eq scaleC_hilbert_schmidt.rep_eq)
    have *: \<open>Re (trace (C* o\<^sub>C\<^sub>L B)) = Re (trace (C o\<^sub>C\<^sub>L B*))\<close> if \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> for B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close>
    proof -
      from that
      obtain B' C' where \<open>B = Rep_hilbert_schmidt B'\<close> and \<open>C = Rep_hilbert_schmidt C'\<close>
        by (meson Rep_hilbert_schmidt_cases mem_Collect_eq)
      then have [transfer_rule]: \<open>cr_hilbert_schmidt B B'\<close> \<open>cr_hilbert_schmidt C C'\<close>
        by (simp_all add: cr_hilbert_schmidt_def)
  
      have \<open>Re (trace (C* o\<^sub>C\<^sub>L B)) = Re (C' \<bullet>\<^sub>C B')\<close>
        apply transfer by simp
      also have \<open>\<dots> = (1/4) * ((norm (C' + B'))\<^sup>2 - (norm (C' - B'))\<^sup>2)\<close>
        by (simp add: cdot_norm)
      also have \<open>\<dots> = (1/4) * ((norm (adj_hs C' + adj_hs B'))\<^sup>2 - (norm (adj_hs C' - adj_hs B'))\<^sup>2)\<close>
        by (simp add: flip: adj_hs_plus adj_hs_minus)
      also have \<open>\<dots> = Re (adj_hs C' \<bullet>\<^sub>C adj_hs B')\<close>
        by (simp add: cdot_norm)
      also have \<open>\<dots> = Re (trace (C o\<^sub>C\<^sub>L B*))\<close>
        apply transfer by simp
      finally show ?thesis
        by -
    qed
    have **: \<open>trace (C* o\<^sub>C\<^sub>L B) = cnj (trace (C o\<^sub>C\<^sub>L B*))\<close> if \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> for B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close>
      using *[OF \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close>]
      using *[OF hilbert_schmidt_scaleC[of _ \<i>, OF \<open>hilbert_schmidt B\<close>] \<open>hilbert_schmidt C\<close>]
      apply (auto simp: trace_scaleC cblinfun_compose_uminus_right trace_uminus)
      by (smt (verit, best) cnj.code complex.collapse)
  
    have \<open>trace (b' o\<^sub>C\<^sub>L a') = trace ((b' o\<^sub>C\<^sub>L C*) o\<^sub>C\<^sub>L B)\<close>
      by (simp add: aCB cblinfun_assoc_left(1))
    also from ** \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> have \<open>\<dots> = cnj (trace ((C o\<^sub>C\<^sub>L b'*) o\<^sub>C\<^sub>L B*))\<close>
      by (metis adj_cblinfun_compose double_adj hilbert_schmidt_comp_left)
    also have \<open>\<dots> = cnj (trace (C o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b')*))\<close>
      by (simp add: cblinfun_assoc_left(1))
    also  from ** \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> have \<open>\<dots> = trace (C* o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b'))\<close>
      by (simp add: hilbert_schmidt_comp_left)
    also have \<open>\<dots> = trace (a' o\<^sub>C\<^sub>L b')\<close>
      by (simp add: aCB cblinfun_compose_assoc)
    finally show ?thesis
      by simp
  qed

  have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (sandwich cblinfun_right (a o\<^sub>C\<^sub>L b) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (sandwich cblinfun_right (a o\<^sub>C\<^sub>L (cblinfun_left* o\<^sub>C\<^sub>L (cblinfun_left :: _\<Rightarrow>\<^sub>C\<^sub>L('a\<times>'b))) o\<^sub>C\<^sub>L b) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (a' o\<^sub>C\<^sub>L b')\<close>
    by (simp only: a'_def b'_def sandwich_apply cblinfun_compose_assoc)
  also have \<open>\<dots> = trace (b' o\<^sub>C\<^sub>L a')\<close>
    by (rule circ')
  also have \<open>\<dots> = trace (sandwich cblinfun_left (b o\<^sub>C\<^sub>L (cblinfun_right* o\<^sub>C\<^sub>L (cblinfun_right :: _\<Rightarrow>\<^sub>C\<^sub>L('a\<times>'b))) o\<^sub>C\<^sub>L a) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by (simp only: a'_def b'_def sandwich_apply cblinfun_compose_assoc)
  also have \<open>\<dots> = trace (sandwich cblinfun_left (b o\<^sub>C\<^sub>L a) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (b o\<^sub>C\<^sub>L a)\<close>
    by simp
  finally show \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
    by -
qed

lemma trace_butterfly_comp: \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
proof -
  have \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = trace (vector_to_cblinfun y* o\<^sub>C\<^sub>L (a o\<^sub>C\<^sub>L (vector_to_cblinfun x :: complex \<Rightarrow>\<^sub>C\<^sub>L _)))\<close>
    unfolding butterfly_def
    by (metis cblinfun_compose_assoc circularity_of_trace trace_class_finite_dim)
  also have \<open>\<dots> = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
    by (simp add: one_dim_iso_cblinfun_comp)
  finally show ?thesis
    by -
qed

lemma trace_butterfly: \<open>trace (butterfly x y) = y \<bullet>\<^sub>C x\<close>
  using trace_butterfly_comp[where a=id_cblinfun] by auto

lemma trace_butterfly_comp': \<open>trace (a o\<^sub>C\<^sub>L butterfly x y) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
  by (simp add: cblinfun_comp_butterfly trace_butterfly)


lemma trace_norm_adj[simp]: \<open>trace_norm (a*) = trace_norm a\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (f)\<close>
proof -
  have \<open>of_real (trace_norm (a*)) = trace (sandwich (polar_decomposition a) *\<^sub>V abs_op a)\<close>
    by (metis abs_op_adj trace_abs_op)
  also have \<open>\<dots> = trace ((polar_decomposition a)* o\<^sub>C\<^sub>L (polar_decomposition a) o\<^sub>C\<^sub>L abs_op a)\<close>
    by (metis (no_types, lifting) abs_op_adj cblinfun_compose_assoc circularity_of_trace double_adj
        polar_decomposition_correct polar_decomposition_correct' sandwich.rep_eq trace_class_abs_op trace_def)
  also have \<open>\<dots> = trace (abs_op a)\<close>
    by (simp add: cblinfun_compose_assoc polar_decomposition_correct polar_decomposition_correct')
  also have \<open>\<dots> = of_real (trace_norm a)\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma trace_class_adj[simp]: \<open>trace_class (a*)\<close> if \<open>trace_class a\<close>
proof (rule ccontr)
  assume asm: \<open>\<not> trace_class (a*)\<close>
  then have \<open>trace_norm (a*) = 0\<close>
    by (simp add: trace_norm_def)
  then have \<open>trace_norm a = 0\<close>
    by (metis trace_norm_adj)
  then have \<open>a = 0\<close>
    using that trace_norm_nondegenerate by blast
  then have \<open>trace_class (a*)\<close>
    by simp
  with asm show False
    by simp
qed

lift_definition adj_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> ('b,'a) trace_class\<close> is adj
  by simp

lift_definition selfadjoint_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> bool\<close> is selfadjoint.

lemma selfadjoint_tc_def': \<open>selfadjoint_tc a \<longleftrightarrow> adj_tc a = a\<close>
  apply transfer
  using selfadjoint_def by blast 

lemma trace_class_finite_dim'[simp]: \<open>trace_class A\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}\<close>
  by (metis double_adj trace_class_adj trace_class_finite_dim)

lemma trace_class_plus[simp]:
  fixes t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>trace_class t\<close> and \<open>trace_class u\<close>
  shows \<open>trace_class (t + u)\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a).
      However, we use a completely different proof that does not need the fact that trace class operators can be diagonalized with countably many diagonal elements.\<close>
proof -
  define II :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>II = cblinfun_left + cblinfun_right\<close>
  define JJ :: \<open>('b\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>JJ = cblinfun_left* + cblinfun_right*\<close>
  define tu :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'b)\<close> where \<open>tu = (cblinfun_left o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  have t_plus_u: \<open>t + u = JJ o\<^sub>C\<^sub>L tu o\<^sub>C\<^sub>L II\<close>
    apply (simp add: II_def JJ_def tu_def cblinfun_compose_add_left cblinfun_compose_add_right cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  have \<open>trace_class tu\<close>
  proof (rule trace_classI)
    define BL BR B :: \<open>('a\<times>'a) set\<close> where \<open>BL = some_chilbert_basis \<times> {0}\<close>
      and \<open>BR = {0} \<times> some_chilbert_basis\<close>
      and \<open>B = BL \<union> BR\<close>
    have \<open>BL \<inter> BR = {}\<close>
      using is_ortho_set_some_chilbert_basis
      by (auto simp: BL_def BR_def is_ortho_set_def)
    show \<open>is_onb B\<close>
      by (simp add: BL_def BR_def B_def is_onb_prod)
    have abs_tu: \<open>abs_op tu = (cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
      using [[show_consts]]
    proof -
      have \<open>((cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*))*
        o\<^sub>C\<^sub>L ((cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*))
        = tu* o\<^sub>C\<^sub>L tu\<close>
      proof -
        have tt[THEN simp_a_oCL_b, simp]: \<open>(abs_op t)* o\<^sub>C\<^sub>L abs_op t = t* o\<^sub>C\<^sub>L t\<close>
          by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
        have uu[THEN simp_a_oCL_b, simp]: \<open>(abs_op u)* o\<^sub>C\<^sub>L abs_op u = u* o\<^sub>C\<^sub>L u\<close>
          by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
        note isometryD[THEN simp_a_oCL_b, simp]
        note cblinfun_right_left_ortho[THEN simp_a_oCL_b, simp]
        note cblinfun_left_right_ortho[THEN simp_a_oCL_b, simp]
        show ?thesis
          using tt[of \<open>cblinfun_left* :: ('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>] uu[of \<open>cblinfun_right* :: ('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>]
          by (simp add: tu_def cblinfun_compose_add_right cblinfun_compose_add_left adj_plus
              cblinfun_compose_assoc)
      qed
      moreover have \<open>(cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*) \<ge> 0\<close>
        apply (rule positive_cblinfunI)
        by (auto simp: cblinfun.add_left cinner_pos_if_pos)
      ultimately show ?thesis
        by (rule abs_opI[symmetric])
    qed
    from assms(1)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op t *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_class_abs_op trace_exists)
    then have sum_BL: \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on BL\<close>
      apply (subst asm_rl[of \<open>BL = (\<lambda>x. (x,0)) ` some_chilbert_basis\<close>])
      by (auto simp: BL_def summable_on_reindex inj_on_def o_def abs_tu cblinfun.add_left)
    from assms(2)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op u *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_class_abs_op trace_exists)
    then have sum_BR: \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on BR\<close>
      apply (subst asm_rl[of \<open>BR = (\<lambda>x. (0,x)) ` some_chilbert_basis\<close>])
      by (auto simp: BR_def summable_on_reindex inj_on_def o_def abs_tu cblinfun.add_left)
    from sum_BL sum_BR
    show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on B\<close>
      using \<open>BL \<inter> BR = {}\<close>
      by (auto intro!: summable_on_Un_disjoint simp: B_def)
  qed
  with t_plus_u
  show \<open>trace_class (t + u)\<close>
    by (simp add: trace_class_comp_left trace_class_comp_right)
qed

lemma trace_class_minus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t - u)\<close>
  for t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis trace_class_plus trace_class_uminus uminus_add_conv_diff)

lemma trace_plus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a + b) = trace a + trace b\<close>
  by (simp add: assms(1) assms(2) trace_plus_prelim)
hide_fact trace_plus_prelim

lemma trace_class_sum:
  fixes a :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows \<open>trace_class (\<Sum>i\<in>I. a i)\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by auto

lemma
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows trace_sum: \<open>trace (\<Sum>i\<in>I. a i) = (\<Sum>i\<in>I. trace (a i))\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by (auto simp: trace_plus trace_class_sum)

lemma cmod_trace_times: \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) \<le> norm a * trace_norm b\<close> if \<open>trace_class b\<close> 
  for b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
proof -
  define W where \<open>W = polar_decomposition b\<close>

  have \<open>norm W \<le> 1\<close>
    by (metis W_def norm_partial_isometry norm_zero order_refl polar_decomposition_partial_isometry zero_less_one_class.zero_le_one)
  have hs1: \<open>hilbert_schmidt (sqrt_op (abs_op b))\<close>
    using that trace_class_iff_sqrt_hs by blast
  then have hs2: \<open>hilbert_schmidt (sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*)\<close>
    by (simp add: hilbert_schmidt_comp_left)

  from \<open>trace_class b\<close>
  have \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close>
    using trace_class_comp_right by blast
  then have sum1: \<open>(\<lambda>e. e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)

  have sum5: \<open>(\<lambda>x. (norm (sqrt_op (abs_op b) *\<^sub>V x))\<^sup>2) summable_on some_chilbert_basis\<close>
    using summable_hilbert_schmidt_norm_square[OF is_onb_some_chilbert_basis hs1]
    by (simp add: power2_eq_square)

  have sum4: \<open>(\<lambda>x. (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V x))\<^sup>2) summable_on some_chilbert_basis\<close>
    using summable_hilbert_schmidt_norm_square[OF is_onb_some_chilbert_basis hs2]
    by (simp add: power2_eq_square)

  have sum3: \<open>(\<lambda>e. norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_summable)
    apply (rule abs_summable_product)
    by (intro sum4 sum5 summable_on_iff_abs_summable_on_real[THEN iffD1])+

  have sum2: \<open>(\<lambda>e. ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) \<bullet>\<^sub>C (sqrt_op (abs_op b) *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    using sum3[THEN summable_on_iff_abs_summable_on_real[THEN iffD1]]
    apply (rule abs_summable_on_comparison_test)
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)

  from \<open>trace_class b\<close>
  have \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) = cmod (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e))\<close>
    by (simp add: trace_class_comp_right trace_def)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e)))\<close>
    using sum1 by (rule norm_infsum_bound)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) \<bullet>\<^sub>C (sqrt_op (abs_op b) *\<^sub>V e)))\<close>
    apply (simp add: positive_hermitianI flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    by (metis (full_types) W_def abs_op_def cblinfun_compose_assoc polar_decomposition_correct sqrt_op_pos sqrt_op_square)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e))\<close>
    using sum2 sum3 apply (rule infsum_mono)
    using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e)))\<close>
    by simp
  also have \<open>\<dots> \<le> sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e)))\<^sup>2) 
                * sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (norm (sqrt_op (abs_op b) *\<^sub>V e)))\<^sup>2)\<close>
    apply (rule Cauchy_Schwarz_ineq_infsum)
    using sum4 sum5 by auto
  also have \<open>\<dots> = sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e))\<^sup>2)
                * sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (sqrt_op (abs_op b) *\<^sub>V e))\<^sup>2)\<close>
    by simp
  also have \<open>\<dots> = hilbert_schmidt_norm (sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    apply (subst infsum_hilbert_schmidt_norm_square, simp, fact hs2)
    apply (subst infsum_hilbert_schmidt_norm_square, simp, fact hs1)
    by simp
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (W* o\<^sub>C\<^sub>L a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis cblinfun_assoc_left(1) hilbert_schmidt_norm_comp_left hilbert_schmidt_norm_pos mult.commute mult_right_mono that trace_class_iff_sqrt_hs)
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (W*) * norm (a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) hilbert_schmidt_norm_pos mult_right_mono norm_cblinfun_compose ordered_comm_semiring_class.comm_mult_left_mono)
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis \<open>norm W \<le> 1\<close> hilbert_schmidt_norm_pos mult.right_neutral mult_left_mono mult_right_mono norm_adj norm_ge_zero)
  also have \<open>\<dots> = norm a * (hilbert_schmidt_norm (sqrt_op (abs_op b)))\<^sup>2\<close>
    by (simp add: power2_eq_square)
  also have \<open>\<dots> = norm a * trace_norm b\<close>
    apply (simp add: hilbert_schmidt_norm_def positive_hermitianI)
    by (metis abs_op_idem of_real_eq_iff trace_abs_op)
  finally show ?thesis
    by -
qed

lemma trace_leq_trace_norm[simp]: \<open>cmod (trace a) \<le> trace_norm a\<close>
proof (cases \<open>trace_class a\<close>)
  case True
  then have \<open>cmod (trace a) \<le> norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a) * trace_norm a\<close>
    using cmod_trace_times[where a=\<open>id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and b=a]
    by simp
  also have \<open>\<dots> \<le> trace_norm a\<close>
    apply (rule mult_left_le_one_le)
    by (auto intro!: mult_left_le_one_le simp: norm_cblinfun_id_le)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis
    by (simp add: trace_def)
qed

lemma trace_norm_triangle: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a + b) \<le> trace_norm a + trace_norm b\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  define w where \<open>w = polar_decomposition (a+b)\<close>
  have \<open>norm (w*) \<le> 1\<close>
    by (metis dual_order.refl norm_adj norm_partial_isometry norm_zero polar_decomposition_partial_isometry w_def zero_less_one_class.zero_le_one)
  have \<open>trace_norm (a + b) = cmod (trace (abs_op (a+b)))\<close>
    by simp
  also have \<open>\<dots> = cmod (trace (w* o\<^sub>C\<^sub>L (a+b)))\<close>
    by (simp add: polar_decomposition_correct' w_def)
  also have \<open>\<dots> \<le> cmod (trace (w* o\<^sub>C\<^sub>L a)) + cmod (trace (w* o\<^sub>C\<^sub>L b))\<close>
    by (simp add: cblinfun_compose_add_right norm_triangle_ineq trace_class_comp_right trace_plus)
  also have \<open>\<dots> \<le> (norm (w*) * trace_norm a) + (norm (w*) * trace_norm b)\<close>
    by (smt (verit, best) assms(1) assms(2) cmod_trace_times)
  also have \<open>\<dots> \<le> trace_norm a + trace_norm b\<close>
    using \<open>norm (w*) \<le> 1\<close>
    by (smt (verit, ccfv_SIG) mult_le_cancel_right2 trace_norm_nneg)
  finally show ?thesis
    by -
qed

instantiation trace_class :: (chilbert_space, chilbert_space) "{complex_vector}" begin
(* Lifted definitions *)
lift_definition zero_trace_class :: \<open>('a,'b) trace_class\<close> is 0 by auto
lift_definition minus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is minus by auto
lift_definition uminus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is uminus by simp
lift_definition plus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is plus by auto
lift_definition scaleC_trace_class :: \<open>complex \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is scaleC
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq trace_class_comp_left)
lift_definition scaleR_trace_class :: \<open>real \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is scaleR
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq scaleR_scaleC trace_class_comp_left)
instance
proof standard
  fix a b c :: \<open>('a,'b) trace_class\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: _ \<Rightarrow> ('a,'b) trace_class)\<close> for r :: real
    by (metis (mono_tags, opaque_lifting) Trace_Class.scaleC_trace_class_def Trace_Class.scaleR_trace_class_def id_apply map_fun_def o_def scaleR_scaleC)
  show \<open>r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b\<close> for r :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_right)
  show \<open>(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a\<close> for r r' :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_left)
  show \<open>r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a\<close> for r r' :: complex
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
qed
end

lemma from_trace_class_0[simp]: \<open>from_trace_class 0 = 0\<close>
  by (simp add: zero_trace_class.rep_eq)

instantiation trace_class :: (chilbert_space, chilbert_space) "{complex_normed_vector}" begin
(* Definitions related to the trace norm *)
lift_definition norm_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> real\<close> is trace_norm .
definition sgn_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> where \<open>sgn_trace_class a = a /\<^sub>R norm a\<close>
definition dist_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> _ \<Rightarrow> _\<close> where \<open>dist_trace_class a b = norm (a - b)\<close>
definition [code del]: "uniformity_trace_class = (INF e\<in>{0<..}. principal {(x::('a,'b) trace_class, y). dist x y < e})"
definition [code del]: "open_trace_class U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "('a,'b) trace_class set"
instance
proof standard
  fix a b :: \<open>('a,'b) trace_class\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (metis (no_types, lifting) Trace_Class.dist_trace_class_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x :: ('a,'b) trace_class, y). dist x y < e})\<close>
    by (simp add: uniformity_trace_class_def)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) trace_class set\<close>
    by (smt (verit, del_insts) case_prod_beta' eventually_mono open_trace_class_def uniformity_trace_class_def)
  show \<open>(norm a = 0) = (a = 0)\<close>
    apply transfer
    by (auto simp add: trace_norm_nondegenerate)
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer
    by (auto simp: trace_norm_triangle)
  show \<open>norm (r *\<^sub>C a) = cmod r * norm a\<close> for r
    apply transfer
    by (auto simp: trace_norm_scaleC)
  then show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r
    by (metis norm_of_real scaleR_scaleC)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_trace_class_def)
qed
end






lemma trace_norm_comp_right:
  fixes a :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>trace_class b\<close>
  shows \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * trace_norm b\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (g)\<close>
proof -
  define w w1 s where \<open>w = polar_decomposition b\<close> and \<open>w1 = polar_decomposition (a o\<^sub>C\<^sub>L b)\<close>
    and \<open>s = w1* o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L w\<close>
  have abs_ab: \<open>abs_op (a o\<^sub>C\<^sub>L b) = s o\<^sub>C\<^sub>L abs_op b\<close>
    by (auto simp: w1_def w_def s_def cblinfun_compose_assoc polar_decomposition_correct polar_decomposition_correct')
  have norm_s_t: \<open>norm s \<le> norm a\<close>
  proof -
    have \<open>norm s \<le> norm (w1* o\<^sub>C\<^sub>L a) * norm w\<close>
      by (simp add: norm_cblinfun_compose s_def)
    also have \<open>\<dots> \<le> norm (w1*) * norm a * norm w\<close>
      by (metis mult.commute mult_left_mono norm_cblinfun_compose norm_ge_zero)
    also have \<open>\<dots> \<le> norm a\<close>
      by (metis (no_types, opaque_lifting) dual_order.refl mult.commute mult.right_neutral mult_zero_left norm_adj norm_ge_zero norm_partial_isometry norm_zero polar_decomposition_partial_isometry w1_def w_def)
    finally show ?thesis
      by -
  qed
  have \<open>trace_norm (a o\<^sub>C\<^sub>L b) = cmod (trace (abs_op (a o\<^sub>C\<^sub>L b)))\<close>
    by simp
  also have \<open>\<dots> = cmod (trace (s o\<^sub>C\<^sub>L abs_op b))\<close>
    using abs_ab by presburger
  also have \<open>\<dots> \<le> norm s * trace_norm (abs_op b)\<close>
    using assms by (simp add: cmod_trace_times)
  also from norm_s_t have \<open>\<dots> \<le> norm a * trace_norm b\<close>
    by (metis abs_op_idem mult_right_mono of_real_eq_iff trace_abs_op trace_norm_nneg)
  finally show ?thesis
    by -
qed

lemma trace_norm_comp_left:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (g)\<close>
  fixes a :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes [simp]: \<open>trace_class a\<close>
  shows \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
proof -
  have \<open>trace_norm (b* o\<^sub>C\<^sub>L a*) \<le> norm (b*) * trace_norm (a*)\<close>
    apply (rule trace_norm_comp_right)
    by simp
  then have \<open>trace_norm ((b* o\<^sub>C\<^sub>L a*)*) \<le> norm b * trace_norm a\<close>
    by (simp del: adj_cblinfun_compose)
  then show ?thesis
    by (simp add: mult.commute)
qed

lemma bounded_clinear_trace_duality: \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (t o\<^sub>C\<^sub>L a))\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
  apply (auto simp add: cblinfun_compose_add_right trace_class_comp_left trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

lemma trace_class_butterfly[simp]: \<open>trace_class (butterfly x y)\<close> for x :: \<open>'a::chilbert_space\<close> and y :: \<open>'b::chilbert_space\<close>
  unfolding butterfly_def
  apply (rule trace_class_comp_left)
  by simp

lemma trace_adj: \<open>trace (a*) = cnj (trace a)\<close>
  by (metis Complex_Inner_Product0.complex_inner_1_right cinner_zero_right double_adj is_onb_some_chilbert_basis is_orthogonal_sym trace_adj_prelim trace_alt_def trace_class_adj)
hide_fact trace_adj_prelim

lemma cmod_trace_times': \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) \<le> norm b * trace_norm a\<close> if \<open>trace_class a\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  apply (subst trace_adj)
  using cmod_trace_times[of \<open>a*\<close> \<open>b*\<close>]
  by (auto intro!: that trace_class_adj hilbert_schmidt_comp_right hilbert_schmidt_adj simp del: adj_cblinfun_compose)


lift_definition iso_trace_class_compact_op_dual' :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> ('b,'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex\<close> is
  \<open>\<lambda>t c. trace (from_compact_op c o\<^sub>C\<^sub>L t)\<close>
proof (rename_tac t)
  include lifting_syntax
  fix t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>t \<in> Collect trace_class\<close>
  then have [simp]: \<open>trace_class t\<close>
    by simp
  have \<open>cmod (trace (from_compact_op x o\<^sub>C\<^sub>L t)) \<le> norm x * trace_norm t\<close> for x
    by (metis \<open>trace_class t\<close> cmod_trace_times from_compact_op_norm)
  then show \<open>bounded_clinear (\<lambda>c. trace (from_compact_op c o\<^sub>C\<^sub>L t))\<close>
    apply (rule_tac bounded_clinearI[where K=\<open>trace_norm t\<close>])
    by (auto simp: from_compact_op_plus from_compact_op_scaleC cblinfun_compose_add_right
        cblinfun_compose_add_left trace_plus trace_class_comp_right trace_scaleC)
qed

lemma iso_trace_class_compact_op_dual'_apply: \<open>iso_trace_class_compact_op_dual' t c = trace (from_compact_op c o\<^sub>C\<^sub>L from_trace_class t)\<close>
  by (simp add: iso_trace_class_compact_op_dual'.rep_eq)

lemma iso_trace_class_compact_op_dual'_plus: \<open>iso_trace_class_compact_op_dual' (a + b) = iso_trace_class_compact_op_dual' a + iso_trace_class_compact_op_dual' b\<close>
  apply transfer
  by (simp add: cblinfun_compose_add_right trace_class_comp_right trace_plus)

lemma iso_trace_class_compact_op_dual'_scaleC: \<open>iso_trace_class_compact_op_dual' (c *\<^sub>C a) = c *\<^sub>C iso_trace_class_compact_op_dual' a\<close>
  apply transfer
  by (simp add: trace_scaleC)

lemma iso_trace_class_compact_op_dual'_bounded_clinear[bounded_clinear, simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 19.1\<close>
    \<open>bounded_clinear (iso_trace_class_compact_op_dual' :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>norm (?iso t) \<le> norm t\<close> for t
  proof (rule norm_cblinfun_bound)
    show \<open>norm t \<ge> 0\<close> by simp
    fix c
    show \<open>cmod (iso_trace_class_compact_op_dual' t *\<^sub>V c) \<le> norm t * norm c\<close>
      apply (transfer fixing: c)
      apply simp
      by (metis cmod_trace_times from_compact_op_norm ordered_field_class.sign_simps(5))
  qed
  then show \<open>bounded_clinear ?iso\<close>
    apply (rule_tac bounded_clinearI[where K=1])
    by (auto simp: iso_trace_class_compact_op_dual'_plus iso_trace_class_compact_op_dual'_scaleC)
qed


lemma iso_trace_class_compact_op_dual'_surjective[simp]: 
  \<open>surj (iso_trace_class_compact_op_dual' :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>\<exists>A. \<Phi> = ?iso A\<close> for \<Phi> :: \<open>('b, 'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  proof -
    define p where \<open>p x y = \<Phi> (butterfly_co y x)\<close> for x y
    have norm_p: \<open>norm (p x y) \<le> norm \<Phi> * norm x * norm y\<close> for x y
    proof -
      have \<open>norm (p x y) \<le> norm \<Phi> * norm (butterfly_co y x)\<close>
        by (auto simp: p_def norm_cblinfun)
      also have \<open>\<dots> = norm \<Phi> * norm (butterfly y x)\<close>
        apply transfer by simp
      also have \<open>\<dots> = norm \<Phi> * norm x * norm y\<close>
        by (simp add: norm_butterfly)
      finally show ?thesis
        by -
    qed
    have [simp]: \<open>bounded_sesquilinear p\<close>
      apply (rule bounded_sesquilinear.intro)
      using norm_p
      by (auto
          intro!: exI[of _ \<open>norm \<Phi>\<close>]
          simp add: p_def butterfly_co_add_left butterfly_co_add_right  complex_vector.linear_add 
          cblinfun.scaleC_right cblinfun.scaleC_left ab_semigroup_mult_class.mult_ac)
    define A where \<open>A = (the_riesz_rep_sesqui p)*\<close>
    then have xAy: \<open>x \<bullet>\<^sub>C (A y) = p x y\<close> for x y
      by (simp add: cinner_adj_right the_riesz_rep_sesqui_apply)
    have \<Phi>C: \<open>\<Phi> C = trace (from_compact_op C o\<^sub>C\<^sub>L A)\<close> if \<open>finite_rank (from_compact_op C)\<close> for C
    proof -
      from that
      obtain x y and n :: nat where C_sum: \<open>from_compact_op C = (\<Sum>i<n. butterfly (y i) (x i))\<close>
        apply atomize_elim by (rule finite_rank_sum_butterfly)
      then have \<open>C = (\<Sum>i<n. butterfly_co (y i) (x i))\<close>
        apply transfer by simp
      then have \<open>\<Phi> C = (\<Sum>i<n. \<Phi> *\<^sub>V butterfly_co (y i) (x i))\<close>
        using cblinfun.sum_right by blast
      also have \<open>\<dots> = (\<Sum>i<n. p (x i) (y i))\<close>
        using p_def by presburger
      also have \<open>\<dots> = (\<Sum>i<n. (x i) \<bullet>\<^sub>C (A (y i)))\<close>
        using xAy by presburger
      also have \<open>\<dots> = (\<Sum>i<n. trace (butterfly (y i) (x i) o\<^sub>C\<^sub>L A))\<close>
        by (simp add: trace_butterfly_comp)
      also have \<open>\<dots> = trace ((\<Sum>i<n. butterfly (y i) (x i)) o\<^sub>C\<^sub>L A)\<close>
        by (metis (mono_tags, lifting) cblinfun_compose_sum_left sum.cong trace_class_butterfly trace_class_comp_left trace_sum)
      also have \<open>\<dots> = trace (from_compact_op C o\<^sub>C\<^sub>L A)\<close>
        using C_sum by presburger
      finally show ?thesis
        by -
    qed
    have \<open>trace_class A\<close>
    proof (rule trace_classI)
      show \<open>is_onb some_chilbert_basis\<close>
        by simp
      define W where \<open>W = polar_decomposition A\<close>
      have \<open>norm (W*) \<le> 1\<close>
        by (metis W_def nle_le norm_adj norm_partial_isometry norm_zero not_one_le_zero polar_decomposition_partial_isometry)
      have \<open>(\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))) \<le> norm \<Phi>\<close> if \<open>finite E\<close> and \<open>E \<subseteq> some_chilbert_basis\<close> for E
      proof -
        define CE where \<open>CE = (\<Sum>x\<in>E. (butterfly x x))\<close>
        from \<open>E \<subseteq> some_chilbert_basis\<close>
        have \<open>norm CE \<le> 1\<close>
          by (auto intro!: sum_butterfly_is_Proj norm_is_Proj is_normal_some_chilbert_basis simp: CE_def is_ortho_set_antimono)
        have \<open>(\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))) = cmod (\<Sum>x\<in>E. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))\<close>
          apply (rule sum_cmod_pos)
          by (simp add: cinner_pos_if_pos)
        also have \<open>\<dots> = cmod (\<Sum>x\<in>E. (W *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (metis W_def cblinfun_apply_cblinfun_compose cinner_adj_right polar_decomposition_correct')
        also have \<open>\<dots> = cmod (\<Sum>x\<in>E. \<Phi> (butterfly_co x (W x)))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (simp flip: p_def xAy)
        also have \<open>\<dots> = cmod (\<Phi> (\<Sum>x\<in>E. butterfly_co x (W x)))\<close>
          by (simp add: cblinfun.sum_right)
        also have \<open>\<dots> \<le> norm \<Phi> * norm (\<Sum>x\<in>E. butterfly_co x (W x))\<close>
          using norm_cblinfun by blast
        also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. butterfly x (W x))\<close>
          apply transfer by simp
        also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. (butterfly x x o\<^sub>C\<^sub>L W*))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (simp add: butterfly_comp_cblinfun)
        also have \<open>\<dots> = norm \<Phi> * norm (CE o\<^sub>C\<^sub>L W*)\<close>
          by (simp add: CE_def cblinfun_compose_sum_left)
        also have \<open>\<dots> \<le> norm \<Phi>\<close>
          apply (rule mult_left_le, simp_all)
          using \<open>norm CE \<le> 1\<close> \<open>norm (W*) \<le> 1\<close>
          by (metis mult_le_one norm_cblinfun_compose norm_ge_zero order_trans)
        finally show ?thesis
          by -
      qed
      then show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
        apply (rule_tac nonneg_bdd_above_summable_on)
        by (auto intro!: bdd_aboveI2)
    qed
    then obtain A' where A': \<open>A = from_trace_class A'\<close>
      using from_trace_class_cases by blast
    from \<Phi>C have \<Phi>C': \<open>\<Phi> C = ?iso A' C\<close> if \<open>finite_rank (from_compact_op C)\<close> for C
      by (simp add: that iso_trace_class_compact_op_dual'_apply A')
    have \<open>\<Phi> = ?iso A'\<close>
      apply (unfold cblinfun_apply_inject[symmetric])
      apply (rule finite_rank_separating_on_compact_op)
      using \<Phi>C' by (auto intro!: cblinfun.bounded_clinear_right)
    then show ?thesis
      by auto
  qed
  then show ?thesis
    by auto
qed

lemma iso_trace_class_compact_op_dual'_isometric[simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 19.1\<close>
  \<open>norm (iso_trace_class_compact_op_dual' t) = norm t\<close> for t :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>norm (?iso t) \<le> norm t\<close> for t
  proof (rule norm_cblinfun_bound)
    show \<open>norm t \<ge> 0\<close> by simp
    fix c
    show \<open>cmod (iso_trace_class_compact_op_dual' t *\<^sub>V c) \<le> norm t * norm c\<close>
      apply (transfer fixing: c)
      apply simp
      by (metis cmod_trace_times from_compact_op_norm ordered_field_class.sign_simps(5))
  qed
  moreover have \<open>norm (?iso t) \<ge> norm t\<close> for t
  proof -
    define s where \<open>s E = (\<Sum>e\<in>E. cmod (e \<bullet>\<^sub>C (abs_op (from_trace_class t) *\<^sub>V e)))\<close> for E
    have bound: \<open>norm (?iso t) \<ge> s E\<close> if \<open>finite E\<close> and \<open>E \<subseteq> some_chilbert_basis\<close> for E
    proof - 
      text \<open>Partial duplication from the proof of @{thm [source] iso_trace_class_compact_op_dual'_surjective}.
In Conway's text, this subproof occurs only once. However, it did not become clear to use how this works:
It seems that Conway's proof only implies that \<^const>\<open>iso_trace_class_compact_op_dual'\<close> is isometric on
the subset of trace-class operators \<^term>\<open>A\<close> constructed in that proof, but not necessarily on others (if \<^const>\<open>iso_trace_class_compact_op_dual'\<close> were non-injective, there might be others)\<close>
      define A \<Phi> where \<open>A = from_trace_class t\<close> and \<open>\<Phi> = ?iso t\<close>
      define W where \<open>W = polar_decomposition A\<close>
      have \<open>norm (W*) \<le> 1\<close>
        by (metis W_def nle_le norm_adj norm_partial_isometry norm_zero not_one_le_zero polar_decomposition_partial_isometry)
      define CE where \<open>CE = (\<Sum>x\<in>E. (butterfly x x))\<close>
      from \<open>E \<subseteq> some_chilbert_basis\<close>
      have \<open>norm CE \<le> 1\<close>
        by (auto intro!: sum_butterfly_is_Proj norm_is_Proj is_normal_some_chilbert_basis simp: CE_def is_ortho_set_antimono)
      have \<open>s E = (\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)))\<close>
        using A_def s_def by blast
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))\<close>
        apply (rule sum_cmod_pos)
        by (simp add: cinner_pos_if_pos)
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. (W *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (metis W_def cblinfun_apply_cblinfun_compose cinner_adj_right polar_decomposition_correct')
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. \<Phi> (butterfly_co x (W x)))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (auto simp: \<Phi>_def iso_trace_class_compact_op_dual'_apply butterfly_co.rep_eq trace_butterfly_comp
            simp flip: A_def)
      also have \<open>\<dots> = cmod (\<Phi> (\<Sum>x\<in>E. butterfly_co x (W x)))\<close>
        by (simp add: cblinfun.sum_right)
      also have \<open>\<dots> \<le> norm \<Phi> * norm (\<Sum>x\<in>E. butterfly_co x (W x))\<close>
        using norm_cblinfun by blast
      also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. butterfly x (W x))\<close>
        apply transfer by simp
      also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. (butterfly x x o\<^sub>C\<^sub>L W*))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (simp add: butterfly_comp_cblinfun)
      also have \<open>\<dots> = norm \<Phi> * norm (CE o\<^sub>C\<^sub>L W*)\<close>
        by (simp add: CE_def cblinfun_compose_sum_left)
      also have \<open>\<dots> \<le> norm \<Phi>\<close>
        apply (rule mult_left_le, simp_all)
        using \<open>norm CE \<le> 1\<close> \<open>norm (W*) \<le> 1\<close>
        by (metis mult_le_one norm_cblinfun_compose norm_ge_zero order_trans)
      finally show ?thesis
        by (simp add: \<Phi>_def)
    qed
    have \<open>trace_class (from_trace_class t)\<close> and \<open>norm t = trace_norm (from_trace_class t)\<close>
      using from_trace_class
      by (auto simp add: norm_trace_class.rep_eq)
    then have \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op (from_trace_class t) *\<^sub>V e))) has_sum norm t) some_chilbert_basis\<close>      
      by (metis (no_types, lifting) has_sum_cong has_sum_infsum is_onb_some_chilbert_basis trace_class_def trace_norm_alt_def trace_norm_basis_invariance)
    then have lim: \<open>(s \<longlongrightarrow> norm t) (finite_subsets_at_top some_chilbert_basis)\<close>
      by (simp add: filterlim_iff has_sum_def s_def)
    show ?thesis
      using _ _ lim apply (rule tendsto_le)
      by (auto intro!: tendsto_const eventually_finite_subsets_at_top_weakI bound)
  qed
  ultimately show ?thesis
    using nle_le by blast
qed


instance trace_class :: (chilbert_space, chilbert_space) cbanach
proof
  let ?UNIVc = \<open>UNIV :: (('b,'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex) set\<close>
  let ?UNIVt = \<open>UNIV :: ('a,'b) trace_class set\<close>
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have lin_inv[simp]: \<open>bounded_clinear (inv ?iso)\<close>
    apply (rule bounded_clinear_inv[where b=1])
    by auto
  have [simp]: \<open>inj ?iso\<close>
  proof (rule injI)
    fix x y assume \<open>?iso x = ?iso y\<close>
    then have \<open>norm (?iso (x - y)) = 0\<close>
      by (metis (no_types, opaque_lifting) add_diff_cancel_left diff_self iso_trace_class_compact_op_dual'_isometric iso_trace_class_compact_op_dual'_plus norm_eq_zero ordered_field_class.sign_simps(12))
    then have \<open>norm (x - y) = 0\<close>
      by simp
    then show \<open>x = y\<close>
      by simp
  qed
  have norm_inv[simp]: \<open>norm (inv ?iso x) = norm x\<close> for x
    by (metis iso_trace_class_compact_op_dual'_isometric iso_trace_class_compact_op_dual'_surjective surj_f_inv_f)
  have \<open>complete ?UNIVc\<close>
    by (simp add: complete_UNIV)
  then have \<open>complete (inv ?iso ` ?UNIVc)\<close>
    apply (rule complete_isometric_image[rotated 4, where e=1])
    by (auto simp: bounded_clinear.bounded_linear)
  then have \<open>complete ?UNIVt\<close>
    by (simp add: inj_imp_surj_inv)
  then show \<open>Cauchy X \<Longrightarrow> convergent X\<close> for X :: \<open>nat \<Rightarrow> ('a, 'b) trace_class\<close>
    by (simp add: complete_def convergent_def)
qed



lemma trace_norm_geq_cinner_abs_op: \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) \<le> trace_norm t\<close> if \<open>trace_class t\<close> and \<open>norm \<psi> = 1\<close>
proof -
  have \<open>\<exists>B. {\<psi>} \<subseteq> B \<and> is_onb B\<close>
    apply (rule orthonormal_basis_exists)
    using \<open>norm \<psi> = 1\<close>
    by auto
  then obtain B where \<open>is_onb B\<close> and \<open>\<psi> \<in> B\<close>
    by auto

  have \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) = (\<Sum>\<^sub>\<infinity>\<psi>\<in>{\<psi>}. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    by simp
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<psi>\<in>B. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    apply (rule infsum_mono_neutral_complex)
    using \<open>\<psi> \<in> B\<close> \<open>is_onb B\<close> that
    by (auto simp add: trace_exists cinner_pos_if_pos)
  also have \<open>\<dots> = trace_norm t\<close>
    using \<open>is_onb B\<close> that
    by (metis trace_abs_op trace_alt_def trace_class_abs_op)
  finally show ?thesis
    by -
qed

lemma norm_leq_trace_norm: \<open>norm t \<le> trace_norm t\<close> if \<open>trace_class t\<close> 
  for t :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> 
proof -
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    using not_not_singleton_cblinfun_zero[of t] negation by simp
  note cblinfun_norm_approx_witness' = cblinfun_norm_approx_witness[internalize_sort' 'a, OF complex_normed_vector_axioms not_singleton]

  show ?thesis
  proof (rule field_le_epsilon)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>

    define \<delta> :: real where 
      \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (norm (sqrt_op (abs_op t)) + 1)))\<close>
    have \<open>\<delta> > 0\<close>
      using \<open>\<epsilon> > 0\<close> apply (auto simp add: \<delta>_def)
      by (smt (verit) norm_not_less_zero zero_less_divide_iff)
    have \<delta>_small: \<open>\<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta> \<le> \<epsilon>\<close>
    proof -
      define n where \<open>n = norm (sqrt_op (abs_op t))\<close>
      then have \<open>n \<ge> 0\<close>
        by simp
      have \<delta>: \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (n + 1)))\<close>
        by (simp add: \<delta>_def n_def)

      have \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon> / 2 + 2 * n * \<delta>\<close>
        apply (rule add_right_mono)
        apply (subst \<delta>) apply (subst min_power_distrib_left)
        using \<open>\<epsilon> > 0\<close> \<open>n \<ge> 0\<close> by auto
      also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * n * (\<epsilon> / (4 * (n + 1)))\<close>
        apply (intro add_left_mono mult_left_mono)
        by (simp_all add: \<delta> \<open>n \<ge> 0\<close>)
      also have \<open>\<dots> = \<epsilon> / 2 + 2 * (n / (n+1)) * (\<epsilon> / 4)\<close>
        by simp
      also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * 1 * (\<epsilon> / 4)\<close>
        apply (intro add_left_mono mult_left_mono mult_right_mono)
        using \<open>n \<ge> 0\<close> \<open>\<epsilon> > 0\<close> by auto
      also have \<open>\<dots> = \<epsilon>\<close>
        by simp
      finally show \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon>\<close>
        by -
    qed

    from \<open>\<delta> > 0\<close> obtain \<psi> where \<psi>\<epsilon>: \<open>norm (sqrt_op (abs_op t)) - \<delta> \<le> norm (sqrt_op (abs_op t) *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
      apply atomize_elim by (rule cblinfun_norm_approx_witness')

    have aux1: \<open>2 * complex_of_real x = complex_of_real (2 * x)\<close> for x
      by simp

    have \<open>complex_of_real (norm t) = norm (abs_op t)\<close>
      by simp
    also have \<open>\<dots> = (norm (sqrt_op (abs_op t)))\<^sup>2\<close>
      by (simp add: positive_hermitianI flip: norm_AadjA)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) + \<delta>)\<^sup>2\<close>
      by (smt (verit) \<psi>\<epsilon> complex_of_real_mono norm_triangle_ineq4 norm_triangle_sub pos2 power_strict_mono)
    also have \<open>\<dots> = (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) * \<delta>\<close>
      by (simp add: power2_sum)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta>\<close>
      apply (rule complex_of_real_mono_iff[THEN iffD2])
      by (smt (z3) \<open>0 < \<delta>\<close> \<open>norm \<psi> = 1\<close> more_arith_simps(11) mult_less_cancel_right_disj norm_cblinfun one_power2 power2_eq_square)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<epsilon>\<close>
      apply (rule complex_of_real_mono_iff[THEN iffD2])
      using \<delta>_small by auto
    also have \<open>\<dots> = ((sqrt_op (abs_op t) *\<^sub>V \<psi>) \<bullet>\<^sub>C (sqrt_op (abs_op t) *\<^sub>V \<psi>)) + \<epsilon>\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>)) + \<epsilon>\<close>
      by (simp add: positive_hermitianI flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> \<le> trace_norm t + \<epsilon>\<close>
      using \<open>norm \<psi> = 1\<close> \<open>trace_class t\<close> by (auto simp add: trace_norm_geq_cinner_abs_op)
    finally show \<open>norm t \<le> trace_norm t + \<epsilon>\<close>
      using complex_of_real_mono_iff by blast
  qed
qed

lemma clinear_from_trace_class[iff]: \<open>clinear from_trace_class\<close>
  apply (rule clinearI; transfer)
  by auto

lemma bounded_clinear_from_trace_class[bounded_clinear]:
  \<open>bounded_clinear (from_trace_class :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    apply (rule bounded_clinearI[where K=1]; transfer)
    by (auto intro!: norm_leq_trace_norm[internalize_sort' 'a] chilbert_space_axioms True)
next
  case False
  then have zero: \<open>A = 0\<close> for A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (rule not_not_singleton_cblinfun_zero)
  show ?thesis
    apply (rule bounded_clinearI[where K=1])
    by (subst zero, simp)+
qed


instantiation trace_class :: (chilbert_space, chilbert_space) order begin
lift_definition less_eq_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less_eq.
lift_definition less_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less.
instance
  apply intro_classes
     apply (auto simp add: less_eq_trace_class.rep_eq less_trace_class.rep_eq)
  by (simp add: from_trace_class_inject)
end


lift_definition compose_tcl :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> ('c::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('c,'b) trace_class\<close> is
  \<open>cblinfun_compose :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  by (simp add: trace_class_comp_left)

lift_definition compose_tcr :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('c::chilbert_space, 'a) trace_class \<Rightarrow> ('c,'b) trace_class\<close> is
  \<open>cblinfun_compose :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  by (simp add: trace_class_comp_right)

lemma norm_compose_tcl: \<open>norm (compose_tcl a b) \<le> norm a * norm b\<close>
  by (auto intro!: trace_norm_comp_left simp: norm_trace_class.rep_eq compose_tcl.rep_eq)

lemma norm_compose_tcr: \<open>norm (compose_tcr a b) \<le> norm a * norm b\<close>
  by (auto intro!: trace_norm_comp_right simp: norm_trace_class.rep_eq compose_tcr.rep_eq)

interpretation compose_tcl: bounded_cbilinear compose_tcl
proof (intro bounded_cbilinear.intro exI[of _ 1] allI)
  fix a a' :: \<open>('a,'b) trace_class\<close> and b b' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and r :: complex
  show \<open>compose_tcl (a + a') b = compose_tcl a b + compose_tcl a' b\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_left)
  show \<open>compose_tcl a (b + b') = compose_tcl a b + compose_tcl a b'\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_right)
  show \<open>compose_tcl (r *\<^sub>C a) b = r *\<^sub>C compose_tcl a b\<close>
    apply transfer
    by simp
  show \<open>compose_tcl a (r *\<^sub>C b) = r *\<^sub>C compose_tcl a b\<close>
    apply transfer
    by simp
  show \<open>norm (compose_tcl a b) \<le> norm a * norm b * 1\<close>
    by (simp add: norm_compose_tcl)
qed

interpretation compose_tcr: bounded_cbilinear compose_tcr
proof (intro bounded_cbilinear.intro exI[of _ 1] allI)
  fix a a' :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b b' :: \<open>('c,'a) trace_class\<close> and r :: complex
  show \<open>compose_tcr (a + a') b = compose_tcr a b + compose_tcr a' b\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_left)
  show \<open>compose_tcr a (b + b') = compose_tcr a b + compose_tcr a b'\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_right)
  show \<open>compose_tcr (r *\<^sub>C a) b = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>compose_tcr a (r *\<^sub>C b) = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>norm (compose_tcr a b) \<le> norm a * norm b * 1\<close>
    by (simp add: norm_compose_tcr)
qed

lemma trace_norm_sandwich: \<open>trace_norm (sandwich e t) \<le> (norm e)^2 * trace_norm t\<close> if \<open>trace_class t\<close>
  apply (simp add: sandwich_apply)
  by (smt (z3) Groups.mult_ac(2) more_arith_simps(11) mult_left_mono norm_adj norm_ge_zero power2_eq_square that trace_class_comp_right trace_norm_comp_left trace_norm_comp_right)

lemma trace_class_sandwich: \<open>trace_class b \<Longrightarrow> trace_class (sandwich a b)\<close>
  by (simp add: sandwich_apply trace_class_comp_right trace_class_comp_left)

definition \<open>sandwich_tc e t = compose_tcl (compose_tcr e t) (e*)\<close>

lemma sandwich_tc_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_trace_class ===> cr_trace_class) (\<lambda>e. (*\<^sub>V) (sandwich e)) sandwich_tc\<close>
  by (auto intro!: rel_funI simp: sandwich_tc_def cr_trace_class_def compose_tcl.rep_eq compose_tcr.rep_eq sandwich_apply)

lemma from_trace_class_sandwich_tc:
  \<open>from_trace_class (sandwich_tc e t) = sandwich e (from_trace_class t)\<close>
  apply transfer
  by (rule sandwich_apply)

lemma norm_sandwich_tc: \<open>norm (sandwich_tc e t) \<le> (norm e)^2 * norm t\<close>
  by (simp add: norm_trace_class.rep_eq from_trace_class_sandwich_tc trace_norm_sandwich)

lemma sandwich_tc_pos: \<open>sandwich_tc e t \<ge> 0\<close> if \<open>t \<ge> 0\<close>
  using that apply (transfer fixing: e)
  by (simp add: sandwich_pos)

lemma trace_norm_bounded:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_class A\<close>
proof -
  have \<open>(\<lambda>x. x \<bullet>\<^sub>C (B *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    by (metis assms(2) is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)
  then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_on_comparison_test)
    using \<open>A \<ge> 0\<close> \<open>A \<le> B\<close>
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos less_eq_cblinfun_def)
  then show ?thesis
    by (auto intro!: trace_classI[OF is_onb_some_chilbert_basis] simp: abs_op_id_on_pos \<open>A \<ge> 0\<close>)
qed

lemma trace_norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_norm A \<le> trace_norm B\<close>
proof -
  from assms have \<open>trace_class A\<close>
    by (rule trace_norm_bounded)
  from \<open>A \<le> B\<close> and \<open>A \<ge> 0\<close>
  have \<open>B \<ge> 0\<close>
    by simp
  have \<open>cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) \<le> cmod (x \<bullet>\<^sub>C (abs_op B *\<^sub>V x))\<close> for x
    using \<open>A \<le> B\<close>
    unfolding less_eq_cblinfun_def
    using \<open>A \<ge> 0\<close> \<open>B \<ge> 0\<close> 
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos)
  then show \<open>trace_norm A \<le> trace_norm B\<close>
    using \<open>trace_class A\<close> \<open>trace_class B\<close>
    by (auto intro!: infsum_mono 
        simp add: trace_norm_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
qed



lemma norm_cblinfun_mono_trace_class:
  fixes A B :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
  using assms
  apply transfer
  apply (rule trace_norm_cblinfun_mono)
  by auto

lemma trace_norm_butterfly: \<open>trace_norm (butterfly a b) = (norm a) * (norm b)\<close>
  for a b :: \<open>_ :: chilbert_space\<close>
proof -
  have \<open>trace_norm (butterfly a b) = trace (abs_op (butterfly a b))\<close>
    by (simp flip: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace (selfbutter b)\<close>
    by (simp add: abs_op_butterfly scaleR_scaleC trace_scaleC del: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace ((vector_to_cblinfun b :: complex \<Rightarrow>\<^sub>C\<^sub>L _)* o\<^sub>C\<^sub>L vector_to_cblinfun b)\<close>
    apply (subst butterfly_def)
    apply (subst circularity_of_trace)
    by simp_all
  also have \<open>\<dots> = (norm a / norm b) * (b \<bullet>\<^sub>C b)\<close>
    by simp
  also have \<open>\<dots> = (norm a) * (norm b)\<close>
    by (simp add: cdot_square_norm power2_eq_square)
  finally show ?thesis
    using of_real_eq_iff by blast
qed


lemma from_trace_class_sum:
  shows \<open>from_trace_class (\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. from_trace_class (f x))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (simp_all add: plus_trace_class.rep_eq)


lemma has_sum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>((\<lambda>x. from_trace_class (f x)) has_sum from_trace_class a) A\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  moreover
  from assms(2)
  have \<open>((\<lambda>x. from_trace_class (g x)) has_sum from_trace_class b) B\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  ultimately have \<open>from_trace_class a \<le> from_trace_class b\<close>
    apply (rule has_sum_mono_neutral_cblinfun)
    using assms by (auto simp: less_eq_trace_class.rep_eq)
  then show ?thesis
    by (auto simp: less_eq_trace_class.rep_eq)
qed

lemma has_sum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_traceclass by force

lemma infsum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_traceclass)

lemma infsum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_mono_neutral_traceclass summable_iff_has_sum_infsum by blast

instance trace_class :: (chilbert_space, chilbert_space) ordered_complex_vector
  apply (intro_classes; transfer)
  by (auto intro!: scaleC_left_mono scaleC_right_mono)

lemma Abs_trace_class_geq0I: \<open>0 \<le> Abs_trace_class t\<close> if \<open>trace_class t\<close> and \<open>t \<ge> 0\<close>
  using that by (simp add: zero_trace_class.abs_eq less_eq_trace_class.abs_eq eq_onp_def)

lift_definition tc_compose :: \<open>('b::chilbert_space, 'c::chilbert_space) trace_class 
                               \<Rightarrow> ('a::chilbert_space, 'b) trace_class \<Rightarrow> ('a,'c) trace_class\<close> is
    cblinfun_compose
  by (simp add: trace_class_comp_left)

lemma norm_tc_compose:
  \<open>norm (tc_compose a b) \<le> norm a * norm b\<close>
proof transfer
  fix a :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'c\<close>
  assume \<open>a \<in> Collect trace_class\<close> and tc_b: \<open>b \<in> Collect trace_class\<close>
  then have \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
    by (simp add: trace_norm_comp_left)
  also have \<open>\<dots> \<le> trace_norm a * trace_norm b\<close>
    using tc_b by (auto intro!: mult_left_mono norm_leq_trace_norm)
  finally show \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * trace_norm b\<close>
    by -
qed


lift_definition trace_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> complex\<close> is trace.

lemma trace_tc_plus: \<open>trace_tc (a + b) = trace_tc a + trace_tc b\<close>
  apply transfer by (simp add: trace_plus)

lemma trace_tc_scaleC: \<open>trace_tc (c *\<^sub>C a) = c *\<^sub>C trace_tc a\<close>
  apply transfer by (simp add: trace_scaleC)

lemma trace_tc_norm: \<open>norm (trace_tc a) \<le> norm a\<close>
  apply transfer by auto

lemma bounded_clinear_trace_tc[bounded_clinear, simp]: \<open>bounded_clinear trace_tc\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp: trace_tc_scaleC trace_tc_plus intro!: trace_tc_norm)


lemma norm_tc_pos: \<open>norm A = trace_tc A\<close> if \<open>A \<ge> 0\<close>
   using that apply transfer by (simp add: trace_norm_pos)

lemma norm_tc_pos_Re: \<open>norm A = Re (trace_tc A)\<close> if \<open>A \<ge> 0\<close>
  using norm_tc_pos[OF that]
  by (metis Re_complex_of_real)

lemma from_trace_class_pos: \<open>from_trace_class A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close>
  by (simp add: less_eq_trace_class.rep_eq)

lemma infsum_tc_norm_bounded_abs_summable:
  fixes A :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'b::chilbert_space) trace_class\<close>
  assumes pos: \<open>\<And>x. x \<in> M \<Longrightarrow> A x \<ge> 0\<close>
  assumes bound_B: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> M \<Longrightarrow> norm (\<Sum>x\<in>F. A x) \<le> B\<close>
  shows \<open>A abs_summable_on M\<close>
proof -
  have \<open>(\<Sum>x\<in>F. norm (A x)) = norm (\<Sum>x\<in>F. A x)\<close> if \<open>F \<subseteq> M\<close> for F
  proof -
    have \<open>complex_of_real (\<Sum>x\<in>F. norm (A x)) = (\<Sum>x\<in>F. complex_of_real (trace_norm (from_trace_class (A x))))\<close>
      by (simp add: norm_trace_class.rep_eq trace_norm_pos)
    also have \<open>\<dots> = (\<Sum>x\<in>F. trace (from_trace_class (A x)))\<close>
      using that pos by (auto intro!: sum.cong simp add: trace_norm_pos less_eq_trace_class.rep_eq)
    also have \<open>\<dots> = trace (from_trace_class (\<Sum>x\<in>F. A x))\<close>
      by (simp add: from_trace_class_sum trace_sum)
    also have \<open>\<dots> = norm (\<Sum>x\<in>F. A x)\<close>
      by (smt (verit, ccfv_threshold) calculation norm_of_real norm_trace_class.rep_eq sum_norm_le trace_leq_trace_norm)
    finally show ?thesis
      using of_real_eq_iff by blast
  qed
  with bound_B have bound_B': \<open>(\<Sum>x\<in>F. norm (A x)) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> M\<close> for F
    by (metis that(1) that(2))
  then show \<open>A abs_summable_on M\<close>
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: bdd_aboveI)
qed

lemma trace_norm_uminus[simp]: \<open>trace_norm (-a) = trace_norm a\<close>
  by (metis abs_op_uminus of_real_eq_iff trace_abs_op)

lemma trace_norm_triangle_minus: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a - b) \<le> trace_norm a + trace_norm b\<close>
  using trace_norm_triangle[of a \<open>-b\<close>]
  by auto

lemma trace_norm_abs_op[simp]: \<open>trace_norm (abs_op t) = trace_norm t\<close>
  by (simp add: trace_norm_def)

lemma
  fixes t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  shows cblinfun_decomp_4pos: \<open>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>  (is ?thesis1)
  and trace_class_decomp_4pos: \<open>trace_class t \<Longrightarrow>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> trace_class t1 \<and> trace_class t2 \<and> trace_class t3 \<and> trace_class t4
               \<and> trace_norm t1 \<le> trace_norm t \<and> trace_norm t2 \<le> trace_norm t \<and> trace_norm t3 \<le> trace_norm t \<and> trace_norm t4 \<le> trace_norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close> (is \<open>_ \<Longrightarrow> ?thesis2\<close>)
proof -
  define th ta where \<open>th = (1/2) *\<^sub>C (t + t*)\<close> and \<open>ta = (-\<i>/2) *\<^sub>C (t - t*)\<close>
  have th_herm: \<open>th* = th\<close>
    by (simp add: adj_plus th_def)
  have \<open>ta* = ta\<close>
    by (simp add: adj_minus ta_def scaleC_diff_right adj_uminus)
  have \<open>t = th + \<i> *\<^sub>C ta\<close>
    by (smt (verit, ccfv_SIG) add.commute add.inverse_inverse complex_i_mult_minus complex_vector.vector_space_assms(1) complex_vector.vector_space_assms(3) diff_add_cancel group_cancel.add2 i_squared scaleC_half_double ta_def th_def times_divide_eq_right)
  define t1 t2 where \<open>t1 = (abs_op th + th) /\<^sub>R 2\<close> and \<open>t2 = (abs_op th - th) /\<^sub>R 2\<close>
  have \<open>t1 \<ge> 0\<close>
    using abs_op_geq_neq[unfolded selfadjoint_def, OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t1_def intro!: scaleR_nonneg_nonneg)
  have \<open>t2 \<ge> 0\<close>
    using abs_op_geq[unfolded selfadjoint_def, OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t2_def intro!: scaleR_nonneg_nonneg)
  have \<open>th = t1 - t2\<close>
    apply (simp add: t1_def t2_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  define t3 t4 where \<open>t3 = (abs_op ta + ta) /\<^sub>R 2\<close> and \<open>t4 = (abs_op ta - ta) /\<^sub>R 2\<close>
  have \<open>t3 \<ge> 0\<close>
    using abs_op_geq_neq[unfolded selfadjoint_def, OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t3_def intro!: scaleR_nonneg_nonneg)
  have \<open>t4 \<ge> 0\<close>
    using abs_op_geq[unfolded selfadjoint_def, OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t4_def intro!: scaleR_nonneg_nonneg)
  have \<open>ta = t3 - t4\<close>
    apply (simp add: t3_def t4_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  have decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    by (simp add: \<open>t = th + \<i> *\<^sub>C ta\<close> \<open>th = t1 - t2\<close> \<open>ta = t3 - t4\<close> scaleC_diff_right)
  from decomp \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
  show ?thesis1
    by auto
  show ?thesis2 if \<open>trace_class t\<close>
  proof -
    have \<open>trace_class th\<close> \<open>trace_class ta\<close>
      by (auto simp add: th_def ta_def
          intro!: \<open>trace_class t\<close> trace_class_scaleC trace_class_plus trace_class_minus trace_class_uminus trace_class_adj)
    then have tc: \<open>trace_class t1\<close> \<open>trace_class t2\<close> \<open>trace_class t3\<close> \<open>trace_class t4\<close>
      by (auto simp add: t1_def t2_def t3_def t4_def scaleR_scaleC intro!: trace_class_scaleC)
    have tn_th: \<open>trace_norm th \<le> trace_norm t\<close>
      using trace_norm_triangle[of t \<open>t*\<close>] 
      by (auto simp add: that th_def trace_norm_scaleC)
    have tn_ta: \<open>trace_norm ta \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of t \<open>t*\<close>] 
      by (auto simp add: that ta_def trace_norm_scaleC)
    have tn1: \<open>trace_norm t1 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t1_def trace_norm_scaleC scaleR_scaleC)
    have tn2: \<open>trace_norm t2 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t2_def trace_norm_scaleC scaleR_scaleC)
    have tn3: \<open>trace_norm t3 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t3_def trace_norm_scaleC scaleR_scaleC)
    have tn4: \<open>trace_norm t4 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t4_def trace_norm_scaleC scaleR_scaleC)
    from decomp tc \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close> tn1 tn2 tn3 tn4
    show ?thesis2
      by auto
  qed
qed

lemma trace_class_decomp_4pos':
  fixes t :: \<open>('a::chilbert_space,'a) trace_class\<close>
  shows \<open>\<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> norm t1 \<le> norm t \<and> norm t2 \<le> norm t \<and> norm t3 \<le> norm t \<and> norm t4 \<le> norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>
proof -
  from trace_class_decomp_4pos[of \<open>from_trace_class t\<close>, OF trace_class_from_trace_class]
  obtain t1' t2' t3' t4'
    where *: \<open>from_trace_class t = t1' - t2' + \<i> *\<^sub>C t3' - \<i> *\<^sub>C t4'
               \<and> trace_class t1' \<and> trace_class t2' \<and> trace_class t3' \<and> trace_class t4'
               \<and> trace_norm t1' \<le> trace_norm (from_trace_class t) \<and> trace_norm t2' \<le> trace_norm (from_trace_class t) \<and> trace_norm t3' \<le> trace_norm (from_trace_class t) \<and> trace_norm t4' \<le> trace_norm (from_trace_class t) 
               \<and> t1' \<ge> 0 \<and> t2' \<ge> 0 \<and> t3' \<ge> 0 \<and> t4' \<ge> 0\<close>
    by auto
  then obtain t1 t2 t3 t4 where
    t1234: \<open>t1' = from_trace_class t1\<close> \<open>t2' = from_trace_class t2\<close> \<open>t3' = from_trace_class t3\<close> \<open>t4' = from_trace_class t4\<close>
    by (metis from_trace_class_cases mem_Collect_eq)
  with * have n1234: \<open>norm t1 \<le> norm t\<close> \<open>norm t2 \<le> norm t\<close> \<open>norm t3 \<le> norm t\<close> \<open>norm t4 \<le> norm t\<close>
    by (metis norm_trace_class.rep_eq)+
  have t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    using * unfolding t1234 
    by (auto simp: from_trace_class_inject
        simp flip: scaleC_trace_class.rep_eq plus_trace_class.rep_eq minus_trace_class.rep_eq)
  have pos1234: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
    using * unfolding t1234 
    by (auto simp: less_eq_trace_class_def)
  from t_decomp pos1234 n1234
  show ?thesis
    by blast
qed

thm bounded_clinear_trace_duality
lemma bounded_clinear_trace_duality': \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (a o\<^sub>C\<^sub>L t))\<close> for t :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
    apply (auto simp add: cblinfun_compose_add_left trace_class_comp_right trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

lemma infsum_nonneg_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_neutral_traceclass)
  using assms by (auto simp: infsum_not_exists)

lemma sandwich_tc_compose: \<open>sandwich_tc (A o\<^sub>C\<^sub>L B) = sandwich_tc A o sandwich_tc B\<close>
  apply (rule ext)
  apply (rule from_trace_class_inject[THEN iffD1])
  apply (transfer fixing: A B)
  by (simp add: sandwich_compose)

lemma sandwich_tc_0_left[simp]: \<open>sandwich_tc 0 = 0\<close>
  by (auto intro!: ext simp add: sandwich_tc_def compose_tcl.zero_left compose_tcr.zero_left)

lemma sandwich_tc_0_right[simp]: \<open>sandwich_tc e 0 = 0\<close>
  by (auto intro!: ext simp add: sandwich_tc_def compose_tcl.zero_left compose_tcr.zero_right)

lemma sandwich_tc_scaleC_left: \<open>sandwich_tc (c *\<^sub>C e) t = (cmod c)^2 *\<^sub>C sandwich_tc e t\<close>
  apply (rule from_trace_class_inject[THEN iffD1])
  by (simp add: from_trace_class_sandwich_tc scaleC_trace_class.rep_eq
      sandwich_scaleC_left)

lemma sandwich_tc_scaleR_left: \<open>sandwich_tc (r *\<^sub>R e) t = r^2 *\<^sub>R sandwich_tc e t\<close>
  by (simp add: scaleR_scaleC sandwich_tc_scaleC_left flip: of_real_power)

lemma bounded_cbilinear_tc_compose: \<open>bounded_cbilinear tc_compose\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  apply (auto intro!: exI[of _ 1] simp: cblinfun_compose_add_left cblinfun_compose_add_right)
  by (meson norm_leq_trace_norm dual_order.trans mult_right_mono trace_norm_comp_right trace_norm_nneg)
lemmas bounded_clinear_tc_compose_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_compose]
lemmas bounded_clinear_tc_compose_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_compose]

lift_definition tc_butterfly :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) trace_class\<close>
  is butterfly
  by simp

lemma norm_tc_butterfly: \<open>norm (tc_butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>)
  by (simp add: trace_norm_butterfly)

lemma comp_tc_butterfly[simp]: \<open>tc_compose (tc_butterfly a b) (tc_butterfly c d) = (b \<bullet>\<^sub>C c) *\<^sub>C tc_butterfly a d\<close>
  apply transfer'
  by simp

lemma tc_butterfly_pos[simp]: \<open>0 \<le> tc_butterfly \<psi> \<psi>\<close>
  apply transfer
  by simp

lift_definition rank1_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> bool\<close> is rank1.
lift_definition finite_rank_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> bool\<close> is finite_rank.

lemma finite_rank_tc_0[iff]: \<open>finite_rank_tc 0\<close>
  apply transfer by simp

lemma finite_rank_tc_plus: \<open>finite_rank_tc (a + b)\<close>
  if \<open>finite_rank_tc a\<close> and \<open>finite_rank_tc b\<close>
  using that apply transfer
  by simp

lemma finite_rank_tc_scale: \<open>finite_rank_tc (c *\<^sub>C a)\<close> if \<open>finite_rank_tc a\<close>
  using that apply transfer by simp

lemma csubspace_finite_rank_tc: \<open>csubspace (Collect finite_rank_tc)\<close>
  apply (rule complex_vector.subspaceI)
  by (auto intro!: finite_rank_tc_plus finite_rank_tc_scale)

lemma rank1_trace_class: \<open>trace_class a\<close> if \<open>rank1 a\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using that by (auto intro!: simp: rank1_iff_butterfly)

lemma finite_rank_trace_class: \<open>trace_class a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  from \<open>finite_rank a\<close> obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> Collect rank1\<close>
    and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, ccfv_threshold) complex_vector.span_explicit finite_rank_def mem_Collect_eq)
  then show \<open>trace_class a\<close>
    unfolding a_def
    apply induction
    by (auto intro!: trace_class_plus trace_class_scaleC intro: rank1_trace_class)
qed

lemma finite_rank_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using finite_rank_comp_right finite_rank_trace_class hilbert_schmidtI that by blast

lemma trace_minus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a - b) = trace a - trace b\<close>
  by (metis (no_types, lifting) add_uminus_conv_diff assms(1) assms(2) trace_class_uminus trace_plus trace_uminus)

lemma trace_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>trace_class A\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace A \<le> trace B\<close>
proof -
  have sumA: \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    by (auto intro!: trace_exists assms)
  moreover have sumB: \<open>(\<lambda>e. e \<bullet>\<^sub>C (B *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    by (auto intro!: trace_exists assms)
  moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close> for x
    using assms(3) less_eq_cblinfun_def by blast
  ultimately have \<open>(\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (B *\<^sub>V e))\<close>
    by (rule infsum_mono_complex)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) diff_ge_0_iff_ge trace_minus trace_pos)
qed

lemma trace_tc_mono:
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_tc A \<le> trace_tc B\<close>
  using assms
  apply transfer
  by (simp add: trace_cblinfun_mono)

lemma trace_tc_0[simp]: \<open>trace_tc 0 = 0\<close>
  apply transfer' by simp

end
