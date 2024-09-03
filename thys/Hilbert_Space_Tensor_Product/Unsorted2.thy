theory Unsorted2
  imports Spectral_Theorem Trace_Class
begin

subsection \<open>Spectral decomposition, trace class\<close>

lift_definition spectral_dec_proj_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> ('a, 'a) trace_class\<close> is
  spectral_dec_proj
  using finite_rank_trace_class spectral_dec_proj_finite_rank trace_class_compact by blast

lift_definition spectral_dec_val_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> complex\<close> is
  spectral_dec_val.

lemma spectral_dec_proj_tc_finite_rank: 
  assumes \<open>adj_tc a = a\<close>
  shows \<open>finite_rank_tc (spectral_dec_proj_tc a n)\<close>
  using assms apply transfer
  by (simp add: spectral_dec_proj_finite_rank trace_class_compact)

lemma spectral_dec_summable_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  abs_summable_on  UNIV\<close>
proof (intro nonneg_bounded_partial_sums_imp_summable_on norm_ge_zero eventually_finite_subsets_at_top_weakI)
  define a' where \<open>a' = from_trace_class a\<close>
  then have [transfer_rule]: \<open>cr_trace_class a' a\<close>
    by (simp add: cr_trace_class_def)

  have \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  fix F :: \<open>nat set\<close> assume \<open>finite F\<close>
  define R where \<open>R = (\<Squnion>n\<in>F. spectral_dec_space a' n)\<close>
  have \<open>(\<Sum>x\<in>F. norm (spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x))
        = norm (\<Sum>x\<in>F. spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x)\<close>
  proof (rule norm_tc_sum_exchange[symmetric]; transfer; rename_tac n m F)
    fix n m :: nat assume (* \<open>n \<in> F\<close> and \<open>m \<in> F\<close> and *) \<open>n \<noteq> m\<close>
    then have *: \<open>Proj (spectral_dec_space a' n) o\<^sub>C\<^sub>L Proj (spectral_dec_space a' m) = 0\<close> if \<open>spectral_dec_val a' n \<noteq> 0\<close> and \<open>spectral_dec_val a' m \<noteq> 0\<close>
      by (auto intro!: orthogonal_projectors_orthogonal_spaces[THEN iffD1] spectral_dec_space_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>simp: )
    show \<open>(spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n)* o\<^sub>C\<^sub>L spectral_dec_val a' m *\<^sub>C spectral_dec_proj a' m = 0\<close>
      by (auto intro!: * simp: spectral_dec_proj_def adj_Proj)
    show \<open>spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n o\<^sub>C\<^sub>L (spectral_dec_val a' m *\<^sub>C spectral_dec_proj a' m)* = 0\<close>
      by (auto intro!: * simp: spectral_dec_proj_def adj_Proj)
  qed
  also have \<open>\<dots> = trace_norm (\<Sum>x\<in>F. spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x)\<close>
    by (metis (no_types, lifting) a'_def spectral_dec_proj_tc.rep_eq spectral_dec_val_tc.rep_eq from_trace_class_sum norm_trace_class.rep_eq scaleC_trace_class.rep_eq sum.cong) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. if x\<in>F then spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x else 0)\<close>
    by (simp add: \<open>finite F\<close> suminf_If_finite_set) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. (spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x) o\<^sub>C\<^sub>L Proj R)\<close>
  proof -
    have \<open>spectral_dec_proj a' n = spectral_dec_proj a' n o\<^sub>C\<^sub>L Proj R\<close> if \<open>n \<in> F\<close> for n
      by (auto intro!: Proj_o_Proj_subspace_left[symmetric] SUP_upper that simp: spectral_dec_proj_def R_def)
    moreover have \<open>spectral_dec_proj a' n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> F\<close> for n
      using that
      by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>
          simp: spectral_dec_proj_def R_def
          simp flip: orthogonal_projectors_orthogonal_spaces)
    ultimately show ?thesis
      by (auto intro!: arg_cong[where f=trace_norm] suminf_cong)
  qed
  also have \<open>\<dots> = trace_norm ((\<Sum>x. spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x) o\<^sub>C\<^sub>L Proj R)\<close>
    apply (intro arg_cong[where f=trace_norm] bounded_linear.suminf[symmetric] 
        bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left sums_summable)
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> spectral_dec_sums by blast
  also have \<open>\<dots> = trace_norm (a' o\<^sub>C\<^sub>L Proj R)\<close>
    using spectral_dec_sums[OF \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>] sums_unique by fastforce 
  also have \<open>\<dots> \<le> trace_norm a' * norm (Proj R)\<close>
    by (auto intro!: trace_norm_comp_left simp: a'_def)
  also have \<open>\<dots> \<le> trace_norm a'\<close>
    by (simp add: mult_left_le norm_Proj_leq1) 
  finally show \<open>(\<Sum>x\<in>F. norm (spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x)) \<le> trace_norm a'\<close>
    by -
qed


lemma spectral_dec_has_sum_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>((\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  has_sum  a) UNIV\<close>
proof -
  define a' b b' where \<open>a' = from_trace_class a\<close>
    and \<open>b = (\<Sum>\<^sub>\<infinity>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)\<close> and \<open>b' = from_trace_class b\<close>
  have [simp]: \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have [simp]: \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  have [simp]: \<open>trace_class b'\<close>
    by (simp add: b'_def) 
  from spectral_dec_summable_tc[OF assms]
  have has_sum_b: \<open>((\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  has_sum  b) UNIV\<close>
    by (metis abs_summable_summable b_def summable_iff_has_sum_infsum) 
  then have \<open>((\<lambda>F. \<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) \<longlongrightarrow> b) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    using LIM_zero tendsto_norm_zero by blast 
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) (filtermap (\<lambda>n. {..<n}) sequentially)\<close>
    by (meson filterlim_compose filterlim_filtermap filterlim_lessThan_at_top) 
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) sequentially\<close>
    by (simp add: filterlim_filtermap) 
  then have \<open>((\<lambda>m. trace_norm ((\<Sum>n\<in>{..<m}. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    unfolding a'_def b'_def
    by transfer
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    apply (rule tendsto_0_le[where K=1])
    by (auto intro!: eventually_sequentiallyI norm_leq_trace_norm trace_class_minus
        trace_class_sum trace_class_scaleC spectral_dec_proj_finite_rank
        intro: finite_rank_trace_class)
  then have \<open>(\<lambda>n. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) sums b'\<close>
    using LIM_zero_cancel sums_def tendsto_norm_zero_iff by blast 
  moreover have \<open>(\<lambda>n. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) sums a'\<close>
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> by (rule spectral_dec_sums)
  ultimately have \<open>a = b\<close>
    using a'_def b'_def from_trace_class_inject sums_unique2 by blast
  with has_sum_b show ?thesis
    by simp
qed


lemma spectral_dec_sums_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  sums  a\<close>
  using assms has_sum_imp_sums spectral_dec_has_sum_tc by blast 


subsection \<open>Misc\<close>


lemma finite_rank_tc_dense_aux: \<open>closure (Collect finite_rank_tc :: ('a::chilbert_space, 'a) trace_class set) = UNIV\<close>
proof (intro order_top_class.top_le subsetI)
  fix a :: \<open>('a,'a) trace_class\<close>
  wlog selfadj: \<open>selfadjoint_tc a\<close> goal \<open>a \<in> closure (Collect finite_rank_tc)\<close> generalizing a
  proof -
    define b c where \<open>b = a + adj_tc a\<close> and \<open>c = \<i> *\<^sub>C (a - adj_tc a)\<close>
    have \<open>adj_tc b = b\<close>
      unfolding b_def
      apply transfer
      by (simp add: adj_plus)
    have \<open>adj_tc c = c\<close>
      unfolding c_def
      apply transfer
      apply (simp add: adj_minus)
      by (metis minus_diff_eq scaleC_right.minus)
    have abc: \<open>a = (1/2) *\<^sub>C b + (-\<i>/2) *\<^sub>C c\<close>
      apply (simp add: b_def c_def)
      by (metis (no_types, lifting) cross3_simps(8) diff_add_cancel group_cancel.add2 scaleC_add_right scaleC_half_double)
    have \<open>b \<in> closure (Collect finite_rank_tc)\<close> and \<open>c \<in> closure (Collect finite_rank_tc)\<close>
      using \<open>adj_tc b = b\<close> \<open>adj_tc c = c\<close> hypothesis selfadjoint_tc_def' by auto
    with abc have \<open>a \<in> cspan (closure (Collect finite_rank_tc))\<close>
      by (metis complex_vector.span_add complex_vector.span_clauses(1) complex_vector.span_clauses(4))
    also have \<open>\<dots> \<subseteq> closure (cspan (Collect finite_rank_tc))\<close>
      by (simp add: closure_mono complex_vector.span_minimal complex_vector.span_superset)
    also have \<open>\<dots> = closure (Collect finite_rank_tc)\<close>
      by (metis Set.basic_monos(1) complex_vector.span_minimal complex_vector.span_superset csubspace_finite_rank_tc subset_antisym)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  sums  a\<close>
    by (simp add: spectral_dec_sums_tc)
  moreover from selfadj 
  have \<open>finite_rank_tc (\<Sum>i<n. spectral_dec_val_tc a i *\<^sub>C spectral_dec_proj_tc a i)\<close> for n
    apply (induction n)
     by (auto intro!: finite_rank_tc_plus spectral_dec_proj_tc_finite_rank finite_rank_tc_scale
        simp: selfadjoint_tc_def')
  ultimately show \<open>a \<in> closure (Collect finite_rank_tc)\<close>
    unfolding sums_def closure_sequential
    apply (auto intro!: simp: sums_def closure_sequential)
    by meson
qed


lemma finite_rank_tc_dense: \<open>closure (Collect finite_rank_tc :: ('a::chilbert_space, 'b::chilbert_space) trace_class set) = UNIV\<close>
proof -
  have \<open>UNIV = closure (Collect finite_rank_tc :: ('a\<times>'b, 'a\<times>'b) trace_class set)\<close>
    by (rule finite_rank_tc_dense_aux[symmetric])
  define l r and corner :: \<open>('a\<times>'b, 'a\<times>'b) trace_class \<Rightarrow> _\<close> where
    \<open>l = cblinfun_left\<close> and \<open>r = cblinfun_right\<close> and
    \<open>corner t = compose_tcl (compose_tcr (r*) t) l\<close> for t
  have [iff]: \<open>bounded_clinear corner\<close>
    by (auto intro: bounded_clinear_compose compose_tcl.bounded_clinear_left compose_tcr.bounded_clinear_right 
        simp: corner_def[abs_def])
  have \<open>UNIV = corner ` UNIV\<close>
  proof (intro UNIV_eq_I range_eqI)
    fix t
    have \<open>from_trace_class (corner (compose_tcl (compose_tcr r t) (l*)))
         = (r* o\<^sub>C\<^sub>L r) o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (l* o\<^sub>C\<^sub>L l)\<close>
      by (simp add: corner_def compose_tcl.rep_eq compose_tcr.rep_eq cblinfun_compose_assoc)
    also have \<open>\<dots> = from_trace_class t\<close>
      by (simp add: l_def r_def)
    finally show \<open>t = corner (compose_tcl (compose_tcr r t) (l*))\<close>
      by (metis from_trace_class_inject)
  qed
  also have \<open>\<dots> = corner ` closure (Collect finite_rank_tc)\<close>
    by (simp add: finite_rank_tc_dense_aux)
  also have \<open>\<dots> \<subseteq> closure (corner ` Collect finite_rank_tc)\<close>
    by (auto intro!: bounded_clinear.bounded_linear closure_bounded_linear_image_subset)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank_tc)\<close>
  proof (intro closure_mono subsetI CollectI)
    fix t assume \<open>t \<in> corner ` Collect finite_rank_tc\<close>
    then obtain u where \<open>finite_rank_tc u\<close> and tu: \<open>t = corner u\<close>
      by blast
    show \<open>finite_rank_tc t\<close>
      using \<open>finite_rank_tc u\<close>
      by (auto intro!: finite_rank_compose_right[of _ l] finite_rank_compose_left[of _ \<open>r*\<close>]
          simp add: corner_def tu finite_rank_tc.rep_eq compose_tcl.rep_eq compose_tcr.rep_eq)
  qed
  finally show ?thesis
    by blast
qed


hide_fact finite_rank_tc_dense_aux



lemma onb_butterflies_span_trace_class:
  fixes A :: \<open>'a::chilbert_space set\<close> and B :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>ccspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B)) = \<top>\<close>
proof -
  have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> Collect rank1_tc\<close>
  proof (rule subsetI)
    \<comment> \<open>This subproof is almost identical to the corresponding one in
        @{thm [source] finite_rank_dense_compact}, and lengthy. Can they be merged into one subproof?\<close>
    fix x :: \<open>('b, 'a) trace_class\<close> assume \<open>x \<in> Collect rank1_tc\<close>
    then obtain a b where xab: \<open>x = tc_butterfly a b\<close>
      apply transfer using rank1_iff_butterfly by fastforce
    define f where \<open>f F G = tc_butterfly (Proj (ccspan F) a) (Proj (ccspan G) b)\<close> for F G
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
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly)
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
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly mult.commute)
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
          by (simp add: f_def tc_butterfly_add_right tc_butterfly_add_left)
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
              case_prod f x \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
    proof (rule eventually_mp[where P=\<open>\<lambda>(F,G). finite F \<and> finite G\<close>])
      show \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. finite F \<and> finite G\<close>
        by (smt (verit) case_prod_conv eventually_finite_subsets_at_top_weakI eventually_prod_filter)
      have f_in_span: \<open>f F G \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close> if [simp]: \<open>finite F\<close> \<open>finite G\<close> and \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> for F G
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
        have \<open>tc_butterfly \<xi> \<eta> \<in> (\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)\<close>
          if \<open>\<eta> \<in> G\<close> and \<open>\<xi> \<in> F\<close> for \<eta> \<xi>
          using \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> that by (auto intro!: pair_imageI)
        then show ?thesis
          by (auto intro!: complex_vector.span_sum complex_vector.span_scale
              intro: complex_vector.span_base[where a=\<open>tc_butterfly _ _\<close>]
              simp add: f_def ProjFsum ProjGsum tc_butterfly_sum_left tc_butterfly_sum_right)
      qed
      show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B.
                      (case x of (F, G) \<Rightarrow> finite F \<and> finite G) \<longrightarrow> (case x of (F, G) \<Rightarrow> f F G) \<in> cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
        apply (rule eventually_mono)
        apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
        by (auto intro!: f_in_span)
    qed
    show \<open>x \<in> closure (cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
      using lim nontriv inside by (rule limit_in_closure)
  qed
  moreover have \<open>cspan (Collect rank1_tc :: ('b,'a) trace_class set) = Collect finite_rank_tc\<close>
    using finite_rank_tc_def' by fastforce
  moreover have \<open>closure (Collect finite_rank_tc :: ('b,'a) trace_class set) = UNIV\<close>
    by (rule finite_rank_tc_dense)
  ultimately have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> UNIV\<close>
    by (smt (verit, del_insts) Un_UNIV_left closed_sum_closure_left closed_sum_cspan closure_closure closure_is_csubspace complex_vector.span_eq_iff complex_vector.subspace_span subset_Un_eq)
  then show ?thesis
    by (metis ccspan.abs_eq ccspan_UNIV closure_UNIV complex_vector.span_UNIV top.extremum_uniqueI)
qed

lemma separating_set_tc_butterfly: \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` (UNIV \<times> UNIV))\<close>
  apply (rule separating_set_mono[where S=\<open>(\<lambda>(g, h). tc_butterfly g h) ` (some_chilbert_basis \<times> some_chilbert_basis)\<close>])
  by (auto intro!: separating_set_bounded_clinear_dense onb_butterflies_span_trace_class) 

lemma separating_set_tc_butterfly_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c conjugate_space) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly g h) ` (A \<times> B))\<close>
proof -
  from separating_set_tc_butterfly
  have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` prod.swap ` (UNIV \<times> UNIV))\<close>
    by simp
  then have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly h g) ` (UNIV \<times> UNIV))\<close>
    unfolding image_image by simp
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` (B \<times> A))\<close>
    apply (rule separating_set_bounded_sesquilinear_nested)
    apply (rule bounded_sesquilinear_tc_butterfly)
    using assms by auto
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` prod.swap ` (A \<times> B))\<close>
    by (smt (verit, del_insts) SigmaE SigmaI eq_from_separatingI image_iff pair_in_swap_image separating_setI)
  then show ?thesis
    unfolding image_image by simp
qed


end
