theory Unsorted2
  imports Spectral_Theorem Trace_Class
begin



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
