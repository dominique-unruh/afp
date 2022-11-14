theory Partial_Trace
  imports Trace_Class Hilbert_Space_Tensor_Product
begin

(* TODO: A different definition is given in Axioms_Complement_Quantum (allows to take partial traces
even of non-traceclass operators). Merge with this proof. *)
definition partial_trace :: \<open>(('a \<times> 'c) ell2, ('b \<times> 'c) ell2) trace_class \<Rightarrow> ('a ell2, 'b ell2) trace_class\<close> where
  \<open>partial_trace t = (\<Sum>\<^sub>\<infinity>j. Abs_trace_class ((tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))))\<close>


lemma partial_trace_abs_summable: 
  \<open>(\<lambda>j. Abs_trace_class ((tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j)))) abs_summable_on UNIV\<close>
  and partial_trace_has_sum:
  \<open>has_sum (\<lambda>j. Abs_trace_class ((tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j)))) UNIV (partial_trace t)\<close>
  and partial_trace_norm_reducing: \<open>norm (partial_trace t) \<le> norm t\<close>
proof -
  define t' where \<open>t' = from_trace_class t\<close>
  define s where \<open>s k = Abs_trace_class (tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k))\<close> for k

  have bound: \<open>(\<Sum>k\<in>F. norm (s k)) \<le> norm t\<close>
    if  \<open>F \<in> {F. F \<subseteq> UNIV \<and> finite F}\<close>
    for F :: \<open>'a set\<close>
  proof -
    from that have [simp]: \<open>finite F\<close>
      by force
    define tk where \<open>tk k = tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k)\<close> for k
    have tc_t'[simp]: \<open>trace_class t'\<close>
      by (simp add: t'_def)
    then have tc_tk[simp]: \<open>trace_class (tk k)\<close> for k
      by (simp add: tk_def trace_class_comp_left trace_class_comp_right)
    define uk where \<open>uk k = (polar_decomposition (tk k))*\<close> for k
    define u where \<open>u = (\<Sum>k\<in>F. uk k \<otimes>\<^sub>o selfbutterket k)\<close>
    define B :: \<open>'b ell2 set\<close> where \<open>B = range ket\<close>

    have aux1: \<open>tensor_ell2_right (ket x)* *\<^sub>V u *\<^sub>V a = 0\<close> if \<open>x \<notin> F\<close> for x a
    proof -
      have \<open>u* o\<^sub>C\<^sub>L tensor_ell2_right (ket x) = 0\<close>
        by (auto intro!: equal_ket simp: u_def sum_adj tensor_op_adjoint tensor_ell2_right_apply
            cblinfun.sum_left tensor_op_ell2 cinner_ket sum_single[where i=x] \<open>x \<notin> F\<close>)
      then have \<open>tensor_ell2_right (ket x)* o\<^sub>C\<^sub>L u = 0\<close>
        apply (rule_tac adj_inject[THEN iffD1])
        by simp 
      then show ?thesis
        by (simp flip: cblinfun_apply_cblinfun_compose)
    qed

    have aux2: \<open>uk x *\<^sub>V tensor_ell2_right (ket x)* *\<^sub>V a = tensor_ell2_right (ket x)* *\<^sub>V u *\<^sub>V a\<close> if \<open>x \<in> F\<close> for x a
    proof - 
      have \<open>tensor_ell2_right (ket x) o\<^sub>C\<^sub>L (uk x)* = u* o\<^sub>C\<^sub>L tensor_ell2_right (ket x)\<close>
        by (auto intro!: equal_ket simp: u_def sum_adj tensor_op_adjoint tensor_ell2_right_apply
            cblinfun.sum_left tensor_op_ell2 \<open>x \<in> F\<close> cinner_ket sum_single[where i=x])
      then have \<open>uk x o\<^sub>C\<^sub>L tensor_ell2_right (ket x)* = tensor_ell2_right (ket x)* o\<^sub>C\<^sub>L u\<close>
        apply (rule_tac adj_inject[THEN iffD1])
        by simp 
      then show ?thesis
        by (simp flip: cblinfun_apply_cblinfun_compose)
    qed

    have sum1: \<open>(\<lambda>(x, y). ket (y, x) \<bullet>\<^sub>C (u *\<^sub>V t' *\<^sub>V ket (y, x))) summable_on UNIV\<close>
    proof -
      have \<open>trace_class (u o\<^sub>C\<^sub>L t')\<close>
        by (simp add: trace_class_comp_right)
      then have \<open>(\<lambda>yx. yx \<bullet>\<^sub>C ((u o\<^sub>C\<^sub>L t') *\<^sub>V yx)) summable_on (range ket)\<close>
        using is_onb_ket trace_exists by blast
      then have \<open>(\<lambda>yx. ket yx \<bullet>\<^sub>C ((u o\<^sub>C\<^sub>L t') *\<^sub>V ket yx)) summable_on UNIV\<close>
        apply (subst summable_on_reindex_bij_betw[where g=ket and A=UNIV and B=\<open>range ket\<close>])
         apply auto using bij_betw_def inj_ket by blast
      then show ?thesis
        apply (subst summable_on_reindex_bij_betw[where g=prod.swap and A=UNIV, symmetric])
        by auto
    qed

    have norm_u: \<open>norm u \<le> 1\<close>
    proof -
      define u2 uk2 where \<open>u2 = u* o\<^sub>C\<^sub>L u\<close> and \<open>uk2 k = (uk k)* o\<^sub>C\<^sub>L uk k\<close> for k (* and \<open>u4 = u2* o\<^sub>C\<^sub>L u2\<close> *)
      have *: \<open>(\<Sum>i\<in>F. (uk i* o\<^sub>C\<^sub>L uk k) \<otimes>\<^sub>o (ket i \<bullet>\<^sub>C ket k) *\<^sub>C butterket i k)
           = (uk k* o\<^sub>C\<^sub>L uk k) \<otimes>\<^sub>o selfbutterket k\<close> if [simp]: \<open>k \<in> F\<close> for k
        apply (subst sum_single[where i=k])
        by (auto simp: cinner_ket)
      have **: \<open>(\<Sum>ka\<in>F. (uk2 ka o\<^sub>C\<^sub>L uk2 k) \<otimes>\<^sub>o (ket ka \<bullet>\<^sub>C ket k) *\<^sub>C butterket ka k)
           = (uk2 k o\<^sub>C\<^sub>L uk2 k) \<otimes>\<^sub>o selfbutterket k\<close> if [simp]: \<open>k \<in> F\<close> for k
        apply (subst sum_single[where i=k])
        by (auto simp: cinner_ket)
      have proj_uk2: \<open>is_Proj (uk2 k)\<close> for k
        unfolding uk2_def
        apply (rule partial_isometry_square_proj)
        by (auto intro!: partial_isometry_square_proj partial_isometry_adj simp: uk_def)
      have u2_explicit: \<open>u2 = (\<Sum>k\<in>F. uk2 k \<otimes>\<^sub>o selfbutterket k)\<close>
        by (simp add: u2_def u_def sum_adj tensor_op_adjoint cblinfun_compose_sum_right 
            cblinfun_compose_sum_left tensor_butter comp_tensor_op * uk2_def)
      have \<open>u2* = u2\<close>
        by (simp add: u2_def)
      moreover have \<open>u2 o\<^sub>C\<^sub>L u2 = u2\<close>
        by (simp add: u2_explicit cblinfun_compose_sum_right cblinfun_compose_sum_left
            comp_tensor_op ** proj_uk2 is_Proj_idempotent)
      ultimately have \<open>is_Proj u2\<close>
        by (simp add: is_Proj_I)
      then have \<open>norm u2 \<le> 1\<close>
        using norm_is_Proj by blast
      then show \<open>norm u \<le> 1\<close>
        by (simp add: power_le_one_iff norm_AAadj u2_def)
    qed

    have \<open>(\<Sum>k\<in>F. norm (s k))
      = (\<Sum>k\<in>F. trace_norm (tk k))\<close>
      by (metis (no_types, opaque_lifting) s_def Abs_trace_class_inverse mem_Collect_eq norm_trace_class.rep_eq tc_tk tk_def)
    also have \<open>\<dots> = cmod (\<Sum>k\<in>F. trace (uk k o\<^sub>C\<^sub>L tk k))\<close>
      by (smt (verit, best) norm_of_real of_real_hom.hom_sum polar_decomposition_correct' sum.cong sum_nonneg trace_abs_op trace_norm_nneg uk_def)
    also have \<open>\<dots> = cmod (\<Sum>k\<in>F. trace (tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k)))\<close>
      apply (rule arg_cong[where f=cmod], rule sum.cong[OF refl], rule arg_cong[where f=trace])
      by (auto intro!: equal_ket simp: tk_def aux2)
    also have \<open>\<dots> = cmod (\<Sum>k\<in>F. \<Sum>\<^sub>\<infinity>j. ket j \<bullet>\<^sub>C ((tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k)) *\<^sub>V ket j))\<close>
      by (auto intro!: sum.cong simp: trace_ket_sum trace_class_comp_left trace_class_comp_right)
    also have \<open>\<dots> = cmod (\<Sum>\<^sub>\<infinity>k\<in>F. \<Sum>\<^sub>\<infinity>j. ket j \<bullet>\<^sub>C ((tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k)) *\<^sub>V ket j))\<close>
      by (simp add: \<open>finite F\<close>)
    also have \<open>\<dots> = cmod (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>j. ket j \<bullet>\<^sub>C ((tensor_ell2_right (ket k)* o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L t' o\<^sub>C\<^sub>L tensor_ell2_right (ket k)) *\<^sub>V ket j))\<close>
      apply (rule arg_cong[where f=cmod])
      apply (rule infsum_cong_neutral)
      by (auto simp: aux1)
    also have \<open>\<dots> = cmod (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>j. ket (j,k) \<bullet>\<^sub>C ((u o\<^sub>C\<^sub>L t') *\<^sub>V ket (j,k)))\<close>
      apply (rule arg_cong[where f=cmod], rule infsum_cong, rule infsum_cong)
      by (simp add: tensor_ell2_right_apply cinner_adj_right tensor_ell2_ket)
    also have \<open>\<dots> = cmod (\<Sum>\<^sub>\<infinity>(k,j). ket (j,k) \<bullet>\<^sub>C ((u o\<^sub>C\<^sub>L t') *\<^sub>V ket (j,k)))\<close>
      apply (rule arg_cong[where f=cmod])
      apply (subst infsum_Sigma'_banach)
      using sum1 by auto
    also have \<open>\<dots> = cmod (\<Sum>\<^sub>\<infinity>jk. ket jk \<bullet>\<^sub>C ((u o\<^sub>C\<^sub>L t') *\<^sub>V ket jk))\<close>
      apply (subst infsum_reindex_bij_betw[where g=prod.swap and A=UNIV, symmetric])
      by auto
    also have \<open>\<dots> = cmod (trace (u o\<^sub>C\<^sub>L t'))\<close>
      by (simp add: trace_ket_sum trace_class_comp_right)
    also have \<open>\<dots> \<le> trace_norm (u o\<^sub>C\<^sub>L t')\<close>
      using trace_leq_trace_norm by blast
    also have \<open>\<dots> \<le> norm u * trace_norm t'\<close>
      by (simp add: trace_norm_comp_right)
    also have \<open>\<dots> \<le> trace_norm t'\<close>
      using norm_u
      by (metis more_arith_simps(5) mult_right_mono trace_norm_nneg)
    also have \<open>\<dots> = norm t\<close>
      by (simp add: norm_trace_class.rep_eq t'_def)
    finally show \<open>(\<Sum>k\<in>F. norm (s k)) \<le> norm t\<close>
      by -
  qed

  show abs_summable: \<open>s abs_summable_on UNIV\<close>
    by (intro nonneg_bdd_above_summable_on bdd_aboveI2[where M=\<open>norm t\<close>] norm_ge_zero bound)

  from abs_summable
  show has_sum: \<open>has_sum s UNIV (partial_trace t)\<close>
    by (simp add: abs_summable_summable partial_trace_def s_def[abs_def] t'_def)

  show \<open>norm (partial_trace t) \<le> norm t\<close>
  proof -
    have \<open>norm (partial_trace t) \<le> (\<Sum>\<^sub>\<infinity>k. norm (s k))\<close>
      using _ has_sum apply (rule norm_has_sum_bound)
      using abs_summable has_sum_infsum by blast
    also from bound have \<open>(\<Sum>\<^sub>\<infinity>k. norm (s k)) \<le> norm t\<close>
      by (simp add: abs_summable infsum_le_finite_sums)
    finally show ?thesis
      by -
  qed
qed

definition partial_trace' where \<open>partial_trace' t = (if trace_class t then from_trace_class (partial_trace (Abs_trace_class t)) else 0)\<close>

lemma partial_trace_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(cr_trace_class ===> cr_trace_class) partial_trace' partial_trace\<close>
  by (auto intro!: rel_funI simp: cr_trace_class_def partial_trace'_def from_trace_class_inverse)


end

