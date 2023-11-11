theory Partial_Trace
  imports Trace_Class Hilbert_Space_Tensor_Product
begin

hide_fact (open) Infinite_Set_Sum.abs_summable_on_Sigma_iff
hide_fact (open) Infinite_Set_Sum.abs_summable_on_comparison_test
hide_const (open) Determinants.trace
hide_fact (open) Determinants.trace_def

(* TODO: use compose_tcl/compose_tcr *)
definition partial_trace :: \<open>(('a \<times> 'c) ell2, ('b \<times> 'c) ell2) trace_class \<Rightarrow> ('a ell2, 'b ell2) trace_class\<close> where
  \<open>partial_trace t = (\<Sum>\<^sub>\<infinity>j. compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) t) (tensor_ell2_right (ket j)))\<close>
  (* \<open>partial_trace t = (\<Sum>\<^sub>\<infinity>j. Abs_trace_class ((tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))))\<close> *)

lemma partial_trace_def': \<open>partial_trace t = (\<Sum>\<^sub>\<infinity>j. sandwich_tc ((tensor_ell2_right (ket j))*) t)\<close>
\<comment> \<open>We cannot use this as the definition of \<^const>\<open>partial_trace\<close> because this definition
      has a more restricted type (\<^term>\<open>t\<close> is a square operator).\<close>
  by (auto intro!: simp: partial_trace_def sandwich_tc_def)

lemma partial_trace_abs_summable:
  \<open>(\<lambda>j. compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) t) (tensor_ell2_right (ket j))) abs_summable_on UNIV\<close>
  and partial_trace_has_sum:
  \<open>((\<lambda>j. compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) t) (tensor_ell2_right (ket j))) has_sum partial_trace t) UNIV\<close>
  and partial_trace_norm_reducing: \<open>norm (partial_trace t) \<le> norm t\<close>
proof -
  define t' where \<open>t' = from_trace_class t\<close>
  define s where \<open>s k = compose_tcl (compose_tcr ((tensor_ell2_right (ket k))*) t) (tensor_ell2_right (ket k))\<close> for k

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
    define u where \<open>u = (\<Sum>k\<in>F. uk k \<otimes>\<^sub>o butterfly (ket k) (ket k))\<close>
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
      have *: \<open>(\<Sum>i\<in>F. (uk i* o\<^sub>C\<^sub>L uk k) \<otimes>\<^sub>o (ket i \<bullet>\<^sub>C ket k) *\<^sub>C butterfly (ket i) (ket k))
           = (uk k* o\<^sub>C\<^sub>L uk k) \<otimes>\<^sub>o butterfly (ket k) (ket k)\<close> if [simp]: \<open>k \<in> F\<close> for k
        apply (subst sum_single[where i=k])
        by (auto simp: cinner_ket)
      have **: \<open>(\<Sum>ka\<in>F. (uk2 ka o\<^sub>C\<^sub>L uk2 k) \<otimes>\<^sub>o (ket ka \<bullet>\<^sub>C ket k) *\<^sub>C butterfly (ket ka) (ket k))
           = (uk2 k o\<^sub>C\<^sub>L uk2 k) \<otimes>\<^sub>o butterfly (ket k) (ket k)\<close> if [simp]: \<open>k \<in> F\<close> for k
        apply (subst sum_single[where i=k])
        by (auto simp: cinner_ket)
      have proj_uk2: \<open>is_Proj (uk2 k)\<close> for k
        unfolding uk2_def
        apply (rule partial_isometry_square_proj)
        by (auto intro!: partial_isometry_square_proj partial_isometry_adj simp: uk_def)
      have u2_explicit: \<open>u2 = (\<Sum>k\<in>F. uk2 k \<otimes>\<^sub>o butterfly (ket k) (ket k))\<close>
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
      by (simp add: s_def tk_def norm_trace_class.rep_eq compose_tcl.rep_eq compose_tcr.rep_eq t'_def)
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
  show has_sum: \<open>(s has_sum partial_trace t) UNIV\<close>
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

lemma partial_trace_abs_summable':
  \<open>(\<lambda>j.  sandwich_tc ((tensor_ell2_right (ket j))*) t) abs_summable_on UNIV\<close>
  and partial_trace_has_sum':
  \<open>((\<lambda>j.  sandwich_tc ((tensor_ell2_right (ket j))*) t) has_sum partial_trace t) UNIV\<close>
  using partial_trace_abs_summable partial_trace_has_sum
  by (auto intro!: simp: sandwich_tc_def sandwich_apply)

(* definition partial_trace' where \<open>partial_trace' t = (if trace_class t then from_trace_class (partial_trace (Abs_trace_class t)) else 0)\<close>

lemma partial_trace_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(cr_trace_class ===> cr_trace_class) partial_trace' partial_trace\<close>
  by (auto intro!: rel_funI simp: cr_trace_class_def partial_trace'_def from_trace_class_inverse) *)


lemma trace_partial_trace_compose_eq_trace_compose_tensor_id: 
  \<open>trace (from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) = trace (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
proof -
  define s where \<open>s = trace (from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x)\<close>
  define s' where \<open>s' e = ket e \<bullet>\<^sub>C ((from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) *\<^sub>V ket e)\<close> for e
  define u where \<open>u j = compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) t) (tensor_ell2_right (ket j))\<close> for j
  define u' where \<open>u' e j = ket e \<bullet>\<^sub>C (from_trace_class (u j) *\<^sub>V x *\<^sub>V ket e)\<close> for e j
  have \<open>(u has_sum partial_trace t) UNIV\<close>
    using partial_trace_has_sum[of t]
    by (simp add: u_def[abs_def])
  then have \<open>((\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) o u has_sum from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e) UNIV\<close> for e
  proof (rule has_sum_comm_additive[rotated -1])
    show \<open>Modules.additive (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e)\<close>
      by (simp add: Modules.additive_def cblinfun.add_left plus_trace_class.rep_eq)
    have bounded_clinear: \<open>bounded_clinear (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e)\<close>
    proof (rule bounded_clinearI[where K=\<open>norm (x *\<^sub>V ket e)\<close>])
      show \<open>from_trace_class (b1 + b2) *\<^sub>V x *\<^sub>V ket e = from_trace_class b1 *\<^sub>V x *\<^sub>V ket e + from_trace_class b2 *\<^sub>V x *\<^sub>V ket e\<close> for b1 b2
        by (simp add: plus_cblinfun.rep_eq plus_trace_class.rep_eq)
      show \<open>from_trace_class (r *\<^sub>C b) *\<^sub>V x *\<^sub>V ket e = r *\<^sub>C (from_trace_class b *\<^sub>V x *\<^sub>V ket e)\<close> for b r
        by (simp add: scaleC_trace_class.rep_eq)
      show \<open>norm (from_trace_class t *\<^sub>V x *\<^sub>V ket e) \<le> norm t * norm (x *\<^sub>V ket e)\<close> for t
      proof -
        have \<open>norm (from_trace_class t *\<^sub>V x *\<^sub>V ket e) \<le> norm (from_trace_class t) * norm (x *\<^sub>V ket e)\<close>
          by (simp add: norm_cblinfun)
        also have \<open>\<dots> \<le> norm t * norm (x *\<^sub>V ket e)\<close>
          by (auto intro!: mult_right_mono simp add: norm_leq_trace_norm norm_trace_class.rep_eq)
        finally show ?thesis
          by -
      qed
    qed
    have \<open>isCont (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) (partial_trace t)\<close>
      using bounded_clinear clinear_continuous_at by auto
    then show \<open>(\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) \<midarrow>partial_trace t\<rightarrow> from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e\<close>
      by (simp add: isCont_def)
  qed
  then have \<open>((\<lambda>v. ket e \<bullet>\<^sub>C v) o ((\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) o u) has_sum ket e \<bullet>\<^sub>C (from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e)) UNIV\<close> for e 
  proof (rule has_sum_comm_additive[rotated -1])
    show \<open>Modules.additive (\<lambda>v. ket e \<bullet>\<^sub>C v)\<close>
      by (simp add: Modules.additive_def cinner_simps(2))
    have bounded_clinear: \<open>bounded_clinear (\<lambda>v. ket e \<bullet>\<^sub>C v)\<close>
      using bounded_clinear_cinner_right by auto
    then have \<open>isCont (\<lambda>v. ket e \<bullet>\<^sub>C v) l\<close> for l
      by simp
    then show \<open>(\<lambda>v. ket e \<bullet>\<^sub>C v) \<midarrow>l\<rightarrow> ket e \<bullet>\<^sub>C l\<close> for l
      by (simp add: isContD)
  qed
  then have has_sum_u': \<open>((\<lambda>j. u' e j) has_sum s' e) UNIV\<close> for e 
    by (simp add: o_def u'_def s'_def)
  then have infsum_u': \<open>s' e = infsum (u' e) UNIV\<close> for e
    by (metis infsumI)
  have tc_u_x[simp]: \<open>trace_class (from_trace_class (u j) o\<^sub>C\<^sub>L x)\<close> for j
    by (simp add: trace_class_comp_left)

  have summable_u'_pairs: \<open>(\<lambda>(e, j). u' e j) summable_on UNIV \<times> UNIV\<close>
  proof -
    have \<open>trace_class (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
      by (simp add: trace_class_comp_left)
    from trace_exists[OF is_onb_ket this]
    have \<open>(\<lambda>ej. ket ej \<bullet>\<^sub>C (from_trace_class t *\<^sub>V (x \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket ej)) summable_on UNIV\<close>
      by (simp_all add: summable_on_reindex o_def)
    then show ?thesis
      by (simp_all add: o_def u'_def[abs_def] u_def
          trace_class_comp_left trace_class_comp_right Abs_trace_class_inverse tensor_ell2_right_apply 
          ket_pair_split tensor_op_ell2 case_prod_unfold cinner_adj_right
          compose_tcl.rep_eq compose_tcr.rep_eq)
  qed

  have u'_tensor: \<open>u' e j = ket (e,j) \<bullet>\<^sub>C ((from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun)) *\<^sub>V ket (e,j))\<close> for e j
    by (simp add: u'_def u_def tensor_op_ell2 tensor_ell2_right_apply  Abs_trace_class_inverse
        trace_class_comp_left trace_class_comp_right cinner_adj_right compose_tcl.rep_eq compose_tcr.rep_eq
        flip: tensor_ell2_ket)

  have \<open>((\<lambda>e. e \<bullet>\<^sub>C ((from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) *\<^sub>V e)) has_sum s) (range ket)\<close>
    unfolding s_def
    apply (rule trace_has_sum)
    by (auto simp: trace_class_comp_left)
  then have \<open>(s' has_sum s) UNIV\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def s'_def[abs_def])
  then have \<open>s = infsum s' UNIV\<close>
    by (simp add: infsumI)
  also have \<open>\<dots> = infsum (\<lambda>e. infsum (u' e) UNIV) UNIV\<close>
    using infsum_u' by presburger
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(e, j)\<in>UNIV. u' e j)\<close>
    apply (subst infsum_Sigma'_banach)
     apply (rule summable_u'_pairs)
    by simp
  also have \<open>\<dots> = trace (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
    unfolding u'_tensor 
    by (simp add: trace_ket_sum cond_case_prod_eta trace_class_comp_left)
  finally show ?thesis
    by (simp add: s_def)
qed



lemma right_amplification_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
  \<comment> \<open>Logically does not belong in this theory but uses the partial trace in the proof.\<close>
proof (unfold weak_star_topology_def', rule continuous_map_pullback_both)
  show \<open>S \<subseteq> f -` UNIV\<close> for S :: \<open>'x set\<close> and f :: \<open>'x \<Rightarrow> 'y\<close>
    by simp
  define g' :: \<open>(('b ell2, 'a ell2) trace_class \<Rightarrow> complex) \<Rightarrow> (('b \<times> 'c) ell2, ('a \<times> 'c) ell2) trace_class \<Rightarrow> complex\<close> where
    \<open>g' \<tau> t = \<tau> (partial_trace t)\<close> for \<tau> t
  have \<open>continuous_on UNIV g'\<close>
    by (simp add: continuous_on_coordinatewise_then_product g'_def)
  then show \<open>continuous_map euclidean euclidean g'\<close>
    using continuous_map_iff_continuous2 by blast
  show \<open>g' (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) =
         (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x \<otimes>\<^sub>o id_cblinfun))\<close> for x
    by (auto intro!: ext simp: g'_def trace_partial_trace_compose_eq_trace_compose_tensor_id)
qed

lemma left_amplification_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b :: ('c\<times>'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c\<times>'b) ell2)\<close>
  \<comment> \<open>Logically does not belong in this theory but uses the partial trace in the proof.\<close>
proof -
  have \<open>continuous_map weak_star_topology weak_star_topology (
        (\<lambda>x. x o\<^sub>C\<^sub>L swap_ell2) o (\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x) o (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a\<times>'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'c) ell2))\<close>
    by (auto intro!: continuous_map_compose[where X'=weak_star_topology]
        continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star)
  then show ?thesis
    by (auto simp: o_def)
qed

end

