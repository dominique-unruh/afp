theory Kraus_Families
  imports
    Wlog.Wlog
    Hilbert_Space_Tensor_Product.Partial_Trace
  
    Misc_Kraus_Maps
  
  abbrevs
    "=kr" = "=\<^sub>k\<^sub>r" and "==kr" = "\<equiv>\<^sub>k\<^sub>r" and "*kr" = "*\<^sub>k\<^sub>r"
begin

unbundle cblinfun_syntax

subsection \<open>Kraus families\<close>

definition \<open>kraus_family \<EE> \<longleftrightarrow> bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  for \<EE> :: \<open>((_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space) \<times> _) set\<close>

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family = 
  \<open>Collect kraus_family :: (('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'x) set set\<close>
  by (rule exI[of _ \<open>{}\<close>], auto simp: kraus_family_def)
setup_lifting type_definition_kraus_family

lemma kraus_familyI:
  assumes \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  shows \<open>kraus_family \<EE>\<close>
  by (meson assms kraus_family_def)

lift_definition kf_apply :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'a) trace_class \<Rightarrow> ('b,'b) trace_class\<close> is
  \<open>\<lambda>\<EE> \<rho>. (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>)\<close> .
notation kf_apply (infixr \<open>*\<^sub>k\<^sub>r\<close> 70)

lemma kraus_family_if_finite[iff]: \<open>kraus_family \<EE>\<close> if \<open>finite \<EE>\<close>
proof -
  define B where \<open>B = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  have \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close> for M
    unfolding B_def
    using \<open>finite \<EE>\<close> \<open>M \<subseteq> \<EE>\<close> apply (rule sum_mono2)
    by (auto intro!: positive_cblinfun_squareI)
  with that show ?thesis
    by (auto intro!: bdd_aboveI[of _ B] simp: kraus_family_def)
qed

lemma kf_apply_scaleC:
  shows \<open>kf_apply \<EE> (c *\<^sub>C x) = c *\<^sub>C kf_apply \<EE> x\<close>
  by (simp add: kf_apply_def cblinfun.scaleC_right case_prod_unfold sandwich_tc_scaleC_right
      flip: infsum_scaleC_right)

lemma kf_apply_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (sandwich_tc x \<rho>) 
      \<le> norm (sandwich_tc x \<rho>1)
      + norm (sandwich_tc x \<rho>2)
      + norm (sandwich_tc x \<rho>3)
      + norm (sandwich_tc x \<rho>4)\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      by (auto simp add: \<rho>_decomp sandwich_tc_plus sandwich_tc_minus  sandwich_tc_scaleC_right
          scaleC_add_right scaleC_diff_right norm_mult
          intro!: norm_triangle_le norm_triangle_le_diff)
    then have *: \<open>norm (sandwich_tc (fst x) \<rho>) \<le> norm (?S (fst x))\<close> for x
      by force
    show ?thesis
      unfolding case_prod_unfold
      apply (rule abs_summable_on_comparison_test[OF _ *])
      apply (intro Misc_Kraus_Maps.abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right pos)
      using hypothesis
      by (simp_all add: case_prod_unfold pos)
  qed

  have aux: \<open>trace_norm x = Re (trace x)\<close> if \<open>x \<ge> 0\<close> and \<open>trace_class x\<close> for x
    by (metis Re_complex_of_real that(1) trace_norm_pos)
  have trace_EE\<rho>_pos: \<open>trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>) \<ge> 0\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    apply (simp add: cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
    by (auto intro!: trace_pos sandwich_pos 
        simp: cblinfun_assoc_left from_trace_class_pos \<rho>_pos 
        simp flip: sandwich_apply)
  have trace_EE\<rho>_lin: \<open>linear (\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (rule linear_compose[where g=Re, unfolded o_def])
    by (auto intro!: bounded_linear.linear bounded_clinear.bounded_linear
        bounded_clinear_trace_duality' bounded_linear_Re)
  have trace_EE\<rho>_mono: \<open>mono_on (Collect ((\<le>) 0)) (\<lambda>A. Re (trace (A o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (auto intro!: mono_onI Re_mono)
    apply (subst diff_ge_0_iff_ge[symmetric])
    apply (subst trace_minus[symmetric])
    by (auto intro!: trace_class_comp_right trace_comp_pos
        simp: from_trace_class_pos \<rho>_pos
        simp flip: cblinfun_compose_minus_left)

  from assms
  have \<open>bdd_above ((\<lambda>F. (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>F. Re (trace ((\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    apply (rule bdd_above_transform_mono_pos)
    by (auto intro!: sum_nonneg positive_cblinfun_squareI[OF refl] trace_EE\<rho>_mono
        simp: case_prod_unfold)
  then have \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. F \<subseteq> \<EE> \<and> finite F})\<close>
    apply (subst (asm) real_vector.linear_sum[where f=\<open>\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>])
    by (auto intro!: trace_EE\<rho>_lin simp: case_prod_unfold conj_commute)
  then have \<open>(\<lambda>(E,_). Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) summable_on \<EE>\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    using trace_EE\<rho>_pos 
    by (auto simp: less_eq_complex_def)
 then have \<open>(\<lambda>(E,_). Re (trace (from_trace_class (sandwich_tc E \<rho>)))) summable_on \<EE>\<close>
    by (simp add: from_trace_class_sandwich_tc sandwich_apply cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
  then have \<open>(\<lambda>(E,_). trace_norm (from_trace_class (sandwich_tc E \<rho>))) summable_on \<EE>\<close>
    by (simp add: aux from_trace_class_pos \<rho>_pos  sandwich_tc_pos)
  then show \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
    by (simp add: norm_trace_class.rep_eq case_prod_unfold)
qed

lemma kf_apply_summable:
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) summable_on (Rep_kraus_family \<EE>)\<close>
  apply (rule abs_summable_summable)
  apply (rule kf_apply_abs_summable)
  using Rep_kraus_family by blast


lemma kf_apply_has_sum:
  shows \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kf_apply \<EE> \<rho>) (Rep_kraus_family \<EE>)\<close>
  using kf_apply_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: has_sum_infsum simp add: kf_apply_def kf_apply_summable case_prod_unfold)

lemma kf_apply_plus_right:
  shows \<open>kf_apply \<EE> (x + y) = kf_apply \<EE> x + kf_apply \<EE> y\<close>
  using kf_apply_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_add
      simp add: kf_apply_def sandwich_tc_plus scaleC_add_right case_prod_unfold)

lemma kf_apply_uminus_right:
  shows \<open>kf_apply \<EE> (- x) = - kf_apply \<EE> x\<close>
  using kf_apply_summable  Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_uminus 
      simp add: kf_apply_def sandwich_tc_uminus_right scaleC_minus_right case_prod_unfold)


lemma kf_apply_minus_right:
  shows \<open>kf_apply \<EE> (x - y) = kf_apply \<EE> x - kf_apply \<EE> y\<close>
  by (simp only: diff_conv_add_uminus kf_apply_plus_right kf_apply_uminus_right)

lemma kf_apply_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg_traceclass scaleC_nonneg_nonneg of_nat_0_le_iff
      sandwich_tc_pos assms simp: kf_apply_def)

lemma kf_apply_mono_right:
  assumes \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> kf_apply \<EE> \<tau>\<close>
  apply (subst diff_ge_0_iff_ge[symmetric])
  apply (subst kf_apply_minus_right[symmetric])
  apply (rule kf_apply_pos)
  using assms by (subst diff_ge_0_iff_ge)

lemma kf_apply_geq_sum:
  assumes \<open>\<rho> \<ge> 0\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> (\<Sum>(E,_)\<in>M. sandwich_tc E \<rho>)\<close>
proof (cases \<open>finite M\<close>)
  case True
  have *: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on X\<close> if \<open>X \<subseteq> Rep_kraus_family \<EE>\<close> for X
    apply (rule summable_on_subset_banach[where A=\<open>Rep_kraus_family \<EE>\<close>])
     apply (rule kf_apply_summable[unfolded case_prod_unfold])
    using assms that by blast
  show ?thesis
    apply (subst infsum_finite[symmetric])
    using assms 
    by (auto intro!: infsum_mono_neutral_traceclass * scaleC_nonneg_nonneg of_nat_0_le_iff 
        True sandwich_tc_pos
        simp: kf_apply_def case_prod_unfold)
next
  case False
  with assms show ?thesis
    by (simp add: kf_apply_pos) 
qed

lift_definition kf_domain :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> 'x set\<close> is
  \<open>\<lambda>\<EE>. snd ` Set.filter (\<lambda>(E,x). E \<noteq> 0) \<EE>\<close>.

lift_definition kf_remove_0 :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>Set.filter (\<lambda>(E,x). E\<noteq>0)\<close>
proof -
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
  have *: \<open>{F. finite F \<and> F \<subseteq> Set.filter (\<lambda>p. fst p \<noteq> 0) \<EE>} \<subseteq> {F. finite F \<and> F \<subseteq> \<EE>}\<close>
    by auto
  show \<open>\<EE> \<in> Collect kraus_family \<Longrightarrow> Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE> \<in> Collect kraus_family\<close>
    by (auto intro: bdd_above_mono2[OF _ *] simp add: kraus_family_def case_prod_unfold)
qed

lemma kf_apply_remove_0[simp]:
  \<open>kf_apply (kf_remove_0 \<EE>) = kf_apply \<EE>\<close>
  by (auto intro!: ext infsum_cong_neutral simp add: kf_apply_def kf_remove_0.rep_eq)


lemma kf_apply_clinear[iff]: \<open>clinear (kf_apply \<EE>)\<close>
  by (auto intro!: clinearI kf_apply_plus_right kf_apply_scaleC mult.commute)


lemma kf_apply_0_right[iff]: \<open>kf_apply \<EE> 0 = 0\<close>
  by (metis ab_left_minus kf_apply_plus_right kf_apply_uminus_right)

lemma kraus_familyI_0:
  assumes \<open>\<And>E x. (E,x) \<in> \<EE> \<Longrightarrow> E = 0\<close>
  shows \<open>kraus_family \<EE>\<close>
proof (unfold kraus_family_def, rule bdd_aboveI2)
  fix F
  assume F: \<open>F \<in> {F. finite F \<and> F \<subseteq> \<EE>}\<close>
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = 0\<close>
  proof (intro sum.neutral ballI)
    fix Ex assume asm: \<open>Ex \<in> F\<close>
    obtain E x where Ex: \<open>Ex = (E,x)\<close>
      by fastforce
    with asm F assms have \<open>E = 0\<close>
      by blast
    then show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) = 0\<close>
      by (simp add: Ex)
  qed
  then show \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
    by simp
qed


subsection \<open>Bound and norm\<close>

lift_definition kf_bound :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> is
  \<open>\<lambda>\<EE>. infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close> .

lemma kf_bound_def':
  \<open>kf_bound \<EE> = Rep_cblinfun_wot (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
  unfolding kf_bound.rep_eq infsum_euclidean_eq[symmetric]
  apply transfer'
  by simp

definition \<open>kf_norm \<EE> = norm (kf_bound \<EE>)\<close>

lemma kf_norm_sum_bdd: \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where B_bound: \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  have \<open>norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (no_types, lifting) B_bound norm_cblinfun_mono positive_cblinfun_squareI split_def sum_nonneg that(1) that(2))
  then show \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
    by (metis (mono_tags, lifting) bdd_aboveI2 mem_Collect_eq)
qed

lemma kf_norm_geq0[iff]:
  shows \<open>kf_norm \<EE> \<ge> 0\<close>
proof (cases \<open>Rep_kraus_family \<EE> \<noteq> {}\<close>)
  case True
  then obtain E where \<open>E \<in> Rep_kraus_family \<EE>\<close> by auto
  have \<open>0 \<le> (\<Squnion>F\<in>{F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E))\<close>
    apply (rule cSUP_upper2[where x=\<open>{E}\<close>])
    using True by (simp_all add: \<open>E \<in> Rep_kraus_family \<EE>\<close> kf_norm_sum_bdd)
  then show ?thesis
    by (simp add: kf_norm_def True)
next
  case False
  then show ?thesis
    by (auto simp: kf_norm_def)
qed

lemma kf_bound_has_sum:
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kf_bound \<EE>)\<close>
proof -
  obtain B where B: \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    using Rep_kraus_family[of \<EE>]
    by (auto simp: kraus_family_def case_prod_unfold bdd_above_def)
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    apply (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: kraus_family_def)
    using B by blast
  then show ?thesis
    by (auto intro!: has_sum_in_infsum_in simp: kf_bound_def)
qed

lemma kraus_family_iff_summable:
  \<open>kraus_family \<EE> \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
proof (rule iffI)
  assume \<open>kraus_family \<EE>\<close>
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (Abs_kraus_family \<EE>))\<close>
    using \<open>kraus_family \<EE>\<close> kf_bound_has_sum summable_on_in_def by blast
  with \<open>kraus_family \<EE>\<close> show \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
    by (simp add: Abs_kraus_family_inverse)
next
  assume \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
  then show \<open>kraus_family \<EE>\<close>
    by (auto intro!: summable_wot_bdd_above[where X=\<EE>] positive_cblinfun_squareI simp: kraus_family_def)
qed

lemma kraus_family_iff_summable':
  \<open>kraus_family \<EE> \<longleftrightarrow> (\<lambda>(E,x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on \<EE>\<close>
  apply (transfer' fixing: \<EE>)
  by (simp add: kraus_family_iff_summable)

lemma kf_bound_summable:
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
  using kf_bound_has_sum summable_on_in_def by blast

lemma kf_bound_has_sum':
  shows \<open>((\<lambda>(E,x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) has_sum Abs_cblinfun_wot (kf_bound \<EE>)) (Rep_kraus_family \<EE>)\<close>
  using kf_bound_has_sum[of \<EE>]
  apply transfer'
  by auto

lemma kf_bound_summable':
  \<open>((\<lambda>(E,x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on Rep_kraus_family \<EE>)\<close>
  using has_sum_imp_summable kf_bound_has_sum' by blast

lemma kf_bound_is_Sup:
  shows \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>}) (kf_bound \<EE>)\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  then have \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>})
     (infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>))\<close>
    apply (rule infsum_wot_is_Sup[OF summable_wot_boundedI[where B=B]])
    by (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: case_prod_beta)
  then show ?thesis
    by (auto intro!: simp: kf_bound_def)
qed

lemma kf_bound_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kf_bound \<EE> \<le> B\<close>
  using kf_bound_is_Sup[of \<EE>]
  by (simp add: assms is_Sup_def)

lemma kf_bound_pos[iff]: \<open>kf_bound \<EE> \<ge> 0\<close>
  using kf_bound_is_Sup[of \<EE>]
  by (metis (no_types, lifting) empty_subsetI finite.emptyI image_iff is_Sup_def mem_Collect_eq sum.empty)


lemma not_not_singleton_kf_norm_0: 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>kf_norm \<EE> = 0\<close>
  by (simp add: not_not_singleton_cblinfun_zero[OF assms] kf_norm_def)

lemma kf_norm_sum_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kf_norm \<EE> \<le> B\<close>
proof -
  have bpos: \<open>B \<ge> 0\<close>
    using assms[of \<open>{}\<close>] by auto
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close> keeping bpos
    using not_not_singleton_kf_norm_0[OF negation, of \<EE>]
    by (simp add: \<open>B \<ge> 0\<close>)
  have [simp]: \<open>norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a) = 1\<close>
    apply (rule norm_cblinfun_id[internalize_sort' 'a])
     apply (rule complex_normed_vector_axioms)
    by (rule not_singleton)
  have *: \<open>selfadjoint (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
    apply (auto intro!: pos_imp_selfadjoint sum_nonneg)
    using positive_cblinfun_squareI by blast
  from assms
  have \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
    apply (rule less_eq_scaled_id_norm)
    by (auto intro!: * )
  then have \<open>kf_bound \<EE> \<le> B *\<^sub>R id_cblinfun\<close>
    using kf_bound_leqI by blast
  then have \<open>norm (kf_bound \<EE>) \<le> norm (B *\<^sub>R (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a))\<close>
    apply (rule norm_cblinfun_mono[rotated])
    by simp
  then show ?thesis
    using bpos by (simp add: kf_norm_def)
qed

lemma kf_bound_geq_sum:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>(\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kf_bound \<EE>\<close>
proof (cases \<open>finite M\<close>)
  case True
  then show ?thesis
  using kf_bound_is_Sup[of \<EE>]
  apply (simp add: is_Sup_def case_prod_beta)
  using assms by blast
next
  case False
  then show ?thesis
    by simp
qed



lemma kf_norm_geq_norm_sum:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kf_norm \<EE>\<close>
  using kf_bound_geq_sum assms
  by (auto intro!: norm_cblinfun_mono sum_nonneg 
      intro: positive_cblinfun_squareI
      simp add: kf_norm_def case_prod_beta)

lemma kf_bound_finite: \<open>kf_bound \<EE> = (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close> if \<open>finite (Rep_kraus_family \<EE>)\<close>
  by (auto intro!: kraus_family_if_finite simp: kf_bound_def that infsum_in_finite)

lemma kf_norm_finite: \<open>kf_norm \<EE> = norm (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  if \<open>finite (Rep_kraus_family \<EE>)\<close>
  by (simp add: kf_norm_def kf_bound_finite that)

lemma kf_apply_bounded_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (kf_apply \<EE> \<rho>) \<le> kf_norm \<EE> * norm \<rho>\<close>
proof -
  have \<open>norm (kf_apply \<EE> \<rho>) = Re (trace_tc (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>))\<close>
    apply (subst Re_complex_of_real[symmetric])
    apply (subst norm_tc_pos)
    using \<open>\<rho> \<ge> 0\<close> apply (rule kf_apply_pos)
    by (simp add: kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. Re (trace_tc (sandwich_tc E \<rho>)))\<close>
    using kf_apply_summable[of _ \<EE>]
    by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: case_prod_unfold bounded_linear_compose[of Re trace_tc] bounded_linear_Re
        o_def bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>(E,_). Re (trace_tc (sandwich_tc E \<rho>))) summable_on (Rep_kraus_family \<EE>)\<close>
      unfolding case_prod_beta
      apply (rule summable_on_bounded_linear[unfolded o_def, where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
      using kf_apply_summable[of _ \<EE>]
      by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear 
        o_def trace_tc_scaleC assms kf_apply_def case_prod_unfold)
    fix M :: \<open>(('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'c) set\<close> assume \<open>finite M\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
    have \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>)))
        = (\<Sum>(E,_)\<in>M. Re (trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)))\<close>
      by (simp add: trace_tc.rep_eq from_trace_class_sandwich_tc sandwich_apply scaleC_trace_class.rep_eq trace_scaleC)
    also have \<open>\<dots> = (\<Sum>(E,_)\<in>M. Re (trace (E* o\<^sub>C\<^sub>L E o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close>
      apply (subst circularity_of_trace)
      by (auto intro!: trace_class_comp_right simp: cblinfun_compose_assoc)
    also have \<open>\<dots> = Re (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (simp only: trace_class_scaleC trace_class_comp_right trace_class_from_trace_class case_prod_unfold
          flip: Re_sum trace_scaleC trace_sum cblinfun.scaleC_left cblinfun_compose_scaleC_left cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> cmod (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (rule complex_Re_le_cmod)
    also have \<open>\<dots> \<le> norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) * trace_norm (from_trace_class \<rho>)\<close>
      apply (rule cmod_trace_times)
      by simp
    also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
      apply (simp add: flip: norm_trace_class.rep_eq)
      apply (rule mult_right_mono)
      apply (rule kf_norm_geq_norm_sum)
      using assms \<open>M \<subseteq> Rep_kraus_family \<EE>\<close> by auto
    finally show \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>))) \<le> kf_norm \<EE> * norm \<rho>\<close>
      by -
  qed
  finally show ?thesis 
    by -
qed

lemma kf_apply_bounded:
  \<comment> \<open>We suspect the factor 4 is not needed here but don't know how to prove that.\<close>
  \<open>norm (kf_apply \<EE> \<rho>) \<le> 4 * kf_norm \<EE> * norm \<rho>\<close>
proof -
  have aux: \<open>4 * x = x + x + x + x\<close> for x :: real
    by auto
  obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
    and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
    and norm: \<open>norm \<rho>1 \<le> norm \<rho>\<close> \<open>norm \<rho>2 \<le> norm \<rho>\<close> \<open>norm \<rho>3 \<le> norm \<rho>\<close> \<open>norm \<rho>4 \<le> norm \<rho>\<close>
    apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
  have \<open>norm (kf_apply \<EE> \<rho>) \<le>
          norm (kf_apply \<EE> \<rho>1) +
          norm (kf_apply \<EE> \<rho>2) +
          norm (kf_apply \<EE> \<rho>3) +
          norm (kf_apply \<EE> \<rho>4)\<close>
    by (auto intro!: norm_triangle_le norm_triangle_le_diff
        simp add: \<rho>_decomp kf_apply_plus_right kf_apply_minus_right
        kf_apply_scaleC)
  also have \<open>\<dots> \<le> 
        kf_norm \<EE> * norm \<rho>1
        + kf_norm \<EE> * norm \<rho>2
        + kf_norm \<EE> * norm \<rho>3
        + kf_norm \<EE> * norm \<rho>4\<close>
    by (auto intro!: add_mono simp add: pos kf_apply_bounded_pos)
  also have \<open>\<dots> = kf_norm \<EE> * (norm \<rho>1 + norm \<rho>2 + norm \<rho>3 + norm \<rho>4)\<close>
    by argo
  also have \<open>\<dots> \<le> kf_norm \<EE> * (norm \<rho> + norm \<rho> + norm \<rho> + norm \<rho>)\<close>
    by (auto intro!: mult_left_mono add_mono kf_norm_geq0 
        simp only: aux norm)
  also have \<open>\<dots> = 4 * kf_norm \<EE> * norm \<rho>\<close>
    by argo
  finally show ?thesis
    by -
qed

lemma kf_apply_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kf_apply \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>4 * kf_norm \<EE>\<close>])
    apply (auto intro!: kf_apply_plus_right kf_apply_scaleC mult.commute)[2]
  using kf_apply_bounded
  by (simp add: mult.commute)

lemma kf_bound_from_map:
  shows \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<phi> = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly \<phi> \<psi>)\<close>
proof -
  have \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kf_bound \<EE>)\<close>
    by (simp add: kf_bound_has_sum)
  then have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum \<psi> \<bullet>\<^sub>C kf_bound \<EE> \<phi>) (Rep_kraus_family \<EE>)\<close>
    by (auto intro!: simp: has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
  moreover have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum trace_tc (kf_apply \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
  proof -
    have *: \<open>trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>)) = \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (auto intro!: simp: trace_tc.rep_eq from_trace_class_sandwich_tc
          sandwich_apply tc_butterfly.rep_eq circularity_of_trace[symmetric, of _ E]
          trace_class_comp_left cblinfun_compose_assoc trace_butterfly_comp)
    from kf_apply_has_sum Rep_kraus_family[of \<EE>]
    have \<open>((\<lambda>(E,x). sandwich_tc E (tc_butterfly \<phi> \<psi>)) has_sum kf_apply \<EE> (tc_butterfly \<phi> \<psi>)) (Rep_kraus_family \<EE>)\<close>
      by blast
    then have \<open>((\<lambda>(E,x). trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>))) has_sum trace_tc (kf_apply \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
      unfolding case_prod_unfold
      apply (rule has_sum_bounded_linear[rotated, unfolded o_def])
      by (simp add: bounded_clinear.bounded_linear)
    then
    show ?thesis
      by (simp add: * )
  qed
  ultimately show ?thesis
    using has_sum_unique by blast
qed

lemma trace_from_kf_bound: \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc (compose_tcr (kf_bound \<EE>) \<rho>)\<close>
proof -
  have \<open>separating_set bounded_clinear (Collect rank1_tc)\<close>
    apply (rule separating_set_bounded_clinear_dense)
    by simp
  moreover have \<open>bounded_clinear (\<lambda>a. trace_tc (\<EE> *\<^sub>k\<^sub>r a))\<close>
    by (intro bounded_linear_intros)
  moreover have \<open>bounded_clinear (\<lambda>a. trace_tc (compose_tcr (kf_bound \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  moreover have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r t) = trace_tc (compose_tcr (kf_bound \<EE>) t)\<close> if \<open>t \<in> Collect rank1_tc\<close> for t
  proof -
    from that obtain x y where t: \<open>t = tc_butterfly x y\<close>
      apply (transfer' fixing: x y)
      by (auto simp: rank1_iff_butterfly)
    then have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r t) = y \<bullet>\<^sub>C kf_bound \<EE> x\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> = trace_tc (compose_tcr (kf_bound \<EE>) (tc_butterfly x y))\<close>
      apply (transfer' fixing: x y \<EE>)
      by (simp add: trace_butterfly_comp')
    also have \<open>\<dots> = trace_tc (compose_tcr (kf_bound \<EE>) t)\<close>
      by (simp add: t)
    finally show ?thesis
      by -
  qed
  ultimately show ?thesis
    by (rule eq_from_separatingI[where P=bounded_clinear and S=\<open>Collect rank1_tc\<close>, THEN fun_cong])
qed

lemma kf_bound_selfadjoint[iff]: \<open>selfadjoint (kf_bound \<EE>)\<close>
  by (simp add: positive_selfadjointI)

lemma kf_bound_leq_kf_norm_id:
  shows \<open>kf_bound \<EE> \<le> kf_norm \<EE> *\<^sub>R id_cblinfun\<close>
  by (auto intro!: less_eq_scaled_id_norm simp: kf_norm_def)

subsection \<open>Basic Kraus families\<close>

lemma kf_emptyset[iff]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def)


instantiation kraus_family :: (chilbert_space, chilbert_space, type) \<open>zero\<close> begin
lift_definition zero_kraus_family :: \<open>('a,'b,'x) kraus_family\<close> is \<open>{}\<close>
  by simp
instance..
end

lemma kf_apply_0[simp]: \<open>kf_apply 0 = 0\<close>
  by (auto simp: kf_apply_def zero_kraus_family.rep_eq)

lemma kf_bound_0[simp]: \<open>kf_bound 0 = 0\<close>
  by (metis (mono_tags, lifting) finite.intros(1) kf_bound.rep_eq kf_bound_finite sum_clauses(1) zero_kraus_family.rep_eq)

lemma kf_norm_0[simp]: \<open>kf_norm 0 = 0\<close>
  by (simp add: kf_norm_def zero_kraus_family.rep_eq)

lift_definition kf_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a, 'b, unit) kraus_family\<close> is
  \<open>\<lambda>E::'a\<Rightarrow>\<^sub>C\<^sub>L'b. {(E, ())}\<close>
  by (auto intro: kraus_family_if_finite)

lemma kf_of_op_norm[simp]: \<open>kf_norm (kf_of_op E) = (norm E)\<^sup>2\<close>
  by (simp add: kf_of_op.rep_eq kf_norm_finite)

definition \<open>kf_id = kf_of_op id_cblinfun\<close>

lemma kf_of_op_id[simp]: \<open>kf_of_op id_cblinfun = kf_id\<close>
  by (simp add: kf_id_def)

lemma kf_norm_id_leq1: \<open>kf_norm kf_id \<le> 1\<close>
  apply (simp add: kf_id_def del: kf_of_op_id)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kf_norm_id_eq1[simp]: \<open>kf_norm (kf_id :: ('a :: {chilbert_space, not_singleton},'a,unit) kraus_family) = 1\<close>
  by (auto intro!: antisym kf_norm_id_leq1 simp: kf_id_def simp del: kf_of_op_id)

instantiation kraus_family :: (chilbert_space, chilbert_space, type) scaleR begin
lift_definition scaleR_kraus_family :: \<open>real \<Rightarrow> ('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>\<lambda>r \<EE>. if r \<le> 0 then {} else (\<lambda>(E,x). (sqrt r *\<^sub>R E, x)) ` \<EE>\<close>
proof (rename_tac r \<EE>)
  fix r and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume asm: \<open>\<EE> \<in> Collect kraus_family\<close>
  define scaled where \<open>scaled = (\<lambda>(E, y). (sqrt r *\<^sub>R E, y)) ` \<EE>\<close>
  show \<open>(if r \<le> 0 then {} else scaled) \<in> Collect kraus_family\<close>
  proof (cases \<open>r > 0\<close>)
    case True
    obtain B where B: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
      using asm
      by (auto intro!: simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R B\<close> if Mr\<EE>: \<open>M \<subseteq> scaled\<close> and \<open>finite M\<close> for M
    proof -
      define M' where \<open>M' = (\<lambda>(E,x). (E /\<^sub>R sqrt r, x)) ` M\<close>
      then have \<open>finite M'\<close>
        using that(2) by blast
      moreover have \<open>M' \<subseteq> \<EE>\<close>
        using Mr\<EE> True by (auto intro!: simp: M'_def scaled_def)
      ultimately have 1: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
        using B by auto
      have 2: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) = r *\<^sub>R (\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E)\<close>
        apply (simp add: M'_def case_prod_unfold)
        apply (subst infsum_reindex)
        using True
        by (auto intro!: inj_onI simp: o_def infsum_scaleR_right
            simp flip: inverse_mult_distrib)

      show ?thesis
        using 1 2 True
        apply auto
        using True scaleR_le_cancel_left_pos by blast
    qed
    then show ?thesis
      by (auto intro!: simp: kraus_family_def bdd_above_def)
  next
    case False
    then show ?thesis
      by (simp add: scaled_def)
  qed
qed
instance..
end

lemma kf_scale_apply:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kf_apply (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kf_apply \<EE> \<rho>\<close>
proof (cases \<open>r > 0\<close>)
  case True
  then show ?thesis
    apply (simp add: scaleR_kraus_family.rep_eq kf_apply_def)
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI
        simp: kf_apply_def case_prod_unfold
        o_def sandwich_tc_scaleR_left cblinfun.scaleR_left infsum_scaleR_right)
next
  case False
  with assms show ?thesis
    by (simp add: kf_apply.rep_eq scaleR_kraus_family.rep_eq)
qed

lemma kf_bound_scale[simp]: \<open>kf_bound (c *\<^sub>R \<EE>) = c *\<^sub>R kf_bound \<EE>\<close> if \<open>c \<ge> 0\<close>
  apply (rule cblinfun_cinner_eqI)
  using that
  by (simp add: kf_bound_from_map cblinfun.scaleR_left kf_scale_apply scaleR_scaleC trace_tc_scaleC)

lemma kf_norm_scale[simp]: \<open>kf_norm (c *\<^sub>R \<EE>) = c * kf_norm \<EE>\<close> if \<open>c \<ge> 0\<close>
  by (simp add: kf_norm_def that)

lemma kf_of_op_apply: \<open>kf_apply (kf_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  by (simp add: kf_apply_def kf_of_op.rep_eq)

lemma kf_id_apply[simp]: \<open>kf_apply kf_id \<rho> = \<rho>\<close>
  by (simp add: kf_id_def kf_of_op_apply del: kf_of_op_id)

lemma kf_scale_apply_neg:
  assumes \<open>r \<le> 0\<close>
  shows \<open>kf_apply (r *\<^sub>R \<EE>) = 0\<close>
  apply (transfer fixing: r)
  using assms
  by (auto intro!: ext simp: scaleR_kraus_family.rep_eq kf_apply.rep_eq)

lemma kf_apply_0_left[iff]: \<open>kf_apply 0 \<rho> = 0\<close>
  apply (transfer' fixing: \<rho>)
  by simp

lemma kf_bound_of_op[simp]: \<open>kf_bound (kf_of_op A) = A* o\<^sub>C\<^sub>L A\<close>
  by (simp add: kf_bound_def kf_of_op.rep_eq infsum_in_finite)

lemma kf_bound_id[simp]: \<open>kf_bound kf_id = id_cblinfun\<close>
  by (simp add: kf_id_def del: kf_of_op_id)

subsection \<open>Filtering\<close>

lift_definition kf_filter :: \<open>('x \<Rightarrow> bool) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close> is
  \<open>\<lambda>(P::'x \<Rightarrow> bool) \<EE>. Set.filter (\<lambda>(E,x). P x) \<EE>\<close>
proof (rename_tac P \<EE>, rule CollectI)
  fix P \<EE>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close>
    by simp
  then show \<open>kraus_family (Set.filter P \<EE>)\<close>
    unfolding kraus_family_def
    apply (rule bdd_above_mono2)
    by auto
qed

lemma kf_filter_false[simp]: \<open>kf_filter (\<lambda>_. False) \<EE> = 0\<close>
  apply transfer by auto

lemma kf_filter_true[simp]: \<open>kf_filter (\<lambda>_. True) \<EE> = \<EE>\<close>
  apply transfer by auto

definition \<open>kf_apply_on \<EE> S = kf_apply (kf_filter (\<lambda>x. x \<in> S) \<EE>)\<close>
notation kf_apply_on ("_ *\<^sub>k\<^sub>r @_/ _" [71, 1000, 70] 70)

lemma kf_apply_on_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply_on \<EE> X \<rho> \<ge> 0\<close>
  by (simp add: kf_apply_on_def kf_apply_pos assms)

lemma kf_apply_on_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kf_apply_on \<EE> X)\<close>
  by (simp add: kf_apply_on_def kf_apply_bounded_clinear)

lemma kf_filter_twice:
  \<open>kf_filter P (kf_filter Q \<EE>) = kf_filter (\<lambda>x. P x \<and> Q x) \<EE>\<close>
  apply (transfer' fixing: P Q)
  by auto

lemma kf_apply_on_union_has_sum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) F\<close>
proof -
  define EE EEf where \<open>EE = Rep_kraus_family \<EE>\<close> and \<open>EEf X = Set.filter (\<lambda>(E,x). x\<in>X) EE\<close> for X
  have inj: \<open>inj_on snd (SIGMA X:F. EEf X)\<close>
    using assms by (force intro!: simp: inj_on_def disjnt_def EEf_def)
  have snd_Sigma: \<open>snd ` (SIGMA X:F. EEf X) = EEf (\<Union>F)\<close>
    apply (auto simp: EEf_def)
    by force
  have map'_infsum: \<open>kf_apply_on \<EE> X \<rho> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>)\<close> for X
    by (simp add: kf_apply_on_def kf_apply.rep_eq EEf_def kf_filter.rep_eq EE_def case_prod_unfold)
  have has_sum: \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> X \<rho>)) (EEf X)\<close> for X
    using kf_apply_has_sum[of \<rho> \<open>kf_filter (\<lambda>x. x \<in> X) \<EE>\<close>]
    by (simp add: kf_apply_on_def kf_filter.rep_eq EEf_def EE_def)
  then have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) (snd ` (SIGMA X:F. EEf X))\<close>
    by (simp add: snd_Sigma)
  then have \<open>((\<lambda>(X,(E,x)). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) (SIGMA X:F. EEf X)\<close>
    apply (subst (asm) has_sum_reindex)
     apply (rule inj)
    by (simp add: o_def case_prod_unfold)
  then have \<open>((\<lambda>X. \<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>) has_sum kf_apply_on \<EE> (\<Union>F) \<rho>) F\<close>
    by (rule has_sum_Sigma'_banach)
  then show \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> (\<Union>F) \<rho>) F\<close>
    by (auto intro: has_sum_cong[THEN iffD2, rotated] simp: map'_infsum)
qed

lemma kf_apply_on_empty[simp]: \<open>kf_apply_on E {} \<rho> = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_union_eqI:
  assumes \<open>\<And>X Y. (X,Y)\<in>F \<Longrightarrow> kf_apply_on \<EE> X \<rho> = kf_apply_on \<FF> Y \<rho>\<close>
  assumes \<open>\<And>X Y X' Y'. (X,Y)\<in>F \<Longrightarrow> (X',Y')\<in>F \<Longrightarrow> (X,Y)\<noteq>(X',Y') \<Longrightarrow> disjnt X X'\<close>
  assumes \<open>\<And>X Y X' Y'. (X,Y)\<in>F \<Longrightarrow> (X',Y')\<in>F \<Longrightarrow> (X,Y)\<noteq>(X',Y') \<Longrightarrow> disjnt Y Y'\<close>
  assumes XX: \<open>XX = \<Union>(fst ` F)\<close> and YY: \<open>YY = \<Union>(snd ` F)\<close>
  shows \<open>kf_apply_on \<EE> XX \<rho> = kf_apply_on \<FF> YY \<rho>\<close>
proof -
  define F' where \<open>F' = Set.filter (\<lambda>(X,Y). X\<noteq>{} \<and> Y\<noteq>{}) F\<close>
  have inj1: \<open>inj_on fst F'\<close>
    apply (rule inj_onI)
    using assms(2)
    unfolding F'_def
    by fastforce
  have inj2: \<open>inj_on snd F'\<close>
    apply (rule inj_onI)
    using assms(3)
    unfolding F'_def
    by fastforce
  have \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) (fst ` F)\<close>
    unfolding XX
    apply (rule kf_apply_on_union_has_sum)
    using assms(2) by force
  then have \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) (fst ` F')\<close>
  proof (rule has_sum_cong_neutral[OF _ _ refl, THEN iffD2, rotated -1])
    show \<open>kf_apply_on \<EE> X \<rho> = 0\<close> if \<open>X \<in> fst ` F' - fst ` F\<close> for X
      using that by (auto simp: F'_def)
    show \<open>kf_apply_on \<EE> X \<rho> = 0\<close> if \<open>X \<in> fst ` F - fst ` F'\<close> for X
    proof -
      from that obtain Y where \<open>(X,Y) \<in> F\<close> and \<open>X = {} \<or> Y = {}\<close>
        apply atomize_elim
        by (auto intro!: simp: F'_def)
      then consider (X) \<open>X = {}\<close> | (Y) \<open>Y = {}\<close>
        by auto
      then show ?thesis
      proof cases
        case X
        then show ?thesis
          by simp
      next
        case Y
        then have \<open>kf_apply_on \<FF> Y \<rho> = 0\<close>
          by simp
        then show ?thesis
          using \<open>(X, Y) \<in> F\<close> assms(1) by presburger
      qed
    qed
  qed
  then have sum1: \<open>((\<lambda>(X,Y). kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) F'\<close>
    apply (subst (asm) has_sum_reindex)
    using inj1 by (auto intro!: simp: o_def case_prod_unfold)
  have \<open>((\<lambda>Y. kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) (snd ` F)\<close>
    unfolding YY
    apply (rule kf_apply_on_union_has_sum)
    using assms(3) by force
  then have \<open>((\<lambda>Y. kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) (snd ` F')\<close>
  proof (rule has_sum_cong_neutral[OF _ _ refl, THEN iffD2, rotated -1])
    show \<open>kf_apply_on \<FF> Y \<rho> = 0\<close> if \<open>Y \<in> snd ` F' - snd ` F\<close> for Y
      using that by (auto simp: F'_def)
    show \<open>kf_apply_on \<FF> Y \<rho> = 0\<close> if \<open>Y \<in> snd ` F - snd ` F'\<close> for Y
    proof -
      from that obtain X where \<open>(X,Y) \<in> F\<close> and \<open>X = {} \<or> Y = {}\<close>
        apply atomize_elim
        by (auto intro!: simp: F'_def)
      then consider (X) \<open>X = {}\<close> | (Y) \<open>Y = {}\<close>
        by auto
      then show ?thesis
      proof cases
        case Y
        then show ?thesis
          by simp
      next
        case X
        then have \<open>kf_apply_on \<EE> X \<rho> = 0\<close>
          by simp
        then show ?thesis
          using \<open>(X, Y) \<in> F\<close> assms(1) by simp
      qed
    qed
  qed
  then have \<open>((\<lambda>(X,Y). kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) F'\<close>
    apply (subst (asm) has_sum_reindex)
    using inj2 by (auto intro!: simp: o_def case_prod_unfold)
  then have sum2: \<open>((\<lambda>(X,Y). kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) F'\<close>
    apply (rule has_sum_cong[THEN iffD1, rotated -1])
    using assms(1) by (auto simp: F'_def)
  from sum1 sum2 show ?thesis
    using has_sum_unique by blast
qed

lemma kf_apply_on_UNIV[simp]: \<open>kf_apply_on \<EE> UNIV = kf_apply \<EE>\<close>
  by (auto simp: kf_apply_on_def)

lemma kf_apply_on_CARD_1[simp]: \<open>(\<lambda>\<EE>. kf_apply_on \<EE> {x::_::CARD_1}) = kf_apply\<close>
  apply (subst asm_rl[of \<open>{x} = UNIV\<close>])
  by auto

(* lemma kf_apply_eqI_from_map':
  assumes \<open>\<And>x. kf_apply_on \<EE> {x} = kf_apply_on \<FF> {x}\<close>
  shows \<open>kf_apply \<EE> = kf_apply \<FF>\<close>
  apply (subst kf_apply_on_UNIV[symmetric])+
  apply (rule ext)
  apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>x. ({x},{x}))\<close> and \<EE>=\<EE> and \<FF>=\<FF>])
  using assms by auto *)

lemma kf_apply_on_union_summable_on:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<lambda>X. kf_apply_on \<EE> X \<rho>) summable_on F\<close>
  using assms by (auto intro!: has_sum_imp_summable kf_apply_on_union_has_sum)

lemma kf_apply_on_union_infsum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>X\<in>F. kf_apply_on \<EE> X \<rho>) = kf_apply_on \<EE> (\<Union>F) \<rho>\<close>
  by (metis assms infsumI kf_apply_on_union_has_sum)


lemma kf_bound_filter:
  \<open>kf_bound (kf_filter P \<EE>) \<le> kf_bound \<EE>\<close>
proof (unfold kf_bound.rep_eq, rule infsum_mono_neutral_wot)
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_filter P \<EE>))\<close>
    using Rep_kraus_family kraus_family_iff_summable by blast
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using Rep_kraus_family kraus_family_iff_summable by blast
  fix Ex :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c\<close>
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by simp
  show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
    if \<open>Ex \<in> Rep_kraus_family (kf_filter P \<EE>) - Rep_kraus_family \<EE>\<close>
    using that
    by (auto simp: kf_filter.rep_eq)
qed

lemma kf_norm_filter:
  \<open>kf_norm (kf_filter P \<EE>) \<le> kf_norm \<EE>\<close>
  unfolding kf_norm_def
  apply (rule norm_cblinfun_mono)
  by (simp_all add: kf_bound_filter)

lemma kf_domain_filter[simp]:
  \<open>kf_domain (kf_filter P E) = Set.filter P (kf_domain E)\<close>
  apply (transfer' fixing: P)
  by force

lemma kf_filter_remove0:
  \<open>kf_filter f (kf_remove_0 \<EE>) = kf_remove_0 (kf_filter f \<EE>)\<close>
  apply (transfer' fixing: f)
  by auto

lemma kf_filter_0_right[simp]: \<open>kf_filter P 0 = 0\<close>
  apply (transfer' fixing: P)
  by auto

lemma kf_apply_on_0_right[simp]: \<open>kf_apply_on \<EE> X 0 = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_0_left[simp]: \<open>kf_apply_on 0 X \<rho> = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_mono3:
  assumes \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @X \<sigma>\<close>
  by (simp add: assms kf_apply_mono_right kf_apply_on_def)

lemma kf_apply_on_mono2:
  assumes \<open>X \<subseteq> Y\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
proof -
  wlog \<open>Y \<noteq> {}\<close>
    using assms(1) negation by auto
  have [simp]: \<open>X \<union> Y = Y\<close>
    using assms(1) by blast
  from kf_apply_on_union_infsum[where F=\<open>{X, Y-X}\<close> and \<EE>=\<EE> and \<rho>=\<rho>]
  have \<open>(\<Sum>X\<in>{X, Y - X}. \<EE> *\<^sub>k\<^sub>r @X \<rho>) = \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
    by (auto simp: disjnt_iff sum.insert)
  then have \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> + \<EE> *\<^sub>k\<^sub>r @(Y-X) \<rho> = \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close> 
    apply (subst (asm) sum.insert)
    using \<open>Y \<noteq> {}\<close>     
    by auto
  moreover have \<open>\<EE> *\<^sub>k\<^sub>r @(Y-X) \<rho> \<ge> 0\<close>
    by (simp add: assms(2) kf_apply_on_pos)
  ultimately show \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
    by (metis le_add_same_cancel1)
qed


subsection \<open>Equivalence\<close>

definition \<open>kf_eq_weak \<EE> \<FF> \<longleftrightarrow> kf_apply \<EE> = kf_apply \<FF>\<close>
definition \<open>kf_eq \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kf_apply_on \<EE> {x} = kf_apply_on \<FF> {x})\<close>

open_bundle kraus_map_syntax begin
notation kf_eq_weak (infix "=\<^sub>k\<^sub>r" 50)
notation kf_eq (infix "\<equiv>\<^sub>k\<^sub>r" 50)
notation kf_apply (infixr \<open>*\<^sub>k\<^sub>r\<close> 70)
notation kf_apply_on ("_ *\<^sub>k\<^sub>r @_/ _" [71, 1000, 70] 70)
end

lemma kf_eq_weak_reflI[iff]: \<open>x =\<^sub>k\<^sub>r x\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_bound_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_bound \<EE> = kf_bound \<FF>\<close>
  using assms by (auto intro!: cblinfun_cinner_eqI simp: kf_eq_weak_def kf_bound_from_map)

lemma kf_norm_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_norm \<EE> = kf_norm \<FF>\<close>
  using assms
  by (simp add: kf_norm_def kf_bound_cong)


lemma kf_eq_weakI:
  assumes \<open>\<And>\<rho>. \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r \<rho> = \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  shows \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  unfolding kf_eq_weak_def
  apply (rule eq_from_separatingI)
     apply (rule separating_density_ops[where B=1])
  using assms by auto

lemma kf_eqI: 
  assumes \<open>\<And>x \<rho>. \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  using kf_eq_weakI
  using assms
  by (auto simp: kf_eq_weak_def kf_eq_def kf_apply_on_def)

lemma kf_norm_remove_0[simp]:
  \<comment> \<open>Logically belongs in a different section but uses lemmas from this section.\<close>
  \<open>kf_norm (kf_remove_0 \<EE>) = kf_norm \<EE>\<close>
  by (auto intro!: kf_eq_weakI kf_norm_cong)

lemma kf_eq_weak_trans[trans]:
  \<open>F =\<^sub>k\<^sub>r G \<Longrightarrow> G =\<^sub>k\<^sub>r H \<Longrightarrow> F =\<^sub>k\<^sub>r H\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_apply_eqI:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> = \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  using assms by (simp add: kf_eq_weak_def)

lemma kf_eq_imp_eq_weak:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  unfolding kf_eq_weak_def 
  apply (subst kf_apply_on_UNIV[symmetric])+
  apply (rule ext)
  apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>x. ({x},{x}))\<close> and \<EE>=\<EE> and \<FF>=\<FF>])
  using assms by (auto simp: kf_eq_def)

lemma kf_filter_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = Q x\<close>
  shows \<open>kf_filter P \<EE> \<equiv>\<^sub>k\<^sub>r kf_filter Q \<FF>\<close>
proof -
  have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> P xa) \<EE>)
      = kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<EE>)\<close> for x
  proof (cases \<open>x \<in> kf_domain \<EE>\<close>)
    case True
    with assms have \<open>P x = Q x\<close>
      by blast
    then have \<open>(\<lambda>xa. xa = x \<and> P xa) = (\<lambda>xa. xa = x \<and> Q xa)\<close>
      by auto
    then show ?thesis
      by simp
  next
    case False
    have *: \<open>(\<Sum>\<^sub>\<infinity>E\<in>Set.filter (\<lambda>(E, xa). xa = x \<and> P xa) \<EE>. sandwich_tc (fst E) \<rho>) = 0\<close>
      if \<open>x \<notin> snd ` Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE>\<close> for \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close> and \<rho> P
      apply (rule infsum_0)
      using that
      by force
    have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> P xa) \<EE>) = 0\<close> for P
      using False
      apply (transfer' fixing: x P)
      using *
      by (auto intro!: ext)
    then show ?thesis
      by simp
  qed
  also have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<EE>)
           = kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<FF>)\<close> for x
  proof (cases \<open>Q x\<close>)
    case True
    then have \<open>(z = x \<and> Q z) \<longleftrightarrow> (z = x)\<close> for z
      by auto
    with assms show ?thesis
      by (simp add: kf_eq_def kf_apply_on_def)
  next
    case False
    then have [simp]: \<open>(z = x \<and> Q z) \<longleftrightarrow> False\<close> for z
      by auto
    show ?thesis
      by (simp add: kf_eq_def kf_apply_on_def)
  qed
  finally show ?thesis
    by (simp add: kf_eq_def kf_apply_on_def kf_filter_twice)
qed


lemma kf_filter_cong_weak:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = Q x\<close>
  shows \<open>kf_filter P \<EE> =\<^sub>k\<^sub>r kf_filter Q \<FF>\<close>
  by (simp add: assms kf_eq_imp_eq_weak kf_filter_cong)

lemma kf_eq_refl[iff]: \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  using kf_eq_def by blast

lemma kf_eq_trans[trans]:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<GG>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<GG>\<close>
  by (metis assms(1) assms(2) kf_eq_def)

lemma kf_eq_sym[sym]:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (metis assms kf_eq_def)

lemma kf_eq_weak_imp_eq_CARD_1:
  fixes \<EE> \<FF> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x::CARD_1) kraus_family\<close>
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  by (metis CARD_1_UNIV assms kf_eqI kf_eq_weak_def kf_apply_on_UNIV)

lemma kf_apply_on_eqI_filter:
  assumes \<open>kf_filter (\<lambda>x. x \<in> X) \<EE> \<equiv>\<^sub>k\<^sub>r kf_filter (\<lambda>x. x \<in> X) \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
proof (rule kf_apply_on_union_eqI[where F=\<open>(\<lambda>x.({x},{x})) ` X\<close>])
  show \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow>
       (A', B') \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow> (A, B) \<noteq> (A', B') \<Longrightarrow> disjnt A A'\<close>
    for A B A' B'
    by force
  show \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow>
       (A', B') \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow> (A, B) \<noteq> (A', B') \<Longrightarrow> disjnt B B'\<close>
    for A B A' B'
    by force
  show \<open>X = \<Union> (fst ` (\<lambda>x. ({x}, {x})) ` X)\<close>
    by simp
  show \<open>X = \<Union> (snd ` (\<lambda>x. ({x}, {x})) ` X)\<close>
    by simp
  show \<open>\<EE> *\<^sub>k\<^sub>r @A \<rho> = \<FF> *\<^sub>k\<^sub>r @B \<rho>\<close> if \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X\<close> for A B
  proof -
    from that obtain x where \<open>x \<in> X\<close> and A: \<open>A = {x}\<close> and B: \<open>B = {x}\<close>
      by blast
    from \<open>x \<in> X\<close> have *: \<open>(\<lambda>x'. x = x' \<and> x' \<in> X) = (\<lambda>x'. x' = x)\<close>
      by blast
    from assms have \<open>kf_filter ((=)x) (kf_filter (\<lambda>x. x \<in> X) \<EE>) =\<^sub>k\<^sub>r kf_filter ((=)x) (kf_filter (\<lambda>x. x \<in> X) \<FF>)\<close>
      by (simp add: kf_filter_cong_weak)
    then have \<open>kf_filter (\<lambda>x'. x'=x) \<EE> =\<^sub>k\<^sub>r kf_filter (\<lambda>x'. x'=x) \<FF>\<close>
      by (simp add: kf_filter_twice * )
    then have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> = \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
      by (simp add: kf_apply_on_def kf_eq_weak_def)
    then show ?thesis
      by (simp add: A B)
  qed
qed

lemma kf_apply_on_eqI:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
  apply (rule kf_apply_on_union_eqI[where F=\<open>(\<lambda>x.({x},{x})) ` X\<close>])
  using assms by (auto simp: kf_eq_def)

lemma kf_apply_eq0I:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> = 0\<close>
  using assms kf_eq_weak_def by force

lemma kf_eq_weak0_imp_kf_eq0:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r 0\<close>
proof -
  have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> = 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho> x
  proof -
    from assms have \<open>\<EE> *\<^sub>k\<^sub>r @UNIV \<rho> = 0\<close>
      by (simp add: kf_eq_weak_def)
    moreover have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @UNIV \<rho>\<close>
      apply (rule kf_apply_on_mono2)
      using that by auto
    moreover have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<ge> 0\<close>
      using that
      by (simp add: kf_apply_on_pos)
    ultimately show ?thesis
      by (simp add: basic_trans_rules(24))
  qed
  then show ?thesis
    by (simp add: kf_eqI)
qed

lemma kf_apply_on_eq0I:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = 0\<close>
proof -
  from assms
  have \<open>\<EE> \<equiv>\<^sub>k\<^sub>r 0\<close>
    by (rule kf_eq_weak0_imp_kf_eq0)
  then have \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = 0 *\<^sub>k\<^sub>r @X \<rho>\<close>
    by (intro kf_apply_on_eqI_filter kf_filter_cong refl)
  then show ?thesis
    by simp
qed

lemma kf_remove_0_eq_weak[iff]: \<open>kf_remove_0 \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_remove_0_eq[iff]: \<open>kf_remove_0 \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: kf_eq_def kf_apply_on_def kf_filter_remove0)

lemma kf_filter_to_domain[simp]:
  \<open>kf_filter (\<lambda>x. x \<in> kf_domain \<EE>) \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
proof -
  have \<open>kf_filter (\<lambda>x. x \<in> kf_domain \<EE>) \<EE> \<equiv>\<^sub>k\<^sub>r
            kf_remove_0 (kf_filter (\<lambda>x. x \<in> kf_domain \<EE>) \<EE>)\<close>
    using kf_eq_sym kf_remove_0_eq by blast
  also have \<open>\<dots> = kf_filter (\<lambda>x. x \<in> kf_domain \<EE>) (kf_remove_0 \<EE>)\<close>
    by (simp add: kf_filter_remove0)
  also have \<open>\<dots> = kf_remove_0 \<EE>\<close>
    apply transfer'
    by (auto simp: image_iff Bex_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
    by (simp add: kf_remove_0_eq)
  finally show ?thesis
    by simp
qed

lemma kf_eq_0_iff_kf_remove_0_is_0: \<open>E =\<^sub>k\<^sub>r 0 \<longleftrightarrow> kf_remove_0 E = 0\<close>
proof (rule iffI)
  assume asm: \<open>E =\<^sub>k\<^sub>r 0\<close>
  show \<open>kf_remove_0 E = 0\<close>
  proof (insert asm, unfold kf_eq_weak_def, transfer, rename_tac \<EE>)
    fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
    assume \<open>\<EE> \<in> Collect kraus_family\<close>
    then have \<open>kraus_family \<EE>\<close>
      by simp
    have summable1: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on \<EE>\<close> for \<rho>
      apply (rule abs_summable_summable)
      using kf_apply_abs_summable[OF \<open>kraus_family \<EE>\<close>]
      by (simp add: case_prod_unfold)
    then have summable2: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on \<EE>-{E}\<close> for E \<rho>
      apply (rule summable_on_subset_banach)
      by simp
    assume \<open>(\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>{}. sandwich_tc (fst E) \<rho>)\<close>
    then have sum0: \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = 0\<close> for \<rho>
      apply simp by meson
    have sand_E\<rho>_0:  \<open>sandwich_tc (fst E) \<rho> = 0\<close> if \<open>E \<in> \<EE>\<close> and \<open>\<rho> \<ge> 0\<close> for E \<rho>
    proof (rule ccontr)
      assume E\<rho>_neq0: \<open>sandwich_tc (fst E) \<rho> \<noteq> 0\<close>
      have E\<rho>_geq0: \<open>sandwich_tc (fst E) \<rho> \<ge> 0\<close>
        by (simp add: \<open>0 \<le> \<rho>\<close> sandwich_tc_pos)
      have E\<rho>_ge0: \<open>sandwich_tc (fst E) \<rho> > 0\<close>
        using E\<rho>_neq0 E\<rho>_geq0 by order
      have \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>-{E}. sandwich_tc (fst E) \<rho>) + sandwich_tc (fst E) \<rho>\<close>
        apply (subst asm_rl[of \<open>\<EE> = insert E (\<EE>-{E})\<close>])
        using that apply blast
        apply (subst infsum_insert)
        by (auto intro!: summable2)
      also have \<open>\<dots> \<ge> 0 + sandwich_tc (fst E) \<rho>\<close> (is \<open>_ \<ge> \<dots>\<close>)
        by (simp add: \<open>0 \<le> \<rho>\<close> infsum_nonneg_traceclass sandwich_tc_pos)
      also have \<open>\<dots> > 0\<close> (is \<open>_ > \<dots>\<close>)
        using E\<rho>_ge0
        by simp
      ultimately have \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) > 0\<close>
        by simp
      then show False
        using sum0 by simp
    qed
    then have \<open>fst E = 0\<close> if \<open>E \<in> \<EE>\<close> for E
      apply (rule sandwich_tc_eq0_D[where B=1])
      using that by auto
    then show \<open>Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE> = {}\<close>
      by auto
  qed
next
  assume \<open>kf_remove_0 E = 0\<close>
  then show \<open>E =\<^sub>k\<^sub>r 0\<close>
    by (metis kf_eq_weak_def kf_apply_0 kf_apply_remove_0)
qed

lemma in_kf_domain_iff_apply_nonzero:
  \<open>x \<in> kf_domain \<EE> \<longleftrightarrow> kf_apply_on \<EE> {x} \<noteq> 0\<close>
proof -
  define \<EE>' where \<open>\<EE>' = Rep_kraus_family \<EE>\<close>
  have \<open>x \<notin> kf_domain \<EE> \<longleftrightarrow> (\<forall>(E,x')\<in>Rep_kraus_family \<EE>. x'=x \<longrightarrow> E=0)\<close>
    by (force simp: kf_domain.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>(E,x')\<in>Rep_kraus_family (kf_filter (\<lambda>y. y=x) \<EE>). E=0)\<close>
    by (auto simp: kf_filter.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> Rep_kraus_family (kf_remove_0 (kf_filter (\<lambda>y. y=x) \<EE>)) = {}\<close>
    by (auto simp: kf_remove_0.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> kf_remove_0 (kf_filter (\<lambda>y. y=x) \<EE>) = 0\<close>
    using Rep_kraus_family_inject zero_kraus_family.rep_eq by auto
  also have \<open>\<dots> \<longleftrightarrow> kf_apply (kf_filter (\<lambda>y. y=x) \<EE>) = 0\<close>
    apply (subst kf_eq_0_iff_kf_remove_0_is_0[symmetric])
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> \<longleftrightarrow> kf_apply_on \<EE> {x} = 0\<close>
    by (simp add: kf_apply_on_def)
  finally show ?thesis
    by auto
qed


lemma kf_domain_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_domain \<EE> = kf_domain \<FF>\<close>
  apply (rule Set.set_eqI)
  using assms
  by (simp add: kf_eq_def in_kf_domain_iff_apply_nonzero)

lemma kf_eq_weak_sym:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<FF> =\<^sub>k\<^sub>r \<EE>\<close>
  by (metis assms kf_eq_weak_def)

lemma kf_eqI_from_filter_eq_weak:
  assumes \<open>\<And>x. kf_filter ((=) x) E =\<^sub>k\<^sub>r kf_filter ((=) x) F\<close>
  shows \<open>E \<equiv>\<^sub>k\<^sub>r F\<close>
  using assms by (simp add: kf_eq_weak_def kf_eq_def kf_apply_on_def flip_eq_const)

lemma kf_eq_weak_from_separatingI:
  fixes E F :: \<open>('q::chilbert_space,'r::chilbert_space,'x) kraus_family\<close>
  assumes \<open>separating_set (bounded_clinear :: (('q,'q) trace_class \<Rightarrow> ('r,'r) trace_class) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>\<rho>. \<rho> \<in> S \<Longrightarrow> E *\<^sub>k\<^sub>r \<rho> = F *\<^sub>k\<^sub>r \<rho>\<close>
  shows \<open>E =\<^sub>k\<^sub>r F\<close>
proof -
  have \<open>kf_apply E = kf_apply F\<close>
    by (metis assms(1) assms(2) kf_apply_bounded_clinear separating_set_def)
  then show ?thesis
    by (simp add: kf_eq_weakI)
qed

lemma kf_eq_weak_eq_trans[trans]: \<open>a =\<^sub>k\<^sub>r b \<Longrightarrow> b \<equiv>\<^sub>k\<^sub>r c \<Longrightarrow> a =\<^sub>k\<^sub>r c\<close>
  by (metis kf_eq_imp_eq_weak kf_eq_weak_def)

lemma kf_eq_eq_weak_trans[trans]: \<open>a \<equiv>\<^sub>k\<^sub>r b \<Longrightarrow> b =\<^sub>k\<^sub>r c \<Longrightarrow> a =\<^sub>k\<^sub>r c\<close>
  by (metis kf_eq_imp_eq_weak kf_eq_weak_def)

instantiation kraus_family :: (chilbert_space,chilbert_space,type) preorder begin
definition less_eq_kraus_family where \<open>\<EE> \<le> \<FF> \<longleftrightarrow> (\<forall>x. \<forall>\<rho>\<ge>0. kf_apply_on \<EE> {x} \<rho> \<le> kf_apply_on \<FF> {x} \<rho>)\<close>
definition less_kraus_family where \<open>\<EE> < \<FF> \<longleftrightarrow> \<EE> \<le> \<FF> \<and> \<not> \<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
lemma kf_antisym: \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF> \<longleftrightarrow> \<EE> \<le> \<FF> \<and> \<FF> \<le> \<EE>\<close>
  for \<EE> \<FF> :: \<open>('a, 'b, 'c) kraus_family\<close>
  by (smt (verit, ccfv_SIG) kf_apply_on_eqI kf_eqI less_eq_kraus_family_def order.refl
      order_antisym_conv)
instance
proof (intro_classes)
  fix \<EE> \<FF> \<GG> :: \<open>('a, 'b, 'c) kraus_family\<close>
  show \<open>(\<EE> < \<FF>) = (\<EE> \<le> \<FF> \<and> \<not> \<FF> \<le> \<EE>)\<close>
    using kf_antisym less_kraus_family_def by auto
  show \<open>\<EE> \<le> \<EE>\<close>
    using less_eq_kraus_family_def by auto
  show \<open>\<EE> \<le> \<FF> \<Longrightarrow> \<FF> \<le> \<GG> \<Longrightarrow> \<EE> \<le> \<GG>\<close>
    by (meson basic_trans_rules(23) less_eq_kraus_family_def)
qed
end

lemma kf_apply_on_mono1: 
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>\<rho> \<ge> 0\<close> 
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
proof -
  have [simp]: \<open>\<Union>((\<lambda>x. {x}) ` X) = X\<close> for X :: \<open>'c set\<close>
    by auto
  have \<open>((\<lambda>X. \<EE> *\<^sub>k\<^sub>r @X \<rho>) has_sum \<EE> *\<^sub>k\<^sub>r @(\<Union>((\<lambda>x. {x}) ` X)) \<rho>) ((\<lambda>x. {x}) ` X)\<close>
    for \<EE> :: \<open>('a, 'b, 'c) kraus_family\<close> and X
    apply (rule kf_apply_on_union_has_sum)
    by auto
  then have sum: \<open>((\<lambda>X. \<EE> *\<^sub>k\<^sub>r @X \<rho>) has_sum \<EE> *\<^sub>k\<^sub>r @X \<rho>) ((\<lambda>x. {x}) ` X)\<close>
    for \<EE> :: \<open>('a, 'b, 'c) kraus_family\<close> and X
    by simp
  from assms
  have leq: \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close> for x
    by (simp add: less_eq_kraus_family_def)
  show ?thesis
    using sum sum apply (rule has_sum_mono_traceclass)
    using leq by fast
qed

lemma kf_apply_mono_left: \<open>\<EE> \<le> \<FF> \<Longrightarrow> \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r \<rho> \<le> \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  by (metis kf_apply_on_UNIV kf_apply_on_mono1)

lemma kf_apply_mono:
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> \<le> \<FF> *\<^sub>k\<^sub>r \<sigma>\<close>
  by (meson assms(1,2,3) basic_trans_rules(23) kf_apply_mono_left kf_apply_mono_right)

lemma kf_apply_on_mono:
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>X \<subseteq> Y\<close> and \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @Y \<sigma>\<close>
  apply (rule order.trans)
  using assms(2,1) apply (rule kf_apply_on_mono1)
  apply (rule order.trans)
  using assms(3,1) apply (rule kf_apply_on_mono2)
  using assms(4) by (rule kf_apply_on_mono3)

subsection \<open>Mapping and flattening\<close>

definition kf_similar_elements :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close> where
  \<comment> \<open>All elements of the Kraus family that are equal up to rescaling (and belong to the same output)\<close>
  \<open>kf_similar_elements \<EE> E = {(F,x) \<in> Rep_kraus_family \<EE>. (\<exists>r>0. E = r *\<^sub>R F)}\<close>

definition kf_element_weight where
  \<comment> \<open>The total weight (norm of the square) of all similar elements\<close>
  \<open>kf_element_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F,_)\<in>kf_similar_elements \<EE> E. norm (F* o\<^sub>C\<^sub>L F))\<close>

lemma kf_element_weight_geq0[simp]: \<open>kf_element_weight \<EE> E \<ge> 0\<close>
  by (auto intro!: infsum_nonneg simp: kf_element_weight_def)

lemma kf_similar_elements_abs_summable:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on (kf_similar_elements \<EE> E)\<close>
proof (cases \<open>E = 0\<close>)
  case True
  show ?thesis
    apply (rule summable_on_cong[where g=\<open>\<lambda>_. 0\<close>, THEN iffD2])
    by (auto simp: kf_similar_elements_def True)
next
  case False
  then obtain \<psi> where E\<psi>: \<open>E \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  define \<phi> where \<open>\<phi> = ((norm E)\<^sup>2 / (\<psi> \<bullet>\<^sub>C (E* *\<^sub>V E *\<^sub>V \<psi>))) *\<^sub>C \<psi>\<close>
  have normFF: \<open>norm (fst Fx* o\<^sub>C\<^sub>L fst Fx) = \<psi> \<bullet>\<^sub>C (fst Fx* *\<^sub>V fst Fx *\<^sub>V \<phi>)\<close>
    if \<open>Fx \<in> kf_similar_elements \<EE> E\<close> for Fx
  proof -
    define F where \<open>F = fst Fx\<close>
    from that obtain r where FE: \<open>F = r *\<^sub>R E\<close>
      apply atomize_elim
      apply (auto intro!: simp: kf_similar_elements_def F_def)
      by (metis Extra_Ordered_Fields.sign_simps(5) rel_simps(70) right_inverse scaleR_one)
    show \<open>norm (F* o\<^sub>C\<^sub>L F) = \<psi> \<bullet>\<^sub>C (F* *\<^sub>V F *\<^sub>V \<phi>)\<close>
      by (simp add: False \<phi>_def FE cblinfun.scaleR_left cblinfun.scaleR_right
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_adj_right E\<psi>)
  qed

  have \<psi>\<phi>_mono: \<open>mono (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
  proof (rule monoI)
    fix A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    assume \<open>A \<le> B\<close>
    then have \<open>B - A \<ge> 0\<close>
      by auto
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<psi>) \<ge> 0\<close>
      by (simp add: cinner_pos_if_pos)
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<phi>) \<ge> 0\<close>
      by (auto intro!: mult_nonneg_nonneg
          simp: \<phi>_def cblinfun.scaleC_right divide_inverse cinner_adj_right power2_eq_square)
    then show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<phi>)\<close>
      by (simp add: cblinfun.diff_left cinner_diff_right)
  qed

  have \<psi>\<phi>_linear: \<open>clinear (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
    by (auto intro!: clinearI simp: cblinfun.add_left cinner_add_right)

  from Rep_kraus_family[of \<EE>]
  have \<open>bdd_above ((\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. finite M \<and> M \<subseteq> Rep_kraus_family \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ _ order.refl])
    by (auto simp: kf_similar_elements_def)
  then have \<open>bdd_above ((\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>)) ` (\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (rule bdd_above_image_mono[OF \<psi>\<phi>_mono])
  then have \<open>bdd_above ((\<lambda>M. \<psi> \<bullet>\<^sub>C ((\<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (simp add: image_image)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. \<psi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    unfolding case_prod_beta
    by (subst complex_vector.linear_sum[OF \<psi>\<phi>_linear, symmetric])
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. complex_of_real (norm (F* o\<^sub>C\<^sub>L F))) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ subset_refl])
    unfolding case_prod_unfold
    apply (subst sum.cong[OF refl normFF])
    by auto
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. norm (F* o\<^sub>C\<^sub>L F)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (auto simp add: bdd_above_def case_prod_unfold less_eq_complex_def)
  then have \<open>(\<lambda>(F,_). norm (F* o\<^sub>C\<^sub>L F)) summable_on (kf_similar_elements \<EE> E)\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    by auto
  then show \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on kf_similar_elements \<EE> E\<close>
    by (simp add: case_prod_unfold)
qed

lemma kf_element_weight_neq0: \<open>kf_element_weight \<EE> E \<noteq> 0\<close> 
  if \<open>(E,x) \<in> Rep_kraus_family \<EE>\<close> and \<open>E \<noteq> 0\<close>
proof -
  have 1: \<open>(E, x) \<in> kf_similar_elements \<EE> E\<close>
    by (auto intro!: exI[where x=1] simp: kf_similar_elements_def that)

  have \<open>kf_element_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements \<EE> E. (norm F)\<^sup>2)\<close>
    by (simp add: kf_element_weight_def)
  moreover have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>(F, x)\<in>{(E,x)}. (norm F)\<^sup>2)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono_neutral)
    using kf_similar_elements_abs_summable
    by (auto intro!: 1 simp: that case_prod_unfold)
  moreover have \<open>\<dots> > 0\<close>
    using that by simp
  ultimately show ?thesis
    by auto
qed


lemma kf_element_weight_0_left[simp]: \<open>kf_element_weight 0 E = 0\<close>
  by (simp add: kf_element_weight_def kf_similar_elements_def zero_kraus_family.rep_eq)

lemma kf_element_weight_0_right[simp]: \<open>kf_element_weight E 0 = 0\<close>
  by (auto intro!: infsum_0 simp add: kf_element_weight_def kf_similar_elements_def)

lemma kf_element_weight_scale:
  assumes \<open>r > 0\<close>
  shows \<open>kf_element_weight \<EE> (r *\<^sub>R E) = kf_element_weight \<EE> E\<close>
proof -
  have [simp]: \<open>(\<exists>r'>0. r *\<^sub>R E = r' *\<^sub>R F) \<longleftrightarrow> (\<exists>r'>0. E = r' *\<^sub>R F)\<close> for F
    apply (rule Ex_iffI[where f=\<open>\<lambda>r'. r' /\<^sub>R r\<close> and g=\<open>\<lambda>r'. r *\<^sub>R r'\<close>])
    using assms apply auto
    by (metis divideR_right mult_zero_right not_square_less_zero pth_5)
  show ?thesis
    using assms
    by (simp add: kf_similar_elements_def kf_element_weight_def)
qed

lemma kf_map_aux:
  fixes f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
  defines \<open>B \<equiv> kf_bound \<EE>\<close>
  defines \<open>filtered y \<equiv> kf_filter (\<lambda>x. f x = y) \<EE>\<close>
  defines \<open>flattened \<equiv> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
  defines \<open>good \<equiv> (\<lambda>(E,y). (norm E)\<^sup>2 = kf_element_weight (filtered y) E \<and> E \<noteq> 0)\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close> (is ?has_sum)
    and \<open>snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close> (is ?snd_sigma)
    and \<open>inj_on snd (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close> (is ?inj_snd)
proof -
  have E_inv: \<open>kf_element_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)

  show snd_sigma: ?snd_sigma
  proof (intro Set.set_eqI iffI)
    fix Fx
    assume asm: \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    with asm obtain E y where Fx_rel_E: \<open>(F, x) \<in> kf_similar_elements (filtered y) E\<close> and \<open>good (E,y)\<close>
      by auto
    then have \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close>
      by (simp add: kf_similar_elements_def filtered_def kf_filter.rep_eq)
    from Fx_rel_E obtain r where \<open>E = r *\<^sub>R F\<close>
      by (smt (verit) kf_similar_elements_def mem_Collect_eq prod.sel(1) split_def)
    with \<open>good (E,y)\<close> have \<open>F \<noteq> 0\<close>
      by (simp add: good_def)
    with \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> show \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
      by (simp add: Fx_def)
  next
    fix Fx
    assume asm: \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    from asm have Fx_\<EE>: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> and [simp]: \<open>F \<noteq> 0\<close>
      by (auto simp: Fx_def)
    have weight_fx_F_not0: \<open>kf_element_weight (filtered (f x)) F \<noteq> 0\<close>
      using Fx_\<EE> by (simp_all add: filtered_def kf_filter.rep_eq kf_element_weight_neq0)
    then have weight_fx_F_pos: \<open>kf_element_weight (filtered (f x)) F > 0\<close>
      using kf_element_weight_geq0 
      by (metis less_eq_real_def)
    define E where \<open>E = (sqrt (kf_element_weight (filtered (f x)) F) / norm F) *\<^sub>R F\<close>
    have [simp]: \<open>E \<noteq> 0\<close>
      by (auto intro!: weight_fx_F_not0 simp: E_def)
    have E_F_same: \<open>kf_element_weight (filtered (f x)) E = kf_element_weight (filtered (f x)) F\<close>
      by (simp add: E_def kf_element_weight_scale weight_fx_F_pos)
    have \<open>good (E, f x)\<close>
      apply (simp add: good_def E_F_same)
      by (simp add: E_def)
    have 1: \<open>sqrt (kf_element_weight (filtered (f x)) F) / norm F > 0\<close>
      by (auto intro!: divide_pos_pos weight_fx_F_pos)
    then have \<open>(F, x) \<in> kf_similar_elements (filtered (f x)) E\<close>
      by (auto intro!: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> simp: kf_similar_elements_def E_def \<open>F \<noteq> 0\<close>
         filtered_def kf_filter.rep_eq)
    with \<open>good (E,f x)\<close>
    show \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (auto intro!: image_eqI[where x=\<open>((E,()),F,x)\<close>] simp: Fx_def filtered_def)
      by force
  qed

  show inj_snd: ?inj_snd
  proof (rule inj_onI)
    fix EFx EFx' :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) \<times> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x\<close>
    assume EFx_in: \<open>EFx \<in> (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
      and EFx'_in: \<open>EFx' \<in> (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
    assume snd_eq: \<open>snd EFx = snd EFx'\<close>
    obtain E F x y where [simp]: \<open>EFx = ((E,y),F,x)\<close>
      by (metis (full_types) old.unit.exhaust surj_pair)
    obtain E' F' x' y' where [simp]: \<open>EFx' = ((E',y'),(F',x'))\<close> 
      by (metis (full_types) old.unit.exhaust surj_pair)
    from snd_eq have [simp]: \<open>F' = F\<close> and [simp]: \<open>x' = x\<close>
      by auto
    from EFx_in have \<open>good (E,y)\<close> and F_rel_E: \<open>(F, x) \<in> kf_similar_elements (filtered y) E\<close>
      by auto
    from EFx'_in have \<open>good (E',y')\<close> and F_rel_E': \<open>(F, x) \<in> kf_similar_elements (filtered y') E'\<close>
      by auto
    from \<open>good (E,y)\<close> have \<open>E \<noteq> 0\<close>
      by (simp add: good_def)
    from \<open>good (E',y')\<close> have \<open>E' \<noteq> 0\<close>
      by (simp add: good_def)
    from F_rel_E obtain r where ErF: \<open>E = r *\<^sub>R F\<close> and \<open>r > 0\<close>
      by (auto intro!: simp: kf_similar_elements_def)
    from F_rel_E' obtain r' where E'rF: \<open>E' = r' *\<^sub>R F\<close> and \<open>r' > 0\<close>
      by (auto intro!: simp: kf_similar_elements_def)

    from EFx_in have \<open>y = f x\<close>
      by (auto intro!: simp: filtered_def kf_similar_elements_def kf_filter.rep_eq)
    moreover from EFx'_in have \<open>y' = f x'\<close>
      by (auto intro!: simp: filtered_def kf_similar_elements_def kf_filter.rep_eq)
    ultimately have [simp]: \<open>y = y'\<close>
      by simp

    define r'' where \<open>r'' = r' / r\<close>
    with E'rF ErF \<open>E \<noteq> 0\<close>
    have E'_E: \<open>E' = r'' *\<^sub>R E\<close>
      by auto
    with \<open>r' > 0\<close> \<open>r > 0\<close> \<open>E' \<noteq> 0\<close>
    have [simp]: \<open>r'' > 0\<close>
      by (fastforce simp: r''_def)
    from E'_E have \<open>kf_element_weight (filtered y') E' = kf_element_weight (filtered y) E\<close>
      by (simp add: kf_element_weight_scale)
    with \<open>good (E,y)\<close> \<open>good (E',y')\<close> have \<open>(norm E')\<^sup>2 = (norm E)\<^sup>2\<close>
      by (auto intro!: simp: good_def)
    with \<open>E' = r'' *\<^sub>R E\<close>
    have \<open>E' = E\<close>
      using \<open>0 < r''\<close> by force
    then show \<open>EFx = EFx'\<close>
      by simp
  qed

  show ?has_sum
  proof (unfold has_sum_in_cweak_operator_topology_pointwise, intro allI)
    fix \<psi> \<phi> :: 'a
    define B' where \<open>B' = \<psi> \<bullet>\<^sub>C B \<phi>\<close>
    define normal where \<open>normal E y = E /\<^sub>R sqrt (kf_element_weight (filtered y) E)\<close> for E y
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(F,x). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<EE>) B\<close>
      using B_def kf_bound_has_sum by blast
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') (Rep_kraus_family \<EE>)\<close>
      by (simp add: B'_def has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by (auto simp: zero_cblinfun_wot_def)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
           (snd ` (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
       (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,x)). (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B')
        (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kf_similar_elements_def kf_element_weight_scale 
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_scaleC_right scaleR_scaleC) 
      by (smt (verit) Extra_Ordered_Fields.mult_sign_intros(5) Extra_Ordered_Fields.sign_simps(5) inverse_eq_iff_eq left_inverse more_arith_simps(11) of_real_eq_0_iff of_real_mult power2_eq_square power_inverse real_inv_sqrt_pow2 zero_less_norm_iff)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                              (norm F)\<^sup>2) *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>))
                        has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kf_element_weight (filtered y) E *\<^sub>R 
                              (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (simp add: kf_element_weight_def)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv 
          cblinfun.scaleR_left scaleR_scaleC
          simp flip: inverse_mult_distrib semigroup_mult.mult_assoc)
      by (metis E_inv field_class.field_inverse kf_element_weight_geq0 mult.commute of_real_eq_0_iff of_real_hom.hom_mult power2_eq_square real_sqrt_pow2)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C ((case x of (E, uu_) \<Rightarrow> E* o\<^sub>C\<^sub>L E) *\<^sub>V \<phi>)) has_sum B') flattened\<close>
      by (simp add: case_prod_unfold)
  qed
qed


lift_definition kf_map :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
proof (rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  define filtered flattened B 
    where \<open>filtered y = kf_filter (\<lambda>x. f x = y) \<EE>\<close>
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kf_bound \<EE>\<close> 
    for y

  from kf_map_aux[of f \<EE>]
  have bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: filtered_def flattened_def B_def)

  from bound_has_sum show \<open>flattened \<in> Collect kraus_family\<close>
    by (auto simp: kraus_family_iff_summable summable_on_in_def)
qed

lemma
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows kf_apply_map[simp]: \<open>kf_apply (kf_map f \<EE>) = kf_apply \<EE>\<close>
    and kf_map_bound: \<open>kf_bound (kf_map f \<EE>) = kf_bound \<EE>\<close>
    and kf_map_norm[simp]: \<open>kf_norm (kf_map f \<EE>) = kf_norm \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  define filtered good flattened B normal \<sigma>
    where \<open>filtered y = kf_filter (\<lambda>x. f x = y) \<EE>\<close>
      and \<open>good = (\<lambda>(E,y). (norm E)\<^sup>2 = kf_element_weight (filtered y) E \<and> E \<noteq> 0)\<close>
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kf_bound \<EE>\<close> 
      and \<open>normal E y = E /\<^sub>R sqrt (kf_element_weight (filtered y) E)\<close>
      and \<open>\<sigma> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    for E y
  have E_inv: \<open>kf_element_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)

  from kf_map_aux[of f \<EE>]
  have snd_sigma: \<open>snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    and inj_snd: \<open>inj_on snd (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
    and bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: good_def filtered_def flattened_def B_def)

  show \<open>kf_apply (kf_map f \<EE>) \<rho> = \<sigma>\<close>
  proof -
    have \<open>(\<lambda>(F,x). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<EE>\<close>
      using kf_apply_summable by (simp add: case_prod_unfold)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) (Rep_kraus_family \<EE>)\<close>
      by (simp add: \<sigma>_def kf_apply_def split_def)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>)
           (snd ` (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). sandwich_tc F \<rho>) has_sum \<sigma>)
       (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,_)). (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>)
                (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kf_similar_elements_def kf_element_weight_scale)
      by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(5) linorder_not_less more_arith_simps(11) mult_eq_0_iff norm_le_zero_iff order.refl power2_eq_square right_inverse scale_one)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E. (norm F)\<^sup>2) *\<^sub>R sandwich_tc (normal E y) \<rho>)
                        has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kf_element_weight (filtered y) E *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (simp add: kf_element_weight_def)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      by (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>kf_map f \<EE> *\<^sub>k\<^sub>r \<rho> = \<sigma>\<close>
      by (simp add: kf_apply.rep_eq kf_map.rep_eq flattened_def
          case_prod_unfold infsumI filtered_def)
  qed

  from bound_has_sum show bound: \<open>kf_bound (kf_map f \<EE>) = B\<close>
    apply (simp add: kf_bound_def flattened_def kf_map.rep_eq B_def filtered_def)
    using has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology summable_on_in_def
    by blast

  from bound show \<open>kf_norm (kf_map f \<EE>) = kf_norm \<EE>\<close>
    by (simp add: kf_norm_def B_def)
qed

abbreviation \<open>kf_flatten \<equiv> kf_map (\<lambda>_. ())\<close>

text \<open>Like \<^const>\<open>kf_map\<close>, but with a much simpler definition.
      However, only makes sense for injective functions.\<close>
lift_definition kf_map_inj :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. (\<lambda>(E,x). (E, f x)) ` \<EE>\<close>
proof (rule CollectI, rule kraus_familyI, rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then obtain B where B: \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<in> {F. finite F \<and> F \<subseteq> \<EE>}\<close> for F
    by (auto simp: kraus_family_def bdd_above_def)
  show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>})\<close>
  proof (rule bdd_aboveI2)
    fix F assume \<open>F \<in> {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>}\<close>
    then obtain F' where \<open>finite F'\<close> and \<open>F' \<subseteq> \<EE>\<close> and F_F': \<open>F = (\<lambda>(E, x). (E, f x)) ` F'\<close>
      and inj: \<open>inj_on (\<lambda>(E, x). (E, f x)) F'\<close>
      by (metis (no_types, lifting) finite_imageD mem_Collect_eq subset_image_inj)
    have \<open>(\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by (auto intro!: B \<open>finite F'\<close> \<open>F' \<subseteq> \<EE>\<close>)
    moreover have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
      apply (simp add: F_F' inj sum.reindex)
      by (simp add: case_prod_beta)
    ultimately show \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by simp
  qed
qed                              

lemma kf_eq_weak_kf_map_left: \<open>kf_map f F =\<^sub>k\<^sub>r G\<close> if \<open>F =\<^sub>k\<^sub>r G\<close>
  using that by (simp add: kf_eq_weak_def kf_apply_map)

lemma kf_eq_weak_kf_map_right: \<open>F =\<^sub>k\<^sub>r kf_map f G\<close> if \<open>F =\<^sub>k\<^sub>r G\<close>
  using that by (simp add: kf_eq_weak_def kf_apply_map)

lemma kf_filter_map:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>kf_filter P (kf_map f \<EE>) = kf_map f (kf_filter (\<lambda>x. P (f x)) \<EE>)\<close>
proof -
  have \<open>(E,x) \<in> Set.filter (\<lambda>(E, y). P y) {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}
   \<longleftrightarrow> (E,x) \<in> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) (kf_filter (\<lambda>x. P (f x)) \<EE>)) E \<and> E \<noteq> 0}\<close>
    for E x and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  proof (cases \<open>P x\<close>)
    case True
    then show ?thesis
      apply (auto simp: kf_filter_twice)
      by metis+
  next
    case False
    then have [simp]: \<open>(\<lambda>z. f z = x \<and> P (f z)) = (\<lambda>_. False)\<close>
      by auto
    from False show ?thesis
      by (auto intro!: simp: kf_filter_twice)
  qed
  then show ?thesis
    apply (transfer' fixing: P f)
    by blast
qed

lemma kf_filter_map_inj:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>kf_filter P (kf_map_inj f \<EE>) = kf_map_inj f (kf_filter (\<lambda>x. P (f x)) \<EE>)\<close>
  apply (transfer' fixing: P f)
  by (force simp: case_prod_beta image_iff)

lemma kf_apply_map_inj[simp]:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
proof -
  define EE where \<open>EE = Set.filter (\<lambda>(E,x). E\<noteq>0) (Rep_kraus_family \<EE>)\<close>
  have \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>)\<close>
    by (simp add: kf_apply.rep_eq kf_map_inj.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` EE. sandwich_tc (fst E) \<rho>)\<close>
    apply (rule infsum_cong_neutral)
      apply (auto simp: EE_def)
    by fastforce
  also have \<open>\<dots> = infsum ((\<lambda>E. sandwich_tc (fst E) \<rho>) \<circ> (\<lambda>(E, x). (E, f x))) EE\<close>
    apply (rule infsum_reindex)
    using assms
    apply (auto intro!: simp: inj_on_def kf_domain.rep_eq EE_def)
    by (metis (mono_tags, lifting) Set.member_filter case_prodI snd_conv)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>EE. sandwich_tc E \<rho>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp: EE_def)
  also have \<open>\<dots> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    by (metis (no_types, lifting) infsum_cong kf_apply.rep_eq prod.case_eq_if)
  finally show \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    by -
qed

lemma kf_map_inj_eq_kf_map:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> \<equiv>\<^sub>k\<^sub>r kf_map f \<EE>\<close>
proof (rule kf_eqI)
  fix x \<rho>
  define \<EE>fx where \<open>\<EE>fx = kf_filter (\<lambda>z. f z = x) \<EE>\<close>
  from assms have inj_\<EE>fx: \<open>inj_on f (kf_domain \<EE>fx)\<close>
    by (simp add: inj_on_def kf_domain.rep_eq \<EE>fx_def kf_filter.rep_eq)
  have \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = kf_filter (\<lambda>z. z=x) (kf_map_inj f \<EE>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_on_def)
  also have \<open>\<dots> = kf_map_inj f \<EE>fx *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_apply t \<rho>\<close>])
    unfolding \<EE>fx_def
    apply (transfer' fixing: f)
    by force
  also have \<open>\<dots> = \<EE>fx *\<^sub>k\<^sub>r \<rho>\<close>
    using inj_\<EE>fx by (rule kf_apply_map_inj)
  also have \<open>\<dots> = kf_map f (kf_filter (\<lambda>z. f z = x) \<EE>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: \<EE>fx_def)
  also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>xa. xa = x) (kf_map f \<EE>)) \<rho>\<close>
    apply (subst kf_filter_map)
    by simp
  also have \<open>\<dots> = kf_map f \<EE> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by (simp add: kf_apply_on_def)
  finally show \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = kf_map f \<EE> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by -
qed

lemma kf_map_inj_id[simp]: \<open>kf_map_inj id \<EE> = \<EE>\<close>
  apply transfer' by simp

lemma kf_map_id: \<open>kf_map id \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (metis inj_on_id kf_eq_sym kf_map_inj_eq_kf_map kf_map_inj_id)

lemma kf_map_inj_bound[simp]:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_bound (kf_map_inj f \<EE>) = kf_bound \<EE>\<close>
  by (metis assms kf_eq_imp_eq_weak kf_map_inj_eq_kf_map kf_bound_cong kf_map_bound)

lemma kf_map_inj_norm[simp]:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_norm (kf_map_inj f \<EE>) = kf_norm \<EE>\<close>
  using assms kf_eq_imp_eq_weak kf_map_inj_eq_kf_map kf_norm_cong by fastforce

lemma kf_map_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_map f \<EE> =\<^sub>k\<^sub>r kf_map g \<FF>\<close>
  by (metis assms kf_eq_weak_def kf_apply_map)

lemma kf_flatten_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_flatten \<EE> =\<^sub>k\<^sub>r kf_flatten \<FF>\<close>
  using assms by (rule kf_map_cong_weak)

lemma kf_flatten_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_flatten \<EE> \<equiv>\<^sub>k\<^sub>r kf_flatten \<FF>\<close>
  by (simp add: assms kf_eq_weak_imp_eq_CARD_1 kf_flatten_cong_weak)

lemma kf_map_twice:
  \<open>kf_map f (kf_map g \<EE>) \<equiv>\<^sub>k\<^sub>r kf_map (f \<circ> g) \<EE>\<close>
  apply (rule kf_eqI)
  by (simp add: kf_filter_map kf_apply_on_def)

lemma kf_map_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_map f \<EE> \<equiv>\<^sub>k\<^sub>r kf_map f \<FF>\<close>
proof -
  from assms
  have \<open>\<EE> *\<^sub>k\<^sub>r @(f-`{x}) \<rho> = \<FF> *\<^sub>k\<^sub>r @(f-`{x}) \<rho>\<close> for x \<rho>
    by (rule kf_apply_on_eqI)
  then show ?thesis
    apply (rule_tac kf_eqI)
    by (simp add: kf_apply_on_def kf_filter_map)
qed

lemma kf_similar_elements_remove_0:
  assumes \<open>E \<noteq> 0\<close>
  shows \<open>kf_similar_elements (kf_remove_0 \<EE>) E = kf_similar_elements \<EE> E\<close>
  using assms by (auto simp: kf_similar_elements_def kf_remove_0.rep_eq)

lemma kf_element_weight_remove_0[simp]:
  \<open>kf_element_weight (kf_remove_0 \<EE>) E = kf_element_weight \<EE> E\<close>
proof (cases \<open>E = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    by (simp add: kf_element_weight_def kf_similar_elements_remove_0)
qed

lemma kf_map_remove_0[simp]:
  \<open>kf_map f (kf_remove_0 \<EE>) = kf_map f \<EE>\<close>
  apply (transfer' fixing: f)
  by (simp add: kf_map.rep_eq kf_filter_remove0)

lemma kf_domain_remove_0[simp]: \<open>kf_domain (kf_remove_0 E) = kf_domain E\<close>
  apply transfer'
  by auto

lemma kf_remove_0_map[simp]:
  \<open>kf_remove_0 (kf_map f \<EE>) = kf_map f \<EE>\<close>
  apply (transfer' fixing: f)
  by auto



lemma kf_domain_map[simp]:
  \<open>kf_domain (kf_map f \<EE>) = f ` kf_domain \<EE>\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x assume \<open>x \<in> kf_domain (kf_map f \<EE>)\<close>
  then obtain a where \<open>(norm a)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) a\<close> and \<open>a \<noteq> 0\<close>
    by (auto intro!: simp: kf_domain.rep_eq kf_map.rep_eq)
  then have \<open>kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) a \<noteq> 0\<close>
    by force
  then have \<open>(\<Sum>\<^sub>\<infinity>(E, _)\<in>kf_similar_elements (kf_filter (\<lambda>xa. f xa = x) \<EE>) a. (norm E)\<^sup>2) \<noteq> 0\<close>
    by (simp add: kf_element_weight_def)
  from this[unfolded not_def, rule_format, OF infsum_0]
  obtain E x' where rel_ops: \<open>(E,x') \<in> kf_similar_elements (kf_filter (\<lambda>xa. f xa = x) \<EE>) a\<close>
    and \<open>(norm E)\<^sup>2 \<noteq> 0\<close>
    by fast
  then have \<open>E \<noteq> 0\<close>
    by force
  with rel_ops obtain E' where \<open>E' \<noteq> 0\<close> and \<open>(E',x') \<in> Rep_kraus_family (kf_filter (\<lambda>xa. f xa = x) \<EE>)\<close>
    apply atomize_elim
    by (auto simp: kf_similar_elements_def)
  then have \<open>(E',x') \<in> Rep_kraus_family \<EE>\<close> and \<open>f x' = x\<close>
    by (auto simp: kf_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> have \<open>x' \<in> kf_domain \<EE>\<close>
    by (force simp: kf_domain.rep_eq)
  with \<open>f x' = x\<close>
  show \<open>x \<in> f ` kf_domain \<EE>\<close>
    by fast
next
  fix x assume \<open>x \<in> f ` kf_domain \<EE>\<close>
  then obtain y where \<open>x = f y\<close> and \<open>y \<in> kf_domain \<EE>\<close>
    by blast
  then obtain E where \<open>E \<noteq> 0\<close> and \<open>(E,y) \<in> Rep_kraus_family \<EE>\<close>
    by (auto simp: kf_domain.rep_eq)
  then have Ey: \<open>(E,y) \<in> Rep_kraus_family (kf_filter (\<lambda>z. f z=x) \<EE>)\<close>
    by (simp add: kf_filter.rep_eq \<open>x = f y\<close>)
  then have \<open>kf_bound (kf_filter (\<lambda>z. f z=x) \<EE>) \<noteq> 0\<close>
  proof -
    define B where \<open>B = kf_bound (kf_filter (\<lambda>z. f z=x) \<EE>)\<close>
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) {(E,y)} (E* o\<^sub>C\<^sub>L E)\<close>
      apply (subst asm_rl[of \<open>E* o\<^sub>C\<^sub>L E = (\<Sum>(E,x)\<in>{(E,y)}. E* o\<^sub>C\<^sub>L E)\<close>], simp)
      apply (rule has_sum_in_finite)
      by auto
    moreover have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_filter (\<lambda>z. f z = x) \<EE>)) B\<close>
      using kf_bound_has_sum B_def by blast
    ultimately have \<open>B \<ge> E* o\<^sub>C\<^sub>L E\<close>
      apply (rule has_sum_mono_neutral_wot)
      using Ey positive_cblinfun_squareI by auto
    then show \<open>B \<noteq> 0\<close>
      by (meson \<open>E \<noteq> 0\<close> basic_trans_rules(24) op_square_nondegenerate positive_cblinfun_squareI)
  qed
  then have \<open>kf_bound (kf_map f (kf_filter (\<lambda>z. f z=x) \<EE>)) \<noteq> 0\<close>
    by (simp add: kf_map_bound)
  then have \<open>kf_bound (kf_filter (\<lambda>z. z=x) (kf_map f \<EE>)) \<noteq> 0\<close>
    by (simp add: kf_filter_map)
  from this[unfolded not_def kf_bound.rep_eq, rule_format, OF infsum_in_0]
  obtain E' x' where \<open>(E',x') \<in> Rep_kraus_family (kf_filter (\<lambda>z. z=x) (kf_map f \<EE>))\<close>
    and \<open>E' \<noteq> 0\<close>
    by fastforce
  then have \<open>(E',x') \<in> Rep_kraus_family (kf_map f \<EE>)\<close> and \<open>x' = x\<close>
    by (auto simp: kf_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> show \<open>x \<in> kf_domain (kf_map f \<EE>)\<close>
    by (auto simp: kf_domain.rep_eq image_iff Bex_def)
qed


lemma kf_apply_on_map[simp]:
  \<open>(kf_map f E) *\<^sub>k\<^sub>r @X \<rho> = E *\<^sub>k\<^sub>r @(f -` X) \<rho>\<close>
  by (auto intro!: simp: kf_apply_on_def kf_filter_map)

lemma kf_map0[simp]: \<open>kf_map f 0 = 0\<close>
  apply transfer'
  by auto

subsection \<open>Addition\<close>

lift_definition kf_plus :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'b,'y) kraus_family \<Rightarrow> ('a,'b,'x+'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>(E,x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` \<FF>\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close> and \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  then have \<open>kraus_family ((\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF>)\<close>
    by (auto intro!: summable_on_Un_disjoint
      summable_on_reindex[THEN iffD2] inj_onI
      simp: kraus_family_iff_summable' o_def case_prod_unfold conj_commute)
  then show \<open>(\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF> \<in> Collect kraus_family\<close>
    by simp
qed

instantiation kraus_family :: (chilbert_space, chilbert_space, type) plus begin
definition plus_kraus_family where \<open>\<EE> + \<FF> = kf_map (\<lambda>xy. case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y) (kf_plus \<EE> \<FF>)\<close>
instance..
end

lemma kf_plus_apply:
  fixes \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('a, 'b, 'y) kraus_family\<close>
  shows \<open>kf_apply (kf_plus \<EE> \<FF>) \<rho> = kf_apply \<EE> \<rho> + kf_apply \<FF> \<rho>\<close>
proof -
  have \<open>kf_apply (kf_plus \<EE> \<FF>) \<rho> = 
    (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x)) ` Rep_kraus_family \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    by (simp add: kf_plus.rep_eq kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x :: 'x+'y)) ` Rep_kraus_family \<EE>. sandwich_tc (fst EF) \<rho>)
                + (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(F,y). (F, Inr y :: 'x+'y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    apply (subst infsum_Un_disjoint)
    using kf_apply_summable
    by (auto intro!: summable_on_reindex[THEN iffD2] inj_onI
        simp: o_def case_prod_unfold kf_apply_summable)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>) + (\<Sum>\<^sub>\<infinity>F\<in>Rep_kraus_family \<FF>. sandwich_tc (fst F) \<rho>)\<close>
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    by (simp add:  o_def case_prod_unfold)
  also have \<open>\<dots> = kf_apply \<EE> \<rho> + kf_apply \<FF> \<rho>\<close>
    by (simp add: kf_apply_def)
  finally show ?thesis
    by -
qed

lemma kf_plus_apply': \<open>(\<EE> + \<FF>) *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho> + \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  by (simp add: kf_plus_apply plus_kraus_family_def)

lemma kf_plus_0_left[simp]: \<open>kf_plus 0 \<EE> = kf_map_inj Inr \<EE>\<close>
  apply transfer' by auto

lemma kf_plus_0_right[simp]: \<open>kf_plus \<EE> 0 = kf_map_inj Inl \<EE>\<close>
  apply transfer' by auto

lemma kf_plus_0_left'[simp]: \<open>0 + \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
proof -
  define merge where \<open>merge xy = (case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)\<close> for xy :: \<open>'c + 'c\<close>
  have \<open>0 + \<EE> = kf_map merge (kf_map_inj Inr \<EE>)\<close>
    by (simp add: plus_kraus_family_def merge_def[abs_def])
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map merge (kf_map Inr \<EE>)\<close>
    by (auto intro!: kf_map_cong kf_map_inj_eq_kf_map)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (merge o Inr) \<EE>\<close>
  by (simp add: kf_map_twice)
  also have \<open>\<dots> = kf_map id \<EE>\<close>
    apply (rule arg_cong2[where f=kf_map])
    by (auto simp: merge_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
    by (simp add: kf_map_id)
  finally show ?thesis
    by -
qed

lemma kf_plus_0_right': \<open>\<EE> + 0 \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
proof -
  define merge where \<open>merge xy = (case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)\<close> for xy :: \<open>'c + 'c\<close>
  have \<open>\<EE> + 0 = kf_map merge (kf_map_inj Inl \<EE>)\<close>
    by (simp add: plus_kraus_family_def merge_def[abs_def])
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map merge (kf_map Inl \<EE>)\<close>
    by (auto intro!: kf_map_cong kf_map_inj_eq_kf_map)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (merge o Inl) \<EE>\<close>
  by (simp add: kf_map_twice)
  also have \<open>\<dots> = kf_map id \<EE>\<close>
    apply (rule arg_cong2[where f=kf_map])
    by (auto simp: merge_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
    by (simp add: kf_map_id)
  finally show ?thesis
    by -
qed

lemma kf_plus_bound: \<open>kf_bound (kf_plus \<EE> \<FF>) = kf_bound \<EE> + kf_bound \<FF>\<close>
proof -
  define l r where \<open>l = (\<lambda>(E::'a\<Rightarrow>\<^sub>C\<^sub>L'b, x) \<Rightarrow> (E, Inl x :: 'c+'d))\<close>
    and \<open>r = (\<lambda>(F::'a\<Rightarrow>\<^sub>C\<^sub>L'b, y) \<Rightarrow> (F, Inr y :: 'c+'d))\<close>
  have \<open>Abs_cblinfun_wot (kf_bound (kf_plus \<EE> \<FF>)) 
    = (\<Sum>\<^sub>\<infinity>(E, x)\<in>l ` Rep_kraus_family \<EE> \<union> r ` Rep_kraus_family \<FF>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    by (simp add: kf_bound_def' kf_plus.rep_eq Rep_cblinfun_wot_inverse flip: l_def r_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>l ` Rep_kraus_family \<EE>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))
                + (\<Sum>\<^sub>\<infinity>(E, x)\<in>r ` Rep_kraus_family \<FF>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (rule infsum_Un_disjoint)
      apply (metis (no_types, lifting) ext Un_empty_right l_def image_empty kf_bound_summable' kf_plus.rep_eq
        zero_kraus_family.rep_eq) 
     apply (metis (no_types, lifting) ext r_def empty_subsetI image_empty kf_bound_summable' kf_plus.rep_eq
        sup.absorb_iff2 zero_kraus_family.rep_eq) 
    by (auto intro!: simp: l_def r_def)
  also have \<open>\<dots> = Abs_cblinfun_wot (kf_bound (kf_map_inj Inl \<EE> :: (_,_,'c+'d) kraus_family)) + Abs_cblinfun_wot (kf_bound (kf_map_inj Inr \<FF> :: (_,_,'c+'d) kraus_family))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse l_def r_def kf_map_inj.rep_eq case_prod_unfold)
  also have \<open>\<dots> = Abs_cblinfun_wot (kf_bound \<EE> + kf_bound \<FF>)\<close>
    by (simp add: kf_map_inj_bound plus_cblinfun_wot.abs_eq)
  finally show ?thesis
    by (metis (no_types, lifting) Rep_cblinfun_wot_inverse kf_bound_def' plus_cblinfun_wot.rep_eq)
qed

lemma kf_plus_bound': \<open>kf_bound (\<EE> + \<FF>) = kf_bound \<EE> + kf_bound \<FF>\<close>
  by (simp add: kf_map_bound kf_plus_bound plus_kraus_family_def)

lemma kf_norm_triangle: \<open>kf_norm (kf_plus \<EE> \<FF>) \<le> kf_norm \<EE> + kf_norm \<FF>\<close>
  by (simp add: kf_norm_def kf_plus_bound norm_triangle_ineq)

lemma kf_norm_triangle': \<open>kf_norm (\<EE> + \<FF>) \<le> kf_norm \<EE> + kf_norm \<FF>\<close>
  by (simp add: kf_norm_def kf_plus_bound' norm_triangle_ineq)

subsection \<open>Composition\<close>

lemma kf_comp_dependent_raw_norm_aux:
  fixes \<EE> :: \<open>'a \<Rightarrow> ('e::chilbert_space, 'f::chilbert_space, 'g) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space, 'e, 'a) kraus_family\<close>
  assumes B: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes [simp]: \<open>B \<ge> 0\<close>
  assumes \<open>finite C\<close>
  assumes C_subset: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  shows \<open>(\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E) \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
proof -
  define BF :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>BF = kf_norm \<FF> *\<^sub>R id_cblinfun\<close>
  then have \<open>kf_bound \<FF> \<le> BF\<close>
    by (simp add: kf_bound_leq_kf_norm_id)
  then have BF: \<open>(\<Sum>(F, y)\<in>M. (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>M \<subseteq> Rep_kraus_family \<FF>\<close> and \<open>finite M\<close> for M
    using dual_order.trans kf_bound_geq_sum that(1) by blast
  define BE :: \<open>'e \<Rightarrow>\<^sub>C\<^sub>L 'e\<close> where \<open>BE = B *\<^sub>R id_cblinfun\<close>
  define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  have BE: \<open>(\<Sum>(E, x)\<in>M. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>y \<in> kf_domain \<FF>\<close> and \<open>M \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>finite M\<close> for M y
  proof -
    from B that(1,2)
    have \<open>norm (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by (smt (verit) kf_norm_geq_norm_sum that)
    then show ?thesis
      by (auto intro!: less_eq_scaled_id_norm pos_selfadjoint sum_nonneg intro: positive_cblinfun_squareI simp: BE_def)
  qed

  define A where \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
  define CE CF where \<open>CE y = (\<lambda>(_,(F,E,y,x)). (E,x)) ` Set.filter (\<lambda>(_,(F,E,y',x)). y'=y) C\<close> 
    and \<open>CF = (\<lambda>(_,(F,E,y,x)). (F,y)) ` C\<close> for y
  with \<open>finite C\<close> have [simp]: \<open>finite (CE y)\<close> \<open>finite CF\<close> for y
    by auto
  have C_C1C2: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y)\<close>
  proof (rule subsetI)
    fix c assume \<open>c \<in> C\<close>
    then obtain EF E F x y where c_def: \<open>c = (EF,(F,E,y,x))\<close>
      by (metis surj_pair)
    from \<open>c \<in> C\<close> have EF_def: \<open>EF = E o\<^sub>C\<^sub>L F\<close>
      using C_subset by (auto intro!: simp: c_def)
    from \<open>c \<in> C\<close> have 1: \<open>(F,y) \<in> CF\<close>
      apply (simp add: CF_def c_def)
      by force
    from \<open>c \<in> C\<close> have 2: \<open>(E,x) \<in> CE y\<close>
      apply (simp add: CE_def c_def)
      by force
    from 1 2 show \<open>c \<in> (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):CF. CE y)\<close>
      apply (simp add: c_def EF_def)
      by force
  qed

  have CE_sub_\<EE>: \<open>CE y \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> for y
    using C_subset by (auto simp add: CE_def CF_def \<FF>x\<EE>_def case_prod_unfold)
  have CE_BE: \<open>(\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>y \<in> kf_domain \<FF>\<close> for y
    using BE[where y=y] CE_sub_\<EE>[of y] that
    by auto

  have \<open>A \<le> (\<Sum>(E,x) \<in> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y). E* o\<^sub>C\<^sub>L E)\<close>
    using C_C1C2 apply (auto intro!: finite_imageI sum_mono2 simp: A_def)
    by (metis adj_cblinfun_compose positive_cblinfun_squareI)
  also have \<open>\<dots> = (\<Sum>((F,y), (E,x))\<in>(SIGMA (F,y):CF. CE y). (F* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L F))\<close>
    apply (subst sum.reindex)
    by (auto intro!: inj_onI simp: case_prod_unfold cblinfun_compose_assoc)
  also have \<open>\<dots> = (\<Sum>(F, y)\<in>CF. sandwich (F*) (\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)))\<close>
    apply (subst sum.Sigma[symmetric])
    by (auto intro!: simp: case_prod_unfold sandwich_apply cblinfun_compose_sum_right cblinfun_compose_sum_left simp flip: )
  also have \<open>\<dots> \<le> (\<Sum>(F, y)\<in>CF. sandwich (F*) BE)\<close>
  proof (rule sum_mono)
    fix i :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'e \<times> 'a\<close> assume \<open>i \<in> CF\<close>
    obtain F y where i: \<open>i = (F,y)\<close>
      by force
    have 1: \<open>sandwich (F*) *\<^sub>V (\<Sum>(E,x)\<in>CE y. E* o\<^sub>C\<^sub>L E) \<le> sandwich (F*) *\<^sub>V BE\<close> if \<open>y \<in> kf_domain \<FF>\<close>
      apply (rule sandwich_mono)
      using that CE_BE by simp
    have \<open>F = 0\<close> if \<open>y \<notin> kf_domain \<FF>\<close>
        using C_subset CF_def \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> \<open>i \<in> CF\<close> that i
        by (smt (verit, ccfv_SIG) Set.basic_monos(7) Set.member_filter case_prodI image_iff kf_domain.rep_eq prod.sel(2))
    then have 2: \<open>sandwich (F*) *\<^sub>V (\<Sum>(E,x)\<in>CE y. E* o\<^sub>C\<^sub>L E) \<le> sandwich (F*) *\<^sub>V BE\<close> if \<open>y \<notin> kf_domain \<FF>\<close>
      using that by simp
    from 1 2 show \<open>(case i of (F, y) \<Rightarrow> sandwich (F*) *\<^sub>V (\<Sum>(E, x)\<in>CE y. E* o\<^sub>C\<^sub>L E))
         \<le> (case i of (F, y) \<Rightarrow> sandwich (F*) *\<^sub>V BE)\<close>
      by (auto simp: case_prod_unfold i)
  qed
  also have \<open>\<dots> = B *\<^sub>R (\<Sum>(F, y)\<in>CF. F* o\<^sub>C\<^sub>L F)\<close>
    by (simp add: scaleR_sum_right case_prod_unfold sandwich_apply BE_def)
  also have \<open>\<dots> \<le> B *\<^sub>R BF\<close>
    using BF by (simp add: \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> scaleR_left_mono case_prod_unfold)
  also have \<open>B *\<^sub>R BF = (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by (simp add: BF_def)
  finally show \<open>A \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by -
qed

lift_definition kf_comp_dependent_raw :: \<open>('x \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'y) kraus_family) \<Rightarrow> ('a::chilbert_space,'b,'x) kraus_family
                    \<Rightarrow> ('a, 'c, 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'x \<times> 'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. if bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>) then
    (\<lambda>((F,y), (E::'b\<Rightarrow>\<^sub>C\<^sub>L'c,x::'y)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F::'a\<Rightarrow>\<^sub>C\<^sub>L'b,y::'x):Rep_kraus_family \<FF>. (Rep_kraus_family (\<EE> y)))
    else {}\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>'x \<Rightarrow> ('b, 'c, 'y) kraus_family\<close> and \<FF> :: \<open>('a, 'b, 'x) kraus_family\<close>
  show \<open>(if bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)
        then (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F, E, y, x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))
        else {})
       \<in> Collect kraus_family\<close>
  proof (cases \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>)
    case True
    obtain B where \<EE>_uniform: \<open>y \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> y) \<le> B\<close> and \<open>B \<ge> 0\<close> for y
    proof atomize_elim
      from True
      obtain B0 where \<open>y \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> y) \<le> B0\<close> for y
        by (auto simp: bdd_above_def)
      then show \<open>\<exists>B. (\<forall>y. y \<in> kf_domain \<FF> \<longrightarrow> kf_norm (\<EE> y) \<le> B) \<and> 0 \<le> B\<close>
        apply (rule_tac exI[of _ \<open>max 0 B0\<close>])
        by force
    qed
    define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    have \<open>bdd_above ((\<lambda>M. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) `
            {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE> \<and> finite M})\<close>
    proof (rule bdd_aboveI, rename_tac A)
      fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>A \<in> (\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE> \<and> finite M}\<close>
      then obtain C where A_def: \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
        and C\<FF>\<EE>: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE>\<close>
        and [simp]: \<open>finite C\<close>
        by auto
      from kf_comp_dependent_raw_norm_aux[OF \<EE>_uniform \<open>B \<ge> 0\<close> \<open>finite C\<close>]
      show \<open>A \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
        using C\<FF>\<EE>
        by (auto intro!: simp: A_def \<FF>x\<EE>_def)
    qed
    then have \<open>kraus_family ((\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))\<close>
      by (auto intro!: kraus_familyI simp: conj_commute \<FF>x\<EE>_def)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by (auto simp: kraus_family_def)
  qed
qed

lemma kf_comp_dependent_raw_norm_leq:
  fixes \<EE> :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'd) kraus_family\<close>
    and \<FF> :: \<open>('e::chilbert_space, 'b, 'a) kraus_family\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes \<open>B \<ge> 0\<close>
  shows \<open>kf_norm (kf_comp_dependent_raw \<EE> \<FF>) \<le> B * kf_norm \<FF>\<close>
proof -
  wlog not_singleton: \<open>class.not_singleton TYPE('e)\<close>
    using not_not_singleton_kf_norm_0[OF negation, of \<FF>]
    using not_not_singleton_kf_norm_0[OF negation, of \<open>kf_comp_dependent_raw \<EE> \<FF>\<close>]
    by simp
  show ?thesis
  proof (rule kf_norm_sum_leqI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> Rep_kraus_family (kf_comp_dependent_raw \<EE> \<FF>)\<close>
    have [simp]: \<open>norm (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e) = 1\<close>
      apply (rule norm_cblinfun_id[internalize_sort' 'a])
      apply (rule complex_normed_vector_axioms)
      by (rule not_singleton)
    from assms have bdd: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
      by fast
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
      using assms \<open>finite F\<close> apply (rule kf_comp_dependent_raw_norm_aux)
      using F_subset by (simp_all add: kf_comp_dependent_raw.rep_eq bdd)
    then have \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm ((B * kf_norm \<FF>) *\<^sub>R (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e))\<close>
      apply (rule norm_cblinfun_mono[rotated])
      apply (auto intro!: sum_nonneg)
      using positive_cblinfun_squareI by blast
    then show \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B * kf_norm \<FF>\<close>
      using \<open>B \<ge> 0\<close> by auto
  qed
qed

hide_fact kf_comp_dependent_raw_norm_aux

definition \<open>kf_comp_dependent \<EE> \<FF> = kf_map (\<lambda>(F,E,y,x). (y,x)) (kf_comp_dependent_raw \<EE> \<FF>)\<close>

definition \<open>kf_comp \<EE> \<FF> = kf_comp_dependent (\<lambda>_. \<EE>) \<FF>\<close>

lemma kf_comp_dependent_norm_leq:
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes \<open>B \<ge> 0\<close>
  shows \<open>kf_norm (kf_comp_dependent \<EE> \<FF>) \<le> B * kf_norm \<FF>\<close>
  using assms by (auto intro!: kf_comp_dependent_raw_norm_leq simp: kf_comp_dependent_def)

lemma kf_comp_norm_leq:
  shows \<open>kf_norm (kf_comp \<EE> \<FF>) \<le> kf_norm \<EE> * kf_norm \<FF>\<close>
  by (auto intro!: kf_comp_dependent_norm_leq simp: kf_comp_def)

lemma kf_comp_dependent_raw_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
            = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> y *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
proof -
  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F \<rho>) summable_on (Rep_kraus_family \<FF>)\<close>
    using kf_apply_summable[of \<rho> \<FF>] (* kraus\<FF> *) by (simp add: case_prod_unfold)
  have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    using kf_apply_summable[of _ \<open>kf_comp_dependent_raw \<EE> \<FF>\<close>] assms
    by (simp add: kf_comp_dependent_raw.rep_eq case_prod_unfold)
  then have sum1: \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>) summable_on (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)

  have \<open>kf_comp_dependent_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (fst E) \<rho>)\<close>
    using assms by (simp add: kf_apply_def kf_comp_dependent_raw.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((F,y), (E,x))\<in>(SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using sum1 by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc E (sandwich_tc F \<rho>))\<close>
    by (simp add: sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kf_apply (\<EE> y) (sandwich_tc F \<rho>))\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  finally show ?thesis
    by -
qed

lemma kf_comp_dependent_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
      = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> y *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
  using assms by (simp add: kf_comp_dependent_def kf_apply_map
      kf_comp_dependent_raw_apply)

lemma kf_comp_apply:
  shows \<open>kf_apply (kf_comp \<EE> \<FF>) = kf_apply \<EE> \<circ> kf_apply \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have sumF: \<open>(\<lambda>(F, y). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<FF>\<close>
    by (rule kf_apply_summable)
  have \<open>kf_comp \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
    by (auto intro!: kf_comp_dependent_apply simp: kf_comp_def)
  also have \<open>\<dots> = kf_apply \<EE> (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc F \<rho>)\<close>
    apply (subst infsum_bounded_linear[symmetric, where h=\<open>kf_apply \<EE>\<close>])
    using sumF by (auto intro!: bounded_clinear.bounded_linear kf_apply_bounded_clinear
        simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (kf_apply \<EE> \<circ> kf_apply \<FF>) \<rho>\<close>
    by (simp add: o_def kf_apply_def case_prod_unfold)
  finally show \<open>kf_apply (kf_comp \<EE> \<FF>) \<rho> = (kf_apply \<EE> \<circ> kf_apply \<FF>) \<rho>\<close>
    by -
qed

lemma kf_comp_cong_weak: \<open>kf_comp F G =\<^sub>k\<^sub>r kf_comp F' G'\<close>
  if \<open>F =\<^sub>k\<^sub>r F'\<close> and \<open>G =\<^sub>k\<^sub>r G'\<close>
  by (metis kf_eq_weak_def kf_comp_apply that)

lemma kf_comp_dependent_raw_assoc: 
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  defines \<open>reorder :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'g \<times> 'f) \<times> 'e
                   \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'g \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'f \<times> 'e \<equiv>
             \<lambda>(FG::'a \<Rightarrow>\<^sub>C\<^sub>L 'c, E::'c \<Rightarrow>\<^sub>C\<^sub>L 'd, (G::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, F::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, g::'g, f::'f), e::'e). 
              (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e)\<close>
  assumes \<open>bdd_above (range (kf_norm o \<EE>))\<close>
  assumes \<open>bdd_above (range (kf_norm o \<FF>))\<close>
  shows \<open>kf_comp_dependent_raw (\<lambda>g::'g. kf_comp_dependent_raw \<EE> (\<FF> g)) \<GG>
        = kf_map_inj reorder (kf_comp_dependent_raw (\<lambda>(_,_,_,f). \<EE> f) (kf_comp_dependent_raw \<FF> \<GG>))\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (rule Rep_kraus_family_inject[THEN iffD1])
  from assms have bdd_E: \<open>bdd_above ((kf_norm o \<EE>) ` X)\<close> for X
    by (simp add: bdd_above_mono2)
  from assms have bdd_F: \<open>bdd_above ((kf_norm o \<FF>) ` X)\<close> for X
    by (simp add: bdd_above_mono2)
  have bdd1: \<open>bdd_above ((\<lambda>x. kf_norm (kf_comp_dependent_raw \<EE> (\<FF> x))) ` X)\<close> for X
  proof -
    from bdd_F[where X=UNIV] obtain BF where BF: \<open>kf_norm (\<FF> x) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    moreover from bdd_E[where X=UNIV] obtain BE where BE: \<open>kf_norm (\<EE> x) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>kf_norm (kf_comp_dependent_raw (\<lambda>x. \<EE> x) (\<FF> x)) \<le> BE * BF\<close> for x
      by (smt (verit, best) kf_comp_dependent_raw_norm_leq kf_norm_geq0 landau_omega.R_mult_left_mono)
    then show ?thesis
      by (auto intro!: bdd_aboveI)
  qed
  have bdd2: \<open>bdd_above ((kf_norm \<circ> (\<lambda>(_::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, _::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, _::'g, y::'f). \<EE> y)) ` X)\<close> for X
    using assms(2) by (auto simp: bdd_above_def)
  define EE FF GG where \<open>EE f = Rep_kraus_family (\<EE> f)\<close> and \<open>FF g = Rep_kraus_family (\<FF> g)\<close> and \<open>GG = Rep_kraus_family \<GG>\<close> for f g
  have \<open>Rep_kraus_family ?lhs
        = (\<lambda>((F,y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
          (SIGMA (F, y):GG. Rep_kraus_family (kf_comp_dependent_raw \<EE> (\<FF> y)))\<close>
    apply (subst kf_comp_dependent_raw.rep_eq)
    using bdd1 by (simp add:  GG_def)
  also have \<open>\<dots> = (\<lambda>((G, g), (EF, x)). (EF o\<^sub>C\<^sub>L G, G, EF, g, x)) `
    (SIGMA (G, g):GG. (\<lambda>((F, f), (E, e)). (E o\<^sub>C\<^sub>L F, F, E, f, e)) ` (SIGMA (F, f):FF g. EE f))\<close>
    unfolding EE_def FF_def
    apply (subst kf_comp_dependent_raw.rep_eq)
    using assms bdd_E by (simp add: case_prod_beta)
  also have \<open>\<dots> = (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) ` 
         (SIGMA (FG, _, _, _, y):(\<lambda>((G, g), (F, f)). (F o\<^sub>C\<^sub>L G, G, F, g, f)) ` (SIGMA (G, g):GG. FF g). EE y)\<close>
    by (force simp: reorder_def image_iff case_prod_unfold cblinfun_compose_assoc)
  also have \<open>\<dots> = (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kf_comp_dependent_raw \<FF> \<GG>). EE f)\<close>
    apply (subst kf_comp_dependent_raw.rep_eq)
    using assms bdd_F
    by (simp add: flip: FF_def GG_def)
  also have \<open>\<dots> =  (\<lambda>(E,z). (E, reorder z)) ` (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kf_comp_dependent_raw \<FF> \<GG>).
        EE f)\<close>
    by (simp add: image_image case_prod_beta)
  also have \<open>\<dots> = (\<lambda>(E,x). (E,reorder x)) ` Rep_kraus_family
     (kf_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kf_comp_dependent_raw \<FF> \<GG>))\<close>
    apply (subst (2) kf_comp_dependent_raw.rep_eq)
    using bdd2 by (simp add: case_prod_unfold EE_def)
  also have \<open>\<dots> = Rep_kraus_family ?rhs\<close>
    by (simp add: kf_map_inj.rep_eq case_prod_beta)
  finally show \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    by -
qed

lemma kf_filter_comp_dependent:
  fixes \<FF> :: \<open>'e \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'e) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<FF>) ` kf_domain \<EE>)\<close>
  shows \<open>kf_filter (\<lambda>(e,f). F e f \<and> E e) (kf_comp_dependent \<FF> \<EE>)
      = kf_comp_dependent (\<lambda>e. kf_filter (F e) (\<FF> e)) (kf_filter E \<EE>)\<close>
proof -
  from assms
  have bdd2: \<open>bdd_above ((\<lambda>e. kf_norm (kf_filter (F e) (\<FF> e))) ` kf_domain \<EE>)\<close>
    apply (rule bdd_above_mono2)
    by (auto intro!: kf_norm_filter)
  then have bdd3: \<open>bdd_above ((\<lambda>x. kf_norm (kf_filter (F x) (\<FF> x))) `
                              kf_domain (kf_filter E \<EE>))\<close>
    apply (rule bdd_above_mono2)
    by auto
  show ?thesis
    unfolding kf_comp_dependent_def kf_filter_map
    apply (rule arg_cong[where f=\<open>kf_map _\<close>])
    using assms bdd2 bdd3 apply (transfer' fixing: F E)
    by (auto intro!: simp: kf_filter.rep_eq case_prod_unfold image_iff Bex_def)
qed

lemma kf_comp_assoc_weak: 
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kf_comp (kf_comp \<EE> \<FF>) \<GG> =\<^sub>k\<^sub>r kf_comp \<EE> (kf_comp \<FF> \<GG>)\<close>
  apply (rule kf_eq_weakI)
  by (simp add: kf_comp_apply)

lemma kf_comp_dependent_raw_cong_left:
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> snd ` Rep_kraus_family \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kf_comp_dependent_raw \<EE> \<FF> = kf_comp_dependent_raw \<EE>' \<FF>\<close>
proof -
  show ?thesis
  apply (rule Rep_kraus_family_inject[THEN iffD1])
    using assms
  by (force simp: kf_comp_dependent_def kf_comp_dependent_raw.rep_eq 
      image_iff case_prod_beta Bex_def) 
qed

lemma kf_remove_0_comp_dependent_raw:
  \<open>kf_remove_0 (kf_comp_dependent_raw \<EE> \<FF>) =
      kf_remove_0 (kf_comp_dependent_raw (\<lambda>x. kf_remove_0 (\<EE> x)) (kf_remove_0 \<FF>))\<close>
  apply transfer'
  by (auto intro!: simp: image_iff case_prod_beta kf_remove_0.rep_eq Bex_def)

lemma kf_comp_dependent_cong_left:
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> = kf_comp_dependent \<EE>' \<FF>\<close>
proof -
  have bdd1: \<open>bdd_above ((kf_norm \<circ> (\<lambda>x. kf_remove_0 (\<EE> x))) ` kf_domain (kf_remove_0 \<FF>))\<close>
    using assms(1) by fastforce
  have bdd2: \<open>bdd_above ((kf_norm \<circ> (\<lambda>x. kf_remove_0 (\<EE>' x))) ` kf_domain (kf_remove_0 \<FF>))\<close>
    using assms(2) by fastforce

  have \<open>kf_comp_dependent \<EE> \<FF> = kf_map (\<lambda>(F, E, y). y) (kf_comp_dependent_raw \<EE> \<FF>)\<close>
    by (simp add: kf_comp_dependent_def id_def)
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) (kf_remove_0 (kf_comp_dependent_raw \<EE> \<FF>))\<close>
    by simp
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) (kf_remove_0 (kf_comp_dependent_raw (\<lambda>x. kf_remove_0 (\<EE> x)) (kf_remove_0 \<FF>)))\<close>
    apply (subst kf_remove_0_comp_dependent_raw)
    by simp
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) (kf_remove_0 (kf_comp_dependent_raw (\<lambda>x. kf_remove_0 (\<EE>' x)) (kf_remove_0 \<FF>)))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_map _ (kf_remove_0 t)\<close>])
    apply (rule kf_comp_dependent_raw_cong_left[OF bdd1 bdd2])
    using assms by (auto intro!: simp: kf_domain.rep_eq kf_remove_0.rep_eq)
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) (kf_remove_0 (kf_comp_dependent_raw \<EE>' \<FF>))\<close>
    apply (subst kf_remove_0_comp_dependent_raw[symmetric])
    by simp
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) (kf_comp_dependent_raw \<EE>' \<FF>)\<close>
    by simp
  also have \<open>\<dots> = kf_comp_dependent \<EE>' \<FF>\<close>
    by (simp add: kf_comp_dependent_def id_def)
  finally show ?thesis
    by -
qed

lemma kf_domain_comp_dependent_subset:
  \<open>kf_domain (kf_comp_dependent \<EE> \<FF>) \<subseteq> (SIGMA x:kf_domain \<FF>. kf_domain (\<EE> x))\<close>
  apply (simp add: kf_comp_dependent_def kf_domain_map id_def)
  apply (auto intro!: simp: kf_comp_dependent_raw.rep_eq kf_domain.rep_eq image_iff Bex_def)
   apply force
  by force

lemma kf_comp_dependent_assoc: 
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes bdd_E: \<open>bdd_above (range (kf_norm o \<EE>))\<close>
  assumes bdd_F: \<open>bdd_above (range (kf_norm o \<FF>))\<close>
  shows \<open>(kf_comp_dependent (\<lambda>g. kf_comp_dependent \<EE> (\<FF> g)) \<GG>) \<equiv>\<^sub>k\<^sub>r
  kf_map (\<lambda>((g,f),e). (g,f,e)) (kf_comp_dependent (\<lambda>(_,f). \<EE> f) (kf_comp_dependent \<FF> \<GG>))\<close>
    (is \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>)
proof (rule kf_eqI)
  fix gfe :: \<open>'g \<times> 'f \<times> 'e\<close> and \<rho>
  obtain g f e where gfe_def: \<open>gfe = (g,f,e)\<close>
    apply atomize_elim
    apply (rule exI[of _ \<open>fst gfe\<close>])
    apply (rule exI[of _ \<open>fst (snd gfe)\<close>])
    apply (rule exI[of _ \<open>snd (snd gfe)\<close>])
    by simp
  have aux: \<open>(\<lambda>x. (fst (fst x), snd (fst x), snd x) = gfe) = (\<lambda>x. x=((g,f),e))\<close>
    by (auto simp: gfe_def)
  have bdd5: \<open>bdd_above (range (\<lambda>x. kf_norm (kf_filter (\<lambda>x. x = f) (\<FF> x))))\<close>
    using kf_norm_filter bdd_F
    by (metis (mono_tags, lifting) bdd_above_mono2 o_def subset_UNIV)
  have bdd2: \<open>bdd_above (range (\<lambda>x. kf_norm (kf_filter (\<lambda>x. x = e) (\<EE> x))))\<close>
    using kf_norm_filter bdd_E
    by (metis (mono_tags, lifting) bdd_above_mono2 o_def subset_UNIV)
  then have bdd3: \<open>bdd_above ((\<lambda>(g, f). kf_norm (kf_filter (\<lambda>x. x = e) (\<EE> f))) ` X)\<close> for X
    by (auto simp: bdd_above_def)
  have bdd1: \<open>bdd_above (range (\<lambda>x. kf_norm (kf_comp_dependent
               (\<lambda>f. kf_filter (\<lambda>x. x = e) (\<EE> f)) (kf_filter (\<lambda>x. x = f) (\<FF> x)))))\<close>
  proof -
    from bdd2 obtain BE where BE: \<open>kf_norm (kf_filter (\<lambda>x. x = e) (\<EE> x)) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    then have \<open>BE \<ge> 0\<close>
      by (smt (z3) kf_norm_geq0)
    from bdd5 obtain BF where BF: \<open>kf_norm (kf_filter (\<lambda>x. x = f) (\<FF> x)) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    have \<open>kf_norm (kf_comp_dependent (\<lambda>x. kf_filter (\<lambda>x. x = e) (\<EE> x)) (kf_filter (\<lambda>x. x = f) (\<FF> x)))
      \<le> BE * kf_norm (kf_filter (\<lambda>x. x = f) (\<FF> x))\<close> for x
      using kf_comp_dependent_norm_leq[OF BE \<open>BE \<ge> 0\<close>] by fast
    then have \<open>kf_norm (kf_comp_dependent 
           (\<lambda>x. kf_filter (\<lambda>x. x = e) (\<EE> x)) (kf_filter (\<lambda>x. x = f) (\<FF> x)))
      \<le> BE * BF\<close> for x
      apply (rule order_trans)      
      using BF \<open>BE \<ge> 0\<close>
      by (auto intro!: mult_left_mono)
    then
    show ?thesis
      by (auto intro!: bdd_aboveI)
  qed
  have bdd6: \<open>bdd_above ((kf_norm \<circ> (\<lambda>g. kf_comp_dependent \<EE> (\<FF> g))) ` X)\<close> for X
  proof -
    from bdd_E obtain BE where BE: \<open>kf_norm (\<EE> x) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    then have \<open>BE \<ge> 0\<close>
      by (smt (z3) kf_norm_geq0)
    from bdd_F obtain BF where BF: \<open>kf_norm (\<FF> x) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    have \<open>kf_norm (kf_comp_dependent \<EE> (\<FF> x))
                  \<le> BE * kf_norm (\<FF> x)\<close> for x
      using kf_comp_dependent_norm_leq[OF BE \<open>BE \<ge> 0\<close>] by fast
    then have \<open>kf_norm (kf_comp_dependent \<EE> (\<FF> x))
      \<le> BE * BF\<close> for x
      apply (rule order_trans)      
      using BF \<open>BE \<ge> 0\<close>
      by (auto intro!: mult_left_mono)
    then
    show ?thesis
      by (auto intro!: bdd_aboveI)
  qed

  have \<open>?lhs *\<^sub>k\<^sub>r @{gfe} \<rho>
       = kf_comp_dependent 
            (\<lambda>g. kf_filter (\<lambda>x. x=(f,e)) (kf_comp_dependent \<EE> (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    unfolding kf_apply_on_def
    apply (subst kf_filter_comp_dependent[symmetric])
     apply (rule bdd6)
    apply (subst asm_rl[of \<open>(\<lambda>(x, y). y = (f, e) \<and> x = g) = (\<lambda>x. x \<in> {gfe})\<close>])
    by (auto simp: gfe_def)
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>g. kf_comp_dependent
                       (\<lambda>f. kf_filter (\<lambda>x. x=e) (\<EE> f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (subst (2) kf_filter_comp_dependent[symmetric])
    using bdd_E apply (simp add: bdd_above_mono2)
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = f) = (\<lambda>x. x = (f, e))\<close>])
    by auto
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>_. kf_comp_dependent
                       (\<lambda>f. kf_filter (\<lambda>x. x=e) (\<EE> f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_apply t \<rho>\<close>])
    apply (rule kf_comp_dependent_cong_left)
    using bdd1 by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>_. kf_comp_dependent
                       (\<lambda>_. kf_filter (\<lambda>x. x=e) (\<EE> f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_comp_dependent t _ *\<^sub>k\<^sub>r \<rho>\<close>])
    apply (rule ext)
    apply (rule kf_comp_dependent_cong_left)
    using bdd2 by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp
            (kf_comp
                       (kf_filter (\<lambda>x. x=e) (\<EE> f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_def)
  also have \<open>\<dots> = kf_comp (kf_filter (\<lambda>x. x=e) (\<EE> f))
                          (kf_comp (kf_filter (\<lambda>x. x=f) (\<FF> g)) (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_assoc_weak[unfolded kf_eq_weak_def])
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=e) (\<EE> f))
            (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_def)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> f))
            (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. t *\<^sub>k\<^sub>r \<rho>\<close>])
    apply (rule kf_comp_dependent_cong_left)
    using bdd3 apply force
    using bdd3 unfolding o_def case_prod_unfold apply force
    using kf_domain_comp_dependent_subset[of \<open>(\<lambda>_. kf_filter (\<lambda>x. x = f) (\<FF> g))\<close> \<open>kf_filter (\<lambda>x. x = g) \<GG>\<close>]
    by (auto intro!: simp: kf_filter.rep_eq case_prod_unfold)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> f))
            (kf_comp_dependent (\<lambda>g. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_comp_dependent _ t *\<^sub>k\<^sub>r _\<close>])
    apply (rule kf_comp_dependent_cong_left)
    using bdd5 by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> f))
            (kf_filter (\<lambda>x. x=(g,f)) (kf_comp_dependent \<FF> \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (subst kf_filter_comp_dependent[symmetric])
    using bdd_F apply (simp add: bdd_above_mono2)
    apply (subst asm_rl[of \<open>(\<lambda>(e, fa). fa = f \<and> e = g) = (\<lambda>x. x = (g, f))\<close>])
    by auto
  also have \<open>\<dots> = kf_filter (\<lambda>x. x=((g,f),e))
       (kf_comp_dependent (\<lambda>(g,f). \<EE> f) (kf_comp_dependent \<FF> \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    unfolding case_prod_beta
    apply (subst kf_filter_comp_dependent[symmetric])
    using bdd_E unfolding bdd_above_def apply force
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = (g, f)) = (\<lambda>x. x = ((g, f), e))\<close>])
    by auto
  also have \<open>\<dots> = kf_filter (\<lambda>x. x=gfe)
        (kf_map (\<lambda>((g, f), e). (g, f, e))
       (kf_comp_dependent (\<lambda>(g,f). \<EE> f) (kf_comp_dependent \<FF> \<GG>))) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_filter_map case_prod_beta aux)
  also have \<open>\<dots> = ?rhs *\<^sub>k\<^sub>r @{gfe} \<rho>\<close>
    by (simp add: kf_apply_on_def)
  finally show \<open>?lhs *\<^sub>k\<^sub>r @{gfe} \<rho> = ?rhs *\<^sub>k\<^sub>r @{gfe} \<rho>\<close>
    by -
qed

lemma kf_comp_assoc:
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kf_comp (kf_comp \<EE> \<FF>) \<GG> \<equiv>\<^sub>k\<^sub>r
   kf_map (\<lambda>((g,f),e). (g,f,e)) (kf_comp \<EE> (kf_comp \<FF> \<GG>))\<close>
  apply (simp add: kf_comp_def)
  apply (rule kf_eq_trans)
   apply (rule kf_comp_dependent_assoc)
  by (auto simp: case_prod_unfold)

lemma kf_apply_comp_dependent_cong:
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e1) kraus_family\<close>
    and \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e2) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes bdd': \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>')\<close>
  assumes \<open>\<And>x y. x \<in> kf_domain \<FF> \<Longrightarrow> kf_apply_on (\<EE> x) E = kf_apply_on (\<EE>' x) E'\<close>
  assumes \<open>kf_apply_on \<FF> {f} = kf_apply_on \<FF>' {f}\<close>
  shows \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({f}\<times>E')\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have rewrite_comp: \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E) = 
        kf_apply (kf_comp (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
                                           (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
    if \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close> 
    for E and \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close> 
      and \<FF> :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  proof -
    have bdd_filter: \<open>bdd_above ((kf_norm \<circ> (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))) ` kf_domain \<FF>)\<close>
      apply (rule bdd_above_mono2[OF _ subset_refl, rotated])
      using kf_norm_filter apply blast
      using that
      by (metis (mono_tags, lifting) bdd_above_mono2 comp_apply kf_norm_filter order.refl)
    have aux: \<open>(\<lambda>(x,y). y\<in>E \<and> x=f) = (\<lambda>x. x\<in>{f}\<times>E)\<close>
      by auto
    have *: \<open>kf_filter (\<lambda>x. x\<in>{f}\<times>E) (kf_comp_dependent \<EE> \<FF>)
        = kf_comp_dependent (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
               (kf_filter (\<lambda>x. x=f) \<FF>)\<close>
      using kf_filter_comp_dependent[where \<EE>=\<FF> and \<FF>=\<EE> and F=\<open>\<lambda>_ x. x\<in>E\<close> and E=\<open>\<lambda>x. x=f\<close>,
            OF that]
      unfolding aux by auto
    have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E)
      = kf_apply (kf_comp_dependent (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
                                                     (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      by (auto intro!: simp: kf_apply_on_def * )
    also have \<open>\<dots> = kf_apply
     (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
       (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      apply (rule arg_cong[where f="\<lambda>z. kf_apply z"])
      apply (rule kf_comp_dependent_cong_left)
      using bdd_filter by auto
    also have \<open>\<dots> = kf_apply (kf_comp (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
       (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      by (simp add: kf_comp_def)
    finally show ?thesis
      by -
  qed

  have rew_\<EE>: \<open>kf_apply (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
      = kf_apply (kf_filter (\<lambda>x. x\<in>E') (\<EE>' f))\<close>
    if \<open>f \<in> kf_domain \<FF>\<close>
    using assms(3)[OF that]
    by (simp add: kf_apply_on_def)
  have rew_\<FF>: \<open>kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>')
     = kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>)\<close>
    using assms(4)
    by (simp add: kf_apply_on_def)
  have \<FF>_0: \<open>kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>) = 0\<close>
    if \<open>f \<notin> kf_domain \<FF>\<close>
  proof -
    have *: \<open>(x = f \<and> x \<in> kf_domain \<FF>) \<longleftrightarrow> False\<close> for x
      using that by simp

    have \<open>kf_filter (\<lambda>f'. f' = f) \<FF> \<equiv>\<^sub>k\<^sub>r
             kf_filter (\<lambda>f'. f' = f) (kf_filter (\<lambda>x. x \<in> kf_domain \<FF>) \<FF>)\<close>
      by (auto intro!: kf_filter_cong intro: kf_eq_sym simp: kf_filter_to_domain)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r (kf_filter (\<lambda>_. False) \<FF>)\<close>
      using that by (simp add: kf_filter_twice * del: kf_filter_false)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r 0\<close>
      by (simp add: kf_filter_false)
    finally show ?thesis
      by (metis kf_apply_0 kf_eq_imp_eq_weak kf_eq_weak_def)
  qed

  show \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @({f} \<times> E) \<rho> =
    kf_comp_dependent \<EE>' \<FF>' *\<^sub>k\<^sub>r @({f} \<times> E') \<rho>\<close>
    apply (cases \<open>f \<in> kf_domain \<FF>\<close>)
    by (auto intro!: ext simp add: rewrite_comp[OF bdd] rewrite_comp[OF bdd']
        kf_comp_apply rew_\<EE> rew_\<FF> \<FF>_0)
qed


lemma kf_comp_dependent_cong:
  fixes \<EE> \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x \<equiv>\<^sub>k\<^sub>r \<EE>' x\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_comp_dependent \<EE>' \<FF>'\<close>
proof (rule kf_eqI)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  fix x :: \<open>'f \<times> 'e\<close>

  note bdd
  moreover have bdd': \<open>bdd_above ((kf_norm \<circ> \<EE>') ` kf_domain \<FF>')\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) image_cong kf_eq_imp_eq_weak kf_norm_cong kf_domain_cong o_apply)
  moreover have \<open>kf_apply_on (\<EE> xa) {snd x} = kf_apply_on (\<EE>' xa) {snd x}\<close> if \<open>xa \<in> kf_domain \<FF>\<close> for xa
    by (meson assms(2) kf_eq_def that)
  moreover have \<open>kf_apply_on \<FF> {fst x} = kf_apply_on \<FF>' {fst x}\<close>
    by (meson assms(3) kf_eq_def)
  ultimately have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({fst x} \<times> {snd x}) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({fst x} \<times> {snd x})\<close>
    by (rule kf_apply_comp_dependent_cong)
  then show \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = kf_comp_dependent \<EE>' \<FF>' *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by simp
qed


lemma kf_comp_cong:
  fixes \<EE> \<EE>' :: \<open>('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_comp \<EE>' \<FF>'\<close>
  by (auto intro!: kf_comp_dependent_cong assms
      simp add: kf_comp_def)

lemma kf_comp_dependent_cong_weak:
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e1) kraus_family\<close>
    and \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e2) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes eq: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x =\<^sub>k\<^sub>r \<EE>' x\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> =\<^sub>k\<^sub>r kf_comp_dependent \<EE>' \<FF>'\<close>
proof -
  have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>UNIV) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({f}\<times>UNIV)\<close> for f
  proof -
    note bdd
    moreover have \<open>bdd_above ((kf_norm \<circ> \<EE>') ` kf_domain \<FF>')\<close>
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) comp_apply image_cong kf_norm_cong kf_domain_cong)
    moreover have \<open>kf_apply_on (\<EE> x) UNIV = kf_apply_on (\<EE>' x) UNIV\<close> if \<open>x \<in> kf_domain \<FF>\<close> for x
      using assms(2) kf_eq_weak_def that
      by (metis kf_apply_on_UNIV)
    moreover have \<open>kf_apply_on \<FF> {f} = kf_apply_on \<FF>' {f}\<close>
      by (meson assms(3) kf_eq_def)
    ultimately show ?thesis
      by (rule kf_apply_comp_dependent_cong)
  qed
  then have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) (\<Union>f. {f}\<times>UNIV) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') (\<Union>f. {f}\<times>UNIV)\<close>
    apply (rule_tac ext)
    apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>f. ({f}\<times>UNIV,{f}\<times>UNIV))\<close>])
    by auto
  moreover have \<open>(\<Union>f. {f} \<times> UNIV) = UNIV\<close>
    by fast
  ultimately show ?thesis
    by (metis kf_eq_weak_def kf_apply_on_UNIV)
qed

lemma kf_bound_comp_dependent_raw_of_op:
  shows \<open>kf_bound (kf_comp_dependent_raw \<EE> (kf_of_op U))
       = sandwich (U*) (kf_bound (\<EE> ()))\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family (\<EE> ())\<close>

  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    by (simp add: EE_def kf_bound_summable)
  then have sum2: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E)) EE\<close>
    by (simp add: case_prod_unfold summable_on_in_wot_compose_left)

  have \<open>kf_bound (kf_comp_dependent_raw \<EE> (kf_of_op U)) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
          ((\<lambda>((F, y), (E, x)). ((E o\<^sub>C\<^sub>L F, F, E, y, x))) ` (SIGMA (F, y):{(U, ())}. EE))\<close>
    by (simp add: kf_bound.rep_eq kf_comp_dependent_raw.rep_eq kf_of_op.rep_eq EE_def)
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (E o\<^sub>C\<^sub>L U, U, E, (), x)) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (E o\<^sub>C\<^sub>L U)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L U)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L U) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = U* o\<^sub>C\<^sub>L infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE o\<^sub>C\<^sub>L U\<close>
    using sum1 sum2 by (simp add: case_prod_unfold infsum_in_wot_compose_right infsum_in_wot_compose_left)
  also have \<open>\<dots> = sandwich (U*) (kf_bound (\<EE> ()))\<close>
  by (simp add: EE_def kf_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed


lemma kf_bound_comp_dependent_of_op:
  shows \<open>kf_bound (kf_comp_dependent \<EE> (kf_of_op U)) = sandwich (U*) (kf_bound (\<EE> ()))\<close>
  by (simp add: kf_comp_dependent_def kf_map_bound kf_bound_comp_dependent_raw_of_op)

lemma kf_bound_comp_of_op:
  shows \<open>kf_bound (kf_comp \<EE> (kf_of_op U)) = sandwich (U*) (kf_bound \<EE>)\<close>
  by (simp add: kf_bound_comp_dependent_of_op kf_comp_def)

lemma kf_norm_comp_dependent_of_op_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kf_norm (kf_comp_dependent \<EE> (kf_of_op U)) = kf_norm (\<EE> ())\<close>
  using assms
  by (simp add: kf_bound_comp_dependent_of_op kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')

lemma kf_norm_comp_of_op_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kf_norm (kf_comp \<EE> (kf_of_op U)) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_of_op kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')

lemma kf_bound_comp_dependend_raw_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp_dependent_raw (\<lambda>_. kf_of_op U) \<EE>)
       = kf_bound \<EE>\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family \<EE>\<close>

  have \<open>bdd_above ((\<lambda>x. (norm U)\<^sup>2) ` kf_domain \<EE>)\<close>
    by auto
  then have \<open>kf_bound (kf_comp_dependent_raw (\<lambda>_. kf_of_op U) \<EE>) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
           ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, ())) ` (SIGMA (F, y):EE. {(U, ())}))\<close>
    by (simp add: kf_bound.rep_eq kf_comp_dependent_raw.rep_eq kf_of_op.rep_eq EE_def)
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (U o\<^sub>C\<^sub>L E, E, U, x, ())) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (U o\<^sub>C\<^sub>L E)* o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L E)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L (U* o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L E) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    using assms by simp
  also have \<open>\<dots> = kf_bound \<EE>\<close>
    by (simp add: EE_def kf_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed

lemma kf_bound_comp_dependent_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp_dependent (\<lambda>_. kf_of_op U) \<EE>) = kf_bound \<EE>\<close>
  using assms by (simp add: kf_comp_dependent_def kf_map_bound kf_bound_comp_dependend_raw_iso)

lemma kf_bound_comp_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp (kf_of_op U) \<EE>) = kf_bound \<EE>\<close>
  using assms by (simp add: kf_bound_comp_dependent_iso kf_comp_def)

lemma kf_norm_comp_dependent_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_norm (kf_comp_dependent (\<lambda>_. kf_of_op U) \<EE>) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_dependent_iso kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')

lemma kf_norm_comp_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_norm (kf_comp (kf_of_op U) \<EE>) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_iso kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')


lemma kf_comp_dependent_raw_0_right: \<open>kf_comp_dependent_raw E 0 =\<^sub>k\<^sub>r 0\<close>
  by (simp add: kf_eq_weakI kf_comp_dependent_raw.rep_eq kf_apply.rep_eq zero_kraus_family.rep_eq)

lemma kf_comp_dependent_raw_0_left: \<open>kf_comp_dependent_raw 0 E =\<^sub>k\<^sub>r 0\<close>
  by (smt (verit, ccfv_SIG) func_zero infsum_0 kf_eq_weakI kf_apply_0_left kf_comp_dependent_raw.abs_eq kf_comp_dependent_raw_apply split_def zero_kraus_family_def)

lemma kf_comp_dependent_0_left[simp]: \<open>kf_comp_dependent 0 E = 0\<close>
proof -
  have \<open>bdd_above ((kf_norm \<circ> 0) ` kf_domain E)\<close>
    by auto
  then have \<open>kf_comp_dependent 0 E =\<^sub>k\<^sub>r 0\<close>
    by (auto intro!: ext simp: kf_eq_weak_def kf_comp_dependent_apply split_def)
  then have \<open>kf_remove_0 (kf_comp_dependent 0 E) = 0\<close>
    using kf_eq_0_iff_kf_remove_0_is_0 by auto
  then show \<open>kf_comp_dependent 0 E = 0\<close>
    by (simp add: kf_comp_dependent_def kf_map_remove_0)
qed

lemma kf_comp_dependent_0_right[simp]: \<open>kf_comp_dependent E 0 = 0\<close>
proof -
  have \<open>kf_comp_dependent E 0 =\<^sub>k\<^sub>r 0\<close>
    by (smt (verit, del_insts) kf_comp_dependent_def kf_eq_weak_def kf_comp_dependent_raw_0_right kf_apply_map)
  then have \<open>kf_remove_0 (kf_comp_dependent E 0) = 0\<close>
    using kf_eq_0_iff_kf_remove_0_is_0 by auto
  then show \<open>kf_comp_dependent E 0 = 0\<close>
    by (simp add: kf_comp_dependent_def kf_map_remove_0)
qed


lemma kf_comp_0_left[simp]: \<open>kf_comp 0 E = 0\<close>
  using kf_comp_dependent_0_left[of E]
  by (simp add: kf_comp_def zero_fun_def)

lemma kf_comp_0_right[simp]: \<open>kf_comp E 0 = 0\<close>
  using kf_comp_dependent_0_right[of \<open>\<lambda>_. E\<close>]
  by (simp add: kf_comp_def)

lemma kf_filter_comp:
  fixes \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'e) kraus_family\<close>
  shows \<open>kf_filter (\<lambda>(e,f). F f \<and> E e) (kf_comp \<FF> \<EE>)
      = kf_comp (kf_filter F \<FF>) (kf_filter E \<EE>)\<close>
  unfolding kf_comp_def
  apply (rule kf_filter_comp_dependent)
  by auto

lemma kf_comp_dependent_invalid:
  assumes \<open>\<not> bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> = 0\<close>
  by (metis (no_types, lifting) Rep_kraus_family_inject assms kf_comp_dependent_def kf_comp_dependent_raw.rep_eq kf_map0 zero_kraus_family.rep_eq)

lemma kf_comp_dependent_map_left:
  \<open>kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F)\<close>
proof (cases \<open>bdd_above ((kf_norm \<circ> E) ` kf_domain F)\<close>)
  case True
  show ?thesis
  proof (rule kf_eqI)
    fix xy :: \<open>'c \<times> 'd\<close> and \<rho>
    obtain x y where xy: \<open>xy = (x, y)\<close>
      by force
    define F' where \<open>F' x = kf_filter (\<lambda>x'. x' = x) F\<close> for x
    define E'f where \<open>E'f y e = kf_filter (\<lambda>x. f e x = y) (E e)\<close> for e y
    have bdd2: \<open>bdd_above ((\<lambda>x. kf_norm (E'f y x)) ` kf_domain (F' x))\<close>
      apply (simp add: E'f_def F'_def)
      by fastforce
    have \<open>kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F *\<^sub>k\<^sub>r @{xy} \<rho>
        = kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x) (kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F) *\<^sub>k\<^sub>r \<rho>\<close>
      (is \<open>?lhs = _\<close>)
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>e. kf_filter (\<lambda>y'. y' = y)
         (kf_map (f e) (E e))) (F' x)) \<rho>\<close>
      using True by (simp add: kf_filter_comp_dependent F'_def)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent
                 (\<lambda>e. kf_map (f e) (E'f y e)) (F' x)) \<rho>\<close>
      by (simp add: kf_filter_map E'f_def)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (E'f y) (F' x)) \<rho>\<close>
      apply (rule kf_apply_eqI)
      apply (rule kf_comp_dependent_cong_weak)
      by (simp_all add: bdd2 kf_eq_weak_def)
    also have \<open>\<dots> = kf_apply 
       (kf_filter (\<lambda>(x',y'). f x' y' = y \<and> x' = x) (kf_comp_dependent E F)) \<rho>\<close>
      apply (subst kf_filter_comp_dependent)
      using True by (simp_all add: o_def F'_def E'f_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_map (\<lambda>(x,y). (x, f x y))
       (kf_filter (\<lambda>(x',y'). f x' y' = y \<and> x' = x) (kf_comp_dependent E F))) \<rho>\<close>
      by simp
    also have \<open>\<dots>
      = kf_apply (kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x)
       (kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F))) \<rho>\<close>
      by (simp add: kf_filter_map case_prod_unfold)
    also have \<open>\<dots> = kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F) *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    finally show \<open>?lhs = \<dots>\<close>
      by -
  qed
next
  case False
  then show ?thesis
    by (simp add: kf_comp_dependent_invalid)
qed

lemma kf_comp_dependent_map_right:
  \<open>kf_comp_dependent E (kf_map f F)
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F)\<close>
proof (cases \<open>bdd_above ((kf_norm \<circ> E) ` kf_domain (kf_map f F))\<close>)
  case True
  show ?thesis
  proof (rule kf_eqI)
    fix xy :: \<open>'c \<times> 'd\<close> and \<rho>
    obtain x y where xy: \<open>xy = (x, y)\<close>
      by force
    define F'f where \<open>F'f x = kf_filter (\<lambda>xa. f xa = x) F\<close> for x
    define E' where \<open>E' y e = kf_filter (\<lambda>y'. y' = y) (E e)\<close> for e y
    have bdd2: \<open>bdd_above ((kf_norm \<circ> E' y) ` kf_domain (kf_map f (F'f x)))\<close>
      apply (simp add: E'_def F'f_def)
      by fastforce
    have bdd3: \<open>bdd_above ((kf_norm \<circ> (\<lambda>x. E (f x))) ` kf_domain F)\<close>
      by (metis (no_types, lifting) ext True comp_apply image_comp kf_domain_map)
    have bdd4: \<open>bdd_above ((kf_norm \<circ> (\<lambda>_. E' y x)) ` kf_domain (F'f x))\<close>
      by fastforce                                   
    have \<open>kf_comp_dependent E (kf_map f F) *\<^sub>k\<^sub>r @{xy} \<rho>
        = kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x) (kf_comp_dependent E (kf_map f F)) *\<^sub>k\<^sub>r \<rho>\<close>
      (is \<open>?lhs = _\<close>)
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (E' y) (kf_filter (\<lambda>x'. x' = x) (kf_map f F))) \<rho>\<close>
      using True by (simp add: kf_filter_comp_dependent F'f_def E'_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_comp_dependent
                 (E' y) (kf_map f (F'f x))) \<rho>\<close>
      by (simp add: kf_filter_map F'f_def)
    also have \<open>\<dots> = kf_apply (kf_comp (E' y x) (kf_map f (F'f x))) \<rho>\<close>
      unfolding kf_comp_def
      apply (rule kf_apply_eqI)
      using bdd2 apply (rule kf_comp_dependent_cong_weak)
      by (auto simp: F'f_def)
    also have \<open>\<dots> = kf_apply (E' y x) (kf_apply (F'f x) \<rho>)\<close>
      by (simp add: kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp (E' y x) (F'f x)) \<rho>\<close>
      by (simp add: kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>e. kf_filter (\<lambda>y'. y' = y) (E (f e))) (F'f x)) \<rho>\<close>
      unfolding kf_comp_def
      apply (rule kf_apply_eqI)
      using bdd4 apply (rule kf_comp_dependent_cong_weak)
      by (auto intro!: simp: F'f_def E'_def)
    also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>(x',y'). y' = y \<and> f x' = x) (kf_comp_dependent (\<lambda>x. E (f x)) F)) \<rho>\<close>
      using bdd3 by (simp add: kf_filter_comp_dependent F'f_def[abs_def] E'_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x)
              (kf_map (\<lambda>(x, y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F))) \<rho>\<close>
      by (simp add: kf_filter_map case_prod_unfold)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F) *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)

    finally show \<open>?lhs = \<dots>\<close>
      by -
  qed
next
  case False
  have not_bdd2: \<open>\<not> bdd_above ((kf_norm \<circ> (\<lambda>x. E (f x))) ` kf_domain F)\<close>
    by (metis (no_types, lifting) False comp_apply image_comp image_cong kf_domain_map)
  show ?thesis
    using False not_bdd2
    by (simp add: kf_comp_dependent_invalid)
qed


lemma kf_comp_map_left:
  \<open>kf_comp (kf_map f E) F \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (x, f y)) (kf_comp E F)\<close>
  by (simp add: kf_comp_def kf_comp_dependent_map_left)

lemma kf_comp_map_right:
  \<open>kf_comp E (kf_map f F) \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (f x, y)) (kf_comp E F)\<close>
  using kf_comp_dependent_map_right[where E=\<open>\<lambda>_. E\<close> and f=f and F=F]
  by (simp add: kf_comp_def)

subsection \<open>Infinite sums\<close>

lift_definition kf_infsum :: \<open>('a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family) \<Rightarrow> 'a set \<Rightarrow> ('b,'c,'a\<times>'x) kraus_family\<close> is
  \<open>\<lambda>\<EE> A. if summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A
         then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A (\<lambda>a. Rep_kraus_family (\<EE> a)) else {}\<close>
proof (rule CollectI, rename_tac \<EE> A)
  fix \<EE> :: \<open>'a \<Rightarrow> ('b, 'c, 'x) kraus_family\<close> and A
  define \<EE>' where \<open>\<EE>' a = Rep_kraus_family (\<EE> a)\<close> for a
  show \<open>kraus_family (if summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A 
                      then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A \<EE>'
                      else {})\<close>
  proof (cases \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>)
    case True
    have \<open>kraus_family ((\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>')\<close>
    proof (intro kraus_familyI bdd_aboveI)
      fix C assume \<open>C \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'}\<close>
      then obtain F where \<open>finite F\<close> and F_subset: \<open>F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'\<close>
        and C_def: \<open>C = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by blast
      define B F' where \<open>B = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
        and \<open>F' = (\<lambda>(E,a,x). (a,E,x)) ` F\<close>

      have [iff]: \<open>finite F'\<close>
        using \<open>finite F\<close> by (auto intro!: simp: F'_def)
      have F'_subset: \<open>F' \<subseteq> Sigma A \<EE>'\<close>
        using F_subset by (auto simp: F'_def)
      have Sigma_decomp: \<open>(SIGMA a:(\<lambda>x. fst x) ` F'. snd ` Set.filter (\<lambda>(a',Ex). a'=a) F') = F'\<close>
        by force

      have \<open>C = (\<Sum>(a, (E, x))\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
        unfolding F'_def
        apply (subst sum.reindex)
        by (auto intro!: inj_onI simp: C_def case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. \<Sum>(E, x)\<in>snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'. E* o\<^sub>C\<^sub>L E)\<close>
        apply (subst sum.Sigma)
        by (auto intro!: finite_imageI simp: Sigma_decomp)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'))\<close>
        apply (rule sum.cong[OF refl])
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a))\<close>
      proof (rule sum_mono, rule infsum_mono_neutral_wot)
        fix a assume \<open>a \<in> fst ` F'\<close>
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a', Ex). a' = a) F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a)\<close>
          using \<EE>'_def[abs_def] kf_bound_has_sum summable_on_in_def by blast
        show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by blast
        have \<open>snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' \<le> \<EE>' a\<close>
          using F'_subset by auto
        then show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
          if \<open>Ex \<in> snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' - \<EE>' a\<close> for Ex
          using that by blast
        show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. kf_bound (\<EE> a))\<close>
        unfolding \<EE>'_def
        apply (transfer' fixing: F')
        by simp
      also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) (fst ` F')\<close>
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
      proof (rule infsum_mono_neutral_wot)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) (fst ` F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
          using True by blast
        show \<open>kf_bound (\<EE> a) \<le> kf_bound (\<EE> a)\<close> for a
          by blast
        show \<open>kf_bound (\<EE> a) \<le> 0\<close> if \<open>a \<in> fst ` F' - A\<close> for a
          using F'_subset that by auto
        show \<open>0 \<le> kf_bound (\<EE> a)\<close> for a
          by simp
      qed
      also have \<open>\<dots> = B\<close>
        using B_def by blast
      finally show \<open>C \<le> B\<close>
        by -
    qed
    with True show ?thesis 
      by simp
  next
    case False
    then show ?thesis
      by (auto intro!: bdd_aboveI simp add: kraus_family_def)
  qed
qed

definition kf_summable :: \<open>('a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>kf_summable \<EE> A \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>

lemma kf_summable_from_abs_summable:
  assumes sum: \<open>(\<lambda>a. kf_norm (\<EE> a)) summable_on A\<close>
  shows \<open>kf_summable \<EE> A\<close>
  using assms
  by (simp add: summable_imp_wot_summable abs_summable_summable kf_summable_def kf_norm_def)

lemma kf_infsum_apply:
  assumes \<open>kf_summable \<EE> A\<close>
  shows \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a *\<^sub>k\<^sub>r \<rho>)\<close>
proof -
  from kf_apply_summable[of \<rho> \<open>kf_infsum \<EE> A\<close>]
  have summable: \<open>(\<lambda>(a, E, x). sandwich_tc E \<rho>) summable_on (SIGMA a:A. Rep_kraus_family (\<EE> a))\<close>
    using assms
    by (simp add: kf_summable_def kf_infsum.rep_eq case_prod_unfold summable_on_reindex inj_on_def prod.expand o_def)
  have \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>(E,ax)\<in>(\<lambda>(a, E, x) \<Rightarrow> (E, a, x)) ` (SIGMA a:A. Rep_kraus_family (\<EE> a)). sandwich_tc E \<rho>)\<close>
    using assms unfolding kf_summable_def
    apply (transfer' fixing: \<EE>)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(a, E, x) \<in> (SIGMA a:A. Rep_kraus_family (\<EE> a)). sandwich_tc E \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<Sum>\<^sub>\<infinity>(E, b)\<in>Rep_kraus_family (\<EE> a). sandwich_tc E \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using summable by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a *\<^sub>k\<^sub>r \<rho>)\<close>
    by (metis (no_types, lifting) infsum_cong kf_apply.rep_eq split_def)
  finally show ?thesis
    by -
qed


lemma kf_bound_infsum:
  fixes f :: \<open>'a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family\<close>
  assumes \<open>kf_summable f A\<close>
  shows \<open>kf_bound (kf_infsum f A) = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (f a)) A\<close>
proof -
  have pos: \<open>0 \<le> compose_wot (adj_wot a) a\<close> for a :: \<open>('b,'c) cblinfun_wot\<close>
    apply transfer'
    using positive_cblinfun_squareI by blast
  have sum3: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family (f x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on A\<close>
  proof -
    define b where \<open>b x = kf_bound (f x)\<close> for x
    have \<open>(\<lambda>x. Abs_cblinfun_wot (b x)) summable_on A\<close>
      using assms unfolding kf_summable_def
      apply (subst (asm) b_def[symmetric])
      apply (transfer' fixing: b A)
      by simp
    then show ?thesis
      by (simp add: Rep_cblinfun_wot_inverse kf_bound_def' b_def)
  qed
  have sum2: \<open>(\<lambda>(E, _). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
         Rep_kraus_family (f x)\<close> if \<open>x \<in> A\<close> for x
    by (rule kf_bound_summable')
  have sum1: \<open>(\<lambda>(_, E, _). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
    (SIGMA a:A. Rep_kraus_family (f a))\<close>
    apply (rule summable_on_Sigma_wotI)
    using sum3 sum2
    by (auto intro!: pos simp: case_prod_unfold)

  have \<open>Abs_cblinfun_wot (kf_bound (kf_infsum f A)) =
        (\<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (kf_infsum f A).
               compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>(\<lambda>(a, E, xa). (E, a, xa)) ` (SIGMA a:A. Rep_kraus_family (f a)).
       compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    using assms by (simp add: kf_infsum.rep_eq kf_summable_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(a, E, x)\<in>(SIGMA a:A. Rep_kraus_family (f a)). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (f a). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_Sigma_topological_monoid)
    using sum1 sum2 by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. Abs_cblinfun_wot (kf_bound (f a)))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = Abs_cblinfun_wot (infsum_in cweak_operator_topology (\<lambda>a. kf_bound (f a)) A)\<close>
    apply (simp only: infsum_euclidean_eq[symmetric])
    apply (transfer' fixing: f A)
    by simp
  finally show ?thesis
    apply (rule Abs_cblinfun_wot_inject[THEN iffD1, rotated -1])
    by simp_all
qed

lemma kf_norm_infsum:
  assumes sum: \<open>(\<lambda>a. kf_norm (\<EE> a)) summable_on A\<close>
  shows \<open>kf_norm (kf_infsum \<EE> A) \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. kf_norm (\<EE> a))\<close>
proof -
  have \<open>kf_norm (kf_infsum \<EE> A) = norm (infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A)\<close>
    unfolding kf_norm_def
    apply (subst kf_bound_infsum)
    by (simp_all add: kf_summable_from_abs_summable assms)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. norm (kf_bound (\<EE> a)))\<close>
    apply (rule triangle_ineq_wot)
    using sum by (simp add: kf_norm_def)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. kf_norm (\<EE> a))\<close>
    by (smt (verit, del_insts) infsum_cong kf_norm_def)
  finally show ?thesis
    by -
qed

lemma kf_filter_infsum:
  assumes \<open>kf_summable \<EE> A\<close>
  shows \<open>kf_filter P (kf_infsum \<EE> A) 
           = kf_infsum (\<lambda>a. kf_filter (\<lambda>x. P (a,x)) (\<EE> a)) {a\<in>A. \<exists>x. P (a,x)}\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof -
  have summ: \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a)))
      {a \<in> A. \<exists>x. P (a, x)}\<close>
  proof (rule summable_wot_boundedI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> {a \<in> A. \<exists>x. P (a, x)}\<close>
    have \<open>(\<Sum>a\<in>F. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a)))
        \<le> (\<Sum>a\<in>F. kf_bound (\<EE> a))\<close>
      by (meson kf_bound_filter sum_mono)
    also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) F\<close>
      apply (rule infsum_in_finite[symmetric])
      by (auto intro!: \<open>finite F\<close>)
    also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
      apply (rule infsum_mono_neutral_wot)
      using F_subset assms
      by (auto intro!: \<open>finite F\<close> intro: summable_on_in_finite simp: kf_summable_def)
    finally show \<open>(\<Sum>a\<in>F. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a))) \<le> \<dots>\<close>
      by -
  next
    show \<open>0 \<le> kf_bound (kf_filter (\<lambda>y. P (x, y)) (\<EE> x))\<close> for x
      by simp
  qed
  have \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    using assms by (force simp add: kf_filter.rep_eq kf_infsum.rep_eq assms summ kf_summable_def)
  then show \<open>?lhs = ?rhs\<close>
    by (simp add: Rep_kraus_family_inject)
qed

lemma kf_infsum_empty[simp]: \<open>kf_infsum \<EE> {} = 0\<close>
  apply transfer' by simp

lemma kf_infsum_singleton[simp]: \<open>kf_infsum \<EE> {a} = kf_map_inj (\<lambda>x. (a,x)) (\<EE> a)\<close>
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  by (force simp add: kf_infsum.rep_eq summable_on_in_finite kf_map_inj.rep_eq)

lemma kf_infsum_invalid: 
  assumes \<open>\<not> kf_summable \<EE> A\<close>
  shows \<open>kf_infsum \<EE> A = 0\<close>
  using assms
  apply transfer'
  unfolding kf_summable_def
  by simp


lemma kf_infsum_cong:
  fixes \<EE> \<FF> :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'x) kraus_family\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> \<EE> a \<equiv>\<^sub>k\<^sub>r \<FF> a\<close>
  shows \<open>kf_infsum \<EE> A \<equiv>\<^sub>k\<^sub>r kf_infsum \<FF> A\<close>
proof (cases \<open>kf_summable \<EE> A\<close>)
  case True
  then have True': \<open>kf_summable \<FF> A\<close>
    unfolding kf_summable_def
    apply (rule summable_on_in_cong[THEN iffD1, rotated])
    by (simp add: kf_bound_cong assms kf_eq_imp_eq_weak)
  show ?thesis
  proof (rule kf_eqI)
    fix ax :: \<open>'a \<times> 'x\<close> and \<rho>
    obtain a x where ax_def: \<open>ax = (a,x)\<close>
      by fastforce
    have *: \<open>{a'. a' = a \<and> a' \<in> A} = (if a\<in>A then {a} else {})\<close>
      by auto
    have \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r @{ax} \<rho> = (if a\<in>A then \<EE> a *\<^sub>k\<^sub>r @{x} \<rho> else 0)\<close>
      by (simp add: ax_def kf_apply_on_def True kf_filter_infsum * 
          kf_apply_map_inj inj_on_def)
    also from assms have \<open>\<dots> = (if a\<in>A then \<FF> a *\<^sub>k\<^sub>r @{x} \<rho> else 0)\<close>
      by (auto intro!: kf_apply_on_eqI)
    also have \<open>\<dots> = kf_infsum \<FF> A *\<^sub>k\<^sub>r @{ax} \<rho>\<close>
      by (simp add: ax_def kf_apply_on_def True' kf_filter_infsum * 
          kf_apply_map_inj inj_on_def)
    finally show \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r @{ax} \<rho> = kf_infsum \<FF> A *\<^sub>k\<^sub>r @{ax} \<rho>\<close>
      by -
  qed
next
  case False
  then have False': \<open>\<not> kf_summable \<FF> A\<close>
    unfolding kf_summable_def
    apply (subst (asm) assms[THEN kf_eq_imp_eq_weak, 
          THEN kf_bound_cong, THEN summable_on_in_cong])
    by auto
  show ?thesis
    by (simp add: kf_infsum_invalid False False')
qed

subsection \<open>Trace-preserving maps\<close>

definition \<open>kf_trace_preserving \<EE> \<longleftrightarrow> (\<forall>\<rho>. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>)\<close>

definition \<open>kf_trace_reducing \<EE> \<longleftrightarrow> (\<forall>\<rho>\<ge>0. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>)\<close>

lemma kf_trace_reducing_iff_norm_leq1: \<open>kf_trace_reducing \<EE> \<longleftrightarrow> kf_norm \<EE> \<le> 1\<close>
proof (unfold kf_trace_reducing_def, intro iffI allI impI)
  assume assm: \<open>kf_norm \<EE> \<le> 1\<close>
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  assume \<open>\<rho> \<ge> 0\<close>
  have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = norm (\<EE> *\<^sub>k\<^sub>r \<rho>)\<close>
    by (simp add: \<open>0 \<le> \<rho>\<close> kf_apply_pos norm_tc_pos)
  also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
    using \<open>0 \<le> \<rho>\<close> complex_of_real_mono kf_apply_bounded_pos by blast
  also have \<open>\<dots> \<le> norm \<rho>\<close>
    by (metis assm complex_of_real_mono kf_norm_geq0 mult_left_le_one_le norm_ge_zero)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    by (simp add: \<open>0 \<le> \<rho>\<close> norm_tc_pos)
  finally show \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>\<close>
    by -
next
  assume assm[rule_format]: \<open>\<forall>\<rho>\<ge>0. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>\<close>
  have \<open>kf_bound \<EE> \<le> id_cblinfun\<close>
  proof (rule cblinfun_leI)
    fix x
    have \<open>x \<bullet>\<^sub>C kf_bound \<EE> x = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly x x)\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> \<le> trace_tc (tc_butterfly x x)\<close>
      apply (rule assm)
      by simp
    also have \<open>\<dots> = x \<bullet>\<^sub>C id_cblinfun x\<close>
      by (simp add: tc_butterfly.rep_eq trace_butterfly trace_tc.rep_eq)
  finally show \<open>x \<bullet>\<^sub>C kf_bound \<EE> x \<le> x \<bullet>\<^sub>C id_cblinfun x\<close>
      by -
  qed
  then show \<open>kf_norm \<EE> \<le> 1\<close>
    by (smt (verit, best) kf_norm_def kf_bound_pos norm_cblinfun_id_le norm_cblinfun_mono)
qed

lemma kf_trace_preserving_iff_bound_id: \<open>kf_trace_preserving \<EE> \<longleftrightarrow> kf_bound \<EE> = id_cblinfun\<close>
proof (unfold kf_trace_preserving_def, intro iffI allI)
  assume asm[rule_format]: \<open>\<forall>\<rho>. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi> = \<psi> \<bullet>\<^sub>C id_cblinfun \<psi>\<close> for \<psi>
  proof -
    have \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi> = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> = trace_tc (tc_butterfly \<psi> \<psi>)\<close>
      by (simp add: asm)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C id_cblinfun \<psi>\<close>
      by (simp add: tc_butterfly.rep_eq trace_butterfly trace_tc.rep_eq)
    finally show ?thesis
      by -
  qed
  then show \<open>kf_bound \<EE> = id_cblinfun\<close>
    using cblinfun_cinner_eq0I[where a=\<open>kf_bound \<EE> - id_cblinfun\<close>]
    by (simp add: cblinfun.real.diff_left cinner_diff_right)
next
  assume asm: \<open>kf_bound \<EE> = id_cblinfun\<close>
  fix \<rho>
  have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc (compose_tcr (kf_bound \<EE>) \<rho>)\<close>
    by (rule trace_from_kf_bound)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    using asm by fastforce
  finally show \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>\<close>
    by -
qed

lemma kf_trace_norm_preserving: \<open>kf_norm \<EE> \<le> 1\<close> if \<open>kf_trace_preserving \<EE>\<close>
  apply (rule kf_trace_reducing_iff_norm_leq1[THEN iffD1])
  using that
  by (simp add: kf_trace_preserving_def kf_trace_reducing_def)

lemma kf_trace_norm_preserving_eq: 
  fixes \<EE> :: \<open>('a::{chilbert_space,not_singleton}, 'b::chilbert_space, 'c) kraus_family\<close>
  assumes \<open>kf_trace_preserving \<EE>\<close>
  shows \<open>kf_norm \<EE> = 1\<close>
  using assms by (simp add: kf_trace_preserving_iff_bound_id kf_norm_def)

subsection \<open>Sampling\<close>

lift_definition kf_sample :: \<open>('x \<Rightarrow> real) \<Rightarrow> ('a::chilbert_space, 'a, 'x) kraus_family\<close> is
  \<open>\<lambda>p. if (\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV then range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)) else {}\<close>
proof -
  fix p :: \<open>'x \<Rightarrow> real\<close>
  show \<open>?thesis p\<close>
  proof (cases \<open>(\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV\<close>)
    case True
    then have \<open>p abs_summable_on UNIV\<close>
      by simp
    from abs_summable_iff_bdd_above[THEN iffD1, OF this]
    obtain B where F_B: \<open>finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> for F
      apply atomize_elim
      using True by (auto simp: bdd_above_def)
    have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
      if \<open>finite F\<close> and \<open>F \<subseteq> range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))\<close>
      for F :: \<open>('a\<Rightarrow>\<^sub>C\<^sub>L'a \<times> 'x) set\<close>
    proof -
      from that
      obtain F' where \<open>finite F'\<close> and F_def: \<open>F = (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)) ` F'\<close>
        using finite_subset_image
        by meson
      then have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>F'. (sqrt (p x) *\<^sub>R id_cblinfun)* o\<^sub>C\<^sub>L (sqrt (p x) *\<^sub>R id_cblinfun))\<close>
        by (simp add: sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x *\<^sub>R id_cblinfun)\<close>
        using True by simp
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x) *\<^sub>R id_cblinfun\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> \<le> B *\<^sub>R id_cblinfun\<close>
        using \<open>\<And>F. finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> \<open>finite F'\<close> positive_id_cblinfun scaleR_right_mono by blast
      finally show ?thesis
        by -
    qed
    then have \<open>kraus_family (range (\<lambda>x. (sqrt (p x) *\<^sub>R (id_cblinfun ::'a\<Rightarrow>\<^sub>C\<^sub>L_), x)))\<close>
      by (auto intro!: bdd_aboveI[where M=\<open>B *\<^sub>R id_cblinfun\<close>] simp: kraus_family_def case_prod_unfold)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma kf_sample_norm:
  fixes p :: \<open>'x \<Rightarrow> real\<close>
  assumes \<open>\<And>x. p x \<ge> 0\<close>
  assumes \<open>p summable_on UNIV\<close>
  shows \<open>kf_norm (kf_sample p :: ('a::{chilbert_space,not_singleton},'a,'x) kraus_family)
             = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
proof -
  define B :: \<open>'a\<Rightarrow>\<^sub>C\<^sub>L'a\<close> where \<open>B = kf_bound (kf_sample p)\<close>
  obtain \<psi> :: 'a where \<open>norm \<psi> = 1\<close>
    using ex_norm1_not_singleton by blast

  have \<open>\<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun *\<^sub>V \<psi>)\<close> 
    if \<open>norm \<psi> = 1\<close> for \<psi>
  proof -
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_sample p)) B\<close>
      using B_def kf_bound_has_sum by blast
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))) B\<close>
      by (simp add: kf_sample.rep_eq assms)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. norm (p x) *\<^sub>R id_cblinfun) UNIV B\<close>
      by (simp add: has_sum_in_reindex inj_on_def o_def)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. p x *\<^sub>R id_cblinfun) UNIV B\<close>
      apply (rule has_sum_in_cong[THEN iffD1, rotated])
      by (simp add: assms(1))
    then have \<open>has_sum_in euclidean (\<lambda>x. \<psi> \<bullet>\<^sub>C (p x *\<^sub>R id_cblinfun) \<psi>) UNIV (\<psi> \<bullet>\<^sub>C B \<psi>)\<close>
      apply (rule has_sum_in_comm_additive[rotated 3, OF cweak_operator_topology_cinner_continuous, unfolded o_def])
      by (simp_all add: Modules.additive_def cblinfun.add_left cinner_simps)
    then have \<open>((\<lambda>x. of_real (p x)) has_sum (\<psi> \<bullet>\<^sub>C B \<psi>)) UNIV\<close>
      apply (simp add: scaleR_scaleC has_sum_euclidean_iff)
      using \<open>norm \<psi> = 1\<close> cnorm_eq_1 by force
    then have \<open>\<psi> \<bullet>\<^sub>C B \<psi> = (\<Sum>\<^sub>\<infinity>x. of_real (p x))\<close>
      by (simp add: infsumI)
    also have \<open>\<dots> = of_real (\<Sum>\<^sub>\<infinity>x. p x)\<close>
      by (metis infsum_of_real)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun) \<psi>\<close>
      using \<open>norm \<psi> = 1\<close> by (simp add: scaleR_scaleC cnorm_eq_1)
    finally show ?thesis
      by -
  qed
  then have \<open>B = (\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun\<close>
    by (rule cblinfun_cinner_eqI)
  then have \<open>norm B = norm (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by (simp add: abs_of_nonneg assms infsum_nonneg)
  finally show ?thesis
    by (simp add: kf_norm_def B_def)
qed

subsection \<open>Trace\<close>

lift_definition kf_trace :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'b::one_dim, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_onb B then (\<lambda>x. (vector_to_cblinfun x*, x)) ` B else {}\<close>
proof (rename_tac B)
  fix B :: \<open>'a set\<close>
  define family :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close> where \<open>family = (\<lambda>x. (vector_to_cblinfun x*, x)) ` B\<close>
  have \<open>kraus_family family\<close> if \<open>is_onb B\<close>
  proof -
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close> if \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close>
    proof -
      obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (vector_to_cblinfun x*, x)) ` G\<close>
        apply atomize_elim
        using \<open>finite F\<close> and FB
        apply (simp add: family_def)
        by (meson finite_subset_image)
      from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
        by (meson \<open>is_onb B\<close> is_onb_def is_ortho_set_antimono)
      from \<open>G \<subseteq> B\<close> have [simp]: \<open>e \<in> G \<Longrightarrow> norm e = 1\<close> for e
        by (meson Set.basic_monos(7) \<open>is_onb B\<close> is_onb_def)
      have [simp]: \<open>inj_on (\<lambda>x. (vector_to_cblinfun x*, x)) G\<close>
        by (meson inj_onI prod.inject)
      have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter x)\<close>
        by (simp add: FG sum.reindex flip: butterfly_def_one_dim)
      also have \<open>(\<Sum>x\<in>G. selfbutter x) \<le> id_cblinfun\<close>
        apply (rule sum_butterfly_leq_id)
        by auto
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)
  qed
  then
  show \<open>(if is_onb B then family else {}) \<in> Collect kraus_family\<close>
    by auto
qed

lemma kf_trace_is_trace: 
  assumes \<open>is_onb B\<close>
  shows \<open>kf_trace B *\<^sub>k\<^sub>r \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
proof -
  define \<rho>' where \<open>\<rho>' = from_trace_class \<rho>\<close>
  have \<open>kf_apply (kf_trace B) \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (vector_to_cblinfun x*) \<rho>)\<close>
    apply (simp add: kf_apply.rep_eq kf_trace.rep_eq assms)
    apply (subst infsum_reindex)
     apply (meson inj_onI prod.simps(1))
    by (simp add: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. one_dim_iso (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    apply (intro infsum_cong from_trace_class_inject[THEN iffD1])
    apply (subst from_trace_class_sandwich_tc)
    by (simp add: sandwich_apply flip: \<rho>'_def)
  also have \<open>\<dots> = one_dim_iso (\<Sum>\<^sub>\<infinity>x\<in>B. (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    by (metis (mono_tags, lifting) \<rho>'_def infsum_cblinfun_apply infsum_cong assms one_cblinfun.rep_eq trace_class_from_trace_class trace_exists)
  also have \<open>\<dots> = one_dim_iso (trace \<rho>')\<close>
    by (metis \<rho>'_def trace_class_from_trace_class trace_alt_def[OF assms])
  also have \<open>\<dots> = one_dim_iso (trace_tc \<rho>)\<close>
    by (simp add: \<rho>'_def trace_tc.rep_eq)
  finally show ?thesis
    by -
qed

lemma kf_eq_weak_kf_trace:
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>kf_trace A =\<^sub>k\<^sub>r kf_trace B\<close>
  by (auto simp: kf_eq_weak_def kf_trace_is_trace assms)

lemma trace_is_kf_trace:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_tc t = one_dim_iso (kf_trace B *\<^sub>k\<^sub>r t)\<close>
  by (simp add: kf_trace_is_trace assms)

lemma kf_trace_bound[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_bound (kf_trace B) = id_cblinfun\<close>
  using assms
  apply (auto intro!: cblinfun_cinner_eqI simp: kf_bound_from_map kf_trace_is_trace)
  by (metis cinner_complex_def cnorm_eq_1 complex_cnj_one norm_tc_butterfly norm_tc_pos of_real_1 of_real_mult one_cinner_one tc_butterfly_pos)

lemma kf_trace_norm_eq1[simp]:
  fixes B :: \<open>'a::{chilbert_space, not_singleton} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_trace B) = 1\<close>
  using assms by (simp add: kf_trace_bound kf_norm_def)

lemma kf_trace_norm_leq1[simp]:
  fixes B :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_trace B) \<le> 1\<close>
  by (simp add: assms kf_norm_def norm_cblinfun_id_le)

subsection \<open>Constant maps\<close>


lift_definition kf_constant_onedim :: \<open>('b,'b) trace_class \<Rightarrow> ('a::one_dim, 'b::chilbert_space, unit) kraus_family\<close> is
  \<open>\<lambda>t::('b,'b) trace_class. if t \<ge> 0 then
    (\<lambda>v. (vector_to_cblinfun v,())) ` spectral_dec_vecs_tc t
  else {}\<close>
proof (rule CollectI, rename_tac t)
  fix t :: \<open>('b,'b) trace_class\<close>
  show \<open>kraus_family (if t \<ge> 0 then (\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t else {})\<close>
  proof (cases \<open>t \<ge> 0\<close>)
    case True
    have \<open>kraus_family ((\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t)\<close>
    proof (intro kraus_familyI bdd_aboveI, rename_tac E)
      fix E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>E \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t}\<close>
      then obtain F where E_def: \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> and \<open>finite F\<close> and \<open>F \<subseteq> (\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t\<close>
        by blast
      then obtain F' where F_def: \<open>F = (\<lambda>v. (vector_to_cblinfun v, ())) ` F'\<close> and \<open>finite F'\<close> and F'_subset: \<open>F' \<subseteq> spectral_dec_vecs_tc t\<close>
        by (meson finite_subset_image)
      have inj: \<open>inj_on (\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ())) F'\<close>
      proof (rule inj_onI, rule ccontr)
        fix x y
        assume \<open>x \<in> F'\<close> and \<open>y \<in> F'\<close>
        assume eq: \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ()) = (vector_to_cblinfun y, ())\<close>
        assume \<open>x \<noteq> y\<close>
        have ortho: \<open>is_ortho_set (spectral_dec_vecs (from_trace_class t))\<close>
          using True
          by (auto intro!: spectral_dec_vecs_ortho trace_class_compact pos_selfadjoint
              simp: selfadjoint_tc.rep_eq from_trace_class_pos)
        with \<open>x \<noteq> y\<close> F'_subset \<open>x \<in> F'\<close> \<open>y \<in> F'\<close>
        have \<open>x \<bullet>\<^sub>C y = 0\<close>
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
        then have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L (vector_to_cblinfun y :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) = 0\<close>
          by simp
        with eq have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)= 0\<close>
          by force
        then have \<open>norm x = 0\<close>
          by (smt (verit, del_insts) norm_vector_to_cblinfun norm_zero)
        with ortho F'_subset \<open>x \<in> F'\<close> show False
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
      qed
      have \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by (simp add: E_def)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L vector_to_cblinfun v)\<close>
        unfolding F_def
        apply (subst sum.reindex)
        by (auto intro!: inj)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. ((norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1)\<close>
        by (auto intro!: sum.cong simp: power2_norm_eq_cinner scaleR_scaleC)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        using \<open>finite F'\<close> by force
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        apply (intro scaleR_right_mono infsum_mono_neutral)
        using F'_subset
        by (auto intro!: one_dim_cblinfun_one_pos spectral_dec_vec_tc_norm_summable True
            simp: \<open>finite F'\<close> )
      finally show \<open>E \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by -
    qed
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

definition kf_constant :: \<open>('b,'b) trace_class \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, unit) kraus_family\<close> where
  \<open>kf_constant \<rho> = kf_flatten (kf_comp (kf_constant_onedim \<rho> :: (complex,_,_) kraus_family) (kf_trace some_chilbert_basis))\<close>

lemma kf_constant_onedim_invalid: \<open>\<not> \<rho> \<ge> 0 \<Longrightarrow> kf_constant_onedim \<rho> = 0\<close>
  apply transfer'
  by simp

lemma kf_constant_invalid: \<open>\<not> \<rho> \<ge> 0 \<Longrightarrow> kf_constant \<rho> = 0\<close>
  by (simp add: kf_constant_def kf_constant_onedim_invalid)

lemma kf_constant_onedim_apply: 
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply (kf_constant_onedim \<rho>) \<sigma> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
proof -
  have \<open>kf_apply (kf_constant_onedim \<rho>) \<sigma>
         = (\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc \<rho>. sandwich_tc E \<sigma>)\<close>
    by (simp add: assms kf_apply.rep_eq kf_constant_onedim.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. sandwich_tc (vector_to_cblinfun v) \<sigma>)\<close>
    apply (subst infsum_reindex)
    using vector_to_cblinfun_inj[of UNIV]
    by (auto simp: o_def inj_on_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. one_dim_iso \<sigma> *\<^sub>C tc_butterfly v v)\<close>
    apply (rule infsum_cong)
    apply (subst one_dim_scaleC_1[symmetric])
    apply (rule from_trace_class_inject[THEN iffD1])
    apply (simp only: sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq scaleC_trace_class.rep_eq
        tc_butterfly.rep_eq cblinfun_compose_scaleC_right cblinfun_compose_scaleC_left)
    by (simp flip: butterfly_def_one_dim)
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. tc_butterfly v v)\<close>
    using infsum_scaleC_right by fastforce
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
    by (simp add: assms butterfly_spectral_dec_vec_tc_has_sum infsumI)
  finally show ?thesis
    by -
qed

lemma kf_constant_apply: 
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply (kf_constant \<rho>) \<sigma> = trace_tc \<sigma> *\<^sub>C \<rho>\<close>
  using assms by (simp add: kf_constant_def kf_comp_apply kf_trace_is_trace kf_constant_onedim_apply)

lemma kf_bound_constant_onedim[simp]: 
  fixes \<rho> :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_constant_onedim \<rho>) = norm \<rho> *\<^sub>R id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: 'b assume \<open>norm \<psi> = 1\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_constant_onedim \<rho>) \<psi> = trace_tc (kf_apply (kf_constant_onedim \<rho>) (tc_butterfly \<psi> \<psi>))\<close>
    by (rule kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (trace_tc (tc_butterfly \<psi> \<psi>) *\<^sub>C \<rho>)\<close>
    by (simp add: kf_constant_onedim_apply assms)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cinner_complex_def complex_cnj_one complex_vector.vector_space_assms(4) norm_mult norm_one norm_tc_butterfly norm_tc_pos of_real_hom.hom_one one_cinner_one tc_butterfly_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (trace_tc \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cblinfun.scaleC_left cinner_scaleC_right cnorm_eq_1 id_apply id_cblinfun.rep_eq of_complex_def one_dim_iso_id one_dim_iso_is_of_complex scaleC_conv_of_complex)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>R id_cblinfun) \<psi>\<close>
    by (simp add: assms norm_tc_pos scaleR_scaleC)
  finally show \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_constant_onedim \<rho>) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>R id_cblinfun) \<psi>\<close>
    by -
qed

lemma kf_bound_constant[simp]: 
  fixes \<rho> :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_constant \<rho>) = norm \<rho> *\<^sub>R id_cblinfun\<close>
  apply (rule cblinfun_cinner_eqI)
  using assms
  by (simp add: kf_bound_from_map kf_constant_apply trace_tc_butterfly norm_tc_pos scaleR_scaleC trace_tc_scaleC)
  
lemma kf_norm_constant_onedim[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_constant_onedim \<rho>) = norm \<rho>\<close>
  using assms
  by (simp add: kf_bound_constant kf_norm_def)

lemma kf_norm_constant:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_constant \<rho> :: ('a::{chilbert_space,not_singleton},'b::chilbert_space,_) kraus_family) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def norm_cblinfun_id)

lemma kf_norm_constant_leq:
  shows \<open>kf_norm (kf_constant \<rho>) \<le> norm \<rho>\<close>
  apply (cases \<open>\<rho> \<ge> 0\<close>)
   apply (simp add: kf_norm_def)
   apply (metis Groups.mult_ac(2) mult_cancel_right1 mult_left_mono norm_cblinfun_id_le norm_ge_zero)
  by (simp add: kf_constant_invalid)

subsection \<open>Tensor products\<close>

lemma kf_tensor_raw_bound_aux:
  fixes \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<EE> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<FF> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> C\<close>
  assumes \<open>finite U\<close>
  assumes \<open>U \<subseteq> ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  shows \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close>
proof -
  from assms(1)[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
    by simp
  define f :: \<open>(('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) \<times> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y)) \<Rightarrow> _\<close>
    where \<open>f = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y)))\<close>
  from assms
  obtain V where V_subset: \<open>V \<subseteq> \<EE> \<times> \<FF>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close>
    apply (simp flip: f_def)
    by (meson finite_subset_image)
  define W where \<open>W = fst ` V \<times> snd ` V\<close>
  have \<open>inj_on f W\<close>
    by (auto intro!: inj_onI simp: f_def)
  from \<open>finite V\<close> have [simp]: \<open>finite W\<close>
    using W_def by blast
  have \<open>W \<supseteq> V\<close>
    by (auto intro!: image_eqI simp: W_def)
  have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> (\<Sum>(G, z)\<in>f ` W. G* o\<^sub>C\<^sub>L G)\<close>
    using \<open>U = f ` V\<close> \<open>V \<subseteq> W\<close>
    by (auto intro!: sum_mono2 positive_cblinfun_squareI)
  also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))\<close>
    apply (subst sum.reindex)
    using \<open>inj_on f W\<close>
    by (auto simp: case_prod_unfold f_def)
  also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (F* o\<^sub>C\<^sub>L F))\<close>
    by (simp add: comp_tensor_op tensor_op_adjoint)
  also have \<open>\<dots> = (\<Sum>(E,x)\<in>fst`V. E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (\<Sum>(F,y)\<in>snd`V. F* o\<^sub>C\<^sub>L F)\<close>
    unfolding W_def
    apply (subst sum.Sigma[symmetric])
      apply (auto intro!: simp: case_prod_beta)
    by (metis (mono_tags, lifting) sum.cong tensor_op_cbilinear.sum_left tensor_op_cbilinear.sum_right)
  also have \<open>\<dots> \<le> B \<otimes>\<^sub>o C\<close>
    using V_subset
    by (auto intro!: tensor_op_mono assms sum_nonneg intro: positive_cblinfun_squareI)
  finally show ?thesis
    by-
qed


lift_definition kf_tensor_raw :: \<open>('a ell2, 'b ell2, 'x) kraus_family \<Rightarrow> ('c ell2, 'd ell2, 'y) kraus_family \<Rightarrow> 
          (('a\<times>'c) ell2, ('b\<times>'d) ell2, (('a ell2\<Rightarrow>\<^sub>C\<^sub>L'b ell2)\<times>('c ell2\<Rightarrow>\<^sub>C\<^sub>L'd ell2)\<times>'x\<times>'y)) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close>
proof (rename_tac \<EE> \<FF>, intro CollectI)
  fix \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  define tensor where \<open>tensor = ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  show \<open>kraus_family tensor\<close>
  proof (intro kraus_familyI)
    from \<open>kraus_family \<EE>\<close>
    obtain B where B: \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    from B[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
      by simp
    from \<open>kraus_family \<FF>\<close>
    obtain C where C: \<open>(\<Sum>(F, x)\<in>T. F* o\<^sub>C\<^sub>L F) \<le> C\<close> if \<open>finite T\<close> and \<open>T \<subseteq> \<FF>\<close> for T
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close> if \<open>finite U\<close> and \<open>U \<subseteq> tensor\<close> for U
      using that by (auto intro!: kf_tensor_raw_bound_aux B C simp: tensor_def)
    then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> tensor})\<close>
      by fast
  qed
qed

lemma kf_apply_tensor_raw_as_infsum:
  \<open>kf_tensor_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    by (auto intro!: inj_onI)
  show \<open>kf_apply (kf_tensor_raw \<EE> \<FF>) \<rho>
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
    apply (simp add: kf_apply.rep_eq kf_tensor_raw.rep_eq infsum_reindex inj o_def)
    by (simp add: case_prod_unfold)
qed

lemma kf_apply_tensor_raw:
  shows \<open>kf_tensor_raw \<EE> \<FF> *\<^sub>k\<^sub>r tc_tensor \<rho> \<sigma> = tc_tensor (\<EE> *\<^sub>k\<^sub>r \<rho>) (\<FF> *\<^sub>k\<^sub>r \<sigma>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    by (auto intro!: inj_onI)
  have [simp]: \<open>bounded_linear (\<lambda>x. tc_tensor x (kf_apply \<FF> \<sigma>))\<close>
    by (intro bounded_linear_intros)
  have [simp]: \<open>bounded_linear (tc_tensor (sandwich_tc E \<rho>))\<close> for E
    by (intro bounded_linear_intros)
  have sum2: \<open>(\<lambda>(E, x). sandwich_tc E \<rho>) summable_on Rep_kraus_family \<EE>\<close>
    using kf_apply_summable by blast
  have sum3: \<open>(\<lambda>(F, y). sandwich_tc F \<sigma>) summable_on Rep_kraus_family \<FF>\<close>
    using kf_apply_summable by blast

  from kf_apply_summable[of _ \<open>kf_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>(\<lambda>((E, x), F, y). sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>)) summable_on Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>\<close>
    apply (simp add: kf_apply.rep_eq kf_tensor_raw.rep_eq summable_on_reindex inj o_def)
    by (simp add: case_prod_unfold)

  have \<open>kf_apply (kf_tensor_raw \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    by (rule kf_apply_tensor_raw_as_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. tc_tensor (sandwich_tc E \<rho>) (sandwich_tc F \<sigma>))\<close>
    by (simp add: sandwich_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. (sandwich_tc F \<sigma>)))\<close>
    apply (subst infsum_bounded_linear[where h=\<open>tc_tensor (sandwich_tc _ \<rho>)\<close>, symmetric])
      apply (auto intro!: sum3)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (kf_apply \<FF> \<sigma>))\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>) (kf_apply \<FF> \<sigma>)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>x. tc_tensor x (kf_apply \<FF> \<sigma>)\<close>, symmetric])
      apply (auto intro!: sum2)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kf_apply \<EE> \<rho>) (kf_apply \<FF> \<sigma>)\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  finally show ?thesis
    by -
qed

hide_fact kf_tensor_raw_bound_aux

definition \<open>kf_tensor \<EE> \<FF> = kf_map (\<lambda>(E, F, x, y). (x,y)) (kf_tensor_raw \<EE> \<FF>)\<close>

lemma kf_apply_tensor:
  \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r tc_tensor \<rho> \<sigma> = tc_tensor (\<EE> *\<^sub>k\<^sub>r \<rho>) (\<FF> *\<^sub>k\<^sub>r \<sigma>)\<close>
  by (auto intro!: simp: kf_tensor_def kf_apply_map kf_apply_tensor_raw)

lemma kf_apply_tensor_as_infsum:
  \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
  by (simp add: kf_tensor_def kf_apply_tensor_raw_as_infsum)


lemma kf_bound_tensor_raw:
  \<open>kf_bound (kf_tensor_raw \<EE> \<FF>) = kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>\<close>
proof (rule cblinfun_cinner_tensor_eqI)
  fix \<psi> \<phi>

  from kf_bound_summable[of \<open>kf_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
     (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    unfolding kf_tensor_raw.rep_eq
    apply (subst (asm) summable_on_in_reindex)
    by (auto simp add: kf_tensor_raw.rep_eq case_prod_unfold inj_on_def o_def)
  have sum4: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using kf_bound_summable by blast
  have sum5: \<open>summable_on_in cweak_operator_topology (\<lambda>(F,y). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<FF>)\<close>
    using kf_bound_summable by blast
  have sum2: \<open>(\<lambda>(E, x). \<psi> \<bullet>\<^sub>C ((E* o\<^sub>C\<^sub>L E) *\<^sub>V \<psi>)) abs_summable_on Rep_kraus_family \<EE>\<close>
    using kf_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise 
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)
  have sum3: \<open>(\<lambda>(F,y). \<phi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) abs_summable_on Rep_kraus_family \<FF>\<close>
    using kf_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)

  have \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kf_bound (kf_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)
      = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology ((\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) \<circ> (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)))
          (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    unfolding kf_bound.rep_eq kf_tensor_raw.rep_eq
    apply (subst infsum_in_reindex)
    by (auto simp add: inj_on_def case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
            (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                         (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F)) (\<psi> \<otimes>\<^sub>s \<phi>))\<close>
    apply (subst infsum_in_cweak_operator_topology_pointwise)
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                     (\<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>) * (\<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>))\<close>
    apply (rule infsum_cong)
    by (simp_all add: tensor_op_adjoint tensor_op_ell2)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x) \<in> Rep_kraus_family \<EE>. \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>)
                      * (\<Sum>\<^sub>\<infinity>(F,y) \<in> Rep_kraus_family \<FF>. \<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>)\<close>
    apply (subst infsum_product')
    using sum2 sum3 by (simp_all add: case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi>) * (\<phi> \<bullet>\<^sub>C kf_bound \<FF> \<phi>)\<close>
    unfolding kf_bound.rep_eq case_prod_unfold
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum4 apply (simp add: case_prod_unfold)
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum5 apply (simp add: case_prod_unfold)
    by (rule refl)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: tensor_op_ell2)
  finally show \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kf_bound (kf_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>) =
       (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by -
qed


lemma kf_bound_tensor:
  \<open>kf_bound (kf_tensor \<EE> \<FF>) = kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>\<close>
  by (simp add: kf_tensor_def kf_map_bound kf_bound_tensor_raw) 

lemma kf_norm_tensor:
  \<open>kf_norm (kf_tensor \<EE> \<FF>) = kf_norm \<EE> * kf_norm \<FF>\<close>
  by (auto intro!: norm_cblinfun_mono
      simp add: kf_norm_def kf_bound_tensor
      simp flip: tensor_op_norm)

lemma kf_tensor_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> =\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_tensor \<EE> \<FF> =\<^sub>k\<^sub>r kf_tensor \<EE>' \<FF>'\<close>
proof (rule kf_eq_weakI)
  show \<open>kf_apply (kf_tensor \<EE> \<FF>) \<rho> = kf_apply (kf_tensor \<EE>' \<FF>') \<rho>\<close> for \<rho>
  proof (rule fun_cong[where x=\<rho>], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear (kf_apply (kf_tensor \<EE> \<FF>))\<close>
      by (simp add: kf_apply_bounded_clinear)
    show \<open>bounded_clinear (kf_apply (kf_tensor \<EE>' \<FF>'))\<close>
      by (simp add: kf_apply_bounded_clinear)
    have \<EE>\<EE>': \<open>kf_apply \<EE> \<rho> = kf_apply \<EE>' \<rho>\<close> for \<rho>
      by (metis assms(1) kf_eq_weak_def)
    have \<FF>\<FF>': \<open>kf_apply \<FF> \<rho> = kf_apply \<FF>' \<rho>\<close> for \<rho>
      by (metis assms(2) kf_eq_weak_def)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('e ell2, 'e ell2) trace_class\<close>
    show \<open>kf_apply (kf_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = kf_apply (kf_tensor \<EE>' \<FF>') (tc_tensor \<rho> \<sigma>)\<close>
      by (auto intro!: simp: kf_apply_tensor \<EE>\<EE>' \<FF>\<FF>'
          simp flip: tensor_ell2_ket tensor_tc_butterfly)
  qed
qed

lemma kf_filter_tensor:
  \<open>kf_filter (\<lambda>(x,y). P x \<and> Q y) (kf_tensor \<EE> \<FF>) = kf_tensor (kf_filter P \<EE>) (kf_filter Q \<FF>)\<close>
  apply (auto intro!: arg_cong[where f=\<open>kf_map _\<close>] simp: kf_tensor_def kf_filter_map)
  apply transfer
  by (force simp add: image_iff case_prod_unfold)

lemma kf_tensor_cong:
  fixes \<EE> \<EE>' :: \<open>('a ell2, 'b ell2, 'x) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('c ell2, 'd ell2, 'y) kraus_family\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_tensor \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_tensor \<EE>' \<FF>'\<close>
proof (rule kf_eqI)
  fix xy :: \<open>'x \<times> 'y\<close> and \<rho>
  obtain x y where [simp]: \<open>xy = (x,y)\<close>
    by fastforce
  have aux1: \<open>(\<lambda>xy'. xy' = (x, y)) = (\<lambda>(x', y'). x' = x \<and> y' = y)\<close>
    by auto
  have \<open>kf_apply_on (kf_tensor \<EE> \<FF>) {xy}
         = kf_apply (kf_tensor (kf_filter (\<lambda>z. z = x) \<EE>) (kf_filter (\<lambda>z. z = y) \<FF>))\<close>
    by (simp add: kf_apply_on_def aux1 kf_filter_tensor)
  also have \<open>\<dots> = kf_apply (kf_tensor (kf_filter (\<lambda>z. z = x) \<EE>') (kf_filter (\<lambda>z. z = y) \<FF>'))\<close>
    apply (rule ext)
    apply (rule kf_apply_eqI)
    apply (rule kf_tensor_cong_weak)
    by (auto intro!: kf_filter_cong_weak assms)
  also have \<open>\<dots> = kf_apply_on (kf_tensor \<EE>' \<FF>') {xy}\<close>
    by (simp add: kf_apply_on_def aux1 kf_filter_tensor)
  finally show \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r @{xy} \<rho> = kf_tensor \<EE>' \<FF>' *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
    by simp
qed

lemma kf_tensor_compose_distrib:
  shows \<open>kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>)
     =\<^sub>k\<^sub>r kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)\<close>
  by (auto intro!: eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor]
      kf_apply_bounded_clinear comp_bounded_clinear
      simp: kf_eq_weak_def kf_apply_tensor kf_comp_apply)

definition kf_tensor_right :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('qu ell2, ('qu\<times>'extra) ell2, unit) kraus_family\<close> where
  \<comment> \<open>\<^term>\<open>kf_tensor_right \<rho>\<close> maps \<^term>\<open>\<sigma>\<close> to \<^term>\<open>\<sigma> \<otimes>\<^sub>o \<rho>\<close>\<close>
  \<open>kf_tensor_right \<rho> = kf_map_inj (\<lambda>_. ()) (kf_comp (kf_tensor kf_id (kf_constant_onedim \<rho>)) (kf_of_op (tensor_ell2_right (ket ()))))\<close>
definition kf_tensor_left :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('qu ell2, ('extra\<times>'qu) ell2, unit) kraus_family\<close> where
  \<comment> \<open>\<^term>\<open>kf_tensor_right \<rho>\<close> maps \<^term>\<open>\<sigma>\<close> to \<^term>\<open>\<rho> \<otimes>\<^sub>o \<sigma>\<close>\<close>
  \<open>kf_tensor_left \<rho> = kf_map_inj (\<lambda>_. ()) (kf_comp (kf_tensor (kf_constant_onedim \<rho>) kf_id) (kf_of_op (tensor_ell2_left (ket ()))))\<close>

lemma kf_apply_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_tensor_right \<rho> *\<^sub>k\<^sub>r \<sigma> = tc_tensor \<sigma> \<rho>\<close>
proof -
  have *: \<open>sandwich_tc (tensor_ell2_right (ket ())) \<sigma> = tc_tensor \<sigma> (tc_butterfly (ket()) (ket()))\<close>
    apply transfer'
    using sandwich_tensor_ell2_right' by blast
  show ?thesis
    by (simp add: kf_tensor_right_def kf_apply_map_inj inj_on_def kf_comp_apply
        kf_of_op_apply * kf_apply_tensor kf_constant_onedim_apply assms trace_tc_butterfly
        flip: trace_tc_one_dim_iso)
qed
lemma kf_apply_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_tensor_left \<rho> *\<^sub>k\<^sub>r \<sigma> = tc_tensor \<rho> \<sigma>\<close>
proof -
  have *: \<open>sandwich_tc (tensor_ell2_left (ket ())) \<sigma> = tc_tensor (tc_butterfly (ket()) (ket())) \<sigma>\<close>
    apply transfer'
    using sandwich_tensor_ell2_left' by blast
  show ?thesis
    by (simp add: kf_tensor_left_def kf_apply_map_inj inj_on_def kf_comp_apply
        kf_of_op_apply * kf_apply_tensor kf_constant_onedim_apply assms trace_tc_butterfly
        flip: trace_tc_one_dim_iso)
qed

lemma kf_bound_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_tensor_right \<rho>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: \<open>'b ell2\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_tensor_right \<rho>) \<psi> = trace_tc (kf_tensor_right \<rho> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (tc_tensor (tc_butterfly \<psi> \<psi>) \<rho>)\<close>
    using assms by (simp add: kf_apply_tensor_right)
  also have \<open>\<dots> = trace_tc (tc_butterfly \<psi> \<psi>) * trace_tc \<rho>\<close>
    by (metis (no_types, lifting) assms norm_tc_pos norm_tc_tensor of_real_mult tc_butterfly_pos tc_tensor_pos)
  also have \<open>\<dots> = norm \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: assms norm_tc_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (simp add: trace_tc_butterfly)
  finally show \<open>\<psi> \<bullet>\<^sub>C (kf_bound (kf_tensor_right \<rho>)) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by -
qed
lemma kf_bound_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_tensor_left \<rho>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: \<open>'b ell2\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_tensor_left \<rho>) \<psi> = trace_tc (kf_tensor_left \<rho> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (tc_tensor \<rho> (tc_butterfly \<psi> \<psi>))\<close>
    using assms by (simp add: kf_apply_tensor_left)
  also have \<open>\<dots> = trace_tc \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (metis (no_types, lifting) assms norm_tc_pos norm_tc_tensor of_real_mult tc_butterfly_pos tc_tensor_pos)
  also have \<open>\<dots> = norm \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: assms norm_tc_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (simp add: trace_tc_butterfly)
  finally show \<open>\<psi> \<bullet>\<^sub>C (kf_bound (kf_tensor_left \<rho>)) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by -
qed


lemma kf_norm_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_tensor_right \<rho>) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def)
lemma kf_norm_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_tensor_left \<rho>) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def)


subsection \<open>Partial trace\<close>

definition kf_partial_trace_right :: \<open>(('a\<times>'b) ell2, 'a ell2, 'b) kraus_family\<close> where
  \<open>kf_partial_trace_right = kf_map (\<lambda>((_,b),_). inv ket b)
  (kf_comp (kf_of_op (tensor_ell2_right (ket ())*))
   (kf_tensor kf_id (kf_trace (range ket))))\<close>

definition kf_partial_trace_left :: \<open>(('a\<times>'b) ell2, 'b ell2, 'a) kraus_family\<close> where
  \<open>kf_partial_trace_left = kf_map_inj snd (kf_comp kf_partial_trace_right (kf_of_op swap_ell2))\<close>

lemma partial_trace_is_kf_partial_trace: 
  fixes t :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>
  shows \<open>partial_trace t = kf_partial_trace_right *\<^sub>k\<^sub>r t\<close>
proof -
  have \<open>partial_trace t = kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
    (kf_apply (kf_tensor kf_id (kf_trace (range ket))) t)\<close>
  proof (rule fun_cong[where x=t], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear partial_trace\<close>
      by simp
    show \<open>bounded_clinear
     (\<lambda>t. kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
           (kf_apply (kf_tensor kf_id (kf_trace (range ket))) t))\<close>
      by (intro bounded_linear_intros)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
    show \<open>partial_trace (tc_tensor \<rho> \<sigma>) =
           kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
            (kf_apply (kf_tensor kf_id (kf_trace (range ket))) (tc_tensor \<rho> \<sigma>))\<close>
       apply (auto intro!: from_trace_class_inject[THEN iffD1]
          simp: partial_trace_tensor kf_apply_tensor kf_trace_is_trace kf_of_op_apply
          from_trace_class_sandwich_tc sandwich_apply trace_tc.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
      by (auto intro!: cblinfun_eqI simp: tensor_op_ell2 ket_CARD_1_is_1)
  qed
  then show ?thesis
    by (simp add: kf_partial_trace_right_def kf_comp_apply)
qed

lemma partial_trace_ignores_kraus_family:
  assumes \<open>kf_trace_preserving \<EE>\<close>
  shows \<open>partial_trace (kf_tensor kf_id \<EE> *\<^sub>k\<^sub>r \<rho>) = partial_trace \<rho>\<close>
proof (rule fun_cong[where x=\<rho>], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear (\<lambda>a. partial_trace (kf_apply (kf_tensor kf_id \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear partial_trace\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('d ell2, 'd ell2) trace_class\<close> and \<sigma> :: \<open>('a ell2, 'a ell2) trace_class\<close>
  from assms
  show \<open>partial_trace (kf_apply (kf_tensor kf_id \<EE>) (tc_tensor \<rho> \<sigma>)) =
           partial_trace (tc_tensor \<rho> \<sigma>)\<close>
    by (auto intro!: simp: kf_apply_tensor partial_trace_tensor kf_trace_preserving_def)
qed

lemma kf_partial_trace_bound[simp]:
  shows \<open>kf_bound kf_partial_trace_right = id_cblinfun\<close>
  by (simp add: kf_partial_trace_right_def kf_map_bound
      unitary_tensor_ell2_right_CARD_1 kf_bound_comp_iso kf_bound_tensor
      kf_trace_bound)

lemma kf_partial_trace_norm[simp]:
  shows \<open>kf_norm kf_partial_trace_right = 1\<close>
  by (simp add: kf_norm_def)

lemma kf_partial_trace_right_apply_singleton:
    \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} \<rho> = sandwich_tc (tensor_ell2_right (ket x)*) \<rho>\<close>
proof -
  have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d))) =
       sandwich_tc (tensor_ell2_right (ket x)*) (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d)))\<close> for a b :: 'a and c d :: 'b
  proof -
    have aux1: \<open>(\<lambda>xa. (case xa of (x, xa) \<Rightarrow> (case x of (uu_, b) \<Rightarrow> \<lambda>_. inv ket b) xa) \<in> {x}) = (\<lambda>(e,f). True \<and> inv ket (snd e) = x)\<close>
      by auto
    have aux2: \<open>(\<lambda>e. inv ket (snd e) = x) = (\<lambda>(a,b). True \<and> inv ket b = x)\<close>
      by auto
    have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d))) =
       sandwich_tc (tensor_ell2_right (ket ())*)
        (tc_tensor (tc_butterfly (ket a) (ket b)) (kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))))\<close>
      by (auto simp only: kf_apply_on_def kf_partial_trace_right_def
          kf_filter_map aux1 kf_filter_comp kf_of_op_apply
          kf_filter_true kf_filter_tensor aux2 kf_apply_map
          kf_comp_apply o_def kf_apply_tensor kf_id_apply)
    also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket ())*) (tc_tensor (tc_butterfly (ket a) (ket b)) (of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())))\<close>
    proof (rule arg_cong[where f=\<open>\<lambda>x. sandwich_tc _ (tc_tensor _ x)\<close>])
      have \<open>kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))
         = sandwich_tc (vector_to_cblinfun (ket x)*) (tc_butterfly (ket c) (ket d))\<close>
        apply (transfer' fixing: x)
        apply (subst infsum_single[where i=\<open>((vector_to_cblinfun (ket x))*, ket x)\<close>])
        by auto
      also have \<open>\<dots> = of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())\<close>
        apply (auto simp add: sandwich_tc_butterfly ket_CARD_1_is_1 cinner_ket)
        by -
      finally show \<open>kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))
           = of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())\<close>
        by -
    qed
    also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x)*) (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d)))\<close>
      by (auto simp: tensor_tc_butterfly sandwich_tc_butterfly)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac fun_cong[where x=\<rho>])
    apply (rule eq_from_separatingI2)
       apply (rule separating_set_bounded_clinear_tc_tensor_nested)
        apply (rule separating_set_tc_butterfly_nested)
         apply (rule separating_set_ket)
        apply (rule separating_set_ket)
       apply (rule separating_set_tc_butterfly_nested)
        apply (rule separating_set_ket)
       apply (rule separating_set_ket)
    by (auto intro!: kf_apply_on_bounded_clinear bounded_clinear_sandwich_tc separating_set_tc_butterfly_nested simp: )
qed

lemma kf_partial_trace_left_apply_singleton:
  \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} \<rho> = sandwich_tc (tensor_ell2_left (ket x)*) \<rho>\<close>
proof -
  have aux1: \<open>(\<lambda>xa. snd xa = x) = (\<lambda>(e,f). f=x \<and> True)\<close>
    by auto
  have aux2: \<open>(\<lambda>xa. xa \<in> {x}) = (\<lambda>xa. xa = x)\<close>
    by auto
  have inj_snd: \<open>inj_on (snd :: unit\<times>'b \<Rightarrow> 'b) X\<close> for X
    by (auto intro!: inj_onI)
  have aux3: \<open>tensor_ell2_right (ket x)* *\<^sub>V ket (b, a) = of_bool (x=a) *\<^sub>R ket b\<close> for x a :: 'x and b :: 'y
    by (smt (verit) cinner_ket_same of_bool_eq(1) of_bool_eq(2) of_real_1 of_real_hom.hom_0_iff orthogonal_ket scaleR_scaleC tensor_ell2_ket tensor_ell2_right_adj_apply)
  have aux4: \<open>tensor_ell2_left (ket x)* *\<^sub>V ket (a, b) = of_bool (x=a) *\<^sub>R ket b\<close> for x a :: 'x and b :: 'y
    by (smt (verit, del_insts) cinner_ket_same of_bool_eq(1) of_bool_eq(2) of_real_1 of_real_hom.hom_0_iff orthogonal_ket scaleR_scaleC tensor_ell2_ket tensor_ell2_left_adj_apply)
  have aux5: \<open>tensor_ell2_right (ket x)* o\<^sub>C\<^sub>L swap_ell2 = tensor_ell2_left (ket x)*\<close>
    apply (rule equal_ket)
    by (auto intro!: simp: aux3 aux4)
  have \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} \<rho>
     = kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (sandwich_tc swap_ell2 \<rho>)\<close>
    by (simp only: kf_partial_trace_left_def kf_apply_on_def kf_filter_map_inj
        aux1 kf_filter_comp kf_apply_map_inj inj_snd kf_filter_true
        kf_comp_apply o_def kf_of_op_apply aux2)
  also have \<open>\<dots> = sandwich_tc (tensor_ell2_left (ket x)*) \<rho>\<close>
    by (auto intro!: arg_cong[where f=\<open>\<lambda>x. sandwich_tc x _\<close>]
        simp: kf_partial_trace_right_apply_singleton aux5
        simp flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
  finally show ?thesis
    by -
qed

lemma kf_domain_partial_trace_right[simp]: \<open>kf_domain kf_partial_trace_right = UNIV\<close>
proof (intro Set.set_eqI iffI UNIV_I)
  fix x :: 'a and y :: 'b

  have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket y) (ket y)) (tc_butterfly (ket x) (ket x)))
      = tc_butterfly (ket y) (ket y)\<close>
    by (simp add: kf_partial_trace_right_apply_singleton tensor_tc_butterfly sandwich_tc_butterfly)
  also have \<open>\<dots> \<noteq> 0\<close>
  proof -
    have \<open>norm (tc_butterfly (ket y) (ket y)) = 1\<close>
      by (simp add: norm_tc_butterfly)
    then show ?thesis
      by auto
  qed
 finally have \<open>kf_apply_on (kf_partial_trace_right :: (('b\<times>'a) ell2, 'b ell2, 'a) kraus_family) {x} \<noteq> 0\<close>
    by auto
  then show \<open>x \<in> kf_domain (kf_partial_trace_right :: (('b\<times>'a) ell2, 'b ell2, 'a) kraus_family)\<close>
    by (rule in_kf_domain_iff_apply_nonzero[THEN iffD2])
qed


lemma kf_domain_partial_trace_left[simp]: \<open>kf_domain kf_partial_trace_left = UNIV\<close>
proof (intro Set.set_eqI iffI UNIV_I)
  fix x :: 'a and y :: 'b

  have \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket x) (ket x)) (tc_butterfly (ket y) (ket y)))
      = tc_butterfly (ket y) (ket y)\<close>
    by (simp add: kf_partial_trace_left_apply_singleton tensor_tc_butterfly sandwich_tc_butterfly)
  also have \<open>\<dots> \<noteq> 0\<close>
  proof -
    have \<open>norm (tc_butterfly (ket y) (ket y)) = 1\<close>
      by (simp add: norm_tc_butterfly)
    then show ?thesis
      by auto
  qed
 finally have \<open>kf_apply_on (kf_partial_trace_left :: (('a\<times>'b) ell2, 'b ell2, 'a) kraus_family) {x} \<noteq> 0\<close>
    by auto
  then show \<open>x \<in> kf_domain (kf_partial_trace_left :: (('a\<times>'b) ell2, 'b ell2, 'a) kraus_family)\<close>
    by (rule in_kf_domain_iff_apply_nonzero[THEN iffD2])
qed


subsection \<open>Complete measurement\<close>

lemma complete_measurement_aux:
  fixes B and F :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'a) set\<close>
  defines \<open>family \<equiv> (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
  assumes \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> and \<open>is_ortho_set B\<close>
  shows \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close>
proof -
  obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (selfbutter (sgn x), x)) ` G\<close>
    apply atomize_elim
    using \<open>finite F\<close> and FB
    apply (simp add: family_def)
    by (meson finite_subset_image)
  from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
    by (simp add: \<open>is_ortho_set B\<close> is_ortho_set_antimono)
  then have [simp]: \<open>e \<in> G \<Longrightarrow> norm (sgn e) = 1\<close> for e
    apply (simp add: is_ortho_set_def)
    by (metis norm_sgn)
  have [simp]: \<open>inj_on (\<lambda>x. (selfbutter (sgn x), x)) G\<close>
    by (meson inj_onI prod.inject)
  have [simp]: \<open>inj_on sgn G\<close>
  proof (rule inj_onI, rule ccontr)
    fix x y assume \<open>x \<in> G\<close> and \<open>y \<in> G\<close> and sgn_eq: \<open>sgn x = sgn y\<close> and \<open>x \<noteq> y\<close>
    with \<open>is_ortho_set G\<close> have \<open>is_orthogonal x y\<close>
      by (meson is_ortho_set_def)
    then have \<open>is_orthogonal (sgn x) (sgn y)\<close>
      by fastforce
    with sgn_eq have \<open>sgn x = 0\<close>
      by force
    with \<open>x \<in> G\<close> \<open>is_ortho_set G\<close> show False
      by (metis \<open>x \<noteq> y\<close> local.sgn_eq sgn_zero_iff)
  qed
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter (sgn x))\<close>
    by (simp add: FG sum.reindex cdot_square_norm)
  also have \<open>(\<Sum>x\<in>G. selfbutter (sgn x)) \<le> id_cblinfun\<close>
    apply (subst sum.reindex[where h=sgn, unfolded o_def, symmetric])
    using \<open>is_ortho_set G\<close>
     apply (auto intro!: sum_butterfly_leq_id simp: is_ortho_set_def sgn_zero_iff)
    by fast
  finally show ?thesis
    by -
qed

lemma complete_measurement_is_kraus_family:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kraus_family ((\<lambda>x. (selfbutter (sgn x), x)) ` B)\<close>
  using complete_measurement_aux[OF _ _ assms]
  by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)

lift_definition kf_complete_measurement :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'a, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_ortho_set B then (\<lambda>x. (selfbutter (sgn x), x)) ` B else {}\<close>
  by (auto intro!: complete_measurement_is_kraus_family)

lemma kf_bound_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kf_bound (kf_complete_measurement B) \<le> id_cblinfun\<close>
  apply (rule kf_bound_leqI)
  by (simp add: assms complete_measurement_aux kf_complete_measurement.rep_eq)

lemma kf_norm_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kf_norm (kf_complete_measurement B) \<le> 1\<close>
  by (smt (verit, ccfv_SIG) assms kf_norm_def kf_bound_complete_measurement kf_bound_pos norm_cblinfun_id_le norm_cblinfun_mono)


lemma kf_complete_measurement_idem[simp]:
  \<open>kf_complete_measurement B *\<^sub>k\<^sub>r kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>
      = kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>\<close>
proof (cases \<open>is_ortho_set B\<close>)
  case True
  have \<open>(\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. 
            sandwich_tc (fst E) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)) =
        (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)\<close>
  proof (rule infsum_cong)
    fix hh assume hh_B: \<open>hh \<in> (\<lambda>h. (selfbutter (sgn h), h)) ` B\<close>
    then obtain h where \<open>h \<in> B\<close> and [simp]: \<open>hh = (selfbutter (sgn h), h)\<close>
      by blast
    from kf_apply_abs_summable[OF complete_measurement_is_kraus_family[OF \<open>is_ortho_set B\<close>]]
    have summ: \<open>(\<lambda>x. sandwich_tc (fst x) \<rho>) summable_on (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
      by (auto intro: abs_summable_summable simp: case_prod_beta)
    have \<open>sandwich_tc (selfbutter (sgn h)) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)
            = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst E) \<rho>))\<close>
      apply (rule infsum_bounded_linear[unfolded o_def, symmetric])
       apply (intro bounded_linear_intros)
      by (rule summ)
    also have \<open>\<dots> = sandwich_tc (selfbutter (sgn h)) \<rho>\<close>
    proof (subst infsum_single[where i=hh])
      fix hh' assume \<open>hh' \<noteq> hh\<close> and \<open>hh' \<in> (\<lambda>h. (selfbutter (sgn h), h)) ` B\<close>
      then obtain h' where \<open>h' \<in> B\<close> and [simp]: \<open>hh' = (selfbutter (sgn h'), h')\<close>
        by blast
      with \<open>hh' \<noteq> hh\<close> have \<open>h \<noteq> h'\<close>
        by force
      then have *: \<open>sgn h \<bullet>\<^sub>C sgn h' = 0\<close>
        using True \<open>h \<in> B\<close> \<open>h' \<in> B\<close> is_ortho_set_def by fastforce
      show \<open>sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh') \<rho>) = 0\<close>
        by (simp add: * flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
    next
      have *: \<open>sgn h \<bullet>\<^sub>C sgn h = 1\<close>
        by (metis True \<open>h \<in> B\<close> cnorm_eq_1 is_ortho_set_def norm_sgn)
      have \<open>(if hh \<in> (\<lambda>x. (selfbutter (sgn x), x)) ` B then sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh) \<rho>) else 0)
      = sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh) \<rho>)\<close> (is \<open>?lhs = _\<close>)
        using hh_B by presburger
      also have \<open>\<dots> = sandwich_tc (selfbutter (sgn h)) \<rho>\<close>
        by (simp add: * flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
      finally show \<open>?lhs = \<dots>\<close>
        by -
    qed
    finally show \<open>sandwich_tc (fst hh) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>) = sandwich_tc (fst hh) \<rho>\<close>
      by simp
  qed
  with True show ?thesis
    apply (transfer fixing: B \<rho>)
    by simp
next
  case False
  then show ?thesis
    apply (transfer fixing: B \<rho>)
    by simp
qed


lemma kf_complete_measurement_apply:
  assumes [simp]: \<open>is_ortho_set B\<close>
  shows \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
proof -
  have \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = 
      (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) t)\<close>
    apply (transfer' fixing: B t)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  finally show ?thesis
    by -
qed

lemma kf_complete_measurement_has_sum:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter (sgn x)) \<rho>) has_sum kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>) B\<close>
  using kf_apply_has_sum[of _ \<open>kf_complete_measurement B\<close>] assms
  by (simp add: kf_complete_measurement_apply kf_complete_measurement.rep_eq
      has_sum_reindex inj_on_def o_def)

lemma kf_complete_measurement_has_sum_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter x) \<rho>) has_sum kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>) B\<close>
proof -
  have \<open>is_ortho_set B\<close>
    using assms by (simp add: is_onb_def)
  have sgnx: \<open>sgn x = x\<close> if \<open>x \<in> B\<close> for x
    using assms that
    by (simp add: is_onb_def sgn_div_norm)
  from kf_complete_measurement_has_sum[OF \<open>is_ortho_set B\<close>]
  show ?thesis
    apply (rule has_sum_cong[THEN iffD1, rotated])
    by (simp add: sgnx)
qed

lemma kf_complete_measurement_apply_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter x) t)\<close>
  using kf_complete_measurement_has_sum_onb[OF assms]
  by (metis (lifting) infsumI)

(* TODO move *)
lemma antilinear_eq_0_on_span:
  assumes \<open>antilinear f\<close>
    and \<open>\<And>x. x \<in> b \<Longrightarrow> f x = 0\<close>
    and \<open>x \<in> cspan b\<close>
  shows \<open>f x = 0\<close>
  by x


(* TODO move *)
lemma antilinear_diff:
  assumes \<open>antilinear f\<close> and \<open>antilinear g\<close>
  shows \<open>antilinear (\<lambda>x. f x - g x)\<close>
  apply (rule antilinearI)
   apply (metis add_diff_add additive.add antilinear_def assms(1,2))
  by (simp add: antilinear.scaleC assms(1,2) scaleC_right.diff)

(* TODO move *)
lemma antilinear_cinner:
  shows \<open>antilinear (\<lambda>x. x \<bullet>\<^sub>C y)\<close>
  by (simp add: antilinearI cinner_add_left)


(* TODO move *)
lemma cinner_extensionality_basis:
  fixes g h :: \<open>'a::complex_inner\<close>
  assumes \<open>ccspan B = \<top>\<close>
  assumes \<open>\<And>x. x \<in> B \<Longrightarrow> x \<bullet>\<^sub>C g = x \<bullet>\<^sub>C h\<close>
  shows \<open>g = h\<close>
proof (rule cinner_extensionality)
  fix y :: 'a
  have \<open>y \<in> closure (cspan B)\<close>
    using assms(1) ccspan.rep_eq by fastforce
  then obtain x where \<open>x \<longlonglongrightarrow> y\<close> and xB: \<open>x i \<in> cspan B\<close> for i
    using closure_sequential by blast
  have lin: \<open>antilinear (\<lambda>a. a \<bullet>\<^sub>C g - a \<bullet>\<^sub>C h)\<close>
    by (intro antilinear_diff antilinear_cinner)
  from lin have \<open>x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h = 0\<close> for i
    apply (rule antilinear_eq_0_on_span[of _ B])
    using xB assms by auto
  then have \<open>(\<lambda>i. x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h) \<longlonglongrightarrow> 0\<close> for i
    by simp
  moreover have \<open>(\<lambda>i. x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h) \<longlonglongrightarrow> y \<bullet>\<^sub>C g - y \<bullet>\<^sub>C h\<close>
    apply (rule_tac continuous_imp_tendsto[unfolded o_def, OF _ \<open>x \<longlonglongrightarrow> y\<close>])
    by simp
  ultimately have \<open>y \<bullet>\<^sub>C g - y \<bullet>\<^sub>C h = 0\<close>
    using LIMSEQ_unique by blast
  then show \<open>y \<bullet>\<^sub>C g = y \<bullet>\<^sub>C h\<close>
    by simp
qed

lemma kf_bound_complete_measurement_onb[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_bound (kf_complete_measurement B) = id_cblinfun\<close>
  apply (rule cblinfun_eq_gen_eqI[where G=B])
   apply (rule cinner_extensionality_basis[where B=B])
proof -
  show \<open>ccspan B = \<top>\<close>
    using assms is_onb_def by blast
  then show \<open>ccspan B = \<top>\<close>
    by -
  fix x y assume \<open>x \<in> B\<close> and \<open>y \<in> B\<close>
  have aux1: \<open>j \<noteq> x \<Longrightarrow> j \<in> B \<Longrightarrow> sandwich_tc (selfbutter j) (tc_butterfly y x) = 0\<close> for j
    apply (transfer' fixing: x B j y)
    by (smt (z3) \<open>x \<in> B\<close> apply_id_cblinfun assms butterfly_0_right butterfly_adjoint butterfly_def cblinfun_apply_cblinfun_compose
        cblinfun_comp_butterfly is_onb_def is_ortho_setD of_complex_eq_id sandwich_apply vector_to_cblinfun_adj_apply)
  have aux2: \<open>trace_tc (sandwich_tc (selfbutter y) (tc_butterfly y y)) = 1\<close>
    apply (transfer' fixing: y)
    by (metis (no_types, lifting) ext \<open>y \<in> B\<close> assms butterfly_adjoint butterfly_comp_butterfly cblinfun_comp_butterfly cinner_simps(6)
        is_onb_def norm_one one_cinner_a_scaleC_one one_cinner_one sandwich_apply selfbutter_pos trace_butterfly trace_norm_butterfly
        trace_norm_pos trace_scaleC)
  have aux3: \<open>x \<noteq> y \<Longrightarrow> trace_tc (sandwich_tc (selfbutter x) (tc_butterfly y x)) = 0\<close>
    apply (transfer' fixing: x y)
    by (metis (no_types, lifting) ext Trace_Class.trace_0 \<open>x \<in> B\<close> \<open>y \<in> B\<close> apply_id_cblinfun assms butterfly_0_left butterfly_def
        cblinfun.zero_right cblinfun_apply_cblinfun_compose cblinfun_comp_butterfly is_onb_def is_ortho_setD of_complex_eq_id
        sandwich_apply vector_to_cblinfun_adj_apply)

  have \<open>x \<bullet>\<^sub>C (kf_bound (kf_complete_measurement B) *\<^sub>V y) = trace_tc (kf_complete_measurement B *\<^sub>k\<^sub>r tc_butterfly y x)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (\<Sum>\<^sub>\<infinity>xa\<in>B. sandwich_tc (selfbutter xa) (tc_butterfly y x))\<close>
    by (simp add: kf_complete_measurement_apply_onb assms)
  also have \<open>\<dots> = trace_tc (if x \<in> B then sandwich_tc (selfbutter x) (tc_butterfly y x) else 0)\<close>
    apply (subst infsum_single[where i=x])
    using aux1 by auto
  also have \<open>\<dots> = of_bool (x = y)\<close>
    using \<open>y \<in> B\<close> aux2 aux3 by (auto intro!: simp: )
  also have \<open>\<dots> = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V y)\<close>
    using \<open>x \<in> B\<close> \<open>y \<in> B\<close> assms cnorm_eq_1 is_onb_def is_ortho_setD by fastforce
  finally show \<open>x \<bullet>\<^sub>C (kf_bound (kf_complete_measurement B) *\<^sub>V y) = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V y)\<close>
    by -
qed

lemma kf_norm_complete_measurement_onb[simp]:
  fixes B :: \<open>'a::{not_singleton, chilbert_space} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_complete_measurement B) = 1\<close>
  by (simp add: kf_norm_def assms)


lemma kf_complete_measurement_apply_ket:
  \<open>kf_complete_measurement (range ket) *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
proof -
  have \<open>kf_apply (kf_complete_measurement (range ket)) t = 
    (\<Sum>\<^sub>\<infinity>x\<in>range ket. sandwich_tc (selfbutter x) t)\<close>
    by (simp add: kf_complete_measurement_apply_onb)
  also have \<open>\<dots>  = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
    by (simp add: infsum_reindex o_def)
  finally show ?thesis
    by -
qed


lemma kf_complete_measurement_diagonal_operator[simp]:
  \<open>kf_complete_measurement (range ket) *\<^sub>k\<^sub>r (diagonal_operator_tc f) = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  have \<open>kf_apply (kf_complete_measurement (range ket)) (diagonal_operator_tc f) = 
            (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (diagonal_operator_tc f))\<close>
    by (simp add: kf_complete_measurement_apply_ket)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (\<Sum>\<^sub>\<infinity>y. f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. sandwich_tc (selfbutter (ket x)) (f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    apply (rule infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def, symmetric])
    by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc tc_butterfly_scaleC_summable True)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. of_bool (y=x) *\<^sub>C f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (rule infsum_cong)+
    apply (transfer' fixing: f)
    by (simp add: sandwich_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (subst infsum_of_bool_scaleC)
    by simp
  also have \<open>\<dots> = diagonal_operator_tc f\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  finally show ?thesis
    by -
next
  case False
  then have \<open>diagonal_operator_tc f = 0\<close>
    by (rule diagonal_operator_tc_invalid)
  then show ?thesis
    by simp
qed

subsection \<open>Reconstruction\<close>

lemma kf_reconstruction_is_bounded_clinear:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  shows \<open>bounded_clinear \<EE>\<close>
proof -
  have linear: \<open>clinear \<EE>\<close>
  proof (rule clinearI)
    fix \<rho> \<sigma> c
    have \<open>((\<lambda>a. sandwich_tc (f a) \<rho> + sandwich_tc (f a) \<sigma>) has_sum (\<EE> \<rho> + \<EE> \<sigma>)) A\<close>
      by (intro has_sum_add assms)
    then have \<open>((\<lambda>a. sandwich_tc (f a) (\<rho> + \<sigma>)) has_sum (\<EE> \<rho> + \<EE> \<sigma>)) A\<close>
      by (meson has_sum_cong sandwich_tc_plus)
    with assms[of \<open>\<rho> + \<sigma>\<close>]
    show \<open>\<EE> (\<rho> + \<sigma>) = \<EE> \<rho> + \<EE> \<sigma>\<close>
      by (rule has_sum_unique)
    from assms[of \<rho>]
    have \<open>((\<lambda>a. sandwich_tc (f a) (c *\<^sub>C \<rho>)) has_sum c *\<^sub>C \<EE> \<rho>) A\<close>
      using has_sum_scaleC_right[where A=A and s=\<open>\<EE> \<rho>\<close>]
      by (auto intro!: has_sum_scaleC_right simp: sandwich_tc_scaleC_right)
    with assms[of \<open>c *\<^sub>C \<rho>\<close>]
    show \<open>\<EE> (c *\<^sub>C \<rho>) = c *\<^sub>C \<EE> \<rho>\<close>
      by (rule has_sum_unique)
  qed
  have pos: \<open>\<EE> \<rho> \<ge> 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    apply (rule has_sum_mono_traceclass[where f=\<open>\<lambda>_.0\<close> and g=\<open>(\<lambda>a. sandwich_tc (f a) \<rho>)\<close>])
    using assms
    by (auto intro!: sandwich_tc_pos simp: that)
  have mono: \<open>\<EE> \<rho> \<le> \<EE> \<sigma>\<close> if \<open>\<rho> \<le> \<sigma>\<close> for \<rho> \<sigma>
  proof -
    have \<open>\<EE> (\<sigma> - \<rho>) \<ge> 0\<close>
      apply (rule pos)
      using that
      by auto
    then show ?thesis
      by (simp add: linear complex_vector.linear_diff)
  qed
  have bounded_pos: \<open>\<exists>B\<ge>0. \<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close>
  proof (rule ccontr)
    assume asm: \<open>\<not> (\<exists>B\<ge>0. \<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>)\<close>
    obtain \<rho>0 where \<EE>_big0: \<open>norm (\<EE> (\<rho>0 i)) > 2^i * norm (\<rho>0 i)\<close> and \<rho>0_pos: \<open>\<rho>0 i \<ge> 0\<close> for i :: nat
    proof (atomize_elim, rule choice2, rule allI, rule ccontr)
      fix i
      define B :: real where \<open>B = 2^i\<close>
      have \<open>B \<ge> 0\<close>
        by (simp add: B_def)
      assume \<open>\<nexists>\<rho>0. B * norm \<rho>0 < norm (\<EE> \<rho>0) \<and> 0 \<le> \<rho>0\<close>
      then have \<open>\<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close>
        by force
      with asm \<open>B \<ge> 0\<close> show False
        by blast
    qed
    have \<rho>0_neq0: \<open>\<rho>0 i \<noteq> 0\<close> for i
      using \<EE>_big0[of i] linear complex_vector.linear_0 by force
    define \<rho> where \<open>\<rho> i = \<rho>0 i /\<^sub>R norm (\<rho>0 i)\<close> for i
    have \<rho>_pos: \<open>\<rho> i \<ge> 0\<close> for i
      by (simp add: \<rho>_def \<rho>0_pos scaleR_nonneg_nonneg)
    have norm_\<rho>: \<open>norm (\<rho> i) = 1\<close> for i
      by (simp add: \<rho>0_neq0 \<rho>_def)
    from \<EE>_big0 have \<EE>_big: \<open>trace_tc (\<EE> (\<rho> i)) \<ge> 2^i\<close> for i :: nat
    proof -
      have \<open>trace_tc (\<EE> (\<rho> i)) = trace_tc (\<EE> (\<rho>0 i) /\<^sub>R norm (\<rho>0 i))\<close>
        by (simp add: \<rho>_def linear scaleR_scaleC clinear.scaleC 
          bounded_clinear_trace_tc[THEN bounded_clinear.clinear])
      also have \<open>\<dots> = norm (\<EE> (\<rho>0 i) /\<^sub>R norm (\<rho>0 i))\<close>
        using \<rho>0_pos pos
        by (metis linordered_field_class.inverse_nonnegative_iff_nonnegative norm_ge_zero norm_tc_pos scaleR_nonneg_nonneg)
      also have \<open>\<dots> = norm (\<EE> (\<rho>0 i)) / norm (\<rho>0 i)\<close>
        by (simp add: divide_inverse_commute)
      also have \<open>\<dots> > (2^i * norm (\<rho>0 i)) / norm (\<rho>0 i)\<close> (is \<open>_ > \<dots>\<close>)
        using \<EE>_big0 \<rho>0_neq0
        by (smt (verit, best) complex_of_real_strict_mono_iff divide_le_eq norm_le_zero_iff)
      thm calculation this
      also have \<open>\<dots> = 2^i\<close>
        using \<rho>0_neq0 by force
      finally show ?thesis
        by simp
    qed
    define \<sigma> \<tau> where \<open>\<sigma> n = (\<Sum>i<n. \<rho> i /\<^sub>R 2^i)\<close> and \<open>\<tau> = (\<Sum>\<^sub>\<infinity>i. \<rho> i /\<^sub>R 2^i)\<close> for n :: nat
    have \<open>(\<lambda>i. \<rho> i /\<^sub>R 2^i) abs_summable_on UNIV\<close>
    proof (rule infsum_tc_norm_bounded_abs_summable)
      from \<rho>_pos show \<open>\<rho> i /\<^sub>R 2^i \<ge> 0\<close> for i
        by (simp add: scaleR_nonneg_nonneg)
      show \<open>norm (\<Sum>i\<in>F. \<rho> i /\<^sub>R 2^i) \<le> 2\<close> if \<open>finite F\<close> for F
      proof -
        from finite_nat_bounded[OF that]
        obtain n where i_leq_n: \<open>i \<le> n\<close> if \<open>i \<in> F\<close> for i
          apply atomize_elim
          by (auto intro!: order.strict_implies_order simp: lessThan_def Ball_def simp flip: Ball_Collect)
        have \<open>norm (\<Sum>i\<in>F. \<rho> i /\<^sub>R 2^i) \<le> (\<Sum>i\<in>F. norm (\<rho> i /\<^sub>R 2^i))\<close>
          by (simp add: sum_norm_le)
        also have \<open>\<dots> = (\<Sum>i\<in>F. (1/2)^i)\<close>
          using norm_\<rho> 
          by (smt (verit, del_insts) Extra_Ordered_Fields.sign_simps(23) divide_inverse_commute linordered_field_class.inverse_nonnegative_iff_nonnegative
              norm_scaleR power_inverse power_one sum.cong zero_le_power)
        also have \<open>\<dots> \<le> (\<Sum>i\<le>n. (1/2)^i)\<close>
          apply (rule sum_mono2)
          using i_leq_n
          by auto
        also have \<open>\<dots> \<le> (\<Sum>i. (1/2)^i)\<close>
          apply (rule sum_le_suminf)
          by auto
        also have \<open>... = 2\<close>
          using suminf_geometric[of \<open>1/2 :: real\<close>]
          by simp
        finally show ?thesis
          by -
      qed
    qed
    then have summable: \<open>(\<lambda>i. \<rho> i /\<^sub>R 2^i) summable_on UNIV\<close>
      by (simp add: abs_summable_summable)
    have \<open>trace_tc (\<EE> \<tau>) \<ge> n\<close> for n :: nat
    proof -
      have \<open>trace_tc (\<EE> \<tau>) \<ge> trace_tc (\<EE> (\<sigma> n))\<close> (is \<open>_ \<ge> \<dots>\<close>)
        by (auto intro!: trace_tc_mono mono infsum_mono_neutral_traceclass
            simp: \<tau>_def \<sigma>_def summable \<rho>_pos scaleR_nonneg_nonneg simp flip: infsum_finite)
      moreover have \<open>\<dots> = (\<Sum>i<n. trace_tc (\<EE> (\<rho> i)) / 2^i)\<close>
        by (simp add: \<sigma>_def complex_vector.linear_sum linear scaleR_scaleC trace_scaleC
            bounded_clinear_trace_tc[THEN bounded_clinear.clinear] clinear.scaleC
            add.commute mult.commute divide_inverse)
      moreover have \<open>\<dots> \<ge> (\<Sum>i<n. 2^i / 2^i)\<close> (is \<open>_ \<ge> \<dots>\<close>)
        apply (intro sum_mono divide_right_mono)
        using \<EE>_big
        by (simp_all add: less_eq_complex_def)
      moreover have \<open>\<dots> = (\<Sum>i<n. 1)\<close>
        by fastforce
      moreover have \<open>\<dots> = n\<close>
        by simp
      ultimately show ?thesis
        by order
    qed
    then have Re: \<open>Re (trace_tc (\<EE> \<tau>)) \<ge> n\<close> for n :: nat
      using Re_mono by fastforce
    obtain n :: nat where \<open>n > Re (trace_tc (\<EE> \<tau>))\<close>
      apply atomize_elim
      by (rule reals_Archimedean2)
    with Re show False
      by (smt (verit, ccfv_threshold))
  qed
  then obtain B where bounded_B: \<open>norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close> and B_pos: \<open>B \<ge> 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    by auto
  have bounded: \<open>norm (\<EE> \<rho>) \<le> (4*B) * norm \<rho>\<close> for \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      and norm: \<open>norm \<rho>1 \<le> norm \<rho>\<close> \<open>norm \<rho>2 \<le> norm \<rho>\<close> \<open>norm \<rho>3 \<le> norm \<rho>\<close> \<open>norm \<rho>4 \<le> norm \<rho>\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (\<EE> \<rho>) \<le> norm (\<EE> \<rho>1) + norm (\<EE> \<rho>2) + norm (\<EE> \<rho>3) + norm (\<EE> \<rho>4)\<close>
      using linear
      by (auto intro!: norm_triangle_le norm_triangle_le_diff
          simp add: \<rho>_decomp kf_apply_plus_right kf_apply_minus_right
          kf_apply_scaleC complex_vector.linear_diff complex_vector.linear_add clinear.scaleC)
    also have \<open>\<dots> \<le> B * norm \<rho>1 + B * norm \<rho>2 + B * norm \<rho>3 + B * norm \<rho>4\<close>
      using pos by (auto intro!: add_mono simp add: pos bounded_B)
    also have \<open>\<dots> = B * (norm \<rho>1 + norm \<rho>2 + norm \<rho>3 + norm \<rho>4)\<close>
      by argo
    also have \<open>\<dots> \<le> B * (norm \<rho> + norm \<rho> + norm \<rho> + norm \<rho>)\<close>
      by (auto intro!: mult_left_mono add_mono pos B_pos
          simp only: norm)
    also have \<open>\<dots> = (4 * B) * norm \<rho>\<close>
      by argo
    finally show ?thesis
      by -
  qed
  show ?thesis
    apply (rule bounded_clinearI[where K=\<open>4*B\<close>])
      apply (simp add: complex_vector.linear_add linear) 
     apply (simp add: complex_vector.linear_scale linear) 
    using bounded by (metis Groups.mult_ac)
qed

lemma kf_reconstruction_is_kraus_family:
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> (\<lambda>a. (f a, a)) ` A\<close>
  shows \<open>kraus_family F\<close>
proof -
  from sum have \<open>bounded_clinear \<EE>\<close>
    by (rule kf_reconstruction_is_bounded_clinear)
  then obtain B where B: \<open>norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close> for \<rho>
    apply atomize_elim
    by (simp add: bounded_clinear_axioms_def bounded_clinear_def mult.commute)
  show ?thesis
  proof (intro kraus_familyI bdd_aboveI2)
    fix S assume \<open>S \<in> {S. finite S \<and> S \<subseteq> F}\<close>
    then have \<open>S \<subseteq> F\<close> and \<open>finite S\<close>
      by auto
    then obtain A' where \<open>finite A'\<close> and \<open>A' \<subseteq> A\<close> and S_A': \<open>S = (\<lambda>a. (f a,a)) ` A'\<close>
      by (metis (no_types, lifting) F_def finite_subset_image)
    show \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>C id_cblinfun\<close>
    proof (rule cblinfun_leI)
      fix h :: 'a assume \<open>norm h = 1\<close>
      have \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) h) = h \<bullet>\<^sub>C (\<Sum>a\<in>A'. (f a)* o\<^sub>C\<^sub>L f a) h\<close>
        by (simp add: S_A' sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>a\<in>A'. h \<bullet>\<^sub>C ((f a)* o\<^sub>C\<^sub>L f a) h)\<close>
        apply (rule complex_vector.linear_sum)
        by (simp add: bounded_clinear.clinear bounded_clinear_cinner_right_comp) 
      also have \<open>\<dots> = (\<Sum>a\<in>A'. trace_tc (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        by (auto intro!: sum.cong[OF refl]
            simp: trace_tc.rep_eq from_trace_class_sandwich_tc (* sandwich_apply *)
            tc_butterfly.rep_eq cblinfun_comp_butterfly sandwich_apply trace_butterfly_comp)
      also have \<open>\<dots> = trace_tc (\<Sum>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        apply (rule complex_vector.linear_sum[symmetric])
        using clinearI trace_tc_plus trace_tc_scaleC by blast
      also have \<open>\<dots> = trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        by (simp add: \<open>finite A'\<close>)
      also have \<open>\<dots> \<le> trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A. (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        apply (intro trace_tc_mono infsum_mono_neutral_traceclass)
        using \<open>A' \<subseteq> A\<close> sum[of \<open>tc_butterfly h h\<close>]
        by (auto intro!: sandwich_tc_pos has_sum_imp_summable simp: \<open>finite A'\<close>)
      also have \<open>\<dots> = trace_tc (\<EE> (tc_butterfly h h))\<close>
        by (metis sum infsumI)
      also have \<open>\<dots> = norm (\<EE> (tc_butterfly h h))\<close>
        by (metis (no_types, lifting) infsumI infsum_nonneg_traceclass norm_tc_pos sandwich_tc_pos sum tc_butterfly_pos)
      also from B have \<open>\<dots> \<le> B * norm (tc_butterfly h h)\<close>
        using complex_of_real_mono by blast
      also have \<open>\<dots> = B\<close>
        by (simp add: \<open>norm h = 1\<close> norm_tc_butterfly)
      also have \<open>\<dots> = h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        using \<open>norm h = 1\<close> cnorm_eq_1 by auto
      finally show \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) *\<^sub>V h) \<le> h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        by -
    qed
  qed
qed

lemma kf_reconstruction:
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> Abs_kraus_family ((\<lambda>a. (f a, a)) ` A)\<close>
  shows \<open>kf_apply F = \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  have Rep_F: \<open>Rep_kraus_family F = (\<lambda>a. (f a,a)) ` A\<close>
    unfolding F_def
    apply (rule Abs_kraus_family_inverse)
    by (auto intro!: kf_reconstruction_is_kraus_family[of _ _ \<EE>] assms simp: F_def)
  have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kf_apply F \<rho>) (Rep_kraus_family F)\<close>
    by (auto intro!: kf_apply_has_sum)
  then have \<open>((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kf_apply F \<rho>) A\<close>
    unfolding Rep_F
    apply (subst (asm) has_sum_reindex)
    by (auto simp: inj_on_def o_def)
  with sum show \<open>kf_apply F \<rho> = \<EE> \<rho>\<close>
    by (metis (no_types, lifting) infsumI)
qed

subsection \<open>Cleanup\<close>

unbundle no cblinfun_syntax
unbundle no kraus_map_syntax

end
