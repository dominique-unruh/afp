theory Trace_Class
  imports Complex_Bounded_Operators.Complex_L2 HS2Ell2
    Weak_Operator_Topology
    "HOL-Computational_Algebra.Formal_Power_Series"
    Positive_Operators
begin

unbundle cblinfun_notation

lemma parseval_infsum_aux1: 
  fixes h :: \<open>'a ell2\<close>
  assumes \<open>is_onb E\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
proof -
  define U h' where \<open>U = unitary_between (range ket) E\<close> and \<open>h' = U* *\<^sub>V h\<close>
  have [simp]: \<open>unitary U\<close>
    using U_def assms is_onb_ket unitary_between_unitary by blast
  have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (\<Sum>\<^sub>\<infinity>k\<in>range ket. (cmod (h \<bullet>\<^sub>C bij_between_bases (range ket) E k))\<^sup>2)\<close>
    apply (rule infsum_reindex_bij_betw[symmetric])
    using assms bij_between_bases_bij is_onb_ket by blast
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h \<bullet>\<^sub>C bij_between_bases (range ket) E (ket i)))\<^sup>2)\<close>
    apply (subst infsum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h \<bullet>\<^sub>C U (ket i)))\<^sup>2)\<close>
    by (simp add: U_def assms unitary_between_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h' \<bullet>\<^sub>C ket i))\<^sup>2)\<close>
    by (simp add: cinner_adj_left h'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (Rep_ell2 h' i))\<^sup>2)\<close>
    by (simp add: cinner_ket_right)
  also have \<open>\<dots> = (norm h')\<^sup>2\<close>
    by (simp add: ell2_norm_square norm_ell2.rep_eq)
  also have \<open>\<dots> = (norm h)\<^sup>2\<close>
    by (simp add: h'_def isometry_preserves_norm)
  finally show ?thesis
    by -
qed


lemma
  fixes h :: \<open>'b::{chilbert_space,not_singleton}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum_aux2: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  using c2l2l2[where 'a = 'b, transfer_rule] apply fail?
  using assms apply transfer
  by (rule parseval_infsum_aux1)

lemma 
  fixes h :: \<open>'b::{chilbert_space, CARD_1}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum_aux3: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  apply (subst everything_the_same[where y=0])
  by simp

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  apply (cases \<open>class.not_singleton TYPE('a)\<close>)
   apply (rule parseval_infsum_aux2[internalize_sort \<open>'b :: {chilbert_space,not_singleton}\<close>])
     apply (auto intro!: assms chilbert_space_axioms)[3]
   apply (rule parseval_infsum_aux3[internalize_sort \<open>'b :: {chilbert_space,CARD_1}\<close>])
  by (auto intro!: assms chilbert_space_axioms not_singleton_vs_CARD_1)

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_abs_summable: \<open>(\<lambda>e. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) abs_summable_on E\<close>
proof (cases \<open>h = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) \<noteq> 0\<close>
    by (simp add: assms parseval_infsum)
  then show ?thesis
    using infsum_not_exists by auto
qed

(* TODO: conway, op, 18.1 Proposition (part) *)
lemma TODO_name1:
  fixes E :: \<open>'a::complex_inner set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
proof
  assume asm: \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t\<close>
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    using asm infsumI by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using asm summable_on_def by auto
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    apply (subst sum1)
    apply (rule infsum_cong)
    using assms(2) by (rule parseval_infsum[symmetric])
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) abs_summable_on E\<close>
    using _ abs1 apply (rule summable_on_cong[THEN iffD2])
    apply (subst parseval_infsum)
    using assms(2) by auto
  have abs3: \<open>(\<lambda>(x, y). (cmod ((A *\<^sub>V x) \<bullet>\<^sub>C y))\<^sup>2) abs_summable_on E \<times> F\<close>
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2], rule conjI)
    using abs2 apply (auto simp del: real_norm_def)
    using assms(2) parseval_abs_summable apply blast
    by auto
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    apply (subst sum2)
    apply (subst infsum_Sigma'_banach[symmetric])
    using abs3 abs_summable_summable apply blast
    by auto
  then show \<open>has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
    using abs3 abs_summable_summable has_sum_infsum by blast
next
  assume asm: \<open>has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
  have abs3: \<open>(\<lambda>(x, y). (cmod ((A *\<^sub>V x) \<bullet>\<^sub>C y))\<^sup>2) abs_summable_on E \<times> F\<close>
    using asm summable_on_def summable_on_iff_abs_summable_on_real by blast
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    using asm infsumI by blast
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    by (metis (mono_tags, lifting) asm infsum_Sigma'_banach infsum_cong sum3 summable_iff_has_sum_infsum)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) abs_summable_on E\<close>
    by (smt (verit, del_insts) abs3 summable_on_Sigma_banach summable_on_cong summable_on_iff_abs_summable_on_real)
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    apply (subst sum2)
    apply (rule infsum_cong)
    using assms(2) parseval_infsum by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using abs2 assms(2) parseval_infsum by fastforce
  show \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t\<close>
    using abs1 sum1 by auto
qed

(* TODO: @{cite conway00operator}, op, 18.1 Proposition (2nd part) *)
lemma TODO_name2:
  fixes E :: \<open>'a::chilbert_space set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) F t\<close>
proof -
  have \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
    using TODO_name1 assms by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) (E\<times>F) t\<close>
    apply (subst cinner_adj_left) apply (subst cinner_commute)
    apply (subst complex_mod_cnj) by rule
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>(f,e). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) (F\<times>E) t\<close>
    apply (subst asm_rl[of \<open>F\<times>E = prod.swap ` (E\<times>F)\<close>])
     apply force
    apply (subst has_sum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) F t\<close>
    using TODO_name1 assms by blast
  finally show ?thesis
    by -
qed

(* TODO: conway op, 18.2 Corollary *)
lemma trace_norm_basis_invariance:
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) E t \<longleftrightarrow> has_sum (\<lambda>f. cmod ((abs_op A *\<^sub>V f) \<bullet>\<^sub>C f)) F t\<close>
proof -
  define B where \<open>B = sqrt_op (abs_op A)\<close>
  have \<open>complex_of_real (cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) = (B* *\<^sub>V B*\<^sub>V e) \<bullet>\<^sub>C e\<close> for e
    apply (simp add: B_def flip: cblinfun_apply_cblinfun_compose)
    by (metis (no_types, lifting) abs_op_pos cblinfun.zero_left cinner_commute cinner_zero_right complex_cnj_complex_of_real complex_of_real_cmod less_eq_cblinfun_def)
  also have \<open>\<dots> e = complex_of_real ((norm (B *\<^sub>V e))\<^sup>2)\<close> for e
    apply (subst cdot_square_norm[symmetric])
    apply (subst cinner_adj_left[symmetric])
    by (simp add: B_def)
  finally have *: \<open>cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e) = (norm (B *\<^sub>V e))\<^sup>2\<close> for e
    by (metis Re_complex_of_real)

  have \<open>has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) E t \<longleftrightarrow> has_sum (\<lambda>e. (norm (B *\<^sub>V e))\<^sup>2) E t\<close>
    by (simp add: *)
  also have \<open>\<dots> = has_sum (\<lambda>f. (norm (B* *\<^sub>V f))\<^sup>2) F t\<close>
    apply (subst TODO_name2[where F=F])
    by (simp_all add: assms)
  also have \<open>\<dots> = has_sum (\<lambda>f. (norm (B *\<^sub>V f))\<^sup>2) F t\<close>
    using TODO_name2 assms(2) by blast
  also have \<open>\<dots> = has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) F t\<close>
    by (simp add: *)
  finally show ?thesis
    by simp
qed

definition trace_class :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> bool\<close> 
  where \<open>trace_class A \<longleftrightarrow> (\<exists>E. is_onb E \<and> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E)\<close>

lemma trace_classI:
  assumes \<open>is_onb E\<close> and \<open>(\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E\<close>
  shows \<open>trace_class A\<close>
  using assms(1) assms(2) trace_class_def by blast

lemma trace_class_iff_summable:
  assumes \<open>is_onb E\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E\<close>
  apply (auto intro!: trace_classI assms simp: trace_class_def)
  using assms summable_on_def trace_norm_basis_invariance by blast

lemma trace_class_0[simp]: \<open>trace_class 0\<close>
  unfolding trace_class_def
  by (auto intro!: exI[of _ some_chilbert_basis] simp: is_onb_def is_normal_some_chilbert_basis)

lemma trace_class_adj: \<open>trace_class a \<Longrightarrow> trace_class (a*)\<close>
  sorry

lemma trace_class_plus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t + u)\<close>
  sorry

lemma trace_class_uminus[simp]: \<open>trace_class t \<Longrightarrow> trace_class (-t)\<close>
  by (auto simp add: trace_class_def)

lemma trace_class_minus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t - u)\<close>
  by (metis trace_class_plus trace_class_uminus uminus_add_conv_diff)

definition trace_norm where \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) else 0)\<close>

definition trace where \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>

lemma trace_0[simp]: \<open>trace 0 = 0\<close>
  unfolding trace_def by simp

lemma trace_class_abs_op[simp]: \<open>trace_class (abs_op A) = trace_class A\<close>
  unfolding trace_class_def
  by simp

lemma trace_abs_op[simp]: \<open>trace (abs_op A) = trace_norm A\<close>
proof (cases \<open>trace_class A\<close>)
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis 
    by (simp add: trace_def trace_norm_def)
qed

lemma trace_norm_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) else 0)\<close>
  by (metis (mono_tags, lifting) assms infsum_eqI' is_onb_some_chilbert_basis trace_norm_basis_invariance trace_norm_def)

lemma trace_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
  sorry

lemma trace_exists:
  assumes \<open>is_onb B\<close> and \<open>trace_class A\<close>
  shows \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) summable_on B\<close>
  sorry

lemma trace_class_finite_dim[simp]: \<open>trace_class A\<close> for A :: \<open>'a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  apply (subst trace_class_iff_summable[of some_chilbert_basis])
  by (auto intro!: summable_on_finite)

lemma trace_class_finite_dim'[simp]: \<open>trace_class A\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}\<close>
  by (metis double_adj trace_class_adj trace_class_finite_dim)

lemma circularity_of_trace:
  assumes \<open>trace_class a\<close>
    \<comment> \<open>Actually, \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b) \<and> trace_class (b o\<^sub>C\<^sub>L a)\<close> is sufficient here, 
        see @{cite "mathoverflow-circ-trace2"} but the proof is more involved.
        Only \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> is not sufficient, 
        see @{cite "mathoverflow-circ-trace1"}.\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
  sorry

lemma trace_class_comp_left: \<open>trace_class a \<Longrightarrow> trace_class (a o\<^sub>C\<^sub>L b)\<close>
  sorry

lemma trace_class_comp_right: \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class b\<close>
  sorry

lemma trace_norm_comp_left: \<open>trace_class a \<Longrightarrow> trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
  sorry

lemma trace_norm_comp_right: \<open>trace_class b \<Longrightarrow> trace_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * trace_norm b\<close>
  sorry

lemma trace_plus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a + b) = trace a + trace b\<close> 
  by (auto simp add: assms trace_exists infsum_add trace_def cblinfun.add_left cinner_add_right)

lemma trace_scaleC: \<open>trace (c *\<^sub>C a) = c * trace a\<close>
proof -
  consider (trace_class) \<open>trace_class a\<close> | (c0) \<open>c = 0\<close> | (non_trace_class) \<open>\<not> trace_class a\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case trace_class
    then show ?thesis sorry
  next
    case c0
    then show ?thesis 
      by simp
  next
    case non_trace_class
    then have \<open>\<not> trace_class (c *\<^sub>C a)\<close>
      by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right complex_vector.vector_space_assms(3) complex_vector.vector_space_assms(4) left_inverse trace_class_comp_left)
    with non_trace_class show ?thesis
      by (simp add: trace_def)
  qed
qed

(* TODO remove (duplicate of trace_class_iff_summable) *)
lemma trace_class_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on B\<close>
  using assms trace_class_iff_summable by blast

lemma trace_class_butterfly[simp]: \<open>trace_class (butterfly x y)\<close> for x :: \<open>'a::complex_inner\<close> and y :: \<open>'b::chilbert_space\<close>
  unfolding butterfly_def
  apply (rule trace_class_comp_left)
  by simp

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

lemma trace_butterfly_comp: \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
proof -
  have \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = trace (vector_to_cblinfun y* o\<^sub>C\<^sub>L (a o\<^sub>C\<^sub>L (vector_to_cblinfun x :: complex \<Rightarrow>\<^sub>C\<^sub>L _)))\<close>
    unfolding butterfly_def
    by (metis butterfly_def_one_dim cblinfun_compose_assoc circularity_of_trace trace_class_finite_dim)
  also have \<open>\<dots> = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
    by (simp add: one_dim_iso_cblinfun_comp)
  finally show ?thesis
    by -
qed

lemma trace_butterfly: \<open>trace (butterfly x y) = y \<bullet>\<^sub>C x\<close>
  using trace_butterfly_comp[where a=id_cblinfun] by auto

lemma trace_norm_0[simp]: \<open>trace_norm 0 = 0\<close>
  by (metis abs_op_0 of_real_eq_0_iff trace_0 trace_abs_op)

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
  have summable: \<open>(\<lambda>e. (abs_op a *\<^sub>V e) \<bullet>\<^sub>C e) abs_summable_on B\<close>
    using trace_class_iff_summable by fastforce

  from that have \<open>0 = trace_norm a\<close>
    by simp
  also from \<open>is_onb B\<close> have \<open>trace_norm a = (\<Sum>\<^sub>\<infinity>e\<in>B. cmod ((abs_op a *\<^sub>V e) \<bullet>\<^sub>C e))\<close>
    by (smt (verit, ccfv_SIG) abs_norm_cancel infsum_cong infsum_not_exists real_norm_def trace_class_def trace_norm_alt_def)
  also have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>e\<in>{sgn x}. cmod ((abs_op a *\<^sub>V e) \<bullet>\<^sub>C e))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono2)
    using summable sgnx_B by auto
  also from xax' have \<open>\<dots> > 0\<close>
    by (simp add: is_orthogonal_sym xax')
  finally show False
    by simp
qed

lemma
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows trace_sum: \<open>trace (\<Sum>i\<in>I. a i) = (\<Sum>i\<in>I. trace (a i))\<close>
    and trace_class_sum: \<open>trace_class (\<Sum>i\<in>I. a i)\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by (auto simp: trace_plus)

lemma trace_leq_trace_norm[simp]: \<open>cmod (trace a) \<le> trace_norm a\<close>
  sorry

lemma bounded_clinear_trace_duality: \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (t o\<^sub>C\<^sub>L a))\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
  apply (auto simp add: cblinfun_compose_add_right trace_class_comp_left trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

typedef (overloaded) 'a::chilbert_space trace_class = \<open>Collect trace_class :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_trace_class

instantiation trace_class :: (chilbert_space) "{complex_vector}" begin
(* Lifted definitions *)
lift_definition zero_trace_class :: \<open>'a trace_class\<close> is 0 by auto
lift_definition minus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is minus by auto
lift_definition uminus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class\<close> is uminus by auto
lift_definition plus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is plus by auto
lift_definition scaleC_trace_class :: \<open>complex \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is scaleC
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq trace_class_comp_left)
lift_definition scaleR_trace_class :: \<open>real \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is scaleR
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq scaleR_scaleC trace_class_comp_left)
instance
proof standard
  fix a b c :: \<open>'a trace_class\<close>
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
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: _ \<Rightarrow> 'a trace_class)\<close> for r :: real
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

instantiation trace_class :: (chilbert_space) "{complex_normed_vector}" begin
(* Definitions related to the trace norm *)
lift_definition norm_trace_class :: \<open>'a trace_class \<Rightarrow> real\<close> is trace_norm .
definition sgn_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class\<close> where \<open>sgn_trace_class a = a /\<^sub>R norm a\<close>
definition dist_trace_class :: \<open>'a trace_class \<Rightarrow> _ \<Rightarrow> _\<close> where \<open>dist_trace_class a b = norm (a - b)\<close>
definition [code del]: "uniformity_trace_class = (INF e\<in>{0<..}. principal {(x::'a trace_class, y). dist x y < e})"
definition [code del]: "open_trace_class U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a trace_class set"
instance
proof standard
  fix a b :: \<open>'a trace_class\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (metis (no_types, lifting) Trace_Class.dist_trace_class_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x :: 'a trace_class, y). dist x y < e})\<close>
    by (simp add: uniformity_trace_class_def)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>'a trace_class set\<close>
    by (smt (verit, del_insts) case_prod_beta' eventually_mono open_trace_class_def uniformity_trace_class_def)
  show \<open>(norm a = 0) = (a = 0)\<close>
    apply transfer
    by (auto simp add: trace_norm_nondegenerate)
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer
    apply auto
    sorry
  show \<open>norm (r *\<^sub>C a) = cmod r * norm a\<close> for r
    apply transfer
    apply auto
    sorry
  then show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r
    by (metis norm_of_real scaleR_scaleC)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_trace_class_def)
qed
end

definition hilbert_schmidt where \<open>hilbert_schmidt a \<longleftrightarrow> trace_class (a* o\<^sub>C\<^sub>L a)\<close>

definition hilbert_schmidt_norm where \<open>hilbert_schmidt_norm a = sqrt (trace_norm (a* o\<^sub>C\<^sub>L a))\<close>

lemma hilbert_schmidt_0[simp]: \<open>hilbert_schmidt 0\<close>
  unfolding hilbert_schmidt_def by simp

typedef (overloaded) ('a::chilbert_space,'b::complex_inner) hilbert_schmidt = \<open>Collect hilbert_schmidt :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_hilbert_schmidt

instantiation hilbert_schmidt :: (chilbert_space, complex_inner) "{zero,norm}" begin
lift_definition zero_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt\<close> is 0 by auto
lift_definition norm_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> real\<close> is hilbert_schmidt_norm .
instance..
end

end
