theory Unsorted1
  imports Trace_Class Tensor_Product.Compact_Operators
    Tensor_Product.Misc_Tensor_Product_TTS
begin






definition invariant_subspace :: \<open>'a::complex_inner ccsubspace \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>invariant_subspace S A \<longleftrightarrow> A *\<^sub>S S \<le> S\<close>

lemma invariant_subspaceI: \<open>A *\<^sub>S S \<le> S \<Longrightarrow> invariant_subspace S A\<close>
  by (simp add: invariant_subspace_def)

definition reducing_subspace :: \<open>'a::complex_inner ccsubspace \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>reducing_subspace S A \<longleftrightarrow> invariant_subspace S A \<and> invariant_subspace (-S) A\<close>

lemma reducing_subspaceI: \<open>A *\<^sub>S S \<le> S \<Longrightarrow> A *\<^sub>S (-S) \<le> -S \<Longrightarrow> reducing_subspace S A\<close>
  by (simp add: reducing_subspace_def invariant_subspace_def)

lemma reducing_subspace_ortho[simp]: \<open>reducing_subspace (-S) A \<longleftrightarrow> reducing_subspace S A\<close>
  for S :: \<open>'a::chilbert_space ccsubspace\<close>
  by (auto intro!: simp: reducing_subspace_def ortho_involution)

lemma invariant_subspace_bot[simp]: \<open>invariant_subspace \<bottom> A\<close>
  by (simp add: invariant_subspaceI) 

lemma invariant_subspace_top[simp]: \<open>invariant_subspace \<top> A\<close>
  by (simp add: invariant_subspaceI) 

lemma reducing_subspace_bot[simp]: \<open>reducing_subspace \<bottom> A\<close>
  by (metis cblinfun_image_bot eq_refl orthogonal_bot orthogonal_spaces_leq_compl reducing_subspaceI) 

lemma reducing_subspace_top[simp]: \<open>reducing_subspace \<top> A\<close>
  by (simp add: reducing_subspace_def)

definition normal_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>normal_op A  \<longleftrightarrow>  A o\<^sub>C\<^sub>L A* = A* o\<^sub>C\<^sub>L A\<close>

definition eigenvalues :: \<open>('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> complex set\<close> where
  \<open>eigenvalues a = {x. eigenspace x a \<noteq> 0}\<close>

lemma eigenvalues_0[simp]: \<open>eigenvalues (0 :: 'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'a) = {0}\<close>
  apply (auto intro!: simp: eigenvalues_def eigenspace_def)
  by (metis id_cblinfun_eq_1 kernel_id kernel_scaleC of_complex_def scaleC_minus1_left zero_ccsubspace_def zero_neq_neg_one)

lemma nonzero_ccsubspace_contains_unit_vector:
  assumes \<open>S \<noteq> 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<in> space_as_set S \<and> norm \<psi> = 1\<close>
proof -
  from assms 
  obtain \<psi> where \<open>\<psi> \<in> space_as_set S\<close> and \<open>\<psi> \<noteq> 0\<close>
    apply transfer
    by (auto simp: complex_vector.subspace_0)
  then have \<open>sgn \<psi> \<in> space_as_set S\<close> and \<open>norm (sgn \<psi>) = 1\<close>
     apply (simp add: complex_vector.subspace_scale scaleR_scaleC sgn_div_norm)
    by (simp add: \<open>\<psi> \<noteq> 0\<close> norm_sgn)
  then show ?thesis
    by auto
qed

lemma unit_eigenvector_ex: 
  assumes \<open>x \<in> eigenvalues a\<close>
  shows \<open>\<exists>h. norm h = 1 \<and> a h = x *\<^sub>C h\<close>
proof -
  from assms have \<open>eigenspace x a \<noteq> 0\<close>
    by (simp add: eigenvalues_def)
  then obtain \<psi> where \<psi>_ev: \<open>\<psi> \<in> space_as_set (eigenspace x a)\<close> and \<open>\<psi> \<noteq> 0\<close>
    using nonzero_ccsubspace_contains_unit_vector by force
  define h where \<open>h = sgn \<psi>\<close>
  with \<open>\<psi> \<noteq> 0\<close> have \<open>norm h = 1\<close>
    by (simp add: norm_sgn)
  from \<psi>_ev have \<open>h \<in> space_as_set (eigenspace x a)\<close>
    by (simp add: h_def sgn_in_spaceI)
  then have \<open>a *\<^sub>V h = x *\<^sub>C h\<close>
    unfolding eigenspace_def
    apply (transfer' fixing: x)
    by simp
  with \<open>norm h = 1\<close> show ?thesis
    by auto    
qed


lemma eigenvalue_norm_bound:
  assumes \<open>e \<in> eigenvalues a\<close>
  shows \<open>norm e \<le> norm a\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ah_eh: \<open>a h = e *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>cmod e = norm (e *\<^sub>C h)\<close>
    by (simp add: \<open>norm h = 1\<close>)
  also have \<open>\<dots> = norm (a h)\<close>
    using ah_eh by presburger
  also have \<open>\<dots> \<le> norm a\<close>
    by (metis \<open>norm h = 1\<close> cblinfun.real.bounded_linear_right mult_cancel_left1 norm_cblinfun.rep_eq onorm)
  finally show \<open>cmod e \<le> norm a\<close>
    by -
qed

lemma eigenvalue_selfadj_real:
  assumes \<open>e \<in> eigenvalues a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>e \<in> \<real>\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ah_eh: \<open>a h = e *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>e = h \<bullet>\<^sub>C (e *\<^sub>C h)\<close>
    by (metis \<open>norm h = 1\<close> cinner_simps(6) mult_cancel_left1 norm_one one_cinner_one power2_norm_eq_cinner power2_norm_eq_cinner)
  also have \<open>\<dots> = h \<bullet>\<^sub>C a h\<close>
    by (simp add: ah_eh)
  also from assms(2) have \<open>\<dots> \<in> \<real>\<close>
    using cinner_hermitian_real selfadjoint_def by blast
  finally show \<open>e \<in> \<real>\<close>
    by -
qed

lemma is_Sup_imp_ex_tendsto:
  fixes X :: \<open>'a::{linorder_topology,first_countable_topology} set\<close>
  assumes sup: \<open>is_Sup X l\<close>
  assumes \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>f. range f \<subseteq> X \<and> f \<longlonglongrightarrow> l\<close>
proof (cases \<open>\<exists>x. x < l\<close>)
  case True
  obtain A :: \<open>nat \<Rightarrow> 'a set\<close> where openA: \<open>open (A n)\<close> and lA: \<open>l \<in> A n\<close>
    and fl: \<open>(\<And>n. f n \<in> A n) \<Longrightarrow> f \<longlonglongrightarrow> l\<close> for n f
    apply (rule Topological_Spaces.countable_basis[of l])
    by blast
  obtain f where fAX: \<open>f n \<in> A n \<inter> X\<close> for n
  proof (atomize_elim, intro choice allI)
    fix n :: nat
    from True obtain x where \<open>x < l\<close>
      by blast
    from open_left[OF openA lA this]
    obtain b where \<open>b < l\<close> and bl_A: \<open>{b<..l} \<subseteq> A n\<close>
      by blast
    from sup \<open>b < l\<close> obtain x where \<open>x \<in> X\<close> and \<open>x > b\<close>
      by (meson is_Sup_def leD leI)
    from \<open>x \<in> X\<close> sup have \<open>x \<le> l\<close>
      by (simp add: is_Sup_def)
    from \<open>x \<le> l\<close> and \<open>x > b\<close> and bl_A
    have \<open>x \<in> A n\<close>
      by fastforce
    with \<open>x \<in> X\<close>
    show \<open>\<exists>x. x \<in> A n \<inter> X\<close>
      by blast
  qed
  with fl have \<open>f \<longlonglongrightarrow> l\<close>
    by auto
  moreover from fAX have \<open>range f \<subseteq> X\<close>
    by auto
  ultimately show ?thesis
    by blast
next
  case False
  from \<open>X \<noteq> {}\<close> obtain x where \<open>x \<in> X\<close>
    by blast
  with \<open>is_Sup X l\<close> have \<open>x \<le> l\<close>
    by (simp add: is_Sup_def)
  with False have \<open>x = l\<close>
    using basic_trans_rules(17) by auto
  with \<open>x \<in> X\<close> have \<open>l \<in> X\<close>
    by simp
  define f where \<open>f n = l\<close> for n :: nat
  then have \<open>f \<longlonglongrightarrow> l\<close>
    by (auto intro!: simp: f_def[abs_def])
  moreover from \<open>l \<in> X\<close> have \<open>range f \<subseteq> X\<close>
    by (simp add: f_def)
  ultimately show ?thesis
    by blast
qed

lemma eigenvaluesI:
  assumes \<open>A *\<^sub>V h = e *\<^sub>C h\<close>
  assumes \<open>h \<noteq> 0\<close>
  shows \<open>e \<in> eigenvalues A\<close>
proof -
  from assms have \<open>h \<in> space_as_set (eigenspace e A)\<close>
    by (simp add: eigenspace_def kernel.rep_eq cblinfun.diff_left)
  moreover from \<open>h \<noteq> 0\<close> have \<open>h \<notin> space_as_set \<bottom>\<close>
    apply transfer by simp
  ultimately have \<open>eigenspace e A \<noteq> \<bottom>\<close>
    by fastforce
  then show ?thesis
    by (simp add: eigenvalues_def)
qed

lemma tendsto_diff_const_left_rewrite:
  fixes c d :: \<open>'a::{topological_group_add, ab_group_add}\<close>
  assumes \<open>((\<lambda>x. f x) \<longlongrightarrow> c - d) F\<close>
  shows \<open>((\<lambda>x. c - f x) \<longlongrightarrow> d) F\<close>
  by (auto intro!: assms tendsto_eq_intros)

lemma not_not_singleton_no_eigenvalues:
  fixes a :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>eigenvalues a = {}\<close>
proof auto
  fix e assume \<open>e \<in> eigenvalues a\<close>
  then have \<open>eigenspace e a \<noteq> \<bottom>\<close>
    by (simp add: eigenvalues_def) 
  then obtain h where \<open>norm h = 1\<close> and \<open>h \<in> space_as_set (eigenspace e a)\<close>
    using nonzero_ccsubspace_contains_unit_vector by auto 
  from assms have \<open>h = 0\<close>
    by (rule not_not_singleton_zero)
  with \<open>norm h = 1\<close>
  show False
    by simp
qed

lemma csubspace_has_basis:
  assumes \<open>csubspace S\<close>
  shows \<open>\<exists>B. cindependent B \<and> cspan B = S\<close>
proof -
  from \<open>csubspace S\<close>
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    apply (rule_tac complex_vector.maximal_independent_subset[where V=S])
    using complex_vector.span_subspace by blast
  then show ?thesis
    by auto
qed

lemma cblinfun_cinner_eq0I:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>h. h \<bullet>\<^sub>C a h = 0\<close>
  shows \<open>a = 0\<close>
  apply (rule cblinfun_cinner_eqI)
  using assms by simp

lemma normal_op_iff_adj_same_norms:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.2.16\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  shows \<open>normal_op a \<longleftrightarrow> (\<forall>h. norm (a h) = norm ((a*) h))\<close>
proof -
  have aux: \<open>(\<And>h. a h = b h) ==> (\<forall>h. a h = (0::complex)) \<longleftrightarrow> (\<forall>h. b h = (0::real))\<close> for a :: \<open>'a \<Rightarrow> complex\<close> and b :: \<open>'a \<Rightarrow> real\<close>
    by simp
  have \<open>normal_op a \<longleftrightarrow> (a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*) = 0\<close>
    using normal_op_def by force
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h = 0)\<close>
    by (auto intro!: cblinfun_cinner_eqI simp: cblinfun.diff_left cinner_diff_right
        simp flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. (norm (a h))\<^sup>2 - (norm ((a*) h))\<^sup>2 = 0)\<close>
  proof (rule aux)
    fix h
    have \<open>(norm (a *\<^sub>V h))\<^sup>2 - (norm (a* *\<^sub>V h))\<^sup>2
        = (a *\<^sub>V h) \<bullet>\<^sub>C (a *\<^sub>V h) - (a* *\<^sub>V h) \<bullet>\<^sub>C (a* *\<^sub>V h)\<close>
      by (simp add: of_real_diff flip: cdot_square_norm of_real_power)
    also have \<open>\<dots> = h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h\<close>
      by (simp add: cblinfun.diff_left cinner_diff_right cinner_adj_left
          cinner_adj_right flip: cinner_adj_left)
    finally show \<open>h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h = (norm (a *\<^sub>V h))\<^sup>2 - (norm (a* *\<^sub>V h))\<^sup>2\<close>
      by simp
  qed
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. norm (a h) = norm ((a*) h))\<close>
    by simp
  finally show ?thesis.
qed


lemma normal_op_same_eigenspace_as_adj:
  \<comment> \<open>Shown inside the proof of \<^cite>\<open>"Proposition II.5.6" in conway2013course\<close>\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>eigenspace l a = eigenspace (cnj l) (a* )\<close>
proof -
  from \<open>normal_op a\<close>
  have \<open>normal_op (a - l *\<^sub>C id_cblinfun)\<close>
    by (auto intro!: simp: normal_op_def cblinfun_compose_minus_left
        cblinfun_compose_minus_right adj_minus scaleC_diff_right)
  then have *: \<open>norm ((a - l *\<^sub>C id_cblinfun) h) = norm (((a - l *\<^sub>C id_cblinfun)*) h)\<close> for h
    using normal_op_iff_adj_same_norms by blast
  show ?thesis
  proof (rule ccsubspace_eqI)
    fix h
    have \<open>h \<in> space_as_set (eigenspace l a) \<longleftrightarrow> norm ((a - l *\<^sub>C id_cblinfun) h) = 0\<close>
      by (simp add: eigenspace_def kernel_member_iff)
    also have \<open>\<dots> \<longleftrightarrow> norm (((a*) - cnj l *\<^sub>C id_cblinfun) h) = 0\<close>
      by (simp add: "*" adj_minus)
    also have \<open>\<dots> \<longleftrightarrow> h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>
      by (simp add: eigenspace_def kernel_member_iff)
    finally show \<open>h \<in> space_as_set (eigenspace l a) \<longleftrightarrow> h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>.
  qed
qed

lemma normal_op_adj_eigenvalues: 
  assumes \<open>normal_op a\<close>
  shows \<open>eigenvalues (a*) = cnj ` eigenvalues a\<close>
  by (auto intro!: complex_cnj_cnj[symmetric] image_eqI
      simp: eigenvalues_def assms normal_op_same_eigenspace_as_adj)

lemma invariant_subspace_iff_PAP:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (b)\<close>
  \<open>invariant_subspace S A \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L Proj S = A o\<^sub>C\<^sub>L Proj S\<close>
proof -
  define S' where \<open>S' = space_as_set S\<close>
  have \<open>invariant_subspace S A \<longleftrightarrow> (\<forall>h\<in>S'. A h \<in> S')\<close>
    apply (auto simp: S'_def invariant_subspace_def less_eq_ccsubspace_def
        Set.basic_monos(7) cblinfun_apply_in_image')
    by (meson cblinfun_image_less_eqI less_eq_ccsubspace.rep_eq subsetD)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. A *\<^sub>V Proj S *\<^sub>V h \<in> S')\<close>
    by (metis (no_types, lifting) Proj_fixes_image Proj_range S'_def cblinfun_apply_in_image)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. Proj S *\<^sub>V A *\<^sub>V Proj S *\<^sub>V h = A *\<^sub>V Proj S *\<^sub>V h)\<close>
    using Proj_fixes_image S'_def space_as_setI_via_Proj by blast
  also have \<open>\<dots> \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L Proj S = A o\<^sub>C\<^sub>L Proj S\<close>
    by (auto intro!: cblinfun_eqI simp: 
        simp flip: cblinfun_apply_cblinfun_compose cblinfun_compose_assoc)
  finally show ?thesis
    by -
qed

lemma reducing_iff_PA:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (e)\<close>
  \<open>reducing_subspace S A \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L Proj S\<close>
proof (rule iffI)
  assume red: \<open>reducing_subspace S A\<close>
  define P where \<open>P = Proj S\<close>
  from red have AP: \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P\<close>
    by (simp add: invariant_subspace_iff_PAP reducing_subspace_def P_def) 
  from red have \<open>reducing_subspace (- S) A\<close>
    by simp 
  then have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (id_cblinfun - P) = A o\<^sub>C\<^sub>L (id_cblinfun - P)\<close>
    using invariant_subspace_iff_PAP[of \<open>- S\<close>] reducing_subspace_def P_def Proj_ortho_compl
    by metis
  then have \<open>P o\<^sub>C\<^sub>L A = P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P\<close>
    by (simp add: cblinfun_compose_minus_left cblinfun_compose_minus_right) 
  with AP show \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close>
    by simp
next
  define P where \<open>P = Proj S\<close>
  assume \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close>
  then have \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P o\<^sub>C\<^sub>L P\<close>
    by simp
  then have \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P\<close>
    by (metis P_def Proj_idempotent cblinfun_assoc_left(1)) 
  then have \<open>invariant_subspace S A\<close>
    by (simp add: P_def invariant_subspace_iff_PAP) 
  have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (id_cblinfun - P) = A o\<^sub>C\<^sub>L (id_cblinfun - P)\<close>
    by (metis (no_types, opaque_lifting) P_def Proj_idempotent Proj_ortho_compl \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close> cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_minus_left cblinfun_compose_minus_right) 
  then have \<open>invariant_subspace (- S) A\<close>
    by (simp add: P_def Proj_ortho_compl invariant_subspace_iff_PAP) 
  with \<open>invariant_subspace S A\<close>
  show \<open>reducing_subspace S A\<close>
    using reducing_subspace_def by blast 
qed

lemma reducing_iff_also_adj_invariant:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (g)\<close>
  shows \<open>reducing_subspace S A \<longleftrightarrow> invariant_subspace S A \<and> invariant_subspace S (A*)\<close>
proof (intro iffI conjI; (erule conjE)?)
  assume \<open>invariant_subspace S A\<close> and \<open>invariant_subspace S (A*)\<close>
  have \<open>invariant_subspace (- S) A\<close>
  proof (intro invariant_subspaceI cblinfun_image_less_eqI)
    fix h assume \<open>h \<in> space_as_set (- S)\<close>
    show \<open>A *\<^sub>V h \<in> space_as_set (- S)\<close>
    proof (unfold uminus_ccsubspace.rep_eq, intro orthogonal_complementI)
      fix g assume \<open>g \<in> space_as_set S\<close>
      with \<open>invariant_subspace S (A*)\<close> have \<open>(A*) g \<in> space_as_set S\<close>
        by (metis Proj_compose_cancelI Proj_range cblinfun_apply_in_image' cblinfun_fixes_range invariant_subspace_def space_as_setI_via_Proj) 
      have \<open>A h \<bullet>\<^sub>C g = h \<bullet>\<^sub>C (A*) g\<close>
        by (simp add: cinner_adj_right)
      also from \<open>(A*) g \<in> space_as_set S\<close> and \<open>h \<in> space_as_set (- S)\<close>
      have \<open>\<dots> = 0\<close>
        using orthogonal_spaces_def orthogonal_spaces_leq_compl by blast 
      finally show \<open>A h \<bullet>\<^sub>C g = 0\<close>
        by blast
    qed
  qed
  with \<open>invariant_subspace S A\<close>
  show \<open>reducing_subspace S A\<close>
    using reducing_subspace_def by blast 
next
  assume \<open>reducing_subspace S A\<close>
  then show \<open>invariant_subspace S A\<close>
    using reducing_subspace_def by blast 
  show \<open>invariant_subspace S (A*)\<close>
    by (metis \<open>reducing_subspace S A\<close> adj_Proj adj_cblinfun_compose reducing_iff_PA reducing_subspace_def) 
qed

lemma eigenspace_is_reducing:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.5.6\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>reducing_subspace (eigenspace l a) a\<close>
proof (unfold reducing_iff_also_adj_invariant invariant_subspace_def,
    intro conjI cblinfun_image_less_eqI subsetI)
  fix h
  assume h_eigen: \<open>h \<in> space_as_set (eigenspace l a)\<close>
  then have \<open>a h = l *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD)
  also have \<open>\<dots> \<in> space_as_set (eigenspace l a)\<close>
    by (simp add: Proj_fixes_image cblinfun.scaleC_right h_eigen space_as_setI_via_Proj)
  finally show \<open>a h \<in> space_as_set (eigenspace l a)\<close>.
next
  fix h
  assume h_eigen: \<open>h \<in> space_as_set (eigenspace l a)\<close>
  then have \<open>h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>
    by (simp add: assms normal_op_same_eigenspace_as_adj)
  then have \<open>(a*) h = cnj l *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD)
  also have \<open>\<dots> \<in> space_as_set (eigenspace l a)\<close>
    by (simp add: Proj_fixes_image cblinfun.scaleC_right h_eigen space_as_setI_via_Proj)
  finally show \<open>(a*) h \<in> space_as_set (eigenspace l a)\<close>.
qed

lemma invariant_subspace_Inf:
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> invariant_subspace S a\<close>
  shows \<open>invariant_subspace (\<Sqinter>M) a\<close>
proof (rule invariant_subspaceI)
  have \<open>a *\<^sub>S \<Sqinter> M \<le> (\<Sqinter>S\<in>M. a *\<^sub>S S)\<close>
    using cblinfun_image_INF_leq[where U=a and V=id and X=M] by simp
  also have \<open>\<dots> \<le> (\<Sqinter>S\<in>M. S)\<close>
    apply (rule INF_superset_mono, simp)
    using assms by (auto simp: invariant_subspace_def)
  also have \<open>\<dots> = \<Sqinter>M\<close>
    by simp
  finally show \<open>a *\<^sub>S \<Sqinter> M \<le> \<Sqinter> M\<close> .
qed

lemma invariant_subspace_INF:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> invariant_subspace (S x) a\<close>
  shows \<open>invariant_subspace (\<Sqinter>x\<in>X. S x) a\<close>
  by (smt (verit) assms imageE invariant_subspace_Inf)

lemma invariant_subspace_Sup:
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> invariant_subspace S a\<close>
  shows \<open>invariant_subspace (\<Squnion>M) a\<close>
proof -
  have *: \<open>a ` cspan (\<Union>S\<in>M. space_as_set S) \<subseteq> space_as_set (\<Squnion>M)\<close>
  proof (rule image_subsetI)
    fix h
    assume \<open>h \<in> cspan (\<Union>S\<in>M. space_as_set S)\<close>
    then obtain F r where \<open>h = (\<Sum>g\<in>F. r g *\<^sub>C g)\<close> and F_in_union: \<open>F \<subseteq> (\<Union>S\<in>M. space_as_set S)\<close>
      by (auto intro!: simp: complex_vector.span_explicit)
    then have \<open>a h = (\<Sum>g\<in>F. r g *\<^sub>C a g)\<close>
      by (simp add: cblinfun.scaleC_right cblinfun.sum_right)
    also have \<open>\<dots> \<in> space_as_set (\<Squnion>M)\<close>
    proof (rule complex_vector.subspace_sum)
      show \<open>csubspace (space_as_set (\<Squnion> M))\<close>
        by simp
      fix g assume \<open>g \<in> F\<close>
      then obtain S where \<open>S \<in> M\<close> and \<open>g \<in> space_as_set S\<close>
        using F_in_union by auto
      from assms[OF \<open>S \<in> M\<close>] \<open>g \<in> space_as_set S\<close>
      have \<open>a g \<in> space_as_set S\<close>
        by (simp add: Set.basic_monos(7) cblinfun_apply_in_image' invariant_subspace_def less_eq_ccsubspace.rep_eq)
      also from \<open>S \<in> M\<close>have \<open>\<dots> \<subseteq> space_as_set (\<Squnion> M)\<close>
        by (meson Sup_upper less_eq_ccsubspace.rep_eq)
      finally show \<open>r g *\<^sub>C (a g) \<in> space_as_set (\<Squnion> M)\<close>
        by (simp add: complex_vector.subspace_scale)
    qed
    finally show \<open>a h \<in> space_as_set (\<Squnion>M)\<close>.
  qed
  have \<open>space_as_set (a *\<^sub>S \<Squnion>M) = closure (a ` closure (cspan (\<Squnion>S\<in>M. space_as_set S)))\<close>
    by (metis Sup_ccsubspace.rep_eq cblinfun_image.rep_eq)
  also have \<open>\<dots> = closure (a ` cspan (\<Squnion>S\<in>M. space_as_set S))\<close>
    apply (rule closure_bounded_linear_image_subset_eq)
    by (simp add: cblinfun.real.bounded_linear_right)
  also from * have \<open>\<dots> \<subseteq> closure (space_as_set (\<Squnion>M))\<close>
    by (meson closure_mono)
  also have \<open>\<dots> = space_as_set (\<Squnion>M)\<close>
    by force
  finally have \<open>a *\<^sub>S \<Squnion>M \<le> \<Squnion>M\<close>
    by (simp add: less_eq_ccsubspace.rep_eq)
  then show ?thesis
    using invariant_subspaceI by blast
qed

lemma invariant_subspace_SUP:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> invariant_subspace (S x) a\<close>
  shows \<open>invariant_subspace (\<Squnion>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE invariant_subspace_Sup)

lemma reducing_subspace_Inf:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> reducing_subspace S a\<close>
  shows \<open>reducing_subspace (\<Sqinter>M) a\<close>
  using assms
  by (auto intro!: invariant_subspace_Inf invariant_subspace_SUP
      simp add: reducing_subspace_def uminus_Inf invariant_subspace_Inf)

lemma reducing_subspace_INF:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> reducing_subspace (S x) a\<close>
  shows \<open>reducing_subspace (\<Sqinter>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE reducing_subspace_Inf)

lemma reducing_subspace_Sup:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> reducing_subspace S a\<close>
  shows \<open>reducing_subspace (\<Squnion>M) a\<close>
  using assms
  by (auto intro!: invariant_subspace_Sup invariant_subspace_INF
      simp add: reducing_subspace_def uminus_Sup invariant_subspace_Inf)

lemma reducing_subspace_SUP:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> reducing_subspace (S x) a\<close>
  shows \<open>reducing_subspace (\<Squnion>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE reducing_subspace_Sup)

lemma selfadjoint_imp_normal: \<open>normal_op a\<close> if \<open>selfadjoint a\<close>
  using that by (simp add: selfadjoint_def normal_op_def)

lemma eigenspaces_orthogonal:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.5.7\<close>
  assumes \<open>e \<noteq> f\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>orthogonal_spaces (eigenspace e a) (eigenspace f a)\<close>
proof (intro orthogonal_spaces_def[THEN iffD2] ballI)
  fix g h assume g_eigen: \<open>g \<in> space_as_set (eigenspace e a)\<close> and h_eigen: \<open>h \<in> space_as_set (eigenspace f a)\<close>
  with \<open>normal_op a\<close> have \<open>g \<in> space_as_set (eigenspace (cnj e) (a*))\<close>
    by (simp add: normal_op_same_eigenspace_as_adj) 
  then have a_adj_g: \<open>(a*) g = cnj e *\<^sub>C g\<close>
    using eigenspace_memberD by blast 
  from h_eigen have a_h: \<open>a h = f *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD) 
  have \<open>f * (g \<bullet>\<^sub>C h) = g \<bullet>\<^sub>C a h\<close>
    by (simp add: a_h) 
  also have \<open>\<dots> = (a*) g \<bullet>\<^sub>C h\<close>
    by (simp add: cinner_adj_left) 
  also have \<open>\<dots> = e * (g \<bullet>\<^sub>C h)\<close>
    using a_adj_g by auto 
  finally have \<open>(f - e) * (g \<bullet>\<^sub>C h) = 0\<close>
    by (simp add: vector_space_over_itself.scale_left_diff_distrib) 
  with \<open>e \<noteq> f\<close> show \<open>g \<bullet>\<^sub>C h = 0\<close>
    by simp 
qed

definition largest_eigenvalue :: \<open>('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> complex\<close> where
  \<open>largest_eigenvalue a = 
    (if \<exists>x. x \<in> eigenvalues a \<and> (\<forall>y \<in> eigenvalues a. cmod x \<ge> cmod y) then
    SOME x. x \<in> eigenvalues a \<and> (\<forall>y \<in> eigenvalues a. cmod x \<ge> cmod y) else 0)\<close>


lemma eigenvalue_in_the_limit_compact_op:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.4.14\<close>
  assumes \<open>compact_op T\<close>
  assumes \<open>l \<noteq> 0\<close>
  assumes normh: \<open>\<And>n. norm (h n) = 1\<close>
  assumes Tl_lim: \<open>(\<lambda>n. (T - l *\<^sub>C id_cblinfun) (h n)) \<longlonglongrightarrow> 0\<close>
  shows \<open>l \<in> eigenvalues T\<close>
proof -
  from assms(1)
  have compact_Tball: \<open>compact (closure (T ` cball 0 1))\<close>
    using compact_op_def2 by blast
  have \<open>T (h n) \<in> closure (T ` cball 0 1)\<close> for n
    by (smt (z3) assms(3) closure_subset image_subset_iff mem_cball_0)
  then obtain n f where lim_Thn: \<open>(\<lambda>k. T (h (n k))) \<longlonglongrightarrow> f\<close> and \<open>strict_mono n\<close>
    using compact_Tball[unfolded compact_def, rule_format, where f=\<open>T o h\<close>, unfolded o_def]
    by fast
  have lThk_lim: \<open>(\<lambda>k. (l *\<^sub>C id_cblinfun - T) (h (n k))) \<longlonglongrightarrow> 0\<close>
  proof -
    have \<open>(\<lambda>n. (l *\<^sub>C id_cblinfun - T) (h n)) \<longlonglongrightarrow> 0\<close>
      using Tl_lim[THEN tendsto_minus]
      by (simp add: cblinfun.diff_left)
    with \<open>strict_mono n\<close> show ?thesis
      by (rule LIMSEQ_subseq_LIMSEQ[unfolded o_def, rotated])
  qed
  have \<open>h (n k) = inverse l *\<^sub>C ((l *\<^sub>C id_cblinfun - T) (h (n k)) + T (h (n k)))\<close> for k
    by (metis assms(2) cblinfun.real.add_left cblinfun.scaleC_left diff_add_cancel divideC_field_splits_simps_1(5) id_cblinfun.rep_eq scaleC_zero_right)
  moreover have \<open>\<dots> \<longlonglongrightarrow> inverse l *\<^sub>C f\<close>
    apply (rule tendsto_scaleC, simp)
    apply (subst add_0_left[symmetric, of f])
    using lThk_lim lim_Thn by (rule tendsto_add)
  ultimately have lim_hn: \<open>(\<lambda>k. h (n k)) \<longlonglongrightarrow> inverse l *\<^sub>C f\<close>
    by simp
  have \<open>f \<noteq> 0\<close>
  proof -
    from lim_hn have \<open>(\<lambda>k. norm (h (n k))) \<longlonglongrightarrow> norm (inverse l *\<^sub>C f)\<close>
      apply (rule isCont_tendsto_compose[unfolded o_def, rotated])
      by fastforce
    moreover have \<open>(\<lambda>_. 1) \<longlonglongrightarrow> 1\<close>
      by simp
    ultimately have \<open>norm (inverse l *\<^sub>C f) = 1\<close>
      unfolding normh
      using LIMSEQ_unique by blast
    then show \<open>f \<noteq> 0\<close>
      by force
  qed
  from lim_hn have \<open>(\<lambda>k. T (h (n k))) \<longlonglongrightarrow> T (inverse l *\<^sub>C f)\<close>
    apply (rule isCont_tendsto_compose[rotated])
    by force
  with lim_Thn have \<open>f = T (inverse l *\<^sub>C f)\<close>
    using LIMSEQ_unique by blast
  with \<open>l \<noteq> 0\<close> have \<open>l *\<^sub>C f = T f\<close>
    by (metis cblinfun.scaleC_right divideC_field_simps(2))
  with \<open>f \<noteq> 0\<close> show \<open>l \<in> eigenvalues T\<close>
    by (auto intro!: eigenvaluesI[where h=f])
qed


lemma norm_is_eigenvalue:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.5.9\<close>
  fixes a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{not_singleton, chilbert_space}\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>norm a \<in> eigenvalues a \<or> - norm a \<in> eigenvalues a\<close>
proof -
  wlog \<open>a \<noteq> 0\<close>
    using negation by auto
  obtain h e where h_lim: \<open>(\<lambda>i. h i \<bullet>\<^sub>C a (h i)) \<longlonglongrightarrow> e\<close> and normh: \<open>norm (h i) = 1\<close> 
    and norme: \<open>cmod e = norm a\<close> for i
  proof atomize_elim
    have sgn_cmod: \<open>sgn x * cmod x = x\<close> for x
      by (simp add: complex_of_real_cmod sgn_mult_abs)
    from cblinfun_norm_is_Sup_cinner[OF \<open>selfadjoint a\<close>]
    obtain f where range_f: \<open>range f \<subseteq> ((\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>))) ` {\<psi>. norm \<psi> = 1})\<close>
      and f_lim: \<open>f \<longlonglongrightarrow> norm a\<close>
      apply atomize_elim
      apply (rule is_Sup_imp_ex_tendsto)
      by (auto simp: ex_norm1_not_singleton)
    obtain h0 where normh0: \<open>norm (h0 i) = 1\<close> and f_h0: \<open>f i = cmod (h0 i \<bullet>\<^sub>C a (h0 i))\<close> for i
      apply (atomize_elim, rule choice2)
      using range_f by auto
    from f_h0 f_lim have h0lim_cmod: \<open>(\<lambda>i. cmod (h0 i \<bullet>\<^sub>C a (h0 i))) \<longlonglongrightarrow> norm a\<close>
      by presburger
    have sgn_sphere: \<open>sgn (h0 i \<bullet>\<^sub>C a (h0 i)) \<in> insert 0 (sphere 0 1)\<close> for i
      using normh0 by (auto intro!: left_inverse simp: sgn_div_norm)
    have compact: \<open>compact (insert 0 (sphere (0::complex) 1))\<close>
      by simp
    obtain r l where \<open>strict_mono r\<close> and l_sphere: \<open>l \<in> insert 0 (sphere 0 1)\<close>
      and h0lim_sgn: \<open>((\<lambda>i. sgn (h0 i \<bullet>\<^sub>C a (h0 i))) \<circ> r) \<longlonglongrightarrow> l\<close>
      using compact[unfolded compact_def, rule_format, OF sgn_sphere]
      by fast
    define h and e where \<open>h i = h0 (r i)\<close> and \<open>e = l * norm a\<close> for i
    have hlim_cmod: \<open>(\<lambda>i. cmod (h i \<bullet>\<^sub>C a (h i))) \<longlonglongrightarrow> norm a\<close>
      using LIMSEQ_subseq_LIMSEQ[OF h0lim_cmod \<open>strict_mono r\<close>]  
      unfolding h_def o_def by auto
    with h0lim_sgn have \<open>(\<lambda>i. sgn (h i \<bullet>\<^sub>C a (h i)) * cmod (h i \<bullet>\<^sub>C a (h i))) \<longlonglongrightarrow> e\<close>
      by (auto intro!: tendsto_mult tendsto_of_real simp: o_def h_def e_def)
    then have hlim: \<open>(\<lambda>i. h i \<bullet>\<^sub>C a (h i)) \<longlonglongrightarrow> e\<close>
      by (simp add: sgn_cmod)
    have \<open>e \<noteq> 0\<close>
    proof (rule ccontr, simp)
      assume \<open>e = 0\<close>
      from hlim have \<open>(\<lambda>i. cmod (h i \<bullet>\<^sub>C a (h i))) \<longlonglongrightarrow> cmod e\<close>
        apply (rule tendsto_compose[where g=cmod, rotated])
        by (smt (verit, del_insts) \<open>e = 0\<close> diff_zero dist_norm metric_LIM_imp_LIM norm_ge_zero norm_zero real_norm_def tendsto_ident_at)
      with \<open>e = 0\<close> hlim_cmod have \<open>norm a = 0\<close>
        using LIMSEQ_unique by fastforce
      with \<open>a \<noteq> 0\<close> show False
        by simp
    qed
    then have norme: \<open>norm e = norm a\<close>
      using l_sphere by (simp add: e_def norm_mult)
    show \<open>\<exists>h e. (\<lambda>i. h i \<bullet>\<^sub>C (a *\<^sub>V h i)) \<longlonglongrightarrow> e \<and> (\<forall>i. norm (h i) = 1) \<and> cmod e = norm a\<close>
      using norme normh0 hlim
      by (auto intro!: exI[of _ h] exI[of _ e] simp: h_def)
  qed
  have \<open>e \<in> \<real>\<close>
  proof -
    from h_lim[THEN tendsto_Im]
    have *: \<open>(\<lambda>i. Im (h i \<bullet>\<^sub>C a (h i))) \<longlonglongrightarrow> Im e\<close>
      by -
    have **: \<open>Im (h i \<bullet>\<^sub>C a (h i)) = 0\<close> for i
      using assms(2) selfadjoint_def cinner_hermitian_real complex_is_Real_iff by auto
    have \<open>Im e = 0\<close>
      using _ * apply (rule tendsto_unique)
      using ** by auto
    then show ?thesis
      using complex_is_Real_iff by presburger
  qed
  define e' where \<open>e' = Re e\<close>
  with \<open>e \<in> \<real>\<close> have ee': \<open>e = of_real e'\<close>
    by (simp add: of_real_Re)
  have \<open>e' \<in> eigenvalues a\<close>
  proof -
    have [trans]: \<open>f \<longlonglongrightarrow> 0\<close> if \<open>\<And>x. f x \<le> g x\<close> and \<open>g \<longlonglongrightarrow> 0\<close> and \<open>\<And>x. f x \<ge> 0\<close> for f g :: \<open>nat \<Rightarrow> real\<close>
      apply (rule real_tendsto_sandwich[where h=g and f=\<open>\<lambda>_. 0\<close>])
      using that by auto
    have \<open>(norm ((a - e' *\<^sub>R id_cblinfun) (h n)))\<^sup>2 = (norm (a (h n)))\<^sup>2 - 2 * e' * Re (h n \<bullet>\<^sub>C a (h n)) + e'\<^sup>2\<close> for n
      apply (simp add: power2_norm_eq_cinner' cblinfun.diff_left cinner_diff_left
        cinner_diff_right cinner_scaleR_left cblinfun.scaleR_left)
      apply (subst cinner_commute[of _ \<open>h n\<close>])
      by (simp add: normh algebra_simps power2_eq_square 
          del: cinner_commute' flip: power2_norm_eq_cinner')
    also have \<open>\<dots>n \<le> e'\<^sup>2 - 2 * e' * Re (h n \<bullet>\<^sub>C a (h n)) + e'\<^sup>2\<close> for n
    proof -
      from norme have \<open>e'\<^sup>2 = (norm a)\<^sup>2\<close>
        apply (simp add: ee')
        by (smt (verit) power2_minus)
      then have \<open>(norm (a *\<^sub>V h n))\<^sup>2 \<le> e'\<^sup>2\<close>
        apply simp
        by (metis mult_cancel_left2 norm_cblinfun normh)
      then show ?thesis
        by auto
    qed
    also have \<open>\<dots> \<longlonglongrightarrow> 0\<close>
      apply (subst asm_rl[of \<open>(\<lambda>n. e'\<^sup>2 - 2 * e' * Re (h n \<bullet>\<^sub>C a (h n)) + e'\<^sup>2) = (\<lambda>n. 2 * e' * (e' - Re (h n \<bullet>\<^sub>C (a *\<^sub>V h n))))\<close>])
       apply (auto intro!: ext simp: right_diff_distrib power2_eq_square)[1]
      using h_lim[THEN tendsto_Re]
      by (auto intro!: tendsto_mult_right_zero tendsto_diff_const_left_rewrite simp: ee')
    finally have \<open>(\<lambda>n. (a - e' *\<^sub>R id_cblinfun) (h n)) \<longlonglongrightarrow> 0\<close>
      by (simp add: tendsto_norm_zero_iff)
    then show \<open>e' \<in> eigenvalues a\<close>
      unfolding scaleR_scaleC
      apply (rule eigenvalue_in_the_limit_compact_op[rotated -1])
      using \<open>a \<noteq> 0\<close> norme by (auto intro!: normh simp: assms ee')
  qed
  from \<open>e \<in> \<real>\<close> norme
  have \<open>e = norm a \<or> e = - norm a\<close>
    by (smt (verit, best) in_Reals_norm of_real_Re)
  with \<open>e' \<in> eigenvalues a\<close> show ?thesis
    using ee' by presburger
qed

lemma largest_eigenvalue_0_aux: 
  \<open>largest_eigenvalue (0 :: 'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'a) = 0\<close>
proof -
  let ?zero = \<open>0 :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  define e where \<open>e = (SOME x. x \<in> eigenvalues ?zero \<and> (\<forall>y \<in> eigenvalues ?zero. cmod x \<ge> cmod y))\<close>
  have \<open>\<exists>e. e \<in> eigenvalues ?zero \<and> (\<forall>y\<in>eigenvalues ?zero. cmod y \<le> cmod e)\<close> (is \<open>\<exists>e. ?P e\<close>)
    by (auto intro!: exI[of _ 0])
  then have \<open>?P e\<close>
    unfolding e_def
    by (rule someI_ex)
  then have \<open>e = 0\<close>
    by simp
  then show \<open>largest_eigenvalue ?zero = 0\<close>
    by (simp add: largest_eigenvalue_def)
qed

lemma largest_eigenvalue_0[simp]:
  \<open>largest_eigenvalue (0 :: 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) = 0\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using complex_normed_vector_axioms True
    by (rule largest_eigenvalue_0_aux[internalize_sort' 'a])
next
  case False
  then have \<open>eigenvalues (0 :: 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) = {}\<close>
    by (rule not_not_singleton_no_eigenvalues)
  then show ?thesis
    by (auto simp add: largest_eigenvalue_def)
qed

hide_fact largest_eigenvalue_0_aux

lemma
  fixes a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{not_singleton, chilbert_space}\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows largest_eigenvalue_norm_aux: \<open>largest_eigenvalue a \<in> {norm a, - norm a}\<close>
    and largest_eigenvalue_ex: \<open>largest_eigenvalue a \<in> eigenvalues a\<close>
proof -
  define l where \<open>l = (SOME x. x \<in> eigenvalues a \<and> (\<forall>y \<in> eigenvalues a. cmod x \<ge> cmod y))\<close>
  from norm_is_eigenvalue[OF assms]
  obtain e where \<open>e \<in> {of_real (norm a), - of_real (norm a)}\<close> and \<open>e \<in> eigenvalues a\<close>
    by auto
  then have norme: \<open>norm e = norm a\<close>
    by auto
  have \<open>e \<in> eigenvalues a \<and> (\<forall>y\<in>eigenvalues a. cmod y \<le> cmod e)\<close> (is \<open>?P e\<close>)
    by (auto intro!: \<open>e \<in> eigenvalues a\<close> simp: eigenvalue_norm_bound norme)
  then have *: \<open>l \<in> eigenvalues a \<and> (\<forall>y\<in>eigenvalues a. cmod y \<le> cmod l)\<close>
    unfolding l_def largest_eigenvalue_def by (rule someI)
  then have l_def': \<open>l = largest_eigenvalue a\<close>
    by (metis (mono_tags, lifting) l_def largest_eigenvalue_def) 
  from * have \<open>l \<in> eigenvalues a\<close>
    by (simp add: l_def)
  then show \<open>largest_eigenvalue a \<in> eigenvalues a\<close>
    by (simp add: l_def')
  have \<open>norm l \<ge> norm a\<close>
    using * norme \<open>e \<in> eigenvalues a\<close> by auto
  moreover have \<open>norm l \<le> norm a\<close>
    using "*" eigenvalue_norm_bound by blast
  ultimately have \<open>norm l = norm a\<close>
    by linarith
  moreover have \<open>l \<in> \<real>\<close>
    using \<open>l \<in> eigenvalues a\<close> assms(2) eigenvalue_selfadj_real by blast
  ultimately have \<open>l \<in> {norm a, - norm a}\<close>
    by (smt (verit, ccfv_SIG) in_Reals_norm insertCI l_def of_real_Re)
  then show \<open>largest_eigenvalue a \<in> {norm a, - norm a}\<close>
    by (simp add: l_def')
qed

lemma largest_eigenvalue_norm:
  fixes a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>largest_eigenvalue a \<in> {norm a, - norm a}\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_class.chilbert_space_axioms True assms 
    by (rule largest_eigenvalue_norm_aux[internalize_sort' 'a])
next
  case False
  then have \<open>a = 0\<close>
    by (rule not_not_singleton_cblinfun_zero)
  then show ?thesis
    by simp
qed

hide_fact largest_eigenvalue_norm_aux

lemma cmod_largest_eigenvalue:
  fixes a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>cmod (largest_eigenvalue a) = norm a\<close>
  using largest_eigenvalue_norm[OF assms] by auto

lemma compact_op_eigenspace_finite_dim:
  fixes a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>e \<noteq> 0\<close>
  shows \<open>finite_dim_ccsubspace (eigenspace e a)\<close>
proof -
  define S where \<open>S = space_as_set (eigenspace e a)\<close>
  obtain B where \<open>ccspan B = eigenspace e a\<close> and \<open>is_ortho_set B\<close>
    and norm_B: \<open>x \<in> B \<Longrightarrow> norm x = 1\<close> for x
    using orthonormal_subspace_basis_exists[where S=\<open>{}\<close> and V=\<open>eigenspace e a\<close>]
    by (auto simp: S_def)
  then have span_BS: \<open>closure (cspan B) = S\<close>
    by (metis S_def ccspan.rep_eq)
  have \<open>finite B\<close>
  proof (rule ccontr)
    assume \<open>infinite B\<close>
    then obtain b :: \<open>nat \<Rightarrow> 'a\<close> where range_b: \<open>range b \<subseteq> B\<close> and \<open>inj b\<close>
      by (meson infinite_countable_subset)
    define f where \<open>f n = a (b n)\<close> for n
    have range_f: \<open>range f \<subseteq> closure (a ` cball 0 1)\<close>
      using norm_B range_b
      by (auto intro!: closure_subset[THEN subsetD] imageI simp: f_def)
    from \<open>compact_op a\<close> have compact: \<open>compact (closure (a ` cball 0 1))\<close>
      using compact_op_def2 by blast
    obtain l r where \<open>strict_mono r\<close> and fr_lim: \<open>(f o r) \<longlonglongrightarrow> l\<close>
      apply atomize_elim
      using range_f compact[unfolded compact_def, rule_format, of f]
      by fast
    define d :: real where \<open>d = cmod e * sqrt 2\<close>
    from \<open>e \<noteq> 0\<close> have \<open>d > 0\<close>
      by (auto intro!: Rings.linordered_semiring_strict_class.mult_pos_pos simp: d_def)
    have aux: \<open>\<exists>n\<ge>N. P n\<close> if \<open>P (Suc N)\<close> for P N
      using Suc_n_not_le_n nat_le_linear that by blast
    have \<open>dist (f (r n)) (f (r (Suc n))) = d\<close> for n
    proof -
      have ortho: \<open>is_orthogonal (b (r n)) (b (r (Suc n)))\<close>
      proof -
        have \<open>b (r n) \<noteq> b (r (Suc n))\<close>
          by (metis Suc_n_not_n \<open>inj b\<close> \<open>strict_mono r\<close> injD strict_mono_eq)
        moreover from range_b have \<open>b (r n) \<in> B\<close> and \<open>b (r (Suc n)) \<in> B\<close>
          by fast+
        ultimately show ?thesis
          using \<open>is_ortho_set B\<close> 
          by (auto intro!: simp: is_ortho_set_def)
      qed
      have normb: \<open>norm (b n) = 1\<close> for n
        by (metis \<open>inj b\<close> image_subset_iff inj_image_mem_iff norm_B range_b range_eqI)
      have \<open>f (r n) = e *\<^sub>C b (r n)\<close> for n
      proof -
        from range_b span_BS
        have \<open>b (r n) \<in> S\<close>
          using complex_vector.span_superset closure_subset
          apply (auto dest!: range_subsetD[where i=\<open>b n\<close>])
          by fast
        then show ?thesis
          by (auto intro!: dest!: eigenspace_memberD simp: S_def f_def)
      qed
      then have \<open>(dist (f (r n)) (f (r (Suc n))))\<^sup>2 = (cmod e * dist (b (r n)) (b (r (Suc n))))\<^sup>2\<close>
        by (simp add: dist_norm flip: scaleC_diff_right)
      also from ortho have \<open>\<dots> = (cmod e * sqrt 2)\<^sup>2\<close>
        by (simp add: dist_norm polar_identity_minus power_mult_distrib normb)
      finally show ?thesis
        by (simp add: d_def)
    qed
    with \<open>d > 0\<close> have \<open>\<not> Cauchy (f o r)\<close>
      by (auto intro!: exI[of _ \<open>d/2\<close>] aux
          simp: Cauchy_altdef2 dist_commute simp del: less_divide_eq_numeral1)
    with fr_lim show False
      using LIMSEQ_imp_Cauchy by blast
  qed
  with span_BS show ?thesis
    using S_def cspan_finite_dim finite_dim_ccsubspace.rep_eq by fastforce
qed


lemma ccsubspace_contains_unit:
  assumes \<open>E \<noteq> \<bottom>\<close>
  shows \<open>\<exists>h\<in>space_as_set E. norm h = 1\<close>
proof -
  from assms have \<open>space_as_set E \<noteq> {0}\<close>
    by (metis bot_ccsubspace.rep_eq space_as_set_inject)
  then obtain h\<^sub>0 where \<open>h\<^sub>0 \<in> space_as_set E\<close> and \<open>h\<^sub>0 \<noteq> 0\<close>
    by auto
  then have \<open>sgn h\<^sub>0 \<in> space_as_set E\<close>
    using csubspace_space_as_set
    by (auto intro!: complex_vector.subspace_scale
        simp add: sgn_div_norm scaleR_scaleC)
  moreover from \<open>h\<^sub>0 \<noteq> 0\<close> have \<open>norm (sgn h\<^sub>0) = 1\<close>
    by (simp add: norm_sgn)
  ultimately show ?thesis
    by auto
qed

lemma eq_on_ccsubspaces_Sup:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>i h. i \<in> I \<Longrightarrow> h \<in> space_as_set (X i) \<Longrightarrow> a h = b h\<close>
  shows \<open>\<And>h. h \<in> space_as_set (\<Squnion>i\<in>I. X i) \<Longrightarrow> a h = b h\<close>
proof -
  from assms
  have \<open>X i \<le> kernel (a - b)\<close> if \<open>i \<in> I\<close> for i
    using that by (auto intro!: ccsubspace_leI simp: kernel.rep_eq minus_cblinfun.rep_eq)
  then have \<open>(\<Squnion>i\<in>I. X i) \<le> kernel (a - b)\<close>
    by (simp add: SUP_least) 
  then show \<open>h \<in> space_as_set (\<Squnion>i\<in>I. X i) \<Longrightarrow> a h = b h\<close> for h
    using kernel_memberD less_eq_ccsubspace.rep_eq 
    by (metis (no_types, opaque_lifting) cblinfun.diff_left cblinfun.real.diff_right cblinfun.real.zero_left diff_eq_diff_eq double_diff mem_simps(6) subset_refl)
qed

lemma eq_on_ccsubspaces_sup:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>h i. h \<in> space_as_set S \<Longrightarrow> a h = b h\<close>
  assumes \<open>\<And>h i. h \<in> space_as_set T \<Longrightarrow> a h = b h\<close>
  shows \<open>\<And>h. h \<in> space_as_set (S \<squnion> T) \<Longrightarrow> a h = b h\<close>
  apply (rule eq_on_ccsubspaces_Sup[where I=\<open>{True,False}\<close> and X=\<open>\<lambda>i. if i then T else S\<close>])
  using assms
   apply presburger
  by fastforce



lemma hilbert_schmidt_norm_geq_norm:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (c)\<close>
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>norm a \<le> hilbert_schmidt_norm a\<close>
proof -
  have \<open>norm (a x) \<le> hilbert_schmidt_norm a\<close> if \<open>norm x = 1\<close> for x
  proof -
    obtain B where \<open>x \<in> B\<close> and \<open>is_onb B\<close>
      using orthonormal_basis_exists[of \<open>{x}\<close>] \<open>norm x = 1\<close>
      by force
    have \<open>(norm (a x))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>{x}. (norm (a x))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a x))\<^sup>2)\<close>
      apply (rule infsum_mono_neutral)
      by (auto intro!: summable_hilbert_schmidt_norm_square \<open>is_onb B\<close> assms \<open>x \<in> B\<close>)
    also have \<open>\<dots> = (hilbert_schmidt_norm a)\<^sup>2\<close>
      using infsum_hilbert_schmidt_norm_square[OF \<open>is_onb B\<close> assms]
      by -
    finally show ?thesis
      by force
  qed
  then show ?thesis
    by (auto intro!: norm_cblinfun_bound_unit)
qed


lemma hilbert_schmidt_compact: \<open>compact_op a\<close> if \<open>hilbert_schmidt a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Corollary 18.7.
      (Only the second part. The first part is stated inside this proof though.)\<close>
proof -
  have \<open>\<exists>b. finite_rank b \<and> hilbert_schmidt_norm (b - a) < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
  proof -
    have \<open>\<epsilon>\<^sup>2 > 0\<close>
      using that by force
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    with \<open>hilbert_schmidt a\<close> have a_sum_B: \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
      by (auto intro!: summable_hilbert_schmidt_norm_square)
    then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2)) B\<close>
      using has_sum_infsum by blast
    from tendsto_iff[THEN iffD1, rule_format, OF this[unfolded has_sum_def] \<open>\<epsilon>\<^sup>2 > 0\<close>]
    obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> B\<close>
      and Fbound: \<open>dist (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2) (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) < \<epsilon>\<^sup>2\<close>
      apply atomize_elim
      by (auto intro!: simp: eventually_finite_subsets_at_top)
    define p b where \<open>p = (\<Sum>x\<in>F. selfbutter x)\<close> and \<open>b = a o\<^sub>C\<^sub>L p\<close>
    have [simp]: \<open>p x = x\<close> if \<open>x \<in> F\<close> for x
      apply (simp add: p_def cblinfun.sum_left)
      apply (subst sum_single[where i=x])
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      by (auto intro!: simp:  cnorm_eq_1 is_onb_def is_ortho_set_def)
    have [simp]: \<open>p x = 0\<close> if \<open>x \<in> B - F\<close> for x
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      apply (auto intro!: sum.neutral simp add: p_def cblinfun.sum_left is_onb_def is_ortho_set_def)
      by auto
    have \<open>finite_rank p\<close>
      by (simp add: finite_rank_sum p_def)
    then have \<open>finite_rank b\<close>
      by (simp add: b_def finite_rank_comp_right)
    with \<open>hilbert_schmidt a\<close> have \<open>hilbert_schmidt (b - a)\<close>
      by (auto intro!: hilbert_schmidt_minus intro: finite_rank_hilbert_schmidt)
    then have \<open>(hilbert_schmidt_norm (b - a))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((b - a) *\<^sub>V x))\<^sup>2)\<close>
      by (simp add: infsum_hilbert_schmidt_norm_square \<open>is_onb B\<close>)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B-F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      by (auto intro!: infsum_cong_neutral
          simp: b_def cblinfun.diff_left)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) - (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      apply (subst infsum_Diff)
      using \<open>F \<subseteq> B\<close> a_sum_B by auto
    also have \<open>\<dots> < \<epsilon>\<^sup>2\<close>
      using Fbound
      by (simp add: dist_norm)
    finally show ?thesis
      using \<open>finite_rank b\<close>
      using power_less_imp_less_base that by fastforce
  qed
  then have \<open>\<exists>b. finite_rank b \<and> dist b a < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    apply (rule ex_mono[rule_format, rotated])
     apply (auto intro!: that simp: dist_norm)
    using hilbert_schmidt_minus \<open>hilbert_schmidt a\<close> finite_rank_hilbert_schmidt hilbert_schmidt_norm_geq_norm
    by fastforce
  then show ?thesis
    by (simp add: compact_op_finite_rank closure_approachable)
qed

lemma trace_class_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>trace_class a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (auto intro!: trace_class_comp_right that simp: hilbert_schmidt_def)

lemma trace_class_compact: \<open>compact_op a\<close> if \<open>trace_class a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (simp add: hilbert_schmidt_compact that trace_class_hilbert_schmidt)


lemma trace_norm_plus_orthogonal:
  assumes \<open>trace_class a\<close> and \<open>trace_class b\<close>
  assumes \<open>a* o\<^sub>C\<^sub>L b = 0\<close> and \<open>a o\<^sub>C\<^sub>L b* = 0\<close>
  shows \<open>trace_norm (a + b) = trace_norm a + trace_norm b\<close>
proof -
  have \<open>trace_norm (a + b) = trace (abs_op (a + b))\<close>
    by simp
  also have \<open>\<dots> = trace (abs_op a + abs_op b)\<close>
   by (simp add: abs_op_plus_orthogonal assms)
  also have \<open>\<dots> = trace (abs_op a) + trace (abs_op b)\<close>
    by (simp add: assms trace_plus)
  also have \<open>\<dots> = trace_norm a + trace_norm b\<close>
    by simp
  finally show ?thesis
    using of_real_eq_iff by blast
qed

lemma norm_tc_plus_orthogonal:
  assumes \<open>tc_compose (adj_tc a) b = 0\<close> and \<open>tc_compose a (adj_tc b) = 0\<close>
  shows \<open>norm (a + b) = norm a + norm b\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_plus_orthogonal)


lemma trace_norm_sum_exchange:
  fixes t :: \<open>_ \<Rightarrow> (_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space)\<close>
  assumes \<open>\<And>i. i \<in> F \<Longrightarrow> trace_class (t i)\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> (t i)* o\<^sub>C\<^sub>L t j = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> t i o\<^sub>C\<^sub>L (t j)* = 0\<close>
  shows \<open>trace_norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. trace_norm (t i))\<close>
proof (insert assms, induction F rule:infinite_finite_induct)
  case (infinite A)
  then show ?case
    by simp
next
  case empty
  show ?case
    by simp
next
  case (insert x F)
  have \<open>trace_norm (\<Sum>i\<in>insert x F. t i) = trace_norm (t x + (\<Sum>x\<in>F. t x))\<close>
    by (simp add: insert)
  also have \<open>\<dots> = trace_norm (t x) + trace_norm (\<Sum>x\<in>F. t x)\<close>
  proof (rule trace_norm_plus_orthogonal)
    show \<open>trace_class (t x)\<close>
      by (simp add: insert.prems)
    show \<open>trace_class (\<Sum>x\<in>F. t x)\<close>
      by (simp add: trace_class_sum insert.prems)
    show \<open>t x* o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x) = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
    show \<open>t x o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x)* = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
  qed
  also have \<open>\<dots> = trace_norm (t x) + (\<Sum>x\<in>F. trace_norm (t x))\<close>
    apply (subst insert.IH)
    by (simp_all add: insert.prems)
  also have \<open>\<dots> = (\<Sum>i\<in>insert x F. trace_norm (t i))\<close>
    by (simp add: insert)
  finally show ?case
    by -
qed

lemma norm_tc_sum_exchange:
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (adj_tc (t i)) (t j) = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (t i) (adj_tc (t j)) = 0\<close>
  shows \<open>norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. norm (t i))\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_sum_exchange)









end