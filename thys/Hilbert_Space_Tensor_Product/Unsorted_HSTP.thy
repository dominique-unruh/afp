theory Unsorted_HSTP
  imports Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    Tensor_Product.Hilbert_Space_Tensor_Product
    Jordan_Normal_Form.Matrix
    Complex_Bounded_Operators.Extra_Jordan_Normal_Form
    Complex_Bounded_Operators.Cblinfun_Matrix
    Partial_Trace
    Tensor_Product_Code
    Von_Neumann_Algebras
begin

(* TODO move everything *)

unbundle cblinfun_notation Finite_Cartesian_Product.no_vec_syntax jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Coset.kernel








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
    using of_real_hom.eq_iff by blast
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





subsection \<open>Spectral decomp, compact op\<close>

fun spectral_dec_val :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> complex\<close>
  \<comment> \<open>The eigenvalues in the spectral decomposition\<close>
  and spectral_dec_space :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> 'a ccsubspace\<close>
  \<comment> \<open>The eigenspaces in the spectral decomposition\<close>
  and spectral_dec_op :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  \<comment> \<open>A sequence of operators mostly for the proof of spectral composition. But see also \<open>spectral_dec_op_spectral_dec_proj\<close> below.\<close>
  where \<open>spectral_dec_val a n = largest_eigenvalue (spectral_dec_op a n)\<close>
  | \<open>spectral_dec_space a n = (if spectral_dec_val a n = 0 then 0 else eigenspace (spectral_dec_val a n) (spectral_dec_op a n))\<close>
  | \<open>spectral_dec_op a (Suc n) = spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)\<close>
  | \<open>spectral_dec_op a 0 = a\<close>

definition spectral_dec_proj :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<comment> \<open>Projectors in the spectral decomposition\<close>
  \<open>spectral_dec_proj a n = Proj (spectral_dec_space a n)\<close>

declare spectral_dec_val.simps[simp del]
declare spectral_dec_space.simps[simp del]

lemmas spectral_dec_def = spectral_dec_val.simps
lemmas spectral_dec_space_def = spectral_dec_space.simps

lemma spectral_dec_op_selfadj:
  assumes \<open>selfadjoint a\<close>
  shows \<open>selfadjoint (spectral_dec_op a n)\<close>
proof (induction n)
  case 0
  with assms show ?case
    by simp
next
  case (Suc n)
  define E T where \<open>E = spectral_dec_space a n\<close> and \<open>T = spectral_dec_op a n\<close>
  from Suc have \<open>normal_op T\<close>
    by (auto intro!: selfadjoint_imp_normal simp: T_def)
  then have \<open>reducing_subspace E T\<close>
    apply (auto intro!: eigenspace_is_reducing simp: spectral_dec_space_def E_def T_def)
    by -
  then have \<open>reducing_subspace (- E) T\<close>
    by simp
  then have *: \<open>Proj (- E) o\<^sub>C\<^sub>L T o\<^sub>C\<^sub>L Proj (- E) = T o\<^sub>C\<^sub>L Proj (- E)\<close>
    by (simp add: invariant_subspace_iff_PAP reducing_subspace_def)
  show ?case
    using Suc
    apply (simp add: flip: T_def E_def * )
    by (simp add: selfadjoint_def adj_Proj cblinfun_compose_assoc)
qed


lemma spectral_dec_op_compact:
  assumes \<open>compact_op a\<close>
  shows \<open>compact_op (spectral_dec_op a n)\<close>
  apply (induction n)
  by (auto intro!: compact_op_comp_left assms)

lemma spectral_dec_val_eigenvalue_of_spectral_dec_op:
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues (spectral_dec_op a n)\<close>
  by (auto intro!: largest_eigenvalue_ex spectral_dec_op_compact spectral_dec_op_selfadj assms
      simp: spectral_dec_def)

lemma spectral_dec_proj_finite_rank: 
  assumes \<open>compact_op a\<close>
  shows \<open>finite_rank (spectral_dec_proj a n)\<close>
  apply (cases \<open>spectral_dec_val a n = 0\<close>)
  by (auto intro!: finite_rank_Proj_finite_dim compact_op_eigenspace_finite_dim spectral_dec_op_compact assms
      simp: spectral_dec_proj_def spectral_dec_space_def)

lemma norm_spectral_dec_op:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>norm (spectral_dec_op a n) = cmod (spectral_dec_val a n)\<close>
  by (simp add: spectral_dec_def cmod_largest_eigenvalue spectral_dec_op_compact spectral_dec_op_selfadj assms)

lemma spectral_dec_op_decreasing_eigenspaces:
  assumes \<open>n \<ge> m\<close> and \<open>e \<noteq> 0\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e (spectral_dec_op a m)\<close>
proof -
  have *: \<open>eigenspace e (spectral_dec_op a (Suc n)) \<le> eigenspace e (spectral_dec_op a n)\<close> for n
  proof (intro ccsubspace_leI subsetI)
    fix h
    assume asm: \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a (Suc n)))\<close>
    have \<open>orthogonal_spaces (eigenspace e (spectral_dec_op a (Suc n))) (kernel (spectral_dec_op a (Suc n)))\<close>
      using spectral_dec_op_selfadj[of a \<open>Suc n\<close>] \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (auto intro!: eigenspaces_orthogonal selfadjoint_imp_normal spectral_dec_op_selfadj
          simp: spectral_dec_space_def simp flip: eigenspace_0)
    then have \<open>eigenspace e (spectral_dec_op a (Suc n)) \<le> - kernel (spectral_dec_op a (Suc n))\<close>
      using orthogonal_spaces_leq_compl by blast 
    also have \<open>\<dots> \<le> - spectral_dec_space a n\<close>
      by (auto intro!: ccsubspace_leI kernel_memberI simp: Proj_0_compl)
    finally have \<open>h \<in> space_as_set (- spectral_dec_space a n)\<close>
      using asm by (simp add: Set.basic_monos(7) less_eq_ccsubspace.rep_eq)
    then have \<open>spectral_dec_op a n h = spectral_dec_op a (Suc n) h\<close>
      by (simp add: Proj_fixes_image) 
    also have \<open>\<dots> = e *\<^sub>C h\<close>
      using asm eigenspace_memberD by blast 
    finally show \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a n))\<close>
      by (simp add: eigenspace_memberI) 
  qed
  define k where \<open>k = n - m\<close>
  from * have \<open>eigenspace e (spectral_dec_op a (m + k)) \<le> eigenspace e (spectral_dec_op a m)\<close>
    apply (induction k)
     apply (auto intro!: simp: simp del: spectral_dec_op.simps simp flip: )
    using order_trans_rules(23) by blast 
  then show ?thesis
    using \<open>n \<ge> m\<close> by (simp add: k_def)
qed

lemma spectral_dec_val_not_not_singleton:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>spectral_dec_val a n = 0\<close>
proof -
  from assms have \<open>spectral_dec_op a n = 0\<close>
    by (rule not_not_singleton_cblinfun_zero)
  then have \<open>largest_eigenvalue (spectral_dec_op a n) = 0\<close>
    by simp
  then show ?thesis
    by (simp add: spectral_dec_def)
qed

lemma spectral_dec_val_eigenvalue_aux:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Theorem II.5.1\<close>
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues a\<close>
proof -
  define e where \<open>e = spectral_dec_val a n\<close>
  with assms have \<open>e \<noteq> 0\<close>
    by fastforce

  from spectral_dec_op_decreasing_eigenspaces[where m=0 and a=a and n=n, OF _ \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>]
  have 1: \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e a\<close>
    by simp
  have 2: \<open>spectral_dec_space a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>spectral_dec_val a n \<in> eigenvalues (spectral_dec_op a n)\<close>
      by (simp add: assms(1) assms(2) spectral_dec_val.simps spectral_dec_op_compact spectral_dec_op_selfadj largest_eigenvalue_ex) 
    then show ?thesis
      using \<open>e \<noteq> 0\<close> by (simp add: eigenvalues_def spectral_dec_space.simps e_def)
  qed
  from 1 2 have \<open>eigenspace e a \<noteq> \<bottom>\<close>
    by (auto simp: spectral_dec_space_def bot_unique simp flip: e_def simp: \<open>e \<noteq> 0\<close>)
  then show \<open>e \<in> eigenvalues a\<close>
    by (simp add: eigenvalues_def)
qed

lemma spectral_dec_val_eigenvalue:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Theorem II.5.1\<close>
  fixes a :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues a\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule spectral_dec_val_eigenvalue_aux[internalize_sort' 'a])
next
  case False
  then have \<open>spectral_dec_val a n = 0\<close>
    by (rule spectral_dec_val_not_not_singleton)
  with assms show ?thesis
    by simp
qed

hide_fact spectral_dec_val_eigenvalue_aux

lemma spectral_dec_val_decreasing:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<ge> m\<close>
  shows \<open>cmod (spectral_dec_val a n) \<le> cmod (spectral_dec_val a m)\<close>
proof -
  have \<open>norm (spectral_dec_op a (Suc n)) \<le> norm (spectral_dec_op a n)\<close> for n
    apply simp
    by (smt (verit) Proj_partial_isometry cblinfun_compose_zero_right mult_cancel_left2 norm_cblinfun_compose norm_le_zero_iff norm_partial_isometry) 
  then have *: \<open>cmod (spectral_dec_val a (Suc n)) \<le> cmod (spectral_dec_val a n)\<close> for n
    by (simp add: cmod_largest_eigenvalue spectral_dec_op_compact assms spectral_dec_op_selfadj spectral_dec_def
        del: spectral_dec_op.simps)
  define k where \<open>k = n - m\<close>
  have \<open>cmod (spectral_dec_val a (m + k)) \<le> cmod (spectral_dec_val a m)\<close>
    apply (induction k arbitrary: m)
     apply simp
    by (metis "*" add_Suc_right order_trans_rules(23)) 
  with \<open>n \<ge> m\<close> show ?thesis
    by (simp add: k_def)
qed


lemma spectral_dec_val_distinct_aux:
  fixes a :: \<open>('a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
proof (rule ccontr)
  assume \<open>\<not> spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
  then have eq: \<open>spectral_dec_val a n = spectral_dec_val a m\<close>
    by blast
  wlog nm: \<open>n > m\<close> goal False generalizing n m keeping eq neq0
    using hypothesis[of n m] negation assms eq neq0
    by auto
  define e where \<open>e = spectral_dec_val a n\<close>
  with neq0 have \<open>e \<noteq> 0\<close>
    by simp

  have \<open>spectral_dec_space a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>e \<in> eigenvalues (spectral_dec_op a n)\<close>
      by (auto intro!: spectral_dec_val_eigenvalue_of_spectral_dec_op assms simp: e_def)
    then show ?thesis
      by (simp add: spectral_dec_space_def eigenvalues_def e_def neq0)
  qed
  then obtain h where \<open>norm h = 1\<close> and h_En: \<open>h \<in> space_as_set (spectral_dec_space a n)\<close>
    using ccsubspace_contains_unit by blast 
  have T_Sucm_h: \<open>spectral_dec_op a (Suc m) h = 0\<close>
  proof -
    have \<open>spectral_dec_space a n = eigenspace e (spectral_dec_op a n)\<close>
      by (simp add: spectral_dec_space_def e_def neq0)
    also have \<open>\<dots> \<le> eigenspace e (spectral_dec_op a m)\<close>
      using \<open>n > m\<close> \<open>e \<noteq> 0\<close> assms
      by (auto intro!: spectral_dec_op_decreasing_eigenspaces simp: )
    also have \<open>\<dots> = spectral_dec_space a m\<close>
      using neq0 by (simp add: spectral_dec_space_def e_def eq)
    finally have \<open>h \<in> space_as_set (spectral_dec_space a m)\<close>
      using h_En
      by (simp add: basic_trans_rules(31) less_eq_ccsubspace.rep_eq) 
    then show \<open>spectral_dec_op a (Suc m) h = 0\<close>
      by (simp add: Proj_0_compl)
  qed
  have \<open>spectral_dec_op a (Suc m + k) h = 0\<close> if \<open>k \<le> n - m - 1\<close> for k
  proof (insert that, induction k)
    case 0
    from T_Sucm_h show ?case
      by simp
  next
    case (Suc k)
    define mk1 where \<open>mk1 = Suc (m + k)\<close>
    from Suc.prems have \<open>mk1 \<le> n\<close>
      using mk1_def by linarith 
    have \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e (spectral_dec_op a mk1)\<close>
      using \<open>mk1 \<le> n\<close> \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (rule spectral_dec_op_decreasing_eigenspaces)
    with h_En have h_mk1: \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a mk1))\<close>
      by (auto simp: e_def spectral_dec_space_def less_eq_ccsubspace.rep_eq neq0)
    have \<open>Proj (- spectral_dec_space a mk1) *\<^sub>V h = 0 \<or> Proj (- spectral_dec_space a mk1) *\<^sub>V h = h\<close>
    proof (cases \<open>e = spectral_dec_val a mk1\<close>)
      case True
      from h_mk1 have \<open>Proj (- spectral_dec_space a mk1) h = 0\<close>
        using \<open>e \<noteq> 0\<close> by (simp add: Proj_0_compl True spectral_dec_space_def)
      then show ?thesis 
        by simp
    next
      case False
      have \<open>orthogonal_spaces (eigenspace e (spectral_dec_op a mk1)) (spectral_dec_space a mk1)\<close>
        by (simp add: False assms eigenspaces_orthogonal spectral_dec_space.simps spectral_dec_op_selfadj selfadjoint_imp_normal) 
      with h_mk1 have \<open>h \<in> space_as_set (- spectral_dec_space a mk1)\<close>
        using less_eq_ccsubspace.rep_eq orthogonal_spaces_leq_compl by blast 
      then have \<open>Proj (- spectral_dec_space a mk1) h = h\<close>
        by (rule Proj_fixes_image)
      then show ?thesis 
        by simp
    qed
    with Suc show ?case
      by (auto simp: mk1_def)
  qed
  from this[where k=\<open>n - m - 1\<close>]
  have \<open>spectral_dec_op a n h = 0\<close>
    using \<open>n > m\<close>
    by (simp del: spectral_dec_op.simps)
  moreover from h_En have \<open>spectral_dec_op a n h = e *\<^sub>C h\<close>
    by (simp add: neq0 e_def eigenspace_memberD spectral_dec_space_def)
  ultimately show False
    using \<open>norm h = 1\<close> \<open>e \<noteq> 0\<close>
    by force
qed

lemma spectral_dec_val_distinct:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule spectral_dec_val_distinct_aux[internalize_sort' 'a])
next
  case False
  then have \<open>spectral_dec_val a n = 0\<close>
    by (rule spectral_dec_val_not_not_singleton)
  with assms show ?thesis
    by simp
qed

hide_fact spectral_dec_val_distinct_aux

lemma spectral_dec_val_tendsto_0:
  (* In the proof of Conway, Functional, Theorem II.5.1 *)
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a \<longlonglongrightarrow> 0\<close>
proof (cases \<open>\<exists>n. spectral_dec_val a n = 0\<close>)
  case True
  then obtain n where \<open>spectral_dec_val a n = 0\<close>
    by auto
  then have \<open>spectral_dec_val a m = 0\<close> if \<open>m \<ge> n\<close> for m
    using spectral_dec_val_decreasing[OF assms that]
    by simp
  then show \<open>spectral_dec_val a \<longlonglongrightarrow> 0\<close>
    by (auto intro!: tendsto_eventually eventually_sequentiallyI)
next
  case False
  define E where \<open>E = spectral_dec_val a\<close>
  from False have \<open>E n \<in> eigenvalues a\<close> for n
    by (simp add: spectral_dec_val_eigenvalue assms E_def)
  then have \<open>eigenspace (E n) a \<noteq> 0\<close> for n
    by (simp add: eigenvalues_def)
  then obtain e where e_E: \<open>e n \<in> space_as_set (eigenspace (E n) a)\<close>
    and norm_e: \<open>norm (e n) = 1\<close> for n
    apply atomize_elim
    using ccsubspace_contains_unit 
    by (auto intro!: choice2)
  then obtain h n where \<open>strict_mono n\<close> and aen_lim: \<open>(\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
  proof atomize_elim
    from \<open>compact_op a\<close>
    have compact:\<open>compact (closure (a ` cball 0 1))\<close>
      by (simp add: compact_op_def2)
    from norm_e have \<open>a (e n) \<in> closure (a ` cball 0 1)\<close> for n
      using closure_subset[of \<open>a ` cball 0 1\<close>] by auto
    with compact[unfolded compact_def, rule_format, of \<open>\<lambda>n. a (e n)\<close>]
    show \<open>\<exists>n h. strict_mono n \<and> (\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
      by (auto simp: o_def)
  qed
  have ortho_en: \<open>is_orthogonal (e (n j)) (e (n k))\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    have \<open>n j \<noteq> n k\<close>
      by (simp add: \<open>strict_mono n\<close> strict_mono_eq that)
    then have \<open>E (n j) \<noteq> E (n k)\<close>
      unfolding E_def
      apply (rule spectral_dec_val_distinct)
      using False assms by auto
    then have \<open>orthogonal_spaces (eigenspace (E (n j)) a) (eigenspace (E (n k)) a)\<close>
      apply (rule eigenspaces_orthogonal)
      by (simp add: assms(2) selfadjoint_imp_normal) 
    with e_E show ?thesis
      using orthogonal_spaces_def by blast
  qed
  have aEe: \<open>a (e n) = E n *\<^sub>C e n\<close> for n
    by (simp add: e_E eigenspace_memberD)
  obtain \<alpha> where E_lim: \<open>(\<lambda>n. norm (E n)) \<longlonglongrightarrow> \<alpha>\<close>
    apply (rule_tac decseq_convergent[where X=\<open>\<lambda>n. cmod (E n)\<close> and B=0])
    using spectral_dec_val_decreasing[OF assms]
    by (auto intro!: simp: decseq_def E_def)
  then have \<open>\<alpha> \<ge> 0\<close>
    apply (rule LIMSEQ_le_const)
    by simp
  have aen_diff: \<open>norm (a (e (n j)) - a (e (n k))) \<ge> \<alpha> * sqrt 2\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    from E_lim and spectral_dec_val_decreasing[OF assms, folded E_def]
    have E_geq_\<alpha>: \<open>cmod (E n) \<ge> \<alpha>\<close> for n
      apply (rule_tac decseq_ge[unfolded decseq_def, rotated])
      by auto
    have \<open>(norm (a (e (n j)) - a (e (n k))))\<^sup>2 = (cmod (E (n j)))\<^sup>2 + (cmod (E (n k)))\<^sup>2\<close>
      by (simp add: polar_identity_minus aEe that ortho_en norm_e)
    also have \<open>\<dots> \<ge> \<alpha>\<^sup>2 + \<alpha>\<^sup>2\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (rule add_mono)
      using E_geq_\<alpha> \<open>\<alpha> \<ge> 0\<close> by auto
    also have \<open>\<dots> = (\<alpha> * sqrt 2)\<^sup>2\<close>
      by (simp add: algebra_simps)
    finally show ?thesis
      apply (rule power2_le_imp_le)
      by simp
  qed
  have \<open>\<alpha> = 0\<close>
  proof -
    have \<open>\<alpha> * sqrt 2 < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof -
      from \<open>strict_mono n\<close> have cauchy: \<open>Cauchy (\<lambda>k. a (e (n k)))\<close>
        using LIMSEQ_imp_Cauchy aen_lim by blast
      obtain k where k: \<open>\<forall>m\<ge>k. \<forall>na\<ge>k. dist (a *\<^sub>V e (n m)) (a *\<^sub>V e (n na)) < \<epsilon>\<close>
        apply atomize_elim
        using cauchy[unfolded Cauchy_def, rule_format, OF \<open>\<epsilon> > 0\<close>]
        by simp
      define j where \<open>j = Suc k\<close>
      then have \<open>j \<noteq> k\<close>
        by simp
      from k have \<open>dist (a (e (n j))) (a (e (n k))) < \<epsilon>\<close>
        by (simp add: j_def)
      with aen_diff[OF \<open>j \<noteq> k\<close>] show \<open>\<alpha> * sqrt 2 < \<epsilon>\<close>
        by (simp add: Cauchy_def dist_norm)
    qed
    with \<open>\<alpha> \<ge> 0\<close> show \<open>\<alpha> = 0\<close>
      by (smt (verit) linordered_semiring_strict_class.mult_pos_pos real_sqrt_le_0_iff)
  qed
  with E_lim show ?thesis
    by (auto intro!: tendsto_norm_zero_cancel simp: E_def)
qed

lemma spectral_dec_op_tendsto:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_op a \<longlonglongrightarrow> 0\<close>
  apply (rule tendsto_norm_zero_cancel)
  using spectral_dec_val_tendsto_0[OF assms]
  apply (simp add: norm_spectral_dec_op assms)
  using tendsto_norm_zero by blast 

lemma spectral_dec_op_spectral_dec_proj:
  \<open>spectral_dec_op a n = a - (\<Sum>i<n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close>
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have \<open>spectral_dec_op a (Suc n) = spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)\<close>
    by simp
  also have \<open>\<dots> = spectral_dec_op a n - spectral_dec_val a n *\<^sub>C spectral_dec_proj a n\<close> (is \<open>?lhs = ?rhs\<close>)
  proof -
    have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (spectral_dec_space a n)\<close> for h
    proof -
      have \<open>?lhs h = 0\<close>
        by (simp add: Proj_0_compl that) 
      have \<open>spectral_dec_op a n *\<^sub>V h = spectral_dec_val a n *\<^sub>C h\<close>
        by (smt (verit, best) Proj_fixes_image \<open>(spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)) *\<^sub>V h = 0\<close> cblinfun_apply_cblinfun_compose complex_vector.scale_eq_0_iff eigenspace_memberD spectral_dec_space.elims kernel_Proj kernel_cblinfun_compose kernel_memberD kernel_memberI ortho_involution that) 
      also have \<open>\<dots> = spectral_dec_val a n *\<^sub>C (spectral_dec_proj a n *\<^sub>V h)\<close>
        by (simp add: Proj_fixes_image spectral_dec_proj_def that) 
      finally
      have \<open>?rhs h = 0\<close>
        by (simp add: cblinfun.diff_left)
      with \<open>?lhs h = 0\<close> show ?thesis
        by simp
    qed
    moreover have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (- spectral_dec_space a n)\<close> for h
      by (simp add: Proj_0_compl Proj_fixes_image cblinfun.diff_left spectral_dec_proj_def that) 
    ultimately have \<open>?lhs h = ?rhs h\<close> 
      if \<open>h \<in> space_as_set (spectral_dec_space a n \<squnion> - spectral_dec_space a n) \<close> for h
      using that by (rule eq_on_ccsubspaces_sup)
    then show \<open>?lhs = ?rhs\<close>
      by (auto intro!: cblinfun_eqI simp add: )
  qed
  also have \<open>\<dots> = a - (\<Sum>i<Suc n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close>
    by (simp add: Suc.IH) 
  finally show ?case
    by -
qed


lemma sequential_tendsto_reorder:
  assumes \<open>inj g\<close>
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(f o g) \<longlonglongrightarrow> l\<close>
proof (intro lim_explicit[THEN iffD2] impI allI)
  fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
  with \<open>f \<longlonglongrightarrow> l\<close>
  obtain M where M: \<open>f m \<in> S\<close> if \<open>m \<ge> M\<close> for m
    using tendsto_obtains_N by blast 
  define N where \<open>N = Max (g -` {..<M}) + 1\<close>
  have N: \<open>g n \<ge> M\<close> if \<open>n \<ge> N\<close> for n
  proof -
    from \<open>inj g\<close> have \<open>finite (g -` {..<M})\<close>
      using finite_vimageI by blast 
    then have \<open>N > n\<close> if \<open>n \<in> g -` {..<M}\<close> for n
      using N_def that
      by (simp add: less_Suc_eq_le) 
    then have \<open>N > n\<close> if \<open>g n < M\<close> for n
      by (simp add: that) 
    with that show \<open>g n \<ge> M\<close>
      using linorder_not_less by blast 
  qed
  from N M show \<open>\<exists>N. \<forall>n\<ge>N. (f \<circ> g) n \<in> S\<close>
    by auto
qed





lemma spectral_dec_sums:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n)  sums  a\<close>
proof -
  from spectral_dec_op_tendsto[OF assms]
  have \<open>(\<lambda>n. a - spectral_dec_op a n) \<longlonglongrightarrow> a\<close>
    by (simp add: tendsto_diff_const_left_rewrite)
  moreover from spectral_dec_op_spectral_dec_proj[of a]
  have \<open>a - spectral_dec_op a n = (\<Sum>i<n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close> for n
    by simp
  ultimately show ?thesis
    by (simp add: sums_def)
qed

lemma spectral_dec_val_real:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a n \<in> \<real>\<close>
  by (metis Reals_0 assms(1) assms(2) eigenvalue_selfadj_real spectral_dec_val_eigenvalue) 


lemma spectral_dec_space_orthogonal:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<noteq> m\<close>
  shows \<open>orthogonal_spaces (spectral_dec_space a n) (spectral_dec_space a m)\<close>
proof (cases \<open>spectral_dec_val a n = 0 \<or> spectral_dec_val a m = 0\<close>)
  case True
  then show ?thesis
    by (auto intro!: simp: spectral_dec_space_def)
next
  case False
  have \<open>spectral_dec_space a n \<le> eigenspace (spectral_dec_val a n) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False spectral_dec_space.elims spectral_dec_op.simps(2) spectral_dec_op_decreasing_eigenspaces zero_le) 
  moreover have \<open>spectral_dec_space a m \<le> eigenspace (spectral_dec_val a m) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False spectral_dec_space.elims spectral_dec_op.simps(2) spectral_dec_op_decreasing_eigenspaces zero_le) 
  moreover have \<open>orthogonal_spaces (eigenspace (spectral_dec_val a n) a) (eigenspace (spectral_dec_val a m) a)\<close>
    apply (intro eigenspaces_orthogonal selfadjoint_imp_normal assms
        spectral_dec_val_distinct)
    using False by simp
  ultimately show ?thesis
    by (meson order.trans orthocomplemented_lattice_class.compl_mono orthogonal_spaces_leq_compl) 
qed

lemma spectral_dec_proj_pos: \<open>spectral_dec_proj a n \<ge> 0\<close>
  apply (auto intro!: simp: spectral_dec_proj_def)
  by (metis Proj_bot Proj_mono bot.extremum) 

lemma
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows spectral_dec_tendsto_pos_op: \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n)  sums  pos_op a\<close>  (is ?thesis1)
    and spectral_dec_tendsto_neg_op: \<open>(\<lambda>n. - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  neg_op a\<close>  (is ?thesis2)
proof -
  define I J where \<open>I = {n. spectral_dec_val a n \<ge> 0}\<close>
    and \<open>J = {n. spectral_dec_val a n \<le> 0}\<close>
  define R S where \<open>R = (\<Squnion>n\<in>I. spectral_dec_space a n)\<close>
    and \<open>S = (\<Squnion>n\<in>J. spectral_dec_space a n)\<close>
  define aR aS where \<open>aR = a o\<^sub>C\<^sub>L Proj R\<close> and \<open>aS = - a o\<^sub>C\<^sub>L Proj S\<close>
  have spectral_dec_cases: \<open>(0 < spectral_dec_val a n \<Longrightarrow> P) \<Longrightarrow>
    (spectral_dec_val a n < 0 \<Longrightarrow> P) \<Longrightarrow>
    (spectral_dec_val a n = 0 \<Longrightarrow> P) \<Longrightarrow> P\<close> for n P
    apply atomize_elim
    using reals_zero_comparable[OF spectral_dec_val_real[OF assms, of n]]
    by auto
  have PRP: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj R = spectral_dec_proj a n\<close> if \<open>n \<in> I\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: R_def SUP_upper that spectral_dec_proj_def)
  have PR0: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> I\<close> for n
    apply (cases rule: spectral_dec_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal assms
        simp: spectral_dec_proj_def R_def I_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  have PSP: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S = spectral_dec_proj a n\<close> if \<open>n \<in> J\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: S_def SUP_upper that spectral_dec_proj_def)
  have PS0: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S = 0\<close> if \<open>n \<notin> J\<close> for n
    apply (cases rule: spectral_dec_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal assms
        simp: spectral_dec_proj_def S_def J_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  from spectral_dec_sums[OF assms]
  have \<open>(\<lambda>n. (spectral_dec_val a n *\<^sub>C spectral_dec_proj a n) o\<^sub>C\<^sub>L Proj R) sums aR\<close>
    unfolding aR_def
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aR: \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n)  sums  aR\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: I_def PR0 PRP max_def)
  from sum_aR have \<open>aR \<ge> 0\<close>
    apply (rule sums_pos_cblinfun)
    by (auto intro!: spectral_dec_proj_pos scaleC_nonneg_nonneg simp: max_def)
  from spectral_dec_sums[OF assms]
  have \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S) sums - aS\<close>
    unfolding aS_def minus_minus cblinfun_compose_uminus_left
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aS': \<open>(\<lambda>n. min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  - aS\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: J_def PS0 PSP min_def)
  then have sum_aS: \<open>(\<lambda>n. - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  aS\<close>
    using sums_minus by fastforce 
  from sum_aS have \<open>aS \<ge> 0\<close>
    apply (rule sums_pos_cblinfun)
    apply (auto intro!: simp: max_def)
    by (auto intro!: spectral_dec_proj_pos scaleC_nonpos_nonneg simp: min_def)
  from sum_aR sum_aS'
  have \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n
           + min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n) sums (aR - aS)\<close>
    using sums_add by fastforce
  then have \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n) sums (aR - aS)\<close>
  proof (rule sums_cong[THEN iffD1, rotated])
    fix n
    have \<open>max 0 (spectral_dec_val a n) + min (spectral_dec_val a n) 0
          = spectral_dec_val a n\<close>
      apply (cases rule: spectral_dec_cases[of n])
      by (auto intro!: simp: max_def min_def)
    then
    show \<open>max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n +
          min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n =
          spectral_dec_val a n *\<^sub>C spectral_dec_proj a n\<close>
      by (metis scaleC_left.add) 
  qed
  with spectral_dec_sums[OF assms]
  have \<open>aR - aS = a\<close>
    using sums_unique2 by blast 
  have \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>
    by (metis (no_types, opaque_lifting) Proj_idempotent \<open>0 \<le> aR\<close> \<open>aR - aS = a\<close> aR_def add_cancel_left_left add_minus_cancel adj_0 adj_Proj adj_cblinfun_compose assms(2) cblinfun_compose_minus_right comparable_hermitean lift_cblinfun_comp(2) selfadjoint_def uminus_add_conv_diff) 
  have \<open>aR = pos_op a\<close> and \<open>aS = neg_op a\<close>
    by (intro pos_op_neg_op_unique[where b=aR and c=aS]
        \<open>aR - aS = a\<close> \<open>0 \<le> aR\<close> \<open>0 \<le> aS\<close> \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>)+
  with sum_aR and sum_aS
  show ?thesis1 and ?thesis2
    by auto
qed

lemma  spectral_dec_tendsto_abs_op:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. cmod (spectral_dec_val a n) *\<^sub>R spectral_dec_proj a n)  sums  abs_op a\<close>
proof -
  from spectral_dec_tendsto_pos_op[OF assms] spectral_dec_tendsto_neg_op[OF assms]
  have \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n
           + - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n) sums (pos_op a + neg_op a)\<close>
    using sums_add by blast
  then have \<open>(\<lambda>n. cmod (spectral_dec_val a n) *\<^sub>R spectral_dec_proj a n)  sums  (pos_op a + neg_op a)\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    using spectral_dec_val_real[OF assms]
    apply (simp add: complex_is_Real_iff cmod_def max_def min_def less_eq_complex_def scaleR_scaleC
        flip: scaleC_add_right)
    by (metis complex_surj zero_complex.code) 
  then show ?thesis
    by (simp add: pos_op_plus_neg_op) 
qed

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

lemma cspan_tc_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_trace_class ===> rel_set cr_trace_class) cspan cspan\<close>
proof (intro rel_funI rel_setI)
  fix B :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> and C
  assume \<open>rel_set cr_trace_class B C\<close>
  then have BC: \<open>B = from_trace_class ` C\<close>
    by (auto intro!: simp: cr_trace_class_def image_iff rel_set_def)

  show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close> if \<open>a \<in> cspan B\<close> for a
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and a_sum: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    from \<open>F \<subseteq> B\<close>
    obtain F' where \<open>F' \<subseteq> C\<close> and FF': \<open>F = from_trace_class ` F'\<close>
      by (auto elim!: subset_imageE simp: BC)
    define t where \<open>t = (\<Sum>x\<in>F'. f (from_trace_class x) *\<^sub>C x)\<close>
    have \<open>a = from_trace_class t\<close>
      by (simp add: a_sum t_def from_trace_class_sum scaleC_trace_class.rep_eq FF'
          sum.reindex o_def from_trace_class_inject inj_on_def)
    moreover have \<open>t \<in> cspan C\<close>
      by (metis (no_types, lifting) \<open>F' \<subseteq> C\<close> complex_vector.span_clauses(4) complex_vector.span_sum complex_vector.span_superset subsetD t_def)
    ultimately show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close>
      by (auto simp: cr_trace_class_def)
  qed

  show \<open>\<exists>a\<in>cspan B. cr_trace_class a t\<close> if \<open>t \<in> cspan C\<close> for t
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> C\<close> and t_sum: \<open>t = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    define a where \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C from_trace_class x)\<close>
    then have \<open>a = from_trace_class t\<close>
      by (simp add: t_sum a_def from_trace_class_sum scaleC_trace_class.rep_eq)
    moreover have \<open>a \<in> cspan B\<close>
      using BC \<open>F \<subseteq> C\<close> 
      by (auto intro!: complex_vector.span_base complex_vector.span_sum complex_vector.span_scale simp: a_def)
    ultimately show ?thesis
      by (auto simp: cr_trace_class_def)
  qed
qed


lemma finite_rank_tc_def': \<open>finite_rank_tc A \<longleftrightarrow> A \<in> cspan (Collect rank1_tc)\<close>
  apply transfer'
  apply (auto simp: finite_rank_def)
   apply (metis (no_types, lifting) Collect_cong rank1_trace_class)
  by (metis (no_types, lifting) Collect_cong rank1_trace_class)

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



lemma tc_butterfly_add_left: \<open>tc_butterfly (a + a') b = tc_butterfly a b + tc_butterfly a' b\<close>
  apply transfer
  by (rule butterfly_add_left)

lemma tc_butterfly_add_right: \<open>tc_butterfly a (b + b') = tc_butterfly a b + tc_butterfly a b'\<close>
  apply transfer
  by (rule butterfly_add_right)

lemma tc_butterfly_sum_left: \<open>tc_butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. tc_butterfly (\<psi> i) \<phi>)\<close>
  apply transfer
  by (rule butterfly_sum_left)

lemma tc_butterfly_sum_right: \<open>tc_butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. tc_butterfly \<psi> (\<phi> i))\<close>
  apply transfer
  by (rule butterfly_sum_right)

lemma tc_butterfly_scaleC_left[simp]: "tc_butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

lemma tc_butterfly_scaleC_right[simp]: "tc_butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

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

interpretation tensor_op_cbilinear: bounded_cbilinear tensor_op
  by simp



lemma tensor_op_mono_left:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and c :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>a \<le> b\<close> and \<open>c \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o c\<close>
proof -
  have \<open>b - a \<ge> 0\<close>
    by (simp add: assms(1))
  with \<open>c \<ge> 0\<close> have \<open>(b - a) \<otimes>\<^sub>o c \<ge> 0\<close>
    by (intro tensor_op_pos)
  then have \<open>b \<otimes>\<^sub>o c - a \<otimes>\<^sub>o c \<ge> 0\<close>
    by (simp add: tensor_op_cbilinear.diff_left)
  then show ?thesis
    by simp
qed

lemma tensor_op_mono_right:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>b \<le> c\<close> and \<open>a \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<le> a \<otimes>\<^sub>o c\<close>
proof -
  have \<open>c - b \<ge> 0\<close>
    by (simp add: assms(1))
  with \<open>a \<ge> 0\<close> have \<open>a \<otimes>\<^sub>o (c - b) \<ge> 0\<close>
    by (intro tensor_op_pos)
  then have \<open>a \<otimes>\<^sub>o c - a \<otimes>\<^sub>o b \<ge> 0\<close>
    by (simp add: tensor_op_cbilinear.diff_right)
  then show ?thesis
    by simp
qed


lemma tensor_op_mono:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and c :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>a \<le> b\<close> and \<open>c \<le> d\<close> and \<open>b \<ge> 0\<close> and \<open>c \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o d\<close>
proof -
  have \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o c\<close>
    using \<open>a \<le> b\<close> and \<open>c \<ge> 0\<close>
    by (rule tensor_op_mono_left)
  also have \<open>\<dots> \<le> b \<otimes>\<^sub>o d\<close>
    using \<open>c \<le> d\<close> and \<open>b \<ge> 0\<close>
    by (rule tensor_op_mono_right)
  finally show ?thesis
    by -
qed

lemma sandwich_tc_tensor: \<open>sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor t u) = tc_tensor (sandwich_tc E t) (sandwich_tc F u)\<close>
  apply (transfer fixing: E F)
  by (simp add: sandwich_tensor_op)


lemma tensor_tc_butterfly: "tc_tensor (tc_butterfly \<psi> \<psi>') (tc_butterfly \<phi> \<phi>') = tc_butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (transfer fixing: \<phi> \<phi>' \<psi> \<psi>') by (simp add: tensor_butterfly)


definition separating_set :: \<open>(('a \<Rightarrow> 'b) \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>separating_set P S \<longleftrightarrow> (\<forall>f g. P f \<longrightarrow> P g \<longrightarrow> (\<forall>x\<in>S. f x = g x) \<longrightarrow> f = g)\<close>

lemma separating_set_mono: \<open>S \<subseteq> T \<Longrightarrow> separating_set P S \<Longrightarrow> separating_set P T\<close>
  unfolding separating_set_def by fast

lemma separating_set_UNIV[simp]: \<open>separating_set P UNIV\<close>
  by (auto intro!: ext simp: separating_set_def)

lemma eq_from_separatingI:
  assumes \<open>separating_set P S\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  shows \<open>f = g\<close>
  using assms by (simp add: separating_set_def)

lemma cblinfun_eq_from_separatingI:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> a x = b x\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma eq_from_separatingI2:
  assumes \<open>separating_set P ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> f (h x y) = g (h x y)\<close>
  shows \<open>f = g\<close>
  apply (rule eq_from_separatingI[OF assms(1)])
  using assms(2-4) by auto

lemma cblinfun_eq_from_separatingI2:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> a (h x y) = b (h x y)\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI2)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma separating_set_bounded_clinear_dense:
  assumes \<open>ccspan S = \<top>\<close>
  shows \<open>separating_set bounded_clinear S\<close>
  using assms
  apply (auto intro!: ext simp: separating_set_def)
  apply (rule bounded_clinear_eq_on_closure[where G=S])
  apply auto
  using ccspan.rep_eq by force


lemma separating_set_bounded_clinear_tc_tensor:
  shows \<open>separating_set bounded_clinear ((\<lambda>(\<rho>,\<sigma>). tc_tensor \<rho> \<sigma>) ` (UNIV \<times> UNIV))\<close>
proof -
  have \<open>\<top> = ccspan ((\<lambda>(x, y). tc_butterfly x y) ` (range ket \<times> range ket))\<close>
    by (simp add: onb_butterflies_span_trace_class)
  also have \<open>\<dots> = ccspan ((\<lambda>(x, y, z, w). tc_butterfly (x \<otimes>\<^sub>s y) (z \<otimes>\<^sub>s w)) ` (range ket \<times> range ket \<times> range ket \<times> range ket))\<close>
    by (auto intro!: arg_cong[where f=ccspan] image_eqI simp: tensor_ell2_ket)
  also have \<open>\<dots> = ccspan ((\<lambda>(x, y, z, w). tc_tensor (tc_butterfly x z) (tc_butterfly y w)) ` (range ket \<times> range ket \<times> range ket \<times> range ket))\<close>
    by (simp add: tensor_tc_butterfly)
  also have \<open>\<dots> \<le> ccspan ((\<lambda>(\<rho>, \<sigma>). tc_tensor \<rho> \<sigma>) ` (UNIV \<times> UNIV))\<close>
    by (auto intro!: ccspan_mono)
  finally show ?thesis
    apply (rule_tac separating_set_bounded_clinear_dense)
    using top_le by blast
qed

lemma separating_setI:
  assumes \<open>\<And>f g. P f \<Longrightarrow> P g \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> f x = g x) \<Longrightarrow> f = g\<close>
  shows \<open>separating_set P S\<close>
  by (simp add: assms separating_set_def)

lemma separating_set_ket: \<open>separating_set bounded_clinear (range ket)\<close>
  by (simp add: bounded_clinear_equal_ket separating_setI)


lemma separating_set_bounded_cbilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_cbilinear h\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)

  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF assms(3)])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF assms(4)])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed

lemma separating_set_bounded_clinear_antilinear:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector conjugate_space) \<Rightarrow> _) A\<close>
  shows \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume \<open>bounded_antilinear f\<close>
  then have lin_f: \<open>bounded_clinear (to_conjugate_space o f)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>bounded_antilinear g\<close>
  then have lin_g: \<open>bounded_clinear (to_conjugate_space o g)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>f x = g x\<close> if \<open>x \<in> A\<close> for x
  then have \<open>(to_conjugate_space o f) x = (to_conjugate_space o g) x\<close> if \<open>x \<in> A\<close> for x
    by (simp add: that)
  with lin_f lin_g
  have \<open>to_conjugate_space o f = to_conjugate_space o g\<close>
    by (rule eq_from_separatingI[OF assms])
  then show \<open>f = g\<close>
    by (metis UNIV_I fun.inj_map_strong to_conjugate_space_inverse)
qed

lemma separating_set_bounded_sesquilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_sesquilinear h\<close>
  assumes sep_A: \<open>separating_set (bounded_clinear :: (_ => 'e conjugate_space) \<Rightarrow> _) A\<close>
  assumes sep_B: \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_antilinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_antilinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)

  from sep_A have sep_A': \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
    by (rule separating_set_bounded_clinear_antilinear)
  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF sep_A'])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF sep_B])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed

lemma separating_set_bounded_clinear_tc_tensor_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(\<rho>,\<sigma>). tc_tensor \<rho> \<sigma>) ` (A \<times> B))\<close>
  using separating_set_bounded_clinear_tc_tensor bounded_cbilinear_tc_tensor assms
  by (rule separating_set_bounded_cbilinear_nested)



lemma bounded_sesquilinear_tc_butterfly[iff]: \<open>bounded_sesquilinear (\<lambda>a b. tc_butterfly b a)\<close>
  by (auto intro!: bounded_sesquilinear.intro exI[of _ 1]
      simp: tc_butterfly_add_left tc_butterfly_add_right norm_tc_butterfly)

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

(* proof (rule separating_setI)
  fix f g :: \<open>('b, 'a) trace_class \<Rightarrow> 'c\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. f (tc_butterfly \<rho> \<sigma>))\<close> for \<sigma>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<sigma>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. f (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
try0
sledgehammer [dont_slice]
by -

  assume \<open>x \<in> (\<lambda>(g, h). tc_butterfly g h) ` (A \<times> B) \<Longrightarrow> f x = g x\<close> for x
  then have \<open>f (tc_butterfly \<rho> \<sigma>) = g (tc_butterfly \<rho> \<sigma>)\<close> if \<open>\<rho> \<in> A\<close> and \<open>\<sigma> \<in> B\<close> for \<rho> \<sigma>
    using that by auto
  then have \<open>(\<lambda>\<rho>. f (tc_butterfly \<rho> \<sigma>)) = (\<lambda>\<rho>. g (tc_butterfly \<rho> \<sigma>))\<close> if \<open>\<sigma> \<in> B\<close> for \<sigma>
    apply (rule eq_from_separatingI[OF assms(1), rotated -1])
    using that by auto
  then have \<open>(\<lambda>\<sigma>. f (tc_butterfly \<rho> \<sigma>)) = (\<lambda>\<sigma>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    apply auto by meson
  then have \<open>f (tc_butterfly \<rho> \<sigma>) = g (tc_butterfly \<rho> \<sigma>)\<close> for \<rho> \<sigma>
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[OF separating_set_tc_butterfly])
qed *)


lemma partial_trace_scaleC: \<open>partial_trace (c *\<^sub>C t) = c *\<^sub>C partial_trace t\<close>
  by (simp add: partial_trace_def infsum_scaleC_right compose_tcr.scaleC_right compose_tcl.scaleC_left)

lemma partial_trace_tensor: \<open>partial_trace (tc_tensor t u) = trace_tc u *\<^sub>C t\<close>
proof -
  define t' u' where \<open>t' = from_trace_class t\<close> and \<open>u' = from_trace_class u\<close>
  have 1: \<open>(\<lambda>j. ket j \<bullet>\<^sub>C (from_trace_class u *\<^sub>V ket j)) summable_on UNIV\<close>
    using  trace_exists[where B=\<open>range ket\<close> and A=\<open>from_trace_class u\<close>]
    by (simp add: summable_on_reindex o_def)
  have \<open>partial_trace (tc_tensor t u) =
      (\<Sum>\<^sub>\<infinity>j. compose_tcl (compose_tcr (tensor_ell2_right (ket j)*) (tc_tensor t u)) (tensor_ell2_right (ket j)))\<close>
    by (simp add: partial_trace_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>j. (ket j \<bullet>\<^sub>C (from_trace_class u *\<^sub>V ket j)) *\<^sub>C t)\<close>
  proof -
    have *: \<open>tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L t' \<otimes>\<^sub>o u' o\<^sub>C\<^sub>L tensor_ell2_right (ket j) =
         (ket j \<bullet>\<^sub>C (u' *\<^sub>V ket j)) *\<^sub>C t'\<close> for j
      by (auto intro!: cblinfun_eqI simp: tensor_op_ell2)
    show ?thesis
    apply (rule infsum_cong)
      by (auto intro!: from_trace_class_inject[THEN iffD1] simp flip: t'_def u'_def
        simp: * compose_tcl.rep_eq compose_tcr.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
  qed
  also have \<open>\<dots> = trace_tc u *\<^sub>C t\<close>
    by (auto intro!: infsum_scaleC_left simp: trace_tc_def trace_alt_def[OF is_onb_ket] infsum_reindex o_def 1)
  finally show ?thesis
    by -
qed

lemma partial_trace_plus: \<open>partial_trace (t + u) = partial_trace t + partial_trace u\<close>
proof -
  from partial_trace_has_sum[of t] and partial_trace_has_sum[of u]
  have \<open>((\<lambda>j. compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) t) (tensor_ell2_right (ket j))
            + compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) u) (tensor_ell2_right (ket j))) has_sum
           partial_trace t + partial_trace u) UNIV\<close> (is \<open>(?f has_sum _) _\<close>)
    by (rule has_sum_add)
  moreover have \<open>?f j = compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) (t + u)) (tensor_ell2_right (ket j))\<close> (is \<open>?f j = ?g j\<close>) for j
    by (simp add: compose_tcl.add_left compose_tcr.add_right)
  ultimately have \<open>(?g has_sum partial_trace t + partial_trace u) UNIV\<close>
    by simp
  moreover have \<open>(?g has_sum partial_trace (t + u)) UNIV\<close>
    by (simp add: partial_trace_has_sum)
  ultimately show ?thesis
    using has_sum_unique by blast
qed


lemma bounded_clinear_partial_trace[bounded_clinear, iff]: \<open>bounded_clinear partial_trace\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp add: partial_trace_plus partial_trace_scaleC partial_trace_norm_reducing)


lemma infsum_bounded_linear_invertible:
  assumes \<open>bounded_linear h\<close>
  assumes \<open>bounded_linear h'\<close>
  assumes \<open>h' o h = id\<close>
  shows \<open>infsum (\<lambda>x. h (f x)) A = h (infsum f A)\<close>
proof (cases \<open>f summable_on A\<close>)
  case True
  then show ?thesis
    using assms(1) infsum_bounded_linear by blast
next
  case False
  have \<open>\<not> (\<lambda>x. h (f x)) summable_on A\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> (\<lambda>x. h (f x)) summable_on A\<close>
    with \<open>bounded_linear h'\<close> have \<open>h' o h o f summable_on A\<close>
      by (auto intro: summable_on_bounded_linear simp: o_def)
    then have \<open>f summable_on A\<close>
      by (simp add: assms(3))
    with False show False
      by blast
  qed
  then show ?thesis
    by (simp add: False assms(1) infsum_not_exists linear_simps(3))
qed




end
