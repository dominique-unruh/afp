text \<open>Files in this directory are intended to be added to other theory files when the next AFP 
      release is near. The reason why they are currently held in a separate file is that this will
      lessen the severity of merge conflicts due to changes made to the Complex_Bounded_Operators
      session in the development branch of the AFP by the AFP maintainers.\<close>

theory BO_Unsorted
  imports Cblinfun_Code
begin

unbundle cblinfun_notation
unbundle jnf_notation
unbundle lattice_syntax
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Order.top
hide_const (open) Coset.kernel
no_notation Order.top ("\<top>\<index>") 

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
(* abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> canonical_basis_length TYPE('a)\<close> *)




lemma infsum_cblinfun_apply_isometry:
  assumes \<open>isometry A\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
proof -
  consider (summable) \<open>g summable_on S\<close> | (summable') \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    | (not_summable) \<open>\<not> g summable_on S\<close> \<open>\<not> (\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case summable'
    then have \<open>(\<lambda>x. A* *\<^sub>V A *\<^sub>V g x) summable_on S\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. A* *\<^sub>V x\<close>, rotated])
      by (intro bounded_linear_intros)
    with \<open>isometry A\<close> have \<open>g summable_on S\<close>
      by (simp add: flip: cblinfun_apply_cblinfun_compose)
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case not_summable
    then show ?thesis 
      by (simp add: infsum_not_exists)
  qed
qed

(* TODO move next to *) thm abs_summable_on_cblinfun_apply
lemma summable_on_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_right] assms
  by (rule summable_on_bounded_linear[unfolded o_def])

(* TODO move next to *) thm abs_summable_on_cblinfun_apply
lemma summable_on_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule summable_on_bounded_linear[unfolded o_def])
lemma abs_summable_on_cblinfun_apply_left:
  assumes \<open>A abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) abs_summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule abs_summable_on_bounded_linear[unfolded o_def])
lemma infsum_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A x *\<^sub>V g) S = (infsum A S) *\<^sub>V g\<close>
  apply (rule infsum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms 
  by (auto simp add: bounded_clinear.bounded_linear bounded_cbilinear_cblinfun_apply)
lemma has_sum_cblinfun_apply_left:
  assumes \<open>(A has_sum x) S\<close>
  shows \<open>((\<lambda>x. A x *\<^sub>V g) has_sum (x *\<^sub>V g)) S\<close>
  apply (rule has_sum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms by (auto simp add: bounded_clinear.bounded_linear cblinfun.bounded_clinear_left)

lemma clinear_scaleR[simp]: \<open>clinear (scaleR x)\<close>
  by (simp add: complex_vector.linear_scale_self scaleR_scaleC)

lemma continuous_cstrong_operator_topology_plus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x + g x)\<close>
  using assms
  by (auto intro!: continuous_map_add
      simp: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.add_left)

lemma continuous_cstrong_operator_topology_uminus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. - f x)\<close>
  using assms
  by (auto simp add: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.minus_left)

lemma continuous_cstrong_operator_topology_minus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro continuous_intros assms)


lemma is_Proj_id[simp]: \<open>is_Proj id_cblinfun\<close>
  apply transfer
  by (auto intro!: exI[of _ UNIV] simp: is_projection_on_def is_arg_min_def)

lemma choice2: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y\<close>
  by (meson that)

lemma choice3: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y\<close>
  by (meson that)

lemma choice4: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x)) \<and> (\<forall>x. Q4 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y \<and> Q4 x y\<close>
  by (meson that)

lemma limitin_cstrong_operator_topology:
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> (\<forall>i. ((\<lambda>j. f j *\<^sub>V i) \<longlongrightarrow> l *\<^sub>V i) F)\<close>
  by (simp add: cstrong_operator_topology_def limitin_pullback_topology 
      tendsto_coordinatewise)

lemma limitin_closure_of:
  assumes limit: \<open>limitin T f c F\<close>
  assumes in_S: \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
  assumes nontrivial: \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
proof (intro in_closure_of[THEN iffD2] conjI impI allI)
  from limit show \<open>c \<in> topspace T\<close>
    by (simp add: limitin_topspace)
  fix U
  assume \<open>c \<in> U \<and> openin T U\<close>
  with limit have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    by (simp add: limitin_def)
  with in_S have \<open>\<forall>\<^sub>F x in F. f x \<in> U \<and> f x \<in> S\<close>
    by (simp add: eventually_frequently_simps)
  with nontrivial
  show \<open>\<exists>y. y \<in> S \<and> y \<in> U\<close>
    using eventually_happens' by blast
qed


(* lemma limitin_closure_of:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) eventually_happens' in_closure_of limitin_def rangeI subsetD)
 *)

(* TODO: can be generalized for more pullback topologies, I think *)
lemma cstrong_operator_topology_in_closureI:
  assumes \<open>\<And>M \<epsilon>. \<epsilon> > 0 \<Longrightarrow> finite M \<Longrightarrow> \<exists>a\<in>A. \<forall>v\<in>M. norm ((b-a) *\<^sub>V v) \<le> \<epsilon>\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof -
  define F :: \<open>('a set \<times> real) filter\<close> where \<open>F = finite_subsets_at_top UNIV \<times>\<^sub>F at_right 0\<close>
  obtain f where fA: \<open>f M \<epsilon> \<in> A\<close> and f: \<open>v \<in> M \<Longrightarrow> norm ((f M \<epsilon> - b) *\<^sub>V v) \<le> \<epsilon>\<close> if \<open>finite M\<close> and \<open>\<epsilon> > 0\<close> for M \<epsilon> v
    apply atomize_elim
    apply (intro allI choice2)
    using assms
    by (metis cblinfun.diff_left norm_minus_commute)
  have F_props: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. finite M \<and> \<epsilon> > 0\<close>
    apply (auto intro!: eventually_prodI simp: F_def case_prod_unfold)
    by (simp add: eventually_at_right_less)
  then have inA: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. f M \<epsilon> \<in> A\<close>
    apply (rule eventually_rev_mp)
    using fA by (auto intro!: always_eventually)
  have \<open>limitin cstrong_operator_topology (case_prod f) b F\<close>
  proof -
    have \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>e > 0\<close> for e v
    proof -
      have 1: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. (finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close>
        apply (unfold F_def case_prod_unfold, rule eventually_prodI)
        using eventually_at_right that
        by (auto simp add: eventually_finite_subsets_at_top)
      have 2: \<open>norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>(finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close> for M \<epsilon>
        by (smt (verit) cblinfun.diff_left f that)
      show ?thesis
        using 1 apply (rule eventually_mono)
        using 2 by auto
    qed
    then have \<open>((\<lambda>(M,\<epsilon>). f M \<epsilon> *\<^sub>V v) \<longlongrightarrow> b *\<^sub>V v) F\<close> for v
      by (simp add: tendsto_iff dist_norm case_prod_unfold)
    then show ?thesis
      by (simp add: case_prod_unfold limitin_cstrong_operator_topology)
  qed
  then show ?thesis
    apply (rule limitin_closure_of)
    using inA by (auto simp: F_def case_prod_unfold prod_filter_eq_bot)
qed



lemma sandwich_arg_compose:
  assumes \<open>isometry U\<close>
  shows \<open>sandwich U x o\<^sub>C\<^sub>L sandwich U y = sandwich U (x o\<^sub>C\<^sub>L y)\<close>
  apply (simp add: sandwich_apply)
  by (metis (no_types, lifting) lift_cblinfun_comp(2) assms cblinfun_compose_id_right isometryD)



lemma isometry_inj:
  assumes \<open>isometry U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule inj_on_inverseI[where g=\<open>U*\<close>])
  using assms by (simp flip: cblinfun_apply_cblinfun_compose)

lemma unitary_inj:
  assumes \<open>unitary U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule isometry_inj)
  using assms by simp

lemma unitary_adj_inv: \<open>unitary U \<Longrightarrow> cblinfun_apply (U*) = inv (cblinfun_apply U)\<close>
  apply (rule inj_imp_inv_eq[symmetric])
   apply (simp add: unitary_inj)
  unfolding unitary_def
  by (simp flip: cblinfun_apply_cblinfun_compose)

lemma isometry_cinner_both_sides:
  assumes \<open>isometry U\<close>
  shows \<open>cinner (U x) (U y) = cinner x y\<close>
  using assms by (simp add: flip: cinner_adj_right cblinfun_apply_cblinfun_compose)

lemma isometry_image_is_ortho_set:
  assumes \<open>is_ortho_set A\<close>
  assumes \<open>isometry U\<close>
  shows \<open>is_ortho_set (U ` A)\<close>
  using assms apply (auto simp add: is_ortho_set_def isometry_cinner_both_sides)
  by (metis cinner_eq_zero_iff isometry_cinner_both_sides)

lemma unitary_image_onb:
  assumes \<open>is_onb A\<close>
  assumes \<open>unitary U\<close>
  shows \<open>is_onb (U ` A)\<close>
  using assms
  by (auto simp add: is_onb_def isometry_image_is_ortho_set isometry_preserves_norm
      simp flip: cblinfun_image_ccspan)

lemma cspan_compose_closed:
  assumes \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L b \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close> and \<open>b \<in> cspan A\<close>
  shows \<open>a o\<^sub>C\<^sub>L b \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  from \<open>b \<in> cspan A\<close>
  obtain G g where \<open>finite G\<close> and \<open>G \<subseteq> A\<close> and b_def: \<open>b = (\<Sum>x\<in>G. g x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  have \<open>a o\<^sub>C\<^sub>L b = (\<Sum>(x,y)\<in>F\<times>G. (f x *\<^sub>C x) o\<^sub>C\<^sub>L (g y *\<^sub>C y))\<close>
    apply (simp add: a_def b_def cblinfun_compose_sum_left)
    by (auto intro!: sum.cong simp add: cblinfun_compose_sum_right scaleC_sum_right sum.cartesian_product case_prod_beta)
  also have \<open>\<dots> = (\<Sum>(x,y)\<in>F\<times>G. (f x * g y) *\<^sub>C (x o\<^sub>C\<^sub>L y))\<close>
    by (metis (no_types, opaque_lifting) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_scaleC)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>G \<subseteq> A\<close> \<open>F \<subseteq> A\<close>
    apply (auto intro!: complex_vector.span_sum complex_vector.span_scale 
        simp: complex_vector.span_clauses)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

lemma cspan_adj_closed:
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close>
  shows \<open>a* \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>a* = (\<Sum>x\<in>F. cnj (f x) *\<^sub>C x*)\<close>
    by (auto simp: sum_adj)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>F \<subseteq> A\<close>
    by (auto intro!: complex_vector.span_sum complex_vector.span_scale simp: complex_vector.span_clauses)
  finally show ?thesis
    by -
qed

lemma kernel_square[simp]: \<open>kernel (A* o\<^sub>C\<^sub>L A) = kernel A\<close>
proof (intro ccsubspace_eqI iffI)
  fix x
  assume \<open>x \<in> space_as_set (kernel A)\<close>
  then show \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
    by (simp add: kernel.rep_eq)
next
  fix x
  assume \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
  then have \<open>A* *\<^sub>V A *\<^sub>V x = 0\<close>
    by (simp add: kernel.rep_eq)
  then have \<open>(A *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x) = 0\<close>
    by (metis cinner_adj_right cinner_zero_right)
  then have \<open>A *\<^sub>V x = 0\<close>
    by auto
  then show \<open>x \<in> space_as_set (kernel A)\<close>
    by (simp add: kernel.rep_eq)
qed

lemma Proj_on_image [simp]: \<open>Proj S *\<^sub>S S = S\<close>
  by (metis Proj_idempotent Proj_range cblinfun_compose_image)

lemma not_not_singleton_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::zero\<close>
  using that unfolding class.not_singleton_def by auto

lemma not_not_singleton_cblinfun_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  apply (rule cblinfun_eqI)
  apply (subst not_not_singleton_zero[OF that])
  by simp

lemma cblinfun_norm_approx_witness':
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using complex_normed_vector_axioms True assms
    by (rule cblinfun_norm_approx_witness[internalize_sort' 'a])
  then have \<open>norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma any_norm_exists:
  assumes \<open>n \<ge> 0\<close>
  shows \<open>\<exists>\<psi>::'a::{real_normed_vector,not_singleton}. norm \<psi> = n\<close>
proof -
  obtain \<psi> :: 'a where \<open>\<psi> \<noteq> 0\<close>
    using not_singleton_card
    by force
  then have \<open>norm (n *\<^sub>R sgn \<psi>) = n\<close>
    using assms by (auto simp: sgn_div_norm abs_mult)
  then show ?thesis
    by blast
qed




lemma sot_weaker_than_norm_limitin: \<open>limitin cstrong_operator_topology a A F\<close> if \<open>(a \<longlongrightarrow> A) F\<close>
proof -
  from that have \<open>((\<lambda>x. a x *\<^sub>V \<psi>) \<longlongrightarrow> A \<psi>) F\<close> for \<psi>
    by (auto intro!: cblinfun.tendsto)
  then show ?thesis
    by (simp add: limitin_cstrong_operator_topology)
qed

instance cblinfun :: (chilbert_space, chilbert_space) ordered_complex_vector
  by intro_classes

lemma less_eq_scaled_id_norm: 
  assumes \<open>norm A \<le> c\<close> and \<open>A = A*\<close>
  shows \<open>A \<le> complex_of_real c *\<^sub>C id_cblinfun\<close>
proof -
  have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> complex_of_real c\<close> if \<open>norm x = 1\<close> for x
  proof -
    have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> norm (A *\<^sub>V x)\<close>
      by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right1 that)
    also have \<open>\<dots> \<le> norm A\<close>
      by (metis more_arith_simps(6) norm_cblinfun that)
    also have \<open>\<dots> \<le> c\<close>
      by (rule assms)
    finally have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> c\<close>
      by -
    moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close>
      by (metis assms(2) cinner_hermitian_real)
    ultimately show ?thesis
      by (metis cnorm_le_square complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff dual_order.trans reals_zero_comparable)
  qed
  then show ?thesis
    by (smt (verit) cblinfun.scaleC_left cblinfun_id_cblinfun_apply cblinfun_leI cinner_scaleC_right cnorm_eq_1 mult_cancel_left2)
qed

lemma abs_summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp: norm_scaleC)

lemma abs_summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms simp: norm_scaleC)


lemma abs_summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp flip: real_norm_def)

lemma abs_summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms)


(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"


unbundle
  no_cblinfun_notation
  no_jnf_notation
  no_lattice_syntax

end
