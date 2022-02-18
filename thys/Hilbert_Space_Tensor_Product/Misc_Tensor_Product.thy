theory Misc_Tensor_Product
  imports Complex_Bounded_Operators.Complex_L2
begin

unbundle cblinfun_notation

(* TODO move, explain *)
lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis

lemma on_closure_leI:
  fixes f g :: \<open>'a::topological_space \<Rightarrow> 'b::linorder_topology\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x\<close>
  assumes xS: \<open>x \<in> closure S\<close>
  assumes cont: \<open>continuous_on UNIV f\<close> \<open>continuous_on UNIV g\<close> (* Is "isCont f x" "isCont g x" sufficient? *)
  shows \<open>f x \<le> g x\<close>
proof -
  define X where \<open>X = {x. f x \<le> g x}\<close>
  have \<open>closed X\<close>
    using cont by (simp add: X_def closed_Collect_le)
  moreover have \<open>S \<subseteq> X\<close>
    by (simp add: X_def eq subsetI)
  ultimately have \<open>closure S \<subseteq> X\<close>
    using closure_minimal by blast
  with xS have \<open>x \<in> X\<close>
    by auto
  then show ?thesis
    using X_def by blast
qed

lemma norm_cblinfun_bound_dense:
  assumes \<open>0 \<le> b\<close>
  assumes S: \<open>closure S = UNIV\<close>
  assumes bound: \<open>\<And>x. x\<in>S \<Longrightarrow> norm (cblinfun_apply f x) \<le> b * norm x\<close>
  shows \<open>norm f \<le> b\<close>
proof -
  have 1: \<open>continuous_on UNIV (\<lambda>a. norm (f *\<^sub>V a))\<close>
    apply (intro continuous_on_norm linear_continuous_on)
    by (simp add: Complex_Vector_Spaces.bounded_clinear.bounded_linear cblinfun.bounded_clinear_right)
  have 2: \<open>continuous_on UNIV (\<lambda>a. b * norm a)\<close>
    using continuous_on_mult_left continuous_on_norm_id by blast
  have \<open>norm (cblinfun_apply f x) \<le> b * norm x\<close> for x
    apply (rule on_closure_leI[where x=x and S=S])
    using S bound 1 2 by auto
  then show \<open>norm f \<le> b\<close>
    apply (rule_tac norm_cblinfun_bound)
    using \<open>0 \<le> b\<close> by auto
qed

lemma orthogonal_complement_of_cspan: \<open>orthogonal_complement A = orthogonal_complement (cspan A)\<close>
  by (metis (no_types, opaque_lifting) closed_csubspace.subspace complex_vector.span_minimal complex_vector.span_superset double_orthogonal_complement_increasing orthogonal_complement_antimono orthogonal_complement_closed_subspace subset_antisym)

lemma orthogonal_complement_orthogonal_complement_closure_cspan:
  \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close> for S :: \<open>'a::chilbert_space set\<close>
proof -
  have \<open>orthogonal_complement (orthogonal_complement S) = orthogonal_complement (orthogonal_complement (closure (cspan S)))\<close>
    by (simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  also have \<open>\<dots> = closure (cspan S)\<close>
    by simp
  finally show \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close>
    by -
qed

lemma dense_span_separating: \<open>closure (cspan S) = UNIV \<Longrightarrow> bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
proof -
  fix F G :: \<open>'a \<Rightarrow> 'b\<close>
  assume dense: \<open>closure (cspan S) = UNIV\<close>
  assume [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
  assume \<open>\<forall>x\<in>S. F x = G x\<close>
  then have \<open>F x = G x\<close> if \<open>x \<in> cspan S\<close> for x
    apply (rule_tac complex_vector.linear_eq_on[of F G _ S])
    using that by (auto simp: bounded_clinear.clinear)
  then show \<open>F = G\<close>
    apply (rule_tac ext)
    apply (rule on_closure_eqI[of \<open>cspan S\<close> F G])
    using dense by (auto intro!: continuous_at_imp_continuous_on clinear_continuous_at)
qed

lemma separating_dense_span: 
  assumes \<open>\<And>F G :: 'a::chilbert_space \<Rightarrow> 'b::{complex_normed_vector,not_singleton}. 
           bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
  shows \<open>closure (cspan S) = UNIV\<close>
proof -
  have \<open>\<psi> = 0\<close> if \<open>\<psi> \<in> orthogonal_complement S\<close> for \<psi>
  proof -
    obtain \<phi> :: 'b where \<open>\<phi> \<noteq> 0\<close>
      by fastforce
    have \<open>(\<lambda>x. cinner \<psi> x *\<^sub>C \<phi>) = (\<lambda>_. 0)\<close> 
      apply (rule assms[rule_format])
      using orthogonal_complement_orthoI that
      by (auto simp add: bounded_clinear_cinner_right bounded_clinear_scaleC_const)
    then have \<open>cinner \<psi> \<psi> = 0\<close>
      by (meson \<open>\<phi> \<noteq> 0\<close> scaleC_eq_0_iff)
    then show \<open>\<psi> = 0\<close>
      by auto
  qed
  then have \<open>orthogonal_complement (orthogonal_complement S) = UNIV\<close>
    by (metis UNIV_eq_I cinner_zero_right orthogonal_complementI)
  then show \<open>closure (cspan S) = UNIV\<close>
    by (simp add: orthogonal_complement_orthogonal_complement_closure_cspan)
qed


lemma ortho_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> closure (cspan B) = UNIV\<close>
proof -
  define on where \<open>on B \<longleftrightarrow> B \<supseteq> S \<and> is_ortho_set B\<close> for B :: \<open>'a set\<close>
  have \<open>\<exists>B\<in>Collect on. \<forall>B'\<in>Collect on. B \<subseteq> B' \<longrightarrow> B' = B\<close>
  proof (rule subset_Zorn_nonempty; simp)
    show \<open>\<exists>S. on S\<close>
      apply (rule exI[of _ S])
      using assms on_def by fastforce
  next
    fix C :: \<open>'a set set\<close>
    assume \<open>C \<noteq> {}\<close>
    assume \<open>subset.chain (Collect on) C\<close>
    then have C_on: \<open>B \<in> C \<Longrightarrow> on B\<close> and C_order: \<open>B \<in> C \<Longrightarrow> B' \<in> C \<Longrightarrow> B \<subseteq> B' \<or> B' \<subseteq> B\<close> for B B'
      by (auto simp: subset.chain_def)
    have \<open>is_orthogonal x y\<close> if \<open>x\<in>\<Union>C\<close> \<open>y\<in>\<Union>C\<close> \<open>x \<noteq> y\<close> for x y
      by (smt (verit) UnionE C_order C_on on_def is_ortho_set_def subsetD that(1) that(2) that(3))
    moreover have \<open>0 \<notin> \<Union> C\<close>
      by (meson UnionE C_on is_ortho_set_def on_def)
    moreover have \<open>\<Union>C \<supseteq> S\<close>
      using C_on \<open>C \<noteq> {}\<close> on_def by blast
    ultimately show \<open>on (\<Union> C)\<close>
      unfolding on_def is_ortho_set_def by simp
  qed
  then obtain B where \<open>on B\<close> and B_max: \<open>B' \<supseteq> B \<Longrightarrow> on B' \<Longrightarrow> B=B'\<close> for B'
    by auto
  have \<open>\<psi> = 0\<close> if \<psi>ortho: \<open>\<forall>b\<in>B. is_orthogonal \<psi> b\<close> for \<psi> :: 'a
  proof (rule ccontr)
    assume \<open>\<psi> \<noteq> 0\<close>
    define \<phi> B' where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close> and \<open>B' = B \<union> {\<phi>}\<close>
    have [simp]: \<open>norm \<phi> = 1\<close>
      using \<open>\<psi> \<noteq> 0\<close> by (auto simp: \<phi>_def)
    have \<phi>ortho: \<open>is_orthogonal \<phi> b\<close> if \<open>b \<in> B\<close> for b
      using \<psi>ortho that \<phi>_def  apply auto
      by (simp add: scaleR_scaleC)
    have orthoB': \<open>is_orthogonal x y\<close> if \<open>x\<in>B'\<close> \<open>y\<in>B'\<close> \<open>x \<noteq> y\<close> for x y
      using that \<open>on B\<close> \<phi>ortho \<phi>ortho[THEN is_orthogonal_sym[THEN iffD1]]
      by (auto simp: B'_def on_def is_ortho_set_def)
    have B'0: \<open>0 \<notin> B'\<close>
      using B'_def \<open>norm \<phi> = 1\<close> \<open>on B\<close> is_ortho_set_def on_def by fastforce
    have \<open>S \<subseteq> B'\<close>
      using B'_def \<open>on B\<close> on_def by auto
    from orthoB' B'0 \<open>S \<subseteq> B'\<close> have \<open>on B'\<close>
      by (simp add: on_def is_ortho_set_def)
    with B_max have \<open>B = B'\<close>
      by (metis B'_def Un_upper1)
    then have \<open>\<phi> \<in> B\<close>
      using B'_def by blast
    then have \<open>is_orthogonal \<phi> \<phi>\<close>
      using \<phi>ortho by blast
    then show False
      using B'0 \<open>B = B'\<close> \<open>\<phi> \<in> B\<close> by fastforce
  qed 
  then have \<open>orthogonal_complement B = {0}\<close>
    by (auto simp: orthogonal_complement_def)
  then have \<open>UNIV = orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (closure (cspan B)))\<close>
    by (metis (mono_tags, opaque_lifting) \<open>orthogonal_complement B = {0}\<close> cinner_zero_left complex_vector.span_superset empty_iff insert_iff orthogonal_complementI orthogonal_complement_antimono orthogonal_complement_of_closure subsetI subset_antisym)
  also have \<open>\<dots> = closure (cspan B)\<close>
    apply (rule double_orthogonal_complement_id)
    by simp
  finally have \<open>closure (cspan B) = UNIV\<close>
    by simp
  with \<open>on B\<close> show ?thesis
    by (auto simp: on_def)
qed

lemma (in vector_space) span_image_scale:
  assumes nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
  shows "span ((\<lambda>x. c x *s x) ` S) = span S"
proof
  have \<open>((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (metis (mono_tags, lifting) image_subsetI in_mono local.span_superset local.subspace_scale local.subspace_span)
  then show \<open>span ((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (simp add: local.span_minimal)
next
  have \<open>x \<in> span ((\<lambda>x. c x *s x) ` S)\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>x = inverse (c x) *s c x *s x\<close>
      by (simp add: nz that)
    moreover have \<open>c x *s x \<in> (\<lambda>x. c x *s x) ` S\<close>
      using that by blast
    ultimately show ?thesis
      by (metis local.span_base local.span_scale)
  qed
  then show \<open>span S \<subseteq> span ((\<lambda>x. c x *s x) ` S)\<close>
    by (simp add: local.span_minimal subsetI)
qed

definition is_onb where \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> ccspan E = \<top>\<close>

lemma orthonormal_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_onb B\<close>
proof -
  from \<open>is_ortho_set S\<close>
  obtain B where \<open>is_ortho_set B\<close> and \<open>B \<supseteq> S\<close> and \<open>closure (cspan B) = UNIV\<close>
    using ortho_basis_exists by blast
  define B' where \<open>B' = (\<lambda>x. x /\<^sub>R norm x) ` B\<close>
  have \<open>S = (\<lambda>x. x /\<^sub>R norm x) ` S\<close>
    by (simp add: assms(2))
  then have \<open>B' \<supseteq> S\<close>
    using B'_def \<open>S \<subseteq> B\<close> by blast
  moreover 
  have \<open>ccspan B' = \<top>\<close>
    apply (transfer fixing: B')
    apply (simp add: B'_def scaleR_scaleC)
    apply (subst complex_vector.span_image_scale)
    using \<open>is_ortho_set B\<close> \<open>closure (cspan B) = UNIV\<close> is_ortho_set_def by auto
  moreover have \<open>is_ortho_set B'\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis cinner_simps(5) is_orthogonal_sym mult_zero_right scaleR_scaleC)
  moreover have \<open>\<forall>b\<in>B'. norm b = 1\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis field_class.field_inverse norm_eq_zero)
  ultimately show ?thesis
    by (auto simp: is_onb_def)
qed


lemma bounded_clinear_equal_ket:
  fixes f g :: \<open>'a ell2 \<Rightarrow> _\<close>
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>bounded_clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule bounded_clinear_eq_on[of f g \<open>range ket\<close>])
  using assms by auto

lemma bounded_antilinear_equal_ket:
  fixes f g :: \<open>'a ell2 \<Rightarrow> _\<close>
  assumes \<open>bounded_antilinear f\<close>
  assumes \<open>bounded_antilinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule bounded_antilinear_eq_on[of f g \<open>range ket\<close>])
  using assms by auto

lemma cspan_eqI:
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> a\<in>cspan B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> b\<in>cspan A\<close>
  shows \<open>cspan A = cspan B\<close>
  apply (rule complex_vector.span_subspace[rotated])
    apply (rule complex_vector.span_minimal)
  using assms by auto

lemma inv_prod_swap[simp]: \<open>inv prod.swap = prod.swap\<close>
  by (simp add: inv_unique_comp)

lemma limitin_pullback_topology: 
  \<open>limitin (pullback_topology A g T) f l F \<longleftrightarrow> l\<in>A \<and> (\<forall>\<^sub>F x in F. f x \<in> A) \<and> limitin T (g o f) (g l) F\<close>
  apply (simp add: topspace_pullback_topology limitin_def openin_pullback_topology imp_ex flip: ex_simps(1))
  apply rule
   apply simp
   apply safe
  using eventually_mono apply fastforce
   apply (simp add: eventually_conj_iff)
  by (simp add: eventually_conj_iff)

lemma tendsto_coordinatewise: \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
proof (intro iffI allI)
  assume asm: \<open>(f \<longlongrightarrow> l) F\<close>
  then show \<open>((\<lambda>i. f i x) \<longlongrightarrow> l x) F\<close> for x
    apply (rule continuous_on_tendsto_compose[where s=UNIV, rotated])
    by auto
next
  assume asm: \<open>(\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
  show \<open>(f \<longlongrightarrow> l) F\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
    from product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>l \<in> S\<close>]
    obtain U where lU: \<open>l \<in> Pi UNIV U\<close> and openU: \<open>\<And>x. open (U x)\<close> and finiteD: \<open>finite {x. U x \<noteq> UNIV}\<close> and US: \<open>Pi UNIV U \<subseteq> S\<close>
      by (auto simp add: PiE_UNIV_domain)

    define D where \<open>D = {x. U x \<noteq> UNIV}\<close>
    with finiteD have finiteD: \<open>finite D\<close>
      by simp
    have PiUNIV: \<open>t \<in> Pi UNIV U \<longleftrightarrow> (\<forall>x\<in>D. t x \<in> U x)\<close> for t
      using D_def by blast

    have f_Ui: \<open>\<forall>\<^sub>F i in F. f i x \<in> U x\<close> for x
      using asm[rule_format, of x] openU[of x]
      using lU topological_tendstoD by fastforce

    have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>D. f x i \<in> U i\<close>
      using finiteD
    proof induction
      case empty
      then show ?case
        by simp
    next
      case (insert x F)
      with f_Ui show ?case
        by (simp add: eventually_conj_iff)
    qed

    then show \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
      using US by (simp add: PiUNIV eventually_mono in_mono)
  qed
qed

lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover


definition rel_topology :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a topology \<Rightarrow> 'b topology \<Rightarrow> bool)\<close> where
  \<open>rel_topology R S T \<longleftrightarrow> (rel_fun (rel_set R) (=)) (openin S) (openin T)\<close>

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R ===> (=)) openin openin\<close>
  by (auto simp add: rel_fun_def rel_topology_def)

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total R\<close>
  shows \<open>(rel_topology R ===> rel_set R) topspace topspace\<close>
  unfolding topspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total S\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>bi_total R\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_topology S ===> (R ===> S) ===> (=)) continuous_map continuous_map\<close>
  unfolding continuous_map_def
  by transfer_prover


lemma limitin_closure_of:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) eventually_happens' in_closure_of limitin_def rangeI subsetD)

lemma limitin_closedin:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> S\<close>
  by (metis assms(1) assms(2) assms(3) assms(4) closure_of_eq limitin_closure_of)


(* TODO: bounded_linear is enough *)
lemma infsum_bounded_clinear:
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  apply (rule infsum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right
  by (auto simp: clinear_continuous_within)

(* TODO: bounded_linear is enough *)
lemma has_sum_bounded_clinear: 
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close>
  apply (rule has_sum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right apply auto
  using clinear_continuous_within isCont_def by fastforce

(* TODO: bounded_linear is enough *)
lemma abs_summable_on_bounded_clinear: 
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(f o g) abs_summable_on S\<close>
proof -
  have bound: \<open>norm (f (g x)) \<le> onorm f * norm (g x)\<close> for x
    apply (rule onorm)
    by (simp add: bounded_clinear.bounded_linear assms(1))

  from assms(2) have \<open>(\<lambda>x. onorm f *\<^sub>C g x) abs_summable_on S\<close>
    by (auto simp: norm_scaleC intro!: summable_on_cmult_right)
  then have \<open>(\<lambda>x. f (g x)) abs_summable_on S\<close>
    apply (rule abs_summable_on_comparison_test)
    using bound by (auto simp: bounded_clinear.bounded_linear assms(1) onorm_pos_le)
  then show ?thesis
    by auto
qed

lemma infsum_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
  apply (rule infsum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma has_sum_cblinfun_apply:
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (\<lambda>x. A *\<^sub>V g x) S (A *\<^sub>V x)\<close>
  apply (rule has_sum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma abs_summable_on_cblinfun_apply:
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) abs_summable_on S\<close>
  using cblinfun.bounded_clinear_right assms
  by (rule abs_summable_on_bounded_clinear[unfolded o_def])

lemma trunc_ell2_UNIV[simp]: \<open>trunc_ell2 UNIV \<psi> = \<psi>\<close>
  apply transfer by simp

lemma ell2_norm_square: \<open>(ell2_norm x)\<^sup>2 = (\<Sum>\<^sub>\<infinity>i. (cmod (x i))\<^sup>2)\<close>
  unfolding ell2_norm_def
  apply (subst real_sqrt_pow2)
   apply (meson Extra_General.infsum_nonneg zero_le_power2)
  by simp

lemma trunc_ell2_norm_mono: \<open>M \<subseteq> N \<Longrightarrow> norm (trunc_ell2 M \<psi>) \<le> norm (trunc_ell2 N \<psi>)\<close>
proof (rule power2_le_imp_le[rotated], force, transfer)
  fix M N :: \<open>'a set\<close> and \<psi> :: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>M \<subseteq> N\<close> and \<open>has_ell2_norm \<psi>\<close>
  have \<open>(ell2_norm (\<lambda>i. if i \<in> M then \<psi> i else 0))\<^sup>2 = (\<Sum>\<^sub>\<infinity>i\<in>M. (cmod (\<psi> i))\<^sup>2)\<close>
    unfolding ell2_norm_square
    apply (rule infsum_cong_neutral)
    by auto
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>N. (cmod (\<psi> i))\<^sup>2)\<close>
    apply (rule infsum_mono2)
    using \<open>has_ell2_norm \<psi>\<close> \<open>M \<subseteq> N\<close>
    by (auto simp add: ell2_norm_square has_ell2_norm_def simp flip: norm_power intro: summable_on_subset_banach)
  also have \<open>\<dots> = (ell2_norm (\<lambda>i. if i \<in> N then \<psi> i else 0))\<^sup>2\<close>
    unfolding ell2_norm_square
    apply (rule infsum_cong_neutral)
    by auto
  finally show \<open>(ell2_norm (\<lambda>i. if i \<in> M then \<psi> i else 0))\<^sup>2 \<le> (ell2_norm (\<lambda>i. if i \<in> N then \<psi> i else 0))\<^sup>2\<close>
    by -
qed

lemma trunc_ell2_twice[simp]: \<open>trunc_ell2 M (trunc_ell2 N \<psi>) = trunc_ell2 (M\<inter>N) \<psi>\<close>
  apply transfer by auto

lemma trunc_ell2_union: \<open>trunc_ell2 (M \<union> N) \<psi> = trunc_ell2 M \<psi> + trunc_ell2 N \<psi> - trunc_ell2 (M\<inter>N) \<psi>\<close>
  apply transfer by auto

lemma trunc_ell2_union_disjoint: \<open>M\<inter>N = {} \<Longrightarrow> trunc_ell2 (M \<union> N) \<psi> = trunc_ell2 M \<psi> + trunc_ell2 N \<psi>\<close>
  by (simp add: trunc_ell2_union)

lemma trunc_ell2_union_Diff: \<open>M \<subseteq> N \<Longrightarrow> trunc_ell2 (N-M) \<psi> = trunc_ell2 N \<psi> - trunc_ell2 M \<psi>\<close>
  using trunc_ell2_union_disjoint[where M=\<open>N-M\<close> and N=M and \<psi>=\<psi>]
  by (simp add: Un_commute inf.commute le_iff_sup)


(* TODO replace existing lemma (strengthening) *)
thm finite_subsets_at_top_inter
lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) = finite_subsets_at_top A"
proof (subst filter_eq_iff, intro allI iffI)
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (finite_subsets_at_top A)"
  then show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
next
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
  then obtain X where \<open>finite X\<close> \<open>X \<subseteq> B\<close> and P: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> P (Y \<inter> A)\<close> for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by metis
  have *: \<open>finite Y \<Longrightarrow> X \<inter> A \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P Y\<close> for Y
    using P[where Y=\<open>Y \<union> (B-A)\<close>]
    apply (subgoal_tac \<open>(Y \<union> (B - A)) \<inter> A = Y\<close>)
    apply (smt (verit, best) Int_Un_distrib2 Int_Un_eq(4) P Un_subset_iff \<open>X \<subseteq> B\<close> \<open>finite X\<close> assms finite_UnI inf.orderE sup_ge2)
    by auto
  show "eventually P (finite_subsets_at_top A)"
    unfolding eventually_finite_subsets_at_top
    apply (rule exI[of _ \<open>X\<inter>A\<close>])
    by (auto simp: \<open>finite X\<close> intro!: *)
qed


lemma trunc_ell2_lim: \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top M)\<close>
proof -
  have \<open>((\<lambda>S. trunc_ell2 S (trunc_ell2 M \<psi>)) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top UNIV)\<close>
    using trunc_ell2_lim_at_UNIV by blast
  then have \<open>((\<lambda>S. trunc_ell2 (S\<inter>M) \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top UNIV)\<close>
    by simp
  then show \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) (finite_subsets_at_top M)\<close>
    unfolding filterlim_def
    apply (subst (asm) filtermap_filtermap[where g=\<open>\<lambda>S. S\<inter>M\<close>, symmetric])
    apply (subst (asm) finite_subsets_at_top_inter[where A=M and B=UNIV])
    by auto
qed

lemma trunc_ell2_lim_general:
  assumes big: \<open>\<And>G. finite G \<Longrightarrow> G \<subseteq> M \<Longrightarrow> (\<forall>\<^sub>F H in F. H \<supseteq> G)\<close>
  assumes small: \<open>\<forall>\<^sub>F H in F. H \<subseteq> M\<close>
  shows \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> trunc_ell2 M \<psi>) F\<close>
proof (rule tendstoI)
  fix e :: real assume \<open>e > 0\<close>
  from trunc_ell2_lim[THEN tendsto_iff[THEN iffD1], rule_format, OF \<open>e > 0\<close>, where M=M and \<psi>=\<psi>]
  obtain G where \<open>finite G\<close> and \<open>G \<subseteq> M\<close> and 
    close: \<open>dist (trunc_ell2 G \<psi>) (trunc_ell2 M \<psi>) < e\<close>
    apply atomize_elim
    unfolding eventually_finite_subsets_at_top
    by blast
  from \<open>finite G\<close> \<open>G \<subseteq> M\<close> and big
  have \<open>\<forall>\<^sub>F H in F. H \<supseteq> G\<close>
    by -
  with small have \<open>\<forall>\<^sub>F H in F. H \<subseteq> M \<and> H \<supseteq> G\<close>
    by (simp add: eventually_conj_iff)
  then show \<open>\<forall>\<^sub>F H in F. dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) < e\<close>
  proof (rule eventually_mono)
    fix H assume GHM: \<open>H \<subseteq> M \<and> H \<supseteq> G\<close>
    have \<open>dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) = norm (trunc_ell2 (M-H) \<psi>)\<close>
      by (simp add: GHM dist_ell2_def norm_minus_commute trunc_ell2_union_Diff)
    also have \<open>\<dots> \<le> norm (trunc_ell2 (M-G) \<psi>)\<close>
      by (simp add: Diff_mono GHM trunc_ell2_norm_mono)
    also have \<open>\<dots>  = dist (trunc_ell2 G \<psi>) (trunc_ell2 M \<psi>)\<close>
      by (simp add: \<open>G \<subseteq> M\<close> dist_ell2_def norm_minus_commute trunc_ell2_union_Diff)
    also have \<open>\<dots> < e\<close>
      using close by simp
    finally show \<open>dist (trunc_ell2 H \<psi>) (trunc_ell2 M \<psi>) < e\<close>
      by -
  qed
qed


lemma closure_nhds_principal: \<open>a \<in> closure A \<longleftrightarrow> nhds a \<sqinter> principal A \<noteq> \<bottom>\<close>
proof (rule iffI)
  show \<open>nhds a \<sqinter> principal A \<noteq> \<bottom>\<close> if \<open>a \<in> closure A\<close>
    apply (cases \<open>a \<in> A\<close>)
     apply (auto simp: filter_eq_iff eventually_inf eventually_principal eventually_nhds) apply blast
    apply (subgoal_tac \<open>a islimpt A\<close>)
     apply ( simp add: filter_eq_iff eventually_inf eventually_principal eventually_nhds islimpt_def)
     apply meson
    by (simp add: islimpt_in_closure that)
  show \<open>a \<in> closure A\<close> if \<open>nhds a \<sqinter> principal A \<noteq> \<bottom>\<close>
    by (metis Diff_empty Diff_insert0 at_within_def closure_subset not_in_closure_trivial_limitI subsetD that)
qed


lemma limit_in_closure:
  assumes lim: \<open>(f \<longlongrightarrow> x) F\<close>
  assumes nt: \<open>F \<noteq> \<bottom>\<close>
  assumes inA: \<open>\<forall>\<^sub>F x in F. f x \<in> A\<close>
  shows \<open>x \<in> closure A\<close>
  apply (cases \<open>x \<in> A\<close>)
   apply (meson closure_subset in_mono)
  apply (auto simp: closure_def filterlim_def islimpt_def le_filter_def eventually_filtermap
      eventually_nhds image_def)
  by (smt (verit, ccfv_threshold) assms(1) assms(3) eventually_elim2 nt tendsto_def trivial_limit_eq)

lemma ket_CARD_1_is_1: \<open>ket x = 1\<close> for x :: \<open>'a::CARD_1\<close>
  apply transfer by simp

lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin 
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)

(* TODO replace *) thm adjoint_eqI
lemma adjoint_eqI:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>\<And>x y. \<langle>(cblinfun_apply F) x, y\<rangle> = \<langle>x, (cblinfun_apply G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using cadjoint_eqI by auto


lemma adj_uminus: \<open>(-A)* = - (A*)\<close>
  apply (rule adjoint_eqI[symmetric])
  by (simp add: cblinfun.minus_left cinner_adj_left)

lemma cblinfun_compose_sum_left: \<open>(\<Sum>i\<in>S. g i) o\<^sub>C\<^sub>L x = (\<Sum>i\<in>S. g i o\<^sub>C\<^sub>L x)\<close>
  apply (induction S rule:infinite_finite_induct)
  by (auto simp: cblinfun_compose_add_left)

lemma cblinfun_compose_sum_right: \<open>x o\<^sub>C\<^sub>L (\<Sum>i\<in>S. g i) = (\<Sum>i\<in>S. x o\<^sub>C\<^sub>L g i)\<close>
  apply (induction S rule:infinite_finite_induct)
  by (auto simp: cblinfun_compose_add_right)


lemma pullback_topology_bi_cont: 
  fixes g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c::topological_space)\<close>
    and f :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and f' :: \<open>'c \<Rightarrow> 'c \<Rightarrow> 'c\<close>
  assumes gf_f'g: \<open>\<And>a b i. g (f a b) i = f' (g a i) (g b i)\<close>
  assumes f'_cont: \<open>\<And>a' b'. (case_prod f' \<longlongrightarrow> f' a' b') (nhds a' \<times>\<^sub>F nhds b')\<close>
  defines \<open>T \<equiv> pullback_topology UNIV g euclidean\<close>
  shows \<open>LIM (x,y) nhdsin T a \<times>\<^sub>F nhdsin T b. f x y :> nhdsin T (f a b)\<close>
proof -
  have topspace[simp]: \<open>topspace T = UNIV\<close>
    unfolding T_def topspace_pullback_topology by simp
  have openin: \<open>openin T U \<longleftrightarrow> (\<exists>V. open V \<and> U = g -` V)\<close> for U
    by (simp add: assms openin_pullback_topology)

  have 1: \<open>nhdsin T a = filtercomap g (nhds (g a))\<close>
    for a :: 'a
    by (auto simp add: filter_eq_iff eventually_filtercomap eventually_nhds eventually_nhdsin openin)

  have \<open>((g \<circ> case_prod f) \<longlongrightarrow> g (f a b)) (nhdsin T a \<times>\<^sub>F nhdsin T b)\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and gfS: \<open>g (f a b) \<in> S\<close>
    obtain U where gf_PiE: \<open>g (f a b) \<in> Pi\<^sub>E UNIV U\<close> and openU: \<open>\<forall>i. openin euclidean (U i)\<close>
      and finiteD: \<open>finite {i. U i \<noteq> topspace euclidean}\<close> and US: \<open>Pi\<^sub>E UNIV U \<subseteq> S\<close>
      using product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] gfS]
      by auto

    define D where \<open>D = {i. U i \<noteq> UNIV}\<close>
    with finiteD have \<open>finite D\<close>
      by auto

    from openU have openU: \<open>open (U i)\<close> for i
      by auto

    have *: \<open>f' (g a i) (g b i) \<in> U i\<close> for i
      by (metis PiE_mem gf_PiE iso_tuple_UNIV_I gf_f'g)

    have \<open>\<forall>\<^sub>F x in nhds (g a i) \<times>\<^sub>F nhds (g b i). case_prod f' x \<in> U i\<close> for i
      using tendsto_def[THEN iffD1, rule_format, OF f'_cont openU *, of i] by -

    then obtain Pa Pb where \<open>eventually (Pa i) (nhds (g a i))\<close> and \<open>eventually (Pb i) (nhds (g b i))\<close>
      and PaPb_plus: \<open>(\<forall>x y. Pa i x \<longrightarrow> Pb i y \<longrightarrow> f' x y \<in> U i)\<close> for i
      unfolding eventually_prod_filter by (metis prod.simps(2))

    from \<open>\<And>i. eventually (Pa i) (nhds (g a i))\<close>
    obtain Ua where \<open>open (Ua i)\<close> and a_Ua: \<open>g a i \<in> Ua i\<close> and Ua_Pa: \<open>Ua i \<subseteq> Collect (Pa i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    from \<open>\<And>i. eventually (Pb i) (nhds (g b i))\<close>
    obtain Ub where \<open>open (Ub i)\<close> and b_Ub: \<open>g b i \<in> Ub i\<close> and Ub_Pb: \<open>Ub i \<subseteq> Collect (Pb i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    have UaUb_plus: \<open>x \<in> Ua i \<Longrightarrow> y \<in> Ub i \<Longrightarrow> f' x y \<in> U i\<close> for i x y
      by (metis PaPb_plus Ua_Pa Ub_Pb mem_Collect_eq subsetD)

    define Ua' where \<open>Ua' i = (if i\<in>D then Ua i else UNIV)\<close> for i
    define Ub' where \<open>Ub' i = (if i\<in>D then Ub i else UNIV)\<close> for i

    have Ua'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ua' i = UNIV\<close> for i
      by (simp add: D_def Ua'_def)
    have Ub'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ub' i = UNIV\<close> for i
      by (simp add: D_def Ub'_def)
    have [simp]: \<open>open (Ua' i)\<close> for i
      by (simp add: Ua'_def \<open>open (Ua _)\<close>)
    have [simp]: \<open>open (Ub' i)\<close> for i
      by (simp add: Ub'_def \<open>open (Ub _)\<close>)
    have a_Ua': \<open>g a i \<in> Ua' i\<close> for i
      by (simp add: Ua'_def a_Ua)
    have b_Ub': \<open>g b i \<in> Ub' i\<close> for i
      by (simp add: Ub'_def b_Ub)
    have UaUb'_plus: \<open>a' \<in> Ua' i \<Longrightarrow> b' \<in> Ub' i \<Longrightarrow> f' a' b' \<in> U i\<close> for i a' b'
      apply (cases \<open>i \<in> D\<close>)
      using UaUb_plus by (auto simp add: Ua'_def  Ub'_def D_def)

    define Ua'' where \<open>Ua'' = Pi UNIV Ua'\<close>
    define Ub'' where \<open>Ub'' = Pi UNIV Ub'\<close>

    have \<open>open Ua''\<close>
      using finiteD Ua'_UNIV
      apply (auto simp add: open_fun_def Ua''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ua'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have \<open>open Ub''\<close>
      using finiteD Ub'_UNIV
      apply (auto simp add: open_fun_def Ub''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ub'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have a_Ua'': \<open>g a \<in> Ua''\<close>
      by (simp add: Ua''_def a_Ua')
    have b_Ub'': \<open>g b \<in> Ub''\<close>
      by (simp add: Ub''_def b_Ub')
    have UaUb''_plus: \<open>a' \<in> Ua'' \<Longrightarrow> b' \<in> Ub'' \<Longrightarrow> f' (a' i) (b' i) \<in> U i\<close> for i a' b'
      using UaUb'_plus apply (auto simp add: Ua''_def  Ub''_def)
      by blast

    define Ua''' where \<open>Ua''' = g -` Ua''\<close>
    define Ub''' where \<open>Ub''' = g -` Ub''\<close>
    have \<open>openin T Ua'''\<close>
      using \<open>open Ua''\<close> by (auto simp: openin Ua'''_def)
    have \<open>openin T Ub'''\<close>
      using \<open>open Ub''\<close> by (auto simp: openin Ub'''_def)
    have a_Ua'': \<open>a \<in> Ua'''\<close>
      by (simp add: Ua'''_def a_Ua'')
    have b_Ub'': \<open>b \<in> Ub'''\<close>
      by (simp add: Ub'''_def b_Ub'')
    have UaUb'''_plus: \<open>a \<in> Ua''' \<Longrightarrow> b \<in> Ub''' \<Longrightarrow> f' (g a i) (g b i) \<in> U i\<close> for i a b
      by (simp add: Ua'''_def UaUb''_plus Ub'''_def)

    define Pa' where \<open>Pa' a \<longleftrightarrow> a \<in> Ua'''\<close> for a
    define Pb' where \<open>Pb' b \<longleftrightarrow> b \<in> Ub'''\<close> for b

    have Pa'_nhd: \<open>eventually Pa' (nhdsin T a)\<close>
      using \<open>openin T Ua'''\<close>
      by (auto simp add: Pa'_def eventually_nhdsin intro!: exI[of _ \<open>Ua'''\<close>] a_Ua'')
    have Pb'_nhd: \<open>eventually Pb' (nhdsin T b)\<close>
      using \<open>openin T Ub'''\<close>
      by (auto simp add: Pb'_def eventually_nhdsin intro!: exI[of _ \<open>Ub'''\<close>] b_Ub'')
    have Pa'Pb'_plus: \<open>(g \<circ> case_prod f) (a, b) \<in> S\<close> if \<open>Pa' a\<close> \<open>Pb' b\<close> for a b
      using that UaUb'''_plus US
      by (auto simp add: Pa'_def Pb'_def PiE_UNIV_domain Pi_iff gf_f'g)

    show \<open>\<forall>\<^sub>F x in nhdsin T a \<times>\<^sub>F nhdsin T b. (g \<circ> case_prod f) x \<in> S\<close>
      using Pa'_nhd Pb'_nhd Pa'Pb'_plus
      unfolding eventually_prod_filter
      apply (rule_tac exI[of _ Pa'])
      apply (rule_tac exI[of _ Pb'])
      by simp
  qed
  then show ?thesis
    unfolding 1 filterlim_filtercomap_iff by -
qed

definition \<open>has_sum_in T f A x \<longleftrightarrow> limitin T (sum f) x (finite_subsets_at_top A)\<close>

definition \<open>summable_on_in T f A \<longleftrightarrow> (\<exists>x. has_sum_in T f A x)\<close>

definition \<open>infsum_in T f A = (if summable_on_in T f A then (THE l. has_sum_in T f A l) else 0)\<close>

definition hausdorff where \<open>hausdorff T \<longleftrightarrow> (\<forall>x \<in> topspace T. \<forall>y \<in> topspace T. x \<noteq> y \<longrightarrow> (\<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>

lemma limitin_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>F \<noteq> \<bottom>\<close>
  assumes lim: \<open>limitin T f l F\<close>
  assumes lim': \<open>limitin T f l' F\<close>
  shows \<open>l = l'\<close>
proof (rule ccontr)
  assume "l \<noteq> l'"
  have \<open>l \<in> topspace T\<close> \<open>l' \<in> topspace T\<close>
    by (meson lim lim' limitin_def)+
  obtain U V where "openin T U" "openin T V" "l \<in> U" "l' \<in> V" "U \<inter> V = {}"
    using \<open>hausdorff T\<close> \<open>l \<noteq> l'\<close> unfolding hausdorff_def
    by (meson \<open>l \<in> topspace T\<close> \<open>l' \<in> topspace T\<close>)
  have "eventually (\<lambda>x. f x \<in> U) F"
    using lim \<open>openin T U\<close> \<open>l \<in> U\<close>
    by (simp add: limitin_def)
  moreover
  have "eventually (\<lambda>x. f x \<in> V) F"
    using lim' \<open>openin T V\<close> \<open>l' \<in> V\<close>
    by (simp add: limitin_def)
  ultimately
  have "eventually (\<lambda>x. False) F"
  proof eventually_elim
    case (elim x)
    then have "f x \<in> U \<inter> V" by simp
    with \<open>U \<inter> V = {}\<close> show ?case by simp
  qed
  with \<open>\<not> trivial_limit F\<close> show "False"
    by (simp add: trivial_limit_def)
qed


lemma has_sum_in_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>has_sum_in T f A l'\<close>
  shows \<open>l = l'\<close>
  using assms(1) _ assms(2,3)[unfolded has_sum_in_def] 
  apply (rule limitin_unique)
  by simp

lemma has_sum_in_infsum_in: 
  assumes \<open>hausdorff T\<close> and summable: \<open>summable_on_in T f A\<close>
  shows \<open>has_sum_in T f A (infsum_in T f A)\<close>
  apply (simp add: infsum_in_def summable)
  apply (rule theI'[of \<open>has_sum_in T f A\<close>])
  using has_sum_in_unique[OF \<open>hausdorff T\<close>, of f A] summable
  by (meson summable_on_in_def)


lemma sum_adj: \<open>(sum a F)* = sum (\<lambda>i. (a i)*) F\<close>
  apply (induction rule:infinite_finite_induct)
  by (auto simp add: adj_plus)

lemma nhdsin_mono:
  assumes [simp]: \<open>\<And>x. openin T' x \<Longrightarrow> openin T x\<close>
  assumes [simp]: \<open>topspace T = topspace T'\<close>
  shows \<open>nhdsin T a \<le> nhdsin T' a\<close>
  unfolding nhdsin_def 
  by (auto intro!: INF_superset_mono)

unbundle no_cblinfun_notation

end
