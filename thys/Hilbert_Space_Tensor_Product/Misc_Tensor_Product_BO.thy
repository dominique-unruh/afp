section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product "HOL-Library.Function_Algebras"
"HOL-ex.Sketch_and_Explore"
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

lemma cblinfun_compose_uminus_left: \<open>(- a) o\<^sub>C\<^sub>L b = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_uminus_right: \<open>a o\<^sub>C\<^sub>L (- b) = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemmas (in bounded_cbilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_cbilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]


(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"




(* (* A copy of Series.Cauchy_product_sums with * replaced by \<bullet>\<^sub>C *)
lemma Cauchy_cinner_product_sums:
  fixes a b :: "nat \<Rightarrow> 'a::chilbert_space"
  assumes a: "summable (\<lambda>k. norm (a k))"
    and b: "summable (\<lambda>k. norm (b k))"
  shows "(\<lambda>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) sums ((\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k))"
proof -
  let ?S1 = "\<lambda>n::nat. {..<n} \<times> {..<n}"
  let ?S2 = "\<lambda>n::nat. {(i,j). i + j < n}"
  have S1_mono: "\<And>m n. m \<le> n \<Longrightarrow> ?S1 m \<subseteq> ?S1 n" by auto
  have S2_le_S1: "\<And>n. ?S2 n \<subseteq> ?S1 n" by auto
  have S1_le_S2: "\<And>n. ?S1 (n div 2) \<subseteq> ?S2 n" by auto
  have finite_S1: "\<And>n. finite (?S1 n)" by simp
  with S2_le_S1 have finite_S2: "\<And>n. finite (?S2 n)" by (rule finite_subset)

  let ?g = "\<lambda>(i,j). a i \<bullet>\<^sub>C b j"
  let ?f = "\<lambda>(i,j). norm (a i) * norm (b j)"
  have f_nonneg: "\<And>x. 0 \<le> ?f x" by auto
  then have norm_sum_f: "\<And>A. norm (sum ?f A) = sum ?f A"
    unfolding real_norm_def
    by (simp only: abs_of_nonneg sum_nonneg [rule_format])

  have "(\<lambda>n. (\<Sum>k<n. a k) \<bullet>\<^sub>C (\<Sum>k<n. b k)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (simp add: a b summable_LIMSEQ summable_norm_cancel tendsto_cinner)
  then have 1: "(\<lambda>n. sum ?g (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (simp only: sum_cinner sum.Sigma [rule_format] finite_lessThan)

  have "(\<lambda>n. (\<Sum>k<n. norm (a k)) * (\<Sum>k<n. norm (b k))) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    using a b by (simp add: summable_LIMSEQ tendsto_mult)
  then have "(\<lambda>n. sum ?f (?S1 n)) \<longlonglongrightarrow> (\<Sum>k. norm (a k)) * (\<Sum>k. norm (b k))"
    by (simp only: sum_product sum.Sigma [rule_format] finite_lessThan)
  then have "convergent (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergentI)
  then have Cauchy: "Cauchy (\<lambda>n. sum ?f (?S1 n))"
    by (rule convergent_Cauchy)
  have "Zfun (\<lambda>n. sum ?f (?S1 n - ?S2 n)) sequentially"
  proof (rule ZfunI, simp only: eventually_sequentially norm_sum_f)
    fix r :: real
    assume r: "0 < r"
    from CauchyD [OF Cauchy r] obtain N
      where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (sum ?f (?S1 m) - sum ?f (?S1 n)) < r" ..
    then have "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> norm (sum ?f (?S1 m - ?S1 n)) < r"
      by (simp only: sum_diff finite_S1 S1_mono)
    then have N: "\<And>m n. N \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> sum ?f (?S1 m - ?S1 n) < r"
      by (simp only: norm_sum_f)
    show "\<exists>N. \<forall>n\<ge>N. sum ?f (?S1 n - ?S2 n) < r"
    proof (intro exI allI impI)
      fix n
      assume "2 * N \<le> n"
      then have n: "N \<le> n div 2" by simp
      have "sum ?f (?S1 n - ?S2 n) \<le> sum ?f (?S1 n - ?S1 (n div 2))"
        by (intro sum_mono2 finite_Diff finite_S1 f_nonneg Diff_mono subset_refl S1_le_S2)
      also have "\<dots> < r"
        using n div_le_dividend by (rule N)
      finally show "sum ?f (?S1 n - ?S2 n) < r" .
    qed
  qed
  then have "Zfun (\<lambda>n. sum ?g (?S1 n - ?S2 n)) sequentially"
    apply (rule Zfun_le [rule_format])
    apply (simp only: norm_sum_f)
    apply (rule order_trans [OF norm_sum sum_mono])
    by (auto simp add: norm_mult_ineq complex_inner_class.Cauchy_Schwarz_ineq2)
  then have 2: "(\<lambda>n. sum ?g (?S1 n) - sum ?g (?S2 n)) \<longlonglongrightarrow> 0"
    unfolding tendsto_Zfun_iff diff_0_right
    by (simp only: sum_diff finite_S1 S2_le_S1)
  with 1 have "(\<lambda>n. sum ?g (?S2 n)) \<longlonglongrightarrow> (\<Sum>k. a k) \<bullet>\<^sub>C (\<Sum>k. b k)"
    by (rule Lim_transform2)
  then show ?thesis
    by (simp only: sums_def sum.triangle_reindex)
qed *)


lemma summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)


lemma summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_right.additive_axioms)

lemma infsum_scaleC_left:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>C c) A = infsum f A *\<^sub>C c"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)

lemma infsum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>C f x) A = c *\<^sub>C infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
      apply (rule infsum_comm_additive)
      using summable by (auto simp add: scaleC_right.additive_axioms)
  next
    case c0
    then show ?thesis by auto
  next
    case not_summable
    have \<open>\<not> (\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
    proof (rule notI)
      assume \<open>(\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
      then have \<open>(\<lambda>x. inverse c *\<^sub>C c *\<^sub>C f x) summable_on A\<close>
        using summable_on_scaleC_right by blast
      then have \<open>f summable_on A\<close>
        using not_summable by auto
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed

lemma cblinfun_power_compose[simp]: \<open>cblinfun_power A n o\<^sub>C\<^sub>L cblinfun_power A m = cblinfun_power A (n+m)\<close>
  apply (induction n)
  apply (auto simp: cblinfun_power_Suc')
  by (metis cblinfun_assoc_left(1))


lemma cblinfun_power_scaleC: \<open>cblinfun_power (c *\<^sub>C a) n = c^n *\<^sub>C cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_scaleR: \<open>cblinfun_power (c *\<^sub>R a) n = c^n *\<^sub>R cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_uminus: \<open>cblinfun_power (-a) n = (-1)^n *\<^sub>R cblinfun_power a n\<close>
  apply (subst asm_rl[of \<open>-a = (-1) *\<^sub>R a\<close>])
   apply simp
  by (rule cblinfun_power_scaleR)


lemma cblinfun_power_adj: \<open>(cblinfun_power S n)* = cblinfun_power (S*) n\<close>
  apply (induction n)
   apply simp
  apply (subst cblinfun_power_Suc)
  apply (subst cblinfun_power_Suc')
  by auto

lemma adj_minus: \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis add_implies_diff adj_plus diff_add_cancel)

lemma complex_of_real_leq_1_iff[iff]: \<open>complex_of_real x \<le> 1 \<longleftrightarrow> x \<le> 1\<close>
  by (metis complex_of_real_mono_iff of_real_1)

lemma cinner_hermitian_real: \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close> if \<open>A* = A\<close>
  by (metis Reals_cnj_iff cinner_adj_right cinner_commute' that)

lemma x_cnj_x: \<open>c * cnj c = (abs c)\<^sup>2\<close>
  by (metis cnj_x_x mult.commute)

thm cblinfun_extension_exists_bounded_dense
term is_Proj

lemma cblinfun_extension_exists_proj:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::cbanach\<close>
  assumes \<open>csubspace S\<close>
  assumes \<open>\<exists>P. is_projection_on P (closure S) \<and> bounded_clinear P\<close> (* Maybe can be replaced by is_Proj if the latter's type class is widened *)
  assumes f_add: \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. x \<in> S \<Longrightarrow> f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows \<open>cblinfun_extension_exists S f\<close>
proof (cases \<open>B \<ge> 0\<close>)
  case True
  note True[simp]
  obtain P where P_proj: \<open>is_projection_on P (closure S)\<close> and P_blin[simp]: \<open>bounded_clinear P\<close>
    using assms(2) by blast 
  have P_lin[simp]: \<open>clinear P\<close>
    by (simp add: bounded_clinear.clinear)
  define f' S' where \<open>f' \<psi> = f (P \<psi>)\<close> and \<open>S' = S + (P -` {0})\<close> for \<psi>
  have \<open>csubspace S'\<close>
    by (simp add: S'_def assms(1) csubspace_set_plus)
  moreover have \<open>closure S' = UNIV\<close>
  proof auto
    fix \<psi>
    have \<open>\<psi> = P \<psi> + (id - P) \<psi>\<close>
      by simp
    also have \<open>\<dots> \<in> closure S + (P -` {0})\<close>
      apply (rule set_plus_intro) 
      using P_proj is_projection_on_in_image 
      by (auto simp: complex_vector.linear_diff is_projection_on_fixes_image is_projection_on_in_image)
    also have \<open>\<dots> \<subseteq> closure (closure S + (P -` {0}))\<close>
      using closure_subset by blast
    also have \<open>\<dots> = closure (S + (P -` {0}))\<close>
      using closed_sum_closure_left closed_sum_def by blast
    also have \<open>\<dots> = closure S'\<close>
      using S'_def by fastforce
    finally show \<open>\<psi> \<in> closure S'\<close>
      by -
  qed

  moreover have \<open>f' (x + y) = f' x + f' y\<close> if \<open>x \<in> S'\<close> and \<open>y \<in> S'\<close> for x y
    by (smt (z3) P_blin P_proj S'_def f'_def add.right_neutral bounded_clinear_CBlinfun_apply cblinfun.add_right closure_subset f_add is_projection_on_fixes_image set_plus_elim singletonD subset_eq that(1) that(2) vimageE)
  moreover have \<open>f' (c *\<^sub>C x) = c *\<^sub>C f' x\<close> if \<open>x \<in> S'\<close> for c x
    by (smt (verit, ccfv_SIG) P_blin P_proj S'_def f'_def add.right_neutral bounded_clinear_CBlinfun_apply cblinfun.add_right cblinfun.scaleC_right closure_subset f_scale is_projection_on_fixes_image set_plus_elim singletonD subset_eq that vimageE)

  moreover 
  from P_blin obtain B' where B': \<open>norm (P x) \<le> B' * norm x\<close> for x
    by (metis bounded_clinear.bounded mult.commute)
  have \<open>norm (f' x) \<le> (B * B') * norm x\<close> if \<open>x \<in> S'\<close> for x
  proof -
    have \<open>norm (f' x) \<le> B* norm (P x)\<close>
      apply (auto simp: f'_def)
      by (smt (verit) P_blin P_proj S'_def add.right_neutral bounded bounded_clinear_CBlinfun_apply cblinfun.add_right closure_subset is_projection_on_fixes_image set_plus_elim singletonD subset_eq that vimageE)
    also have \<open>\<dots> \<le> B * B' * norm x\<close>
      by (simp add: B' mult.assoc mult_mono)
    finally show ?thesis
      by auto
  qed

  ultimately have F_ex: \<open>cblinfun_extension_exists S' f'\<close>
    by (rule cblinfun_extension_exists_bounded_dense)
  define F where \<open>F = cblinfun_extension S' f'\<close>
  from F_ex have *: \<open>F \<psi> = f' \<psi>\<close> if \<open>\<psi> \<in> S'\<close> for \<psi>
    by (simp add: F_def cblinfun_extension_apply that)
  then have \<open>F \<psi> = f \<psi>\<close> if \<open>\<psi> \<in> S\<close> for \<psi>
    apply (auto simp: S'_def f'_def)
    by (metis (no_types, lifting) P_lin P_proj add.right_neutral closure_subset complex_vector.linear_subspace_vimage complex_vector.subspace_0 complex_vector.subspace_single_0 is_projection_on_fixes_image set_plus_intro subset_eq that)
  then show \<open>cblinfun_extension_exists S f\<close>
    using cblinfun_extension_exists_def by blast
next
  case False
  then have \<open>S \<subseteq> {0}\<close>
    using bounded apply auto
    by (meson norm_ge_zero norm_le_zero_iff order_trans zero_le_mult_iff)
  then show \<open>cblinfun_extension_exists S f\<close>
    apply (rule_tac cblinfun_extension_existsI[where B=0])
    apply auto
    using bounded by fastforce
qed

lemma closed_space_as_set[simp]: \<open>closed (space_as_set S)\<close>
  apply transfer by (simp add: closed_csubspace.closed)


lemma Proj_fixes_image: \<open>Proj S *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set S\<close>
  by (simp add: Proj.rep_eq closed_csubspace_def projection_fixes_image that)

lemma orthogonal_projectors_orthogonal_spaces:
  fixes S T :: \<open>'a::chilbert_space set\<close>
  shows \<open>(\<forall>x\<in>S. \<forall>y\<in>T. is_orthogonal x y) \<longleftrightarrow> Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close>
proof (intro ballI iffI)
  fix x y assume \<open>Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close> \<open>x \<in> S\<close> \<open>y \<in> T\<close>
  then show \<open>is_orthogonal x y\<close>
    by (smt (verit, del_insts) Proj_idempotent Proj_range adj_Proj cblinfun.zero_left cblinfun_apply_cblinfun_compose cblinfun_fixes_range ccspan_superset cinner_adj_right cinner_zero_right in_mono)
next 
  assume \<open>\<forall>x\<in>S. \<forall>y\<in>T. is_orthogonal x y\<close>
  then have \<open>ccspan S \<le> - ccspan T\<close>
    by (simp add: ccspan_leq_ortho_ccspan)
  then show \<open>Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close>
    by (metis (no_types, opaque_lifting) Proj_range adj_Proj adj_cblinfun_compose basic_trans_rules(31) cblinfun.zero_left cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_eqI kernel_Proj kernel_memberD less_eq_ccsubspace.rep_eq)
qed

lemma cblinfun_image_bot_zero[simp]: \<open>A *\<^sub>S top = bot \<longleftrightarrow> A = 0\<close>
  by (metis Complex_Bounded_Linear_Function.zero_cblinfun_image bot_ccsubspace.rep_eq cblinfun_apply_in_image cblinfun_eqI empty_iff insert_iff zero_ccsubspace_def)
(* proof (rule iffI, rule ccontr)
  assume Atopbot: \<open>A *\<^sub>S \<top> = \<bottom>\<close> and \<open>A \<noteq> 0\<close>
  then obtain x where Ax: \<open>A *\<^sub>V x \<noteq> 0\<close>
    by (metis cblinfun_eqI zero_cblinfun.rep_eq)
  have \<open>A *\<^sub>V x \<in> space_as_set (A *\<^sub>S \<top>)\<close>
    by auto
  also have \<open>\<dots> = {0}\<close>
    by (simp add: Atopbot)
  finally have \<open>A *\<^sub>V x = 0\<close>
    by simp
  with Ax show False
    by simp
qed simp *)


definition some_chilbert_basis :: \<open>'a::chilbert_space set\<close> where
  \<open>some_chilbert_basis = (SOME B::'a set. is_onb B)\<close>

lemma is_onb_some_chilbert_basis[simp]: \<open>is_onb (some_chilbert_basis :: 'a::chilbert_space set)\<close>
  using orthonormal_basis_exists[OF is_ortho_set_empty]
  by (auto simp add: some_chilbert_basis_def intro: someI2)

lemma is_ortho_set_some_chilbert_basis[simp]: \<open>is_ortho_set some_chilbert_basis\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma is_normal_some_chilbert_basis: \<open>\<And>x. x \<in> some_chilbert_basis \<Longrightarrow> norm x = 1\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma ccspan_some_chilbert_basis[simp]: \<open>ccspan some_chilbert_basis = top\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma span_some_chilbert_basis[simp]: \<open>closure (cspan some_chilbert_basis) = UNIV\<close>
  by (metis ccspan.rep_eq ccspan_some_chilbert_basis top_ccsubspace.rep_eq)

lemma cindependent_some_chilbert_basis[simp]: \<open>cindependent some_chilbert_basis\<close>
  using is_ortho_set_cindependent is_ortho_set_some_chilbert_basis by blast

lemma finite_some_chilbert_basis[simp]: \<open>finite (some_chilbert_basis :: 'a :: {chilbert_space, cfinite_dim} set)\<close>
  apply (rule cindependent_cfinite_dim_finite)
  by simp

lemma some_chilbert_basis_nonempty: \<open>(some_chilbert_basis :: 'a::{chilbert_space, not_singleton} set) \<noteq> {}\<close>
proof (rule ccontr, simp)
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  assume [simp]: \<open>B = {}\<close>
  have \<open>UNIV = closure (cspan B)\<close>
    using B_def span_some_chilbert_basis by blast
  also have \<open>\<dots> = {0}\<close>
    by simp
  also have \<open>\<dots> \<noteq> UNIV\<close>
    using Extra_General.UNIV_not_singleton by blast
  finally show False
    by simp
qed

instance prod :: (complex_normed_vector, complex_normed_vector) complex_normed_vector 
proof
  fix c :: complex and x y :: "'a \<times> 'b"
  show "norm (c *\<^sub>C x) = cmod c * norm x"
    unfolding norm_prod_def
    apply (simp add: power_mult_distrib)
    apply (simp add: distrib_left [symmetric])
    by (simp add: real_sqrt_mult)
qed

instance prod :: (chilbert_space, chilbert_space) chilbert_space ..

lift_definition cblinfun_left :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b::complex_normed_vector)\<close> is \<open>(\<lambda>x. (x,0))\<close>
  by (auto intro!: bounded_clinearI[where K=1])
lift_definition cblinfun_right :: \<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L ('a::complex_normed_vector\<times>'b)\<close> is \<open>(\<lambda>x. (0,x))\<close>
  by (auto intro!: bounded_clinearI[where K=1])

lemma isometry_cblinfun_left[simp]: \<open>isometry cblinfun_left\<close>
  apply (rule orthogonal_on_basis_is_isometry[of some_chilbert_basis])
   apply simp
  apply transfer
  by simp

lemma isometry_cblinfun_right[simp]: \<open>isometry cblinfun_right\<close>
  apply (rule orthogonal_on_basis_is_isometry[of some_chilbert_basis])
   apply simp
  apply transfer
  by simp

lemma cblinfun_left_right_ortho[simp]: \<open>cblinfun_left* o\<^sub>C\<^sub>L cblinfun_right = 0\<close>
proof -
  have \<open>x \<bullet>\<^sub>C ((cblinfun_left* o\<^sub>C\<^sub>L cblinfun_right) *\<^sub>V y) = 0\<close> for x :: 'b and y :: 'a
    apply (simp add: cinner_adj_right)
    apply transfer
    by auto
  then show ?thesis
    by (metis cblinfun.zero_left cblinfun_eqI cinner_eq_zero_iff)
qed

lemma cblinfun_right_left_ortho[simp]: \<open>cblinfun_right* o\<^sub>C\<^sub>L cblinfun_left = 0\<close>
proof -
  have \<open>x \<bullet>\<^sub>C ((cblinfun_right* o\<^sub>C\<^sub>L cblinfun_left) *\<^sub>V y) = 0\<close> for x :: 'b and y :: 'a
    apply (simp add: cinner_adj_right)
    apply transfer
    by auto
  then show ?thesis
    by (metis cblinfun.zero_left cblinfun_eqI cinner_eq_zero_iff)
qed

lemma cblinfun_left_apply[simp]: \<open>cblinfun_left *\<^sub>V \<psi> = (\<psi>,0)\<close>
  apply transfer by simp

lemma cblinfun_left_adj_apply[simp]: \<open>cblinfun_left* *\<^sub>V \<psi> = fst \<psi>\<close>
  apply (cases \<psi>)
  by (auto intro!: cinner_extensionality[of \<open>_ *\<^sub>V _\<close>] simp: cinner_adj_right)

lemma cblinfun_right_apply[simp]: \<open>cblinfun_right *\<^sub>V \<psi> = (0,\<psi>)\<close>
  apply transfer by simp

lemma cblinfun_right_adj_apply[simp]: \<open>cblinfun_right* *\<^sub>V \<psi> = snd \<psi>\<close>
  apply (cases \<psi>)
  by (auto intro!: cinner_extensionality[of \<open>_ *\<^sub>V _\<close>] simp: cinner_adj_right)

lift_definition ccsubspace_Times :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> 'b::complex_normed_vector ccsubspace \<Rightarrow> ('a\<times>'b) ccsubspace\<close> is
  Product_Type.Times
proof -
  fix S :: \<open>'a set\<close> and T :: \<open>'b set\<close>
  assume [simp]: \<open>closed_csubspace S\<close> \<open>closed_csubspace T\<close>
  have \<open>csubspace (S \<times> T)\<close>
    by (simp add: complex_vector.subspace_Times)
  moreover have \<open>closed (S \<times> T)\<close>
    by (simp add: closed_Times closed_csubspace.closed)
  ultimately show \<open>closed_csubspace (S \<times> T)\<close>
    by (rule closed_csubspace.intro)
qed

lemma cspan_Times: \<open>cspan (S \<times> T) = cspan S \<times> cspan T\<close> if \<open>0 \<in> S\<close> and \<open>0 \<in> T\<close>
proof 
  have \<open>fst ` cspan (S \<times> T) \<subseteq> cspan S\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    using that complex_vector.module_hom_fst by auto
  moreover have \<open>snd ` cspan (S \<times> T) \<subseteq> cspan T\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    using that complex_vector.module_hom_snd by auto
  ultimately show \<open>cspan (S \<times> T) \<subseteq> cspan S \<times> cspan T\<close>
    by auto

  show \<open>cspan S \<times> cspan T \<subseteq> cspan (S \<times> T)\<close>
  proof
    fix x assume assm: \<open>x \<in> cspan S \<times> cspan T\<close>
    then have \<open>fst x \<in> cspan S\<close>
      by auto
    then obtain t1 r1 where fst_x: \<open>fst x = (\<Sum>a\<in>t1. r1 a *\<^sub>C a)\<close> and [simp]: \<open>finite t1\<close> and \<open>t1 \<subseteq> S\<close>
      by (auto simp add: complex_vector.span_explicit)
    from assm
    have \<open>snd x \<in> cspan T\<close>
      by auto
    then obtain t2 r2 where snd_x: \<open>snd x = (\<Sum>a\<in>t2. r2 a *\<^sub>C a)\<close> and [simp]: \<open>finite t2\<close> and \<open>t2 \<subseteq> T\<close>
      by (auto simp add: complex_vector.span_explicit)
    define t :: \<open>('a+'b) set\<close> and r :: \<open>('a+'b) \<Rightarrow> complex\<close> and f :: \<open>('a+'b) \<Rightarrow> ('a\<times>'b)\<close>
      where \<open>t = t1 <+> t2\<close>
      and \<open>r a = (case a of Inl a1 \<Rightarrow> r1 a1 | Inr a2 \<Rightarrow> r2 a2)\<close>
      and \<open>f a = (case a of Inl a1 \<Rightarrow> (a1,0) | Inr a2 \<Rightarrow> (0,a2))\<close>
    for a
    have \<open>finite t\<close>
      by (simp add: t_def)
    moreover have \<open>f ` t \<subseteq> S \<times> T\<close>
      using  \<open>t1 \<subseteq> S\<close> \<open>t2 \<subseteq> T\<close> that
      by (auto simp: f_def t_def)
    moreover have \<open>(fst x, snd x) = (\<Sum>a\<in>t. r a *\<^sub>C f a)\<close>
      apply (simp only: fst_x snd_x)
      by (auto simp: t_def sum.Plus r_def f_def sum_prod)
    ultimately show \<open>x \<in> cspan (S \<times> T)\<close>
      apply auto
      by (smt (verit, best) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset image_subset_iff subset_iff)
  qed
qed

lemma ccspan_Times: \<open>ccspan (S \<times> T) = ccsubspace_Times (ccspan S) (ccspan T)\<close> if \<open>0 \<in> S\<close> and \<open>0 \<in> T\<close>
proof (transfer fixing: S T)
  from that have \<open>closure (cspan (S \<times> T)) = closure (cspan S \<times> cspan T)\<close>
    by (simp add: cspan_Times)
  also have \<open>\<dots> = closure (cspan S) \<times> closure (cspan T)\<close>
    using closure_Times by blast
  finally   show \<open>closure (cspan (S \<times> T)) = closure (cspan S) \<times> closure (cspan T)\<close>
    by -
qed

lemma ccspan_Times_sing1: \<open>ccspan ({0::'a::complex_normed_vector} \<times> B) = ccsubspace_Times 0 (ccspan B)\<close>
proof (transfer fixing: B)
  have \<open>closure (cspan ({0::'a} \<times> B)) = closure ({0} \<times> cspan B)\<close>
    by (simp add: complex_vector.span_Times_sing1)
  also have \<open>\<dots> = closure {0} \<times> closure (cspan B)\<close>
    using closure_Times by blast
  also have \<open>\<dots> = {0} \<times> closure (cspan B)\<close>
    by simp
  finally show \<open>closure (cspan ({0::'a} \<times> B)) = {0} \<times> closure (cspan B)\<close>
    by -
qed

lemma ccspan_Times_sing2: \<open>ccspan (B \<times> {0::'a::complex_normed_vector}) = ccsubspace_Times (ccspan B) 0\<close>
proof (transfer fixing: B)
  have \<open>closure (cspan (B \<times> {0::'a})) = closure (cspan B \<times> {0})\<close>
    by (simp add: complex_vector.span_Times_sing2)
  also have \<open>\<dots> = closure (cspan B) \<times> closure {0}\<close>
    using closure_Times by blast
  also have \<open>\<dots> = closure (cspan B) \<times> {0}\<close>
    by simp
  finally show \<open>closure (cspan (B \<times> {0::'a})) = closure (cspan B) \<times> {0}\<close>
    by -
qed


lemma ccspan_0[simp]: \<open>ccspan {0} = 0\<close>
  apply transfer
  by simp

lemma set_Times_plus_distrib: \<open>(A \<times> B) + (C \<times> D) = (A + C) \<times> (B + D)\<close>
  by (auto simp: Sigma_def set_plus_def)

lemma ccsubspace_Times_sup: \<open>sup (ccsubspace_Times A B) (ccsubspace_Times C D) = ccsubspace_Times (sup A C) (sup B D)\<close>
proof transfer
  fix A C :: \<open>'a set\<close> and B D :: \<open>'b set\<close>
  have \<open>A \<times> B +\<^sub>M C \<times> D = closure ((A \<times> B) + (C \<times> D))\<close>
    using closed_sum_def by blast
  also have \<open>\<dots> = closure ((A + C) \<times> (B + D))\<close>
    by (simp add: set_Times_plus_distrib)
  also have \<open>\<dots> = closure (A + C) \<times> closure (B + D)\<close>
    by (simp add: closure_Times)
  also have \<open>\<dots> = (A +\<^sub>M C) \<times> (B +\<^sub>M D)\<close>
    by (simp add: closed_sum_def)
  finally show \<open>A \<times> B +\<^sub>M C \<times> D = (A +\<^sub>M C) \<times> (B +\<^sub>M D)\<close>
    by -
qed

lemma ccsubspace_Times_top_top[simp]: \<open>ccsubspace_Times top top = top\<close>
  apply transfer
  by simp

lemma is_onb_prod:
  assumes \<open>is_onb B\<close> \<open>is_onb B'\<close>
  shows \<open>is_onb ((B \<times> {0}) \<union> ({0} \<times> B'))\<close>
proof -
  from assms
  have 1: \<open>is_ortho_set ((B \<times> {0}) \<union> ({0} \<times> B'))\<close>
    unfolding is_ortho_set_def
    apply (auto simp: is_onb_def is_ortho_set_def zero_prod_def)
    by (meson is_onb_def is_ortho_set_def)+

  have 2: \<open>(l, r) \<in> B \<times> {0} \<Longrightarrow> norm (l, r) = 1\<close> for l :: 'a and r :: 'b
    using \<open>is_onb B\<close> is_onb_def by auto

  have 3: \<open>(l, r) \<in> {0} \<times> B' \<Longrightarrow> norm (l, r) = 1\<close> for l :: 'a and r :: 'b
    using \<open>is_onb B'\<close> is_onb_def by auto

  have [simp]: \<open>ccspan B = top\<close> \<open>ccspan B' = top\<close>
    using assms is_onb_def by auto

  have 4: \<open>ccspan ((B \<times> {0}) \<union> ({0} \<times> B')) = top\<close>
    by (auto simp: ccspan_Times_sing1 ccspan_Times_sing2 ccsubspace_Times_sup simp flip: ccspan_union)

  from 1 2 3 4
  show \<open>is_onb ((B \<times> {0}) \<union> ({0} \<times> B'))\<close>
    by (auto simp add: is_onb_def)
qed

lemma simp_a_oCL_b: \<open>a o\<^sub>C\<^sub>L b = c \<Longrightarrow> a o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L d) = c o\<^sub>C\<^sub>L d\<close>
  \<comment> \<open>A convenience lemma to transform simplification rules of the form \<^term>\<open>a o\<^sub>C\<^sub>L b = c\<close>.
     E.g., \<open>simp_a_oCL_b[OF isometryD, simp]\<close> declares a simp-rule for simplifying \<^term>\<open>x* o\<^sub>C\<^sub>L (x o\<^sub>C\<^sub>L y) = id_cblinfun o\<^sub>C\<^sub>L y\<close>.\<close>
  by (simp add: cblinfun_assoc_left(1))

lemma simp_a_oCL_b': \<open>a o\<^sub>C\<^sub>L b = c \<Longrightarrow> a *\<^sub>V (b *\<^sub>V d) = c *\<^sub>V d\<close>
  \<comment> \<open>A convenience lemma to transform simplification rules of the form \<^term>\<open>a o\<^sub>C\<^sub>L b = c\<close>.
     E.g., \<open>simp_a_oCL_b'[OF isometryD, simp]\<close> declares a simp-rule for simplifying \<^term>\<open>x* *\<^sub>V x *\<^sub>V y = id_cblinfun *\<^sub>V y\<close>.\<close>
  by auto

lemma cblinfun_compose_Proj_kernel[simp]: \<open>a o\<^sub>C\<^sub>L Proj (kernel a) = 0\<close>
  apply (rule cblinfun_eqI)
  apply simp
  by (metis Proj_range cblinfun_apply_in_image kernel_memberD)

lemma partial_isometry_adj_a_o_a:
  assumes \<open>partial_isometry a\<close>
  shows \<open>a* o\<^sub>C\<^sub>L a = Proj (- kernel a)\<close>
proof (rule cblinfun_cinner_eqI)
  define P where \<open>P = Proj (- kernel a)\<close>
  have aP: \<open>a o\<^sub>C\<^sub>L P = a\<close>
    by (auto intro!: simp: cblinfun_compose_minus_right P_def Proj_ortho_compl)
  have is_Proj_P[simp]: \<open>is_Proj P\<close>
    by (simp add: P_def)

  fix \<psi> :: 'a
  have \<open>\<psi> \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V \<psi>) = a \<psi> \<bullet>\<^sub>C a \<psi>\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> = a (P \<psi>) \<bullet>\<^sub>C a (P \<psi>)\<close>
    by (metis aP cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> = P \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by (metis P_def Proj_range assms cblinfun_apply_in_image cdot_square_norm partial_isometry_def)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by (simp flip: cinner_adj_right add: is_proj_selfadj is_Proj_idempotent[THEN simp_a_oCL_b'])
  finally show \<open>\<psi> \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by -
qed

lemma kernel_compl_adj_range:
  shows \<open>kernel a = - (a* *\<^sub>S top)\<close>
proof (rule ccsubspace_eqI)
  fix x
  have \<open>x \<in> space_as_set (kernel a) \<longleftrightarrow> a x = 0\<close>
    apply transfer by simp
  also have \<open>a x = 0 \<longleftrightarrow> (\<forall>y. is_orthogonal y (a x))\<close>
    by (metis cinner_gt_zero_iff cinner_zero_right)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y. is_orthogonal (a* *\<^sub>V y) x)\<close>
    by (simp add: cinner_adj_left)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> space_as_set (- (a* *\<^sub>S top))\<close>
    apply transfer
    by (metis (mono_tags, opaque_lifting) UNIV_I image_iff is_orthogonal_sym orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI')
  finally show \<open>x \<in> space_as_set (kernel a) \<longleftrightarrow> x \<in> space_as_set (- (a* *\<^sub>S top))\<close>
    by -
qed


definition the_riesz_rep :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow> 'a\<close> where
  \<open>the_riesz_rep f = (SOME t. \<forall>x. f x = \<langle>t, x\<rangle>)\<close>

lemma the_riesz_rep[simp]: \<open>the_riesz_rep f \<bullet>\<^sub>C x = f *\<^sub>V x\<close>
  unfolding the_riesz_rep_def
  apply (rule someI2_ex)
  by (simp_all add: riesz_frechet_representation_cblinfun_existence)

lemma the_riesz_rep_unique:
  assumes \<open>\<And>x. f *\<^sub>V x = t \<bullet>\<^sub>C x\<close>
  shows \<open>t = the_riesz_rep f\<close>
  using assms riesz_frechet_representation_cblinfun_unique the_riesz_rep by metis

lemma the_riesz_rep_scaleC: \<open>the_riesz_rep (c *\<^sub>C f) = cnj c *\<^sub>C the_riesz_rep f\<close>
  apply (rule the_riesz_rep_unique[symmetric])
  by auto

lemma the_riesz_rep_add: \<open>the_riesz_rep (f + g) = the_riesz_rep f + the_riesz_rep g\<close>
  apply (rule the_riesz_rep_unique[symmetric])
  by (auto simp: cinner_add_left cblinfun.add_left)

lemma the_riesz_rep_norm[simp]: \<open>norm (the_riesz_rep f) = norm f\<close>
  apply (rule riesz_frechet_representation_cblinfun_norm[symmetric])
  by simp

lemma bounded_antilinear_the_riesz_rep[bounded_antilinear]: \<open>bounded_antilinear the_riesz_rep\<close>
  by (metis (no_types, opaque_lifting) bounded_antilinear_intro dual_order.refl mult.commute mult_1 the_riesz_rep_add the_riesz_rep_norm the_riesz_rep_scaleC)

definition the_riesz_rep_bilinear' :: \<open>('a::complex_normed_vector \<Rightarrow> 'b::chilbert_space \<Rightarrow> complex) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>the_riesz_rep_bilinear' p x = the_riesz_rep (CBlinfun (p x))\<close>

lemma the_riesz_rep_bilinear'_correct:
  assumes \<open>bounded_clinear (p x)\<close>
  shows \<open>(the_riesz_rep_bilinear' p x) \<bullet>\<^sub>C y = p x y\<close>
  by (auto simp add: the_riesz_rep_bilinear'_def assms bounded_clinear_CBlinfun_apply)

lemma CBlinfun_plus: 
  assumes [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  shows \<open>CBlinfun (f + g) = CBlinfun f + CBlinfun g\<close>
  by (auto intro!: cblinfun_eqI simp: plus_fun_def bounded_clinear_add CBlinfun_inverse cblinfun.add_left)

lemma CBlinfun_scaleC:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>CBlinfun (\<lambda>y. c *\<^sub>C f y) = c *\<^sub>C CBlinfun f\<close>
  by (simp add: assms eq_onp_same_args scaleC_cblinfun.abs_eq)


lemma the_riesz_rep_bilinear'_plus1:
  assumes \<open>\<And>x. bounded_clinear (p x)\<close> and \<open>\<And>x. bounded_clinear (q x)\<close>
  shows \<open>the_riesz_rep_bilinear' (p + q) = the_riesz_rep_bilinear' p + the_riesz_rep_bilinear' q\<close>
  by (auto intro!: ext simp add: the_riesz_rep_add CBlinfun_plus the_riesz_rep_bilinear'_def 
      assms bounded_clinear_CBlinfun_apply)

lemma the_riesz_rep_bilinear'_plus2:
  assumes \<open>bounded_sesquilinear p\<close>
  shows \<open>the_riesz_rep_bilinear' p (x + y) = the_riesz_rep_bilinear' p x + the_riesz_rep_bilinear' p y\<close>
proof -
  have [simp]: \<open>p (x + y) = p x + p y\<close>
    using assms bounded_sesquilinear.add_left by fastforce
  have [simp]: \<open>bounded_clinear (p x)\<close> for x
    by (simp add: assms bounded_sesquilinear.bounded_clinear_right)
  show ?thesis
    by (auto intro!: ext simp add: the_riesz_rep_add CBlinfun_plus the_riesz_rep_bilinear'_def
      assms bounded_clinear_CBlinfun_apply)
qed

lemma the_riesz_rep_bilinear'_scaleC1:
  assumes \<open>\<And>x. bounded_clinear (p x)\<close>
  shows \<open>the_riesz_rep_bilinear' (\<lambda>x y. c *\<^sub>C p x y) = (\<lambda>x. cnj c *\<^sub>C the_riesz_rep_bilinear' p x)\<close>
  by (auto intro!: ext simp add: the_riesz_rep_scaleC CBlinfun_scaleC the_riesz_rep_bilinear'_def 
      assms bounded_clinear_CBlinfun_apply
      simp del: complex_scaleC_def scaleC_conv_of_complex)

lemma the_riesz_rep_bilinear'_scaleC2:
  assumes \<open>bounded_sesquilinear p\<close>
  shows \<open>the_riesz_rep_bilinear' p (c *\<^sub>C x) = c *\<^sub>C the_riesz_rep_bilinear' p x\<close>
proof -
  have [simp]: \<open>p (c *\<^sub>C x) = (\<lambda>y. cnj c *\<^sub>C p x y)\<close>
    using assms bounded_sesquilinear.scaleC_left by blast
  have [simp]: \<open>bounded_clinear (p x)\<close> for x
    by (simp add: assms bounded_sesquilinear.bounded_clinear_right)
  show ?thesis
    by (auto intro!: ext simp add: the_riesz_rep_scaleC CBlinfun_scaleC the_riesz_rep_bilinear'_def
      assms bounded_clinear_CBlinfun_apply
      simp del: complex_scaleC_def scaleC_conv_of_complex)
qed

lemma bounded_clinear_the_riesz_rep_bilinear'2:
  assumes \<open>bounded_sesquilinear p\<close>
  shows \<open>bounded_clinear (the_riesz_rep_bilinear' p)\<close>
proof -
  obtain K0 where K0: \<open>cmod (p x y) \<le> norm x * norm y * K0\<close> for x y
    using assms bounded_sesquilinear.bounded  by blast
  define K where \<open>K = max K0 0\<close>
  with K0 have K: \<open>cmod (p x y) \<le> norm x * norm y * K\<close> for x y
    by (smt (verit, del_insts) mult_nonneg_nonneg mult_nonneg_nonpos norm_ge_zero)
  have [simp]: \<open>K \<ge> 0\<close>
    by (simp add: K_def)
  have [simp]: \<open>bounded_clinear (p x)\<close> for x
    by (simp add: assms bounded_sesquilinear.bounded_clinear_right)
  have "norm (the_riesz_rep_bilinear' p x) \<le> norm x * K" for x
    unfolding the_riesz_rep_bilinear'_def
    using K by (auto intro!: norm_cblinfun_bound simp: bounded_clinear_CBlinfun_apply mult.commute mult.left_commute)
  then show ?thesis
    apply (rule_tac bounded_clinearI)
    by (auto simp: assms the_riesz_rep_bilinear'_plus2 the_riesz_rep_bilinear'_scaleC2)
qed

lift_definition the_riesz_rep_bilinear:: \<open>('a::complex_normed_vector \<Rightarrow> 'b::chilbert_space \<Rightarrow> complex) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b)\<close> is
  \<open>\<lambda>p. if bounded_sesquilinear p then the_riesz_rep_bilinear' p else 0\<close>
  by (auto simp: bounded_clinear_the_riesz_rep_bilinear'2 zero_fun_def)

lemma the_riesz_rep_bilinear_correct:
  assumes \<open>bounded_sesquilinear p\<close>
  shows \<open>(the_riesz_rep_bilinear p x) \<bullet>\<^sub>C y = p x y\<close>
  apply (transfer fixing: p)
  by (simp add: assms bounded_sesquilinear.bounded_clinear_right the_riesz_rep_bilinear'_correct)


lemma onorm_case_prod_plus: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::{real_normed_vector, not_singleton}) = sqrt 2\<close>
proof -
  obtain x :: 'a where \<open>x \<noteq> 0\<close>
    apply atomize_elim by auto
  show ?thesis
    apply (rule onormI[where x=\<open>(x,x)\<close>])
    using norm_plus_leq_norm_prod apply force
    using  \<open>x \<noteq> 0\<close>
    by (auto simp add: zero_prod_def norm_prod_def real_sqrt_mult
        simp flip: scaleR_2)
qed

lemma comparable_hermitean:
  assumes \<open>a \<le> b\<close>
  assumes \<open>a* = a\<close>
  shows \<open>b* = b\<close>
  by (smt (verit, best) assms(1) assms(2) cinner_hermitian_real cinner_real_hermiteanI comparable complex_is_real_iff_compare0 less_eq_cblinfun_def)

lemma comparable_hermitean':
  assumes \<open>a \<le> b\<close>
  assumes \<open>b* = b\<close>
  shows \<open>a* = a\<close>
  by (smt (verit, best) assms(1) assms(2) cinner_hermitian_real cinner_real_hermiteanI comparable complex_is_real_iff_compare0 less_eq_cblinfun_def)

lemma sum_butterfly_is_Proj:
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>is_Proj (\<Sum>e\<in>E. butterfly e e)\<close>
proof (cases \<open>finite E\<close>)
  case True
  show ?thesis
  proof (rule is_Proj_I)
    show \<open>(\<Sum>e\<in>E. butterfly e e)* = (\<Sum>e\<in>E. butterfly e e)\<close>
      by (simp add: sum_adj)
    have ortho: \<open>f \<noteq> e \<Longrightarrow> e \<in> E \<Longrightarrow> f \<in> E \<Longrightarrow> is_orthogonal f e\<close> for f e
      by (meson assms(1) is_ortho_set_def)
    have unit: \<open>e \<bullet>\<^sub>C e = 1\<close> if \<open>e \<in> E\<close> for e
      using assms(2) cnorm_eq_1 that by blast
    have *: \<open>(\<Sum>f\<in>E. (f \<bullet>\<^sub>C e) *\<^sub>C butterfly f e) = butterfly e e\<close> if \<open>e \<in> E\<close> for e
      apply (subst sum_single[where i=e])
      by (auto intro!: simp: that ortho unit True)
    show \<open>(\<Sum>e\<in>E. butterfly e e) o\<^sub>C\<^sub>L (\<Sum>e\<in>E. butterfly e e) = (\<Sum>e\<in>E. butterfly e e)\<close>
      by (auto simp: * cblinfun_compose_sum_right cblinfun_compose_sum_left)
  qed
next
  case False
  then show ?thesis
    by simp
qed

lemma norm_is_Proj: \<open>norm P \<le> 1\<close> if \<open>is_Proj P\<close>
  using is_Proj_partial_isometry norm_partial_isometry that by fastforce

lemma bounded_clinear_inv:
  assumes [simp]: \<open>bounded_clinear f\<close>
  assumes b: \<open>b > 0\<close>
  assumes bound: \<open>\<And>x. norm (f x) \<ge> b * norm x\<close>
  assumes \<open>surj f\<close>
  shows \<open>bounded_clinear (inv f)\<close>
proof (rule bounded_clinear_intro)
  fix x y :: 'b and r :: complex
  define x' y' where \<open>x' = inv f x\<close> and \<open>y' = inv f y\<close>
  have [simp]: \<open>clinear f\<close>
    by (simp add: bounded_clinear.clinear)
  have [simp]: \<open>inj f\<close>
  proof (rule injI)
    fix x y assume \<open>f x = f y\<close>
    then have \<open>norm (f (x - y)) = 0\<close>
      by (simp add: complex_vector.linear_diff)
    with bound b have \<open>norm (x - y) = 0\<close>
      by (metis linorder_not_le mult_le_0_iff nle_le norm_ge_zero)
    then show \<open>x = y\<close>
      by simp
  qed

  from \<open>surj f\<close>
  have [simp]: \<open>x = f x'\<close> \<open>y = f y'\<close>
    by (simp_all add: surj_f_inv_f x'_def y'_def)
  show "inv f (x + y) = inv f x + inv f y"
    by (simp flip: complex_vector.linear_add)
  show "inv f (r *\<^sub>C x) = r *\<^sub>C inv f x"
    by (simp flip: clinear.scaleC)
  from bound have "b * norm (inv f x) \<le> norm x" 
    by (simp flip: clinear.scaleC)
  with b show "norm (inv f x) \<le> norm x * inverse b" 
    by (smt (verit, ccfv_threshold) left_inverse mult.commute mult_cancel_right1 mult_le_cancel_left_pos vector_space_over_itself.scale_scale)
qed

lemma sum_cmod_pos: 
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>(\<Sum>x\<in>A. cmod (f x)) = cmod (\<Sum>x\<in>A. f x)\<close>
  by (metis (mono_tags, lifting) assms complex_of_real_cmod of_real_eq_iff of_real_sum sum.cong sum_nonneg)

lemma adj_inject: \<open>adj a = adj b \<longleftrightarrow> a = b\<close>
  by (metis (mono_tags, lifting) adj_minus cblinfun_compose_zero_left eq_iff_diff_eq_0 op_square_nondegenerate)

lemma norm_AadjA[simp]: \<open>norm (A* o\<^sub>C\<^sub>L A) = (norm A)\<^sup>2\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis double_adj norm_AAadj norm_adj)

lemma partial_isometry_square_proj: \<open>is_Proj (a* o\<^sub>C\<^sub>L a)\<close> if \<open>partial_isometry a\<close>
  by (simp add: partial_isometry_adj_a_o_a that)

lemma partial_isometry_adj[simp]: \<open>partial_isometry (a*)\<close> if \<open>partial_isometry a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have ran_ker: \<open>a *\<^sub>S top = - kernel (a*)\<close>
    by (simp add: kernel_compl_adj_range)

  have \<open>norm (a* *\<^sub>V h) = norm h\<close> if \<open>h \<in> range a\<close> for h
  proof -
    from that obtain x where h: \<open>h = a x\<close>
      by auto
    have \<open>norm (a* *\<^sub>V h) = norm (a* *\<^sub>V a *\<^sub>V x)\<close>
      by (simp add: h)
    also have \<open>\<dots> = norm (Proj (- kernel a) *\<^sub>V x)\<close>
      by (simp add: \<open>partial_isometry a\<close> partial_isometry_adj_a_o_a simp_a_oCL_b')
    also have \<open>\<dots> = norm (a *\<^sub>V Proj (- kernel a) *\<^sub>V x)\<close>
      by (metis Proj_range \<open>partial_isometry a\<close> cblinfun_apply_in_image partial_isometry_def)
    also have \<open>\<dots> = norm (a *\<^sub>V x)\<close>
      by (smt (verit, best) Proj_idempotent \<open>partial_isometry a\<close> adj_Proj cblinfun_apply_cblinfun_compose cinner_adj_right cnorm_eq partial_isometry_adj_a_o_a)
    also have \<open>\<dots> = norm h\<close>
      using h by auto
    finally show ?thesis
      by -
  qed

  then have norm_pres: \<open>norm (a* *\<^sub>V h) = norm h\<close> if \<open>h \<in> closure (range a)\<close> for h
    using that apply (rule on_closure_eqI)
      apply assumption
    by (intro continuous_intros)+

  show ?thesis
    apply (rule partial_isometryI)
    by (auto simp: cblinfun_image.rep_eq norm_pres simp flip: ran_ker)
qed

unbundle no_cblinfun_notation

end
