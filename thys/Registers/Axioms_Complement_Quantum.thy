section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum With_Type.With_Type_Inst_Complex_Bounded_Operators Quantum_Extra Tensor_Product.Weak_Star_Topology
    Tensor_Product.Partial_Trace
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")


(* lemma finite_subsets_at_top_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_set R ===> rel_filter (rel_set R)) finite_subsets_at_top finite_subsets_at_top\<close>
proof -
  have \<open>\<exists>Z. (\<forall>\<^sub>F (S', T') in Z. rel_set R S' T')
          \<and> map_filter_on {(x, y). rel_set R x y} fst Z = finite_subsets_at_top S
          \<and> map_filter_on {(x, y). rel_set R x y} snd Z = finite_subsets_at_top T\<close>
    if \<open>rel_set R S T\<close> for S T
  proof -
    from that \<open>bi_unique R\<close>
    obtain s2t where T_s2t_S: "T = s2t ` S" and "inj_on s2t S" and R_s2t: "\<forall>x\<in>S. R x (s2t x)"
      using bi_unique_rel_set_lemma by blast
    define Z where \<open>Z = filtermap (\<lambda>S. (S, s2t ` S)) (finite_subsets_at_top S)\<close>
    have R_S2T: \<open>rel_set R S' (s2t ` S')\<close> if \<open>S' \<subseteq> S\<close> for S'
      by (smt (verit, ccfv_threshold) R_s2t \<open>inj_on s2t S\<close> f_inv_into_f in_mono inj_on_image_mem_iff inv_into_into rel_setI that)
    then have ev_R: \<open>\<forall>\<^sub>F (S', T') in Z. rel_set R S' T'\<close>
      by (auto simp: Z_def eventually_filtermap intro!: eventually_finite_subsets_at_top_weakI)
    have 1: \<open>map_filter_on {(x, y). rel_set R x y} fst Z = finite_subsets_at_top S\<close>
      apply (simp add: filter_eq_iff eventually_map_filter_on ev_R)
      by (simp add: Z_def eventually_filtermap R_S2T eventually_finite_subsets_at_top)
    note More_List.no_leading_Cons[rule del]
    have P_s2t: \<open>S' \<subseteq> S \<Longrightarrow> finite T' \<Longrightarrow> s2t ` S' \<subseteq> T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> P T'\<close> 
      if P: \<open>\<forall>S''. finite S'' \<and> S' \<subseteq> S'' \<and> S'' \<subseteq> S \<longrightarrow> P (s2t ` S'')\<close>
      for S' P T'
      using P[rule_format, of \<open>inv_into S s2t ` T'\<close>]
      by (metis T_s2t_S \<open>inj_on s2t S\<close> equalityE finite_imageI image_inv_into_cancel image_mono inv_into_image_cancel)

    have 2: \<open>map_filter_on {(x, y). rel_set R x y} snd Z = finite_subsets_at_top T\<close>
      apply (simp add: filter_eq_iff eventually_map_filter_on ev_R)
      apply (simp add: Z_def eventually_filtermap R_S2T eventually_finite_subsets_at_top)
      apply (intro allI Ex_iffI[where f=\<open>image s2t\<close> and g=\<open>image (inv_into S s2t)\<close>])
       apply (safe intro!: intro: P_s2t)
        (* Sledgehammer proofs below *)
           apply blast
          using T_s2t_S apply blast
         apply (metis P_s2t)
        apply blast
       apply (metis T_s2t_S in_mono inv_into_into)
      by (metis T_s2t_S finite_imageI image_inv_into_cancel image_mono)

    from ev_R 1 2
    show ?thesis
      by auto
  qed
  then show ?thesis
    by (simp add: rel_filter.simps rel_funI)
qed *)

(* TODO: do we even need this, given sum_parametric'? *)
(* lemma sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> rel_set R ===> cr_cblinfun_weak_star) sum sum\<close>
  apply (rule sum_parametric')
    apply transfer_step
    apply transfer_prover
  by transfer_prover *)
(* proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd\<close> and g A B
  assume Rfg[transfer_rule]: \<open>(R ===> cr_cblinfun_weak_star) f g\<close>
  assume [transfer_rule]: \<open>rel_set R A B\<close>
  with \<open>bi_unique R\<close>
  obtain m where BFA: "B = m ` A" and inj: "inj_on m A" and Rf: "\<forall>x\<in>A. R x (m x)"
    using bi_unique_rel_set_lemma by blast
  show \<open>cr_cblinfun_weak_star (sum f A) (sum g B)\<close>
    apply (subst BFA) using inj Rf
  proof (induction A rule:infinite_finite_induct)
    case (infinite A)
    then show ?case
      by (auto simp: zero_cblinfun_weak_star.transfer)
  next
    case empty
    show ?case
      by (auto simp: zero_cblinfun_weak_star.transfer)
  next
    case (insert x F)
    have \<open>cr_cblinfun_weak_star (f x + a) (g y + b)\<close>
      if [transfer_rule]: \<open>cr_cblinfun_weak_star a b\<close> and [transfer_rule]: \<open>R x y\<close> for a b y
      by transfer_prover
    with insert show ?case
      by simp
  qed
qed *)

(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
lemma has_sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star ===> (\<longleftrightarrow>)) (has_sum_in weak_star_topology) has_sum\<close>
  unfolding has_sum_euclidean_iff[symmetric]
  by transfer_prover

lemma summable_on_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> (\<longleftrightarrow>)) (summable_on_in weak_star_topology) Infinite_Sum.summable_on\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
  unfolding summable_on_def summable_on_in_def
  by transfer_prover


lemma infsum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star) (infsum_in weak_star_topology) infsum\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd\<close> and g A B
  assume [transfer_rule]: \<open>(R ===> cr_cblinfun_weak_star) f g\<close>
  assume [transfer_rule]: \<open>rel_set R A B\<close>
  show \<open>cr_cblinfun_weak_star (infsum_in Weak_Star_Topology.weak_star_topology f A) (infsum g B)\<close>
  proof (cases \<open>g summable_on B\<close>)
    case True
    then have True': \<open>summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    define a b where \<open>a = infsum_in weak_star_topology f A\<close> and \<open>b = infsum g B\<close>
    from True' have 1: \<open>has_sum_in weak_star_topology f A a\<close>
      by (simp add: a_def has_sum_in_infsum_in)
    from True have \<open>has_sum g B b\<close>
      using b_def summable_iff_has_sum_infsum by blast
    then have 2: \<open>b' = b\<close> if \<open>has_sum g B b'\<close> for b'
      using infsumI that by blast
    from 1 2 show \<open>cr_cblinfun_weak_star a b\<close>
      unfolding cr_cblinfun_weak_star_def
      apply transfer
      by simp
  next
    case False
    then have False': \<open>\<not> summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    then show ?thesis
      by (simp add: False infsum_not_exists not_summable_infsum_in_0 zero_cblinfun_weak_star.transfer)
  qed
qed

definition \<open>register_decomposition_basis \<Phi> = (SOME B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = \<Phi> (selfbutterket undefined) *\<^sub>S \<top>)\<close> 
  for \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>

lemma bounded_clinear_cblinfun_compose_left: \<open>bounded_clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose)
lemma bounded_clinear_cblinfun_compose_right: \<open>bounded_clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose)
lemma clinear_cblinfun_compose_left: \<open>clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose bounded_clinear.clinear)
lemma clinear_cblinfun_compose_right: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_clinear.clinear bounded_clinear_cblinfun_compose_right)

typedef temp = "{undefined::nat}"
  sorry
find_theorems "_::temp"
setup_lifting type_definition_temp
find_theorems "_::temp"

lemma closure_of_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close> and T :: \<open>'a topology\<close> and U :: \<open>'b topology\<close>
  assumes haus: \<open>hausdorff U\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes xS: \<open>x \<in> T closure_of S\<close>
  assumes cont: \<open>continuous_map T U f\<close> \<open>continuous_map T U g\<close>
  shows \<open>f x = g x\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 't::topological_space = topspace T with (\<lambda>S. openin T (S \<inter> topspace T)). 
        \<forall>\<^sub>\<tau> 'u::t2_space = topspace U with (\<lambda>S. openin U (S \<inter> topspace U)).
        f x = g x\<close>
  proof (rule with_typeI)
    show \<open>fst (topspace T, \<lambda>S. openin T (S \<inter> topspace T)) \<noteq> {}\<close>
      apply auto
      by (metis equals0D in_closure_of xS)
    have \<open>Domainp (rel_fun (rel_set (equal_onp (topspace T))) (=)) (\<lambda>S. openin T (S \<inter> topspace T))\<close>
      apply (intro Domainp.intros[where b=\<open>(\<lambda>S. openin T (S \<inter> topspace T))\<close>] rel_funI)
      by (metis equal_onp_def order_antisym_conv rel_setD1 rel_setD2 subset_eq)
    moreover have \<open>with_type_topological_space_class_pred' (\<lambda>x. x \<in> topspace T) (\<lambda>S. openin T (S \<inter> topspace T))\<close>
      apply (simp add: with_type_topological_space_class_pred'_def)
      apply safe
       apply (metis Int_ac(3) Int_ac(4) inf.orderE openin_clauses(2) unfold_simps(2))
      by (metis inf.orderE openin_clauses(2) openin_clauses(3) openin_topspace subset_eq)
    ultimately show \<open>fst with_type_topological_space_class (fst (topspace T, \<lambda>S. openin T (S \<inter> topspace T)))
     (snd (topspace T, \<lambda>S. openin T (S \<inter> topspace T)))\<close>
      by (auto simp: with_type_topological_space_class_def with_type_topological_space_class_pred_def
          with_type_topological_space_class_dom_def   )
    show \<open>with_type_compat_rel (fst with_type_topological_space_class) (fst (topspace T, \<lambda>S. openin T (S \<inter> topspace T)))
         (snd with_type_topological_space_class)\<close>
      apply (simp add: with_type_compat_rel_def with_type_topological_space_class_def
          with_type_topological_space_class_pred_def with_type_topological_space_class_dom_def
          with_type_topological_space_class_pred'_def with_type_t2_space_class_rel_def)
      apply safe
      by (metis DomainPI with_type_has_domain_def with_type_topological_space_class_dom_def with_type_topological_space_class_has_dom)
    fix RepT :: \<open>'t \<Rightarrow> 'a\<close> and AbsT and abs_ops_T
    assume typedefT: \<open>type_definition RepT AbsT (fst (topspace T, \<lambda>S. openin T (S \<inter> topspace T)))\<close>
      (* Like on_closure_eqI *)
    define crT where \<open>crT \<equiv> \<lambda>x y. x = RepT y\<close>
    have [transfer_rule]: \<open>bi_unique crT\<close>
      using typedefT
      by (simp add: crT_def typedef_bi_unique)
    have [transfer_rule]: \<open>right_total crT\<close>
      by (simp add: crT_def right_totalI)
    have [transfer_rule]: \<open>rel_fun crT (=) (\<lambda>x. x) RepT\<close>
      by (simp add: crT_def rel_funI)
    have [transfer_rule]: \<open>Domainp crT = (\<lambda>x. x \<in> topspace T)\<close>
      sorry
    assume \<open>snd with_type_topological_space_class (\<lambda>x y. x = RepT y)
        (snd (topspace T, \<lambda>S. openin T (S \<inter> topspace T))) abs_ops_T\<close>
    then have [transfer_rule]: \<open>rel_fun (rel_set (\<lambda>x y. x = RepT y)) (=) (\<lambda>S. openin T (S \<inter> topspace T)) abs_ops_T\<close>
      by (simp add: with_type_topological_space_class_def
          with_type_topological_space_class_rel_def)
    show \<open>\<forall>\<^sub>\<tau> 'u::t2_space = topspace U with (\<lambda>S. openin U (S \<inter> topspace U)).
        f x = g x\<close>
    proof (rule with_typeI)
      show \<open>fst (topspace U, \<lambda>S. openin U (S \<inter> topspace U)) \<noteq> {}\<close>
        apply auto
        sorry
      have \<open>Domainp (rel_fun (rel_set (equal_onp (topspace U))) (=)) (\<lambda>S. openin U (S \<inter> topspace U))\<close>
        apply (intro Domainp.intros[where b=\<open>(\<lambda>S. openin U (S \<inter> topspace U))\<close>] rel_funI)
        by (metis equal_onp_def order_antisym_conv rel_setD1 rel_setD2 subset_eq)
      moreover have \<open>with_type_t2_space_class_pred' (\<lambda>x. x \<in> topspace U) (\<lambda>S. openin U (S \<inter> topspace U))\<close>
        apply (simp add: with_type_t2_space_class_pred'_def)
        apply safe
          apply (metis Int_ac(3) Int_ac(4) inf.orderE openin_clauses(2) unfold_simps(2))
         apply (metis inf.orderE openin_clauses(2) openin_clauses(3) openin_topspace subset_eq)
        by (smt (verit) assms(1) hausdorff_def inf_absorb1 openin_subset subsetD)
      ultimately show \<open>fst with_type_t2_space_class (fst (topspace U, \<lambda>S. openin U (S \<inter> topspace U)))
     (snd (topspace U, \<lambda>S. openin U (S \<inter> topspace U)))\<close>
        by (auto simp: with_type_t2_space_class_def with_type_t2_space_class_pred_def
            with_type_t2_space_class_dom_def   )
      show \<open>with_type_compat_rel (fst with_type_t2_space_class) (fst (topspace U, \<lambda>S. openin U (S \<inter> topspace U)))
         (snd with_type_t2_space_class)\<close>
        apply (simp add: with_type_compat_rel_def with_type_t2_space_class_def
            with_type_t2_space_class_pred_def with_type_t2_space_class_dom_def
            with_type_t2_space_class_pred'_def with_type_t2_space_class_rel_def)
        apply safe
        by -
      fix RepU :: \<open>'u \<Rightarrow> 'b\<close> and AbsU and abs_ops_U
      assume typedefU: \<open>type_definition RepU AbsU (fst (topspace U, \<lambda>S. openin U (S \<inter> topspace U)))\<close>
      define crU where \<open>crU \<equiv> \<lambda>x y. x = RepU y\<close>
      have [transfer_rule]: \<open>bi_unique crU\<close>
        using typedefU
        by (simp add: crU_def typedef_bi_unique)
      have [transfer_rule]: \<open>right_total crU\<close>
        by (simp add: crU_def right_totalI)
      have [transfer_rule]: \<open>rel_fun crU (=) (\<lambda>x. x) RepU\<close>
        by (simp add: crU_def rel_funI)
      have [transfer_rule]: \<open>Domainp crU = (\<lambda>x. x \<in> topspace U)\<close>
sledgehammer
sorry

        sorry
      assume \<open>snd with_type_t2_space_class (\<lambda>x y. x = RepU y) (snd (topspace U, \<lambda>S. openin U (S \<inter> topspace U)))
        abs_ops_U\<close>
      then have [transfer_rule]: \<open>rel_fun (rel_set (\<lambda>x y. x = RepU y)) (=) (\<lambda>S. openin U (S \<inter> topspace U)) abs_ops_U\<close>
        by (simp add: with_type_t2_space_class_def
            with_type_t2_space_class_rel_def)
      note on_closure_eqI[where 'a='t and 'b='u]
      then show \<open>f x = g x\<close>
        apply transfer
qed


(* lemma xxx: \<open>\<forall>\<^sub>\<tau> 's::chilbert_space = closure (cspan S) with (scaleR, scaleC, plus, 0, minus, uminus, dist, norm, sgn, uniformity, open, cinner). 
          \<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
  sorry
thm xxx[cancel_with_type] *)

lemma map_filter_on_id: \<open>map_filter_on S (\<lambda>x. x) F = F\<close> if \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
  using that
  by (auto intro!: filter_eq_iff[THEN iffD2] simp: eventually_map_filter_on eventually_frequently_simps)

lemma inverse_real_inverse: \<open>inverse_real_inst.inverse_real = inverse\<close>
  by (simp add: HOL.nitpick_unfold)

named_theorems with_type_intros
lemma [with_type_intros]: \<open>fst (A,B) \<noteq> {}\<close> if \<open>A \<noteq> {}\<close>
  using that by simp
lemma [with_type_intros]: \<open>with_type_compat_rel C (fst (S,p)) R\<close> if \<open>with_type_compat_rel C S R\<close>
  using that by simp
declare with_typeI[with_type_intros]

lemma with_type_chilbert_space_class_subspaceI[with_type_intros]: \<open>fst with_type_chilbert_space_class
     (fst (S, (*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity_on S, openin (top_of_set S), (\<bullet>\<^sub>C)))
     (snd (S, (*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity_on S, openin (top_of_set S), (\<bullet>\<^sub>C)))\<close>
  if [simp]: \<open>csubspace S\<close> \<open>closed S\<close>
  (* TODO open and uniformity may need to be restricted! *)
proof -
  have open1: \<open>(\<exists>y. \<forall>x ya. rel_set (equal_onp S) x ya \<longrightarrow> open x = y ya)\<close>
    apply (rule exI[of _ \<open>open\<close>])
    by (smt (verit, ccfv_threshold) equal_onp_def rel_setD1 rel_setD2 subset_iff topological_space_class.openI)
  have uniformity: \<open>rel_filter (rel_prod (equal_onp S) (equal_onp S)) (uniformity_on S) (uniformity_on S)\<close>
    apply (rule rel_filter.intros[where Z=\<open>map_filter_on (S\<times>S) (\<lambda>x. (x,x)) (uniformity_on S)\<close>])
      apply (simp add: eventually_map_filter_on always_eventually equal_onp_def eventually_inf_principal)
     apply (subst map_filter_on_comp)
    apply (auto simp add: map_filter_on_comp equal_onp_def eventually_inf_principal map_filter_on_id o_def)[3]
     apply (subst map_filter_on_comp)
    by (auto simp add: map_filter_on_comp equal_onp_def eventually_inf_principal map_filter_on_id o_def)
  have 0: \<open>(\<exists>y. \<forall>x ya. rel_set (equal_onp S) x ya \<longrightarrow> openin (top_of_set S) x = y ya)\<close>
    apply (rule exI[of _ \<open>openin (top_of_set S)\<close>])
    by (metis equal_onp_def equalityI rel_setD1 rel_setD2 subset_iff)
  have 1: \<open>with_type_chilbert_space_class_dom S ((*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity_on S, openin (top_of_set S), (\<bullet>\<^sub>C))\<close>
    apply (simp add: with_type_chilbert_space_class_dom_def Domainp_iff rel_fun_def equal_onp_def)
    by (auto intro!: 0 exI uniformity simp add: scaleR_scaleC complex_vector.subspace_scale
        complex_vector.subspace_add complex_vector.subspace_0 complex_vector.subspace_diff
        complex_vector.subspace_neg sgn_div_norm open1)
  have 2: \<open>with_type_chilbert_space_class_pred' (\<lambda>x. x \<in> S)
     ((*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity_on S, open, (\<bullet>\<^sub>C))\<close>
    apply (simp add: with_type_chilbert_space_class_pred'_def scaleR_scaleC)
    apply (intro conjI)
               apply (auto simp add: complex_vector.vector_space_assms dist_norm sgn_div_norm scaleR_scaleC
        cinner_simps inverse_real_inverse simp flip: of_real_inverse norm_eq_sqrt_cinner)
            defer
  defer
  defer
             defer
             defer
             defer
    using norm_diff_triangle_le norm_imp_pos_and_ge norm_minus_commute apply blast

    defer
            defer
    by -
  from 1 2
  show ?thesis
    by (simp add: with_type_chilbert_space_class_def with_type_chilbert_space_class_pred_def)
qed

lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
proof -
  note [[show_hyps]]
  (* TODO open and uniformity may need to be restricted! *)
  have \<open>\<forall>\<^sub>\<tau> 's::chilbert_space = closure (cspan S) with (scaleR, scaleC, plus, 0, minus, uminus, dist, norm, sgn, uniformity, open, cinner). 
          \<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
  proof (intro with_type_intros)
    show \<open>closure (cspan S) \<noteq> {}\<close>
      using complex_vector.span_clauses(2) by auto
    show \<open>csubspace (closure (cspan S))\<close>
      using closure_is_csubspace by blast
    show \<open>closed (closure (cspan S))\<close>
      by simp
    show \<open>with_type_compat_rel (fst with_type_chilbert_space_class)
     (closure (cspan S)) (snd with_type_chilbert_space_class)\<close>
      by (rule with_type_chilbert_space_class_rel_compat)
    fix Rep :: \<open>'s \<Rightarrow> 'a\<close> and Abs abs_ops
    assume \<open>type_definition Rep Abs
        (fst (closure (cspan S), (*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity, open, (\<bullet>\<^sub>C)))\<close>
    then have \<open>type_definition Rep Abs (closure (cspan S))\<close>
      by simp
    assume \<open>snd with_type_chilbert_space_class (\<lambda>x y. x = Rep y)
        (snd (closure (cspan S), (*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity, open, (\<bullet>\<^sub>C))) abs_ops\<close>
    then have \<open>with_type_chilbert_space_class_rel (\<lambda>x y. x = Rep y)
        ((*\<^sub>R), (*\<^sub>C), (+), 0, (-), uminus, dist, norm, sgn, uniformity, open, (\<bullet>\<^sub>C)) abs_ops\<close>
      unfolding with_type_chilbert_space_class_def
      by simp
    show \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
      apply transfer
      thm orthonormal_basis_exists
      by -
  next show x for x by -
  qed
  from this[cancel_with_type]
  show ?thesis
    by simp
qed

(* TODO move *)
lemma has_sum_in_comm_additive:
  fixes f :: \<open>'a \<Rightarrow> 'b :: comm_monoid_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: comm_monoid_add\<close>
  assumes \<open>continuous_map T U g\<close>
  assumes \<open>\<And>x y. g (x+y) = g x + g y\<close>
  assumes \<open>has_sum_in T f A l\<close>
  shows \<open>has_sum_in U (g o f) A (g l)\<close>
  sorry


lemma infsum_butterfly_ket_a: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (a *\<^sub>V ket i) (ket i)) UNIV a\<close>
proof -
  have \<open>has_sum_in weak_star_topology ((\<lambda>b. a o\<^sub>C\<^sub>L b) \<circ> (\<lambda>i. Misc.selfbutterket i)) UNIV (a o\<^sub>C\<^sub>L id_cblinfun)\<close>
    apply (rule has_sum_in_comm_additive)
    by (auto intro!: continuous_map_left_comp_weak_star infsum_butterfly_ket simp: cblinfun_compose_add_right)
  then show ?thesis
    by (auto simp: o_def cblinfun_comp_butterfly)
qed


lemma finite_rank_sum: \<open>finite_rank (\<Sum>x\<in>F. f x)\<close> if \<open>\<And>x. x\<in>F \<Longrightarrow> finite_rank (f x)\<close>
  using that apply (induction F rule:infinite_finite_induct)
  by (auto intro!: finite_rank_plus)

lemma finite_rank_weak_star_dense[simp]: \<open>weak_star_topology closure_of (Collect finite_rank) = (UNIV :: ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set)\<close>
proof -
  have \<open>x \<in> weak_star_topology closure_of (Collect finite_rank)\<close> for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  proof (rule limitin_closure_of)
    define f :: \<open>'a \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>f = (\<lambda>i. butterfly (x *\<^sub>V ket i) (ket i))\<close>
    have \<open>has_sum_in weak_star_topology f UNIV x\<close>
      using f_def infsum_butterfly_ket_a by blast
    then show \<open>limitin weak_star_topology (sum f) x (finite_subsets_at_top UNIV)\<close>
      using has_sum_in_def by blast
    show \<open>range (sum f) \<subseteq> Collect finite_rank\<close>
      by (auto intro!: finite_rank_sum simp: f_def)
    show \<open>finite_subsets_at_top UNIV \<noteq> \<bottom>\<close>
      by simp
  qed
  then show ?thesis
    by auto
qed

(* TODO move *)
lemma butterkets_weak_star_dense[simp]:
  \<open>weak_star_topology closure_of cspan {butterket (\<xi>::'a) (\<eta>::'b) |\<xi> \<eta>. True} = UNIV\<close>
proof -
  from continuous_map_image_closure_subset[OF weak_star_topology_weaker_than_euclidean]
  have \<open>weak_star_topology closure_of (cspan {butterket (\<xi>::'a) (\<eta>::'b) |\<xi> \<eta>. True}) \<supseteq> closure (cspan {butterket \<xi> \<eta> |\<xi> \<eta>. True})\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    by auto
  moreover from finite_rank_dense_compact
  have \<open>\<dots> \<supseteq> Collect finite_rank\<close>
    by (metis closure_subset compact_op_def mem_Collect_eq subsetI subset_antisym)
  ultimately have *: \<open>weak_star_topology closure_of (cspan {butterket (\<xi>::'a) (\<eta>::'b) |\<xi> \<eta>. True}) \<supseteq> Collect finite_rank\<close>
    by simp
  have \<open>weak_star_topology closure_of cspan {butterket \<xi> \<eta> |\<xi> \<eta>. True}
        = weak_star_topology closure_of (weak_star_topology closure_of cspan {butterket (\<xi>::'a) (\<eta>::'b) |\<xi> \<eta>. True})\<close>
  by simp
  also have \<open>\<dots> \<supseteq> weak_star_topology closure_of Collect finite_rank\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    using * closure_of_mono by blast
  also have \<open>\<dots> = UNIV\<close>
    by simp
  finally show ?thesis
    by auto
qed

lemma sandwich_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (sandwich A)\<close>
  using continuous_map_compose[OF continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star]
  by (auto simp: o_def sandwich_def[abs_def])

(* lemma continuous_map_cong:
  assumes \<open>\<And>x. x \<in> topspace T \<Longrightarrow> f x = g x\<close>
  shows \<open>continuous_map T S f \<longleftrightarrow> continuous_map T S g\<close>
  by (metis assms continuous_map_eq)
 *)

(* 
definition infsumopt where \<open>infsumopt f A = (if f summable_on A then Some (infsum f A) else None)\<close>

syntax (ASCII)
  "_infsumopt" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add option"  ("(3INFSUM? (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_infsumopt" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add option"  ("(2\<Sum>\<^sub>\<infinity>\<^sub>?(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>\<infinity>\<^sub>?i\<in>A. b" \<rightleftharpoons> "CONST infsumopt (\<lambda>i. b) A"

syntax (ASCII)
  "_univinfsumopt" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a option"  ("(3INFSUM? _./ _)" [0, 10] 10)
syntax
  "_univinfsumopt" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a option"  ("(2\<Sum>\<^sub>\<infinity>\<^sub>?_./ _)" [0, 10] 10)
translations
  "\<Sum>\<^sub>\<infinity>\<^sub>?x. t" \<rightleftharpoons> "CONST infsumopt (\<lambda>x. t) (CONST UNIV)"
 *)

ML \<open>
type lifted_typ = Type.


type env = (bool * typ) list
fun lift_term_to_maybe (env:env) (Bound i) : (bool * typ * term) = let val (lifted, typ) = nth env i in (lifted, typ, Bound i) end
  | lift_term_to_maybe env (Const(\<^const_name>\<open>divide\<close>, _)
\<close>
    

lemma TODO_NAME: \<open>trace (partial_trace' t o\<^sub>C\<^sub>L x) = trace (t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close> if \<open>trace_class t\<close>
  sorry

(* lemma continuous_map_cong:
  assumes \<open>\<And>x. x \<in> topspace T \<Longrightarrow> f x = g x\<close>
  shows \<open>continuous_map T S f \<longleftrightarrow> continuous_map T S g\<close>
sledgehammer
  by (metis assms continuous_map_eq)
sorry
 *)

lemma continuous_map_pullback_both:
  assumes cont: \<open>continuous_map T1 T2 g'\<close>
  assumes g'g: \<open>\<And>x. f1 x \<in> topspace T1 \<and> x \<in> A1 \<Longrightarrow> g' (f1 x) = f2 (g x)\<close>
  assumes top1: \<open>f1 -` topspace T1 \<inter> A1 \<subseteq> g -` A2\<close>
  shows \<open>continuous_map (pullback_topology A1 f1 T1) (pullback_topology A2 f2 T2) g\<close>
proof -
  from cont
  have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (g' \<circ> f1)\<close>
    by (rule continuous_map_pullback)
  then have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (f2 \<circ> g)\<close>
    apply (rule continuous_map_eq)
    by (simp add: g'g topspace_pullback_topology)
  then show ?thesis
    apply (rule continuous_map_pullback')
    by (simp add: top1 topspace_pullback_topology)
qed

definition partial_trace :: \<open>(('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'c) ell2)  \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close> where
  \<open>partial_trace t = (\<Sum>\<^sub>\<infinity>j. (tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j)))\<close>

lemma  
  assumes \<open>trace_class t\<close>
  shows partial_trace_has_sum: \<open>has_sum (\<lambda>j. (tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))) UNIV (partial_trace t)\<close>
  and partial_trace_summable: \<open>(\<lambda>j. (tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))) abs_summable_on UNIV\<close>
proof -
  show \<open>(\<lambda>j. (tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))) abs_summable_on UNIV\<close>
    by -
  then show \<open>has_sum (\<lambda>j. (tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j))) UNIV (partial_trace t)\<close>
    by (simp add: Axioms_Complement_Quantum.partial_trace_def abs_summable_summable)
qed

lemma partial_trace_trace_class[simp]: \<open>trace_class (partial_trace t)\<close> if \<open>trace_class t\<close>
proof -
  have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op (partial_trace t) *\<^sub>V x)) abs_summable_on range ket\<close>
    by -
  then show \<open>trace_class (partial_trace t)\<close>
    using is_onb_ket
    by (rule trace_classI[rotated])
qed

lemma TODO_NAME2: \<open>trace (partial_trace t o\<^sub>C\<^sub>L x) = trace (t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close> if \<open>trace_class t\<close>
  sorry

(* TODO move *)
lemma amplification_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
(* Two proofs (due to merge), I think first is more current. *)
  sorry
(*
proof (unfold weak_star_topology_def, rule continuous_map_pullback_both)
  define g' :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<Rightarrow> complex)
   \<Rightarrow> ('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'c) ell2 \<Rightarrow> complex\<close> where \<open>g' \<tau> t = \<tau> (if trace_class t then partial_trace t else 0)\<close> for \<tau> t
  have \<open>continuous_on UNIV g'\<close>
    by (simp add: continuous_on_coordinatewise_then_product g'_def)
  then show \<open>continuous_map euclidean euclidean g'\<close>
    using continuous_map_iff_continuous2 by blast
  show \<open>g' (\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) =
         (\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x \<otimes>\<^sub>o id_cblinfun) else 0)\<close> for x
    by (auto intro!: ext simp: g'_def TODO_NAME2) 
qed auto
 *)
(*
proof (unfold weak_star_topology_def', rule continuous_map_pullback_both)
  define g' :: \<open>(('b ell2, 'a ell2) trace_class \<Rightarrow> complex) \<Rightarrow> (('b \<times> 'c) ell2, ('a \<times> 'c) ell2) trace_class \<Rightarrow> complex\<close> where
    \<open>g' \<tau> t = \<tau> (partial_trace t)\<close> for \<tau> t
  have \<open>continuous_on UNIV g'\<close>
    by (simp add: continuous_on_coordinatewise_then_product g'_def)
  then show \<open>continuous_map euclidean euclidean g'\<close>
    using continuous_map_iff_continuous2 by blast
  show \<open>g' (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) = (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x \<otimes>\<^sub>o id_cblinfun))\<close> for x
    by (auto intro!: ext simp: g'_def TODO_NAME) 
qed auto
 *)

lemma register_decomposition:
  fixes \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis \<Phi>.
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
  \<comment> \<open>Proof based on @{cite daws21unitalanswer}\<close>
proof (rule with_typeI; unfold fst_conv snd_conv)
  show \<open>fst with_type_type_class (register_decomposition_basis \<Phi>) ()\<close>
    by (simp add: with_type_type_class_def)
  show \<open>with_type_compat_rel (fst with_type_type_class) (register_decomposition_basis \<Phi>) (snd with_type_type_class)\<close>
    using with_type_compat_rel_type by blast

  note [[simproc del: compatibility_warn]]
  define \<xi>0 :: 'a where \<open>\<xi>0 = undefined\<close>

  have \<open>bounded_clinear \<Phi>\<close>
    using assms register_def by blast
  then have [simp]: \<open>clinear \<Phi>\<close>
    by (simp add: bounded_clinear.clinear)

  define P where \<open>P i = selfbutterket i\<close> for i :: 'a

  note blinfun_cblinfun_eq_bi_unique[transfer_rule del]
  note cblinfun.bi_unique[transfer_rule del]
  note cblinfun.left_unique[transfer_rule del]
  note cblinfun.right_unique[transfer_rule del]
  note cblinfun.right_total[transfer_rule del]
  note id_cblinfun.transfer[transfer_rule del]

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>is_Proj (P' i)\<close> for i
    by (simp add: P_def P'_def butterfly_is_Proj register_projector)
  have sumP'id2: \<open>has_sum_in weak_star_topology (\<lambda>i. P' i) UNIV id_cblinfun\<close> (* TODO: we use this one *)
  proof -
    from infsum_butterfly_ket
    have \<open>has_sum_in weak_star_topology (\<Phi> o selfbutterket) UNIV (\<Phi> id_cblinfun)\<close>
      apply (rule has_sum_in_comm_additive[rotated -1])
      using assms by (auto simp: complex_vector.linear_add register_def)
    then show ?thesis
      by (simp add: P'_def P_def o_def)
  qed

  define S where \<open>S i = P' i *\<^sub>S \<top>\<close> for i :: 'a
  have P'id: \<open>P' i *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i \<psi>
    using S_def that proj_P'
    by (metis cblinfun_fixes_range is_Proj_algebraic)

  define S_iso' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a update\<close> where \<open>S_iso' i j = classical_operator (Some o Transposition.transpose i j)\<close> for i j :: 'a
  have S_iso'_apply: \<open>S_iso' i j *\<^sub>V ket i = ket j\<close> for i j
    by (simp add: S_iso'_def classical_operator_ket classical_operator_exists_inj)
  have S_iso'_unitary: \<open>unitary (S_iso' i j)\<close> for i j
    by (simp add: S_iso'_def unitary_classical_operator)
  have S_iso'_id: \<open>S_iso' i i = id_cblinfun\<close> for i
    by (auto intro!: equal_ket simp: S_iso'_def classical_operator_ket classical_operator_exists_inj)
  have S_iso'_adj_apply: \<open>(S_iso' i j)* *\<^sub>V ket j = ket i\<close> for i j
    by (metis S_iso'_apply S_iso'_unitary cblinfun_apply_cblinfun_compose id_cblinfun_apply unitaryD1)
  define S_iso where \<open>S_iso i j = \<Phi> (S_iso' i j)\<close> for i j
  have uni_S_iso: \<open>unitary (S_iso i j)\<close> for i j
    by (simp add: S_iso_def S_iso'_unitary register_unitary)
  have S_iso_S: \<open>S_iso i j *\<^sub>S S i = S j\<close> for i j
  proof -
    have \<open>S_iso i j *\<^sub>S S i = S_iso i j *\<^sub>S P' i *\<^sub>S S_iso j i *\<^sub>S \<top>\<close>
      by (simp add: S_def uni_S_iso)
    also have \<open>\<dots> = S j\<close>
      by (simp add: S_def P'_def S_iso_def P_def register_mult butterfly_comp_cblinfun cblinfun_comp_butterfly S_iso'_apply S_iso'_adj_apply
        flip: cblinfun_compose_image)
    finally show ?thesis
      by -
  qed
  have S_iso_id[simp]: \<open>S_iso i i = id_cblinfun\<close> for i
    by (simp add: S_iso'_id S_iso_def)

  obtain B\<^sub>0 where B\<^sub>0: \<open>is_ortho_set B\<^sub>0\<close> \<open>\<And>b. b \<in> B\<^sub>0 \<Longrightarrow> norm b = 1\<close> \<open>ccspan B\<^sub>0 = S \<xi>0\<close>
    using orthonormal_subspace_basis_exists[where S="{}" and V=\<open>S \<xi>0\<close>]
    apply atomize_elim by auto

  have register_decomposition_basis_\<Phi>: \<open>is_ortho_set (register_decomposition_basis \<Phi>) \<and>
       (\<forall>b\<in>register_decomposition_basis \<Phi>. norm b = 1) \<and>
       ccspan (register_decomposition_basis \<Phi>) = S \<xi>0\<close>
    unfolding register_decomposition_basis_def
    apply (rule someI2[where a=B\<^sub>0])
    using B\<^sub>0 by (auto simp: S_def P'_def P_def \<xi>0_def)

  define B where \<open>B i = S_iso \<xi>0 i ` register_decomposition_basis \<Phi>\<close> for i
  have B\<xi>0: \<open>B \<xi>0 = register_decomposition_basis \<Phi>\<close>
    using B_def by force
  have orthoB: \<open>is_ortho_set (B i)\<close> for i
    apply (auto simp add: B_def is_ortho_set_def)
    apply (metis (no_types, lifting) register_decomposition_basis_\<Phi> UNIV_I cblinfun_apply_cblinfun_compose cblinfun_fixes_range cinner_adj_left id_cblinfun_adjoint is_ortho_set_def top_ccsubspace.rep_eq uni_S_iso unitaryD1 unitary_id unitary_range)
    by (metis register_decomposition_basis_\<Phi> cinner_ket_same cinner_zero_left cnorm_eq_1 isometry_preserves_norm orthogonal_ket uni_S_iso unitary_isometry)
  have normalB: \<open>\<And>b. b \<in> B i \<Longrightarrow> norm b = 1\<close> for i
    by (metis (no_types, lifting) register_decomposition_basis_\<Phi> B_def imageE isometry_preserves_norm uni_S_iso unitary_twosided_isometry)
  have cspanB: \<open>ccspan (B i) = S i\<close> for i
    by (simp add: B_def register_decomposition_basis_\<Phi> B\<xi>0 S_iso_S flip: cblinfun_image_ccspan)

  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
  proof -
    have \<open>P' i o\<^sub>C\<^sub>L P' j = 0\<close>
      using \<open>i \<noteq> j\<close>
      by (simp add: P'_def P_def register_mult butterfly_comp_butterfly cinner_ket
          \<open>clinear \<Phi>\<close> complex_vector.linear_0)
    then have *: \<open>Proj (ccspan (B i)) o\<^sub>C\<^sub>L Proj (ccspan (B j)) = 0\<close>
      by (simp add: Proj_on_own_range S_def cspanB proj_P')
    then show \<open>is_orthogonal x y\<close>
      by (meson orthogonal_projectors_orthogonal_spaces orthogonal_spaces_ccspan that(1) that(2))
  qed

  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>

  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding cspanB S_def
    using proj_P' Proj_on_own_range'[symmetric] is_Proj_algebraic by blast

  show \<open>register_decomposition_basis \<Phi> \<noteq> {}\<close>
  proof (rule ccontr, simp)
    assume \<open>register_decomposition_basis \<Phi> = {}\<close>
    then have \<open>B i = {}\<close> for i
      by (simp add: B_def)
    then have \<open>S i = 0\<close> for i
      using cspanB by force
    then have \<open>P' i = 0\<close> for i
      by (simp add: P'B cspanB)
    with sumP'id2
    have \<open>has_sum_in weak_star_topology (\<lambda>i. 0) UNIV id_cblinfun\<close>
      by (metis (no_types, lifting) UNIV_I has_sum_in_0 has_sum_in_cong has_sum_in_unique hausdorff_weak_star id_cblinfun_not_0 weak_star_topology_topspace)
    then have \<open>id_cblinfun = 0\<close>
      using has_sum_in_0 has_sum_in_unique hausdorff_weak_star id_cblinfun_not_0 weak_star_topology_topspace by fastforce
    then show False
      using id_cblinfun_not_0 by blast
  qed

  from orthoBiBj orthoB have orthoB': \<open>is_ortho_set B'\<close>
    unfolding B'_def is_ortho_set_def by blast
  then have indepB': \<open>cindependent B'\<close>
    using is_ortho_set_cindependent by blast

  from orthoBiBj orthoB
  have Bdisj: \<open>B i \<inter> B j = {}\<close> if \<open>i \<noteq> j\<close> for i j
    unfolding is_ortho_set_def
    apply auto by (metis cinner_eq_zero_iff that)

  fix rep_c :: \<open>'c \<Rightarrow> 'b ell2\<close> and abs_c
  assume typedef_c: \<open>type_definition rep_c abs_c (register_decomposition_basis \<Phi>)\<close>
  then interpret type_definition rep_c abs_c \<open>register_decomposition_basis \<Phi>\<close> .

  have bij_rep_c: \<open>bij_betw rep_c (UNIV :: 'c set) (B \<xi>0)\<close>
    unfolding B\<xi>0
    apply (rule bij_betwI[where g=abs_c])
    using Rep Rep_inverse Abs_inverse by blast+

  define u where \<open>u = (\<lambda>(\<xi>,\<alpha>). \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>)\<close> for \<xi> :: 'a and \<alpha> :: \<open>'c\<close>

  have cinner_u: \<open>cinner (u \<xi>\<alpha>) (u \<xi>'\<alpha>') = of_bool (\<xi>\<alpha> = \<xi>'\<alpha>')\<close> for \<xi>\<alpha> \<xi>'\<alpha>'
  proof -
    obtain \<xi> \<alpha> \<xi>' \<alpha>' where \<xi>\<alpha>: \<open>\<xi>\<alpha> = (\<xi>,\<alpha>)\<close> and \<xi>'\<alpha>': \<open>\<xi>'\<alpha>' = (\<xi>',\<alpha>')\<close>
      apply atomize_elim by auto
    have \<open>cinner (u (\<xi>,\<alpha>)) (u (\<xi>', \<alpha>')) = cinner (\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>) (\<Phi> (butterket \<xi>' \<xi>0) *\<^sub>V rep_c \<alpha>')\<close>
      unfolding u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterket \<xi>' \<xi>0))* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>' \<xi>0 *) *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>0 \<xi>' o\<^sub>C\<^sub>L butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: register_mult cblinfun_apply_cblinfun_compose[symmetric])
    also have \<open>\<dots> = cinner (\<Phi> (of_bool (\<xi>'=\<xi>) *\<^sub>C selfbutterket \<xi>0) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: cinner_ket_left ket.rep_eq)
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (\<Phi> (selfbutterket \<xi>0) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: complex_vector.linear_0)
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (P' \<xi>0 *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      using P_def P'_def by simp
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (rep_c \<alpha>) (rep_c \<alpha>')\<close>
      apply (subst P'id)
      apply (metis B\<xi>0 Rep ccspan_superset cspanB in_mono)
      by simp
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * of_bool (\<alpha>=\<alpha>')\<close>
      using bij_rep_c orthoB normalB unfolding is_ortho_set_def
      by (smt (verit, best) B\<xi>0 Rep Rep_inject cnorm_eq_1 of_bool_eq(1) of_bool_eq(2))
    finally show ?thesis
      by (simp add: \<xi>'\<alpha>' \<xi>\<alpha>)
  qed
  define U where \<open>U = cblinfun_extension (range ket) (u o inv ket)\<close>
  have Uapply: \<open>U *\<^sub>V ket \<xi>\<alpha> = u \<xi>\<alpha>\<close> for \<xi>\<alpha>
    unfolding U_def
    apply (subst cblinfun_extension_apply)
    using cinner_u apply (auto intro!: cblinfun_extension_exists_ortho[where B=1])
    by (metis (full_types) cinner_u cnorm_eq_1 of_bool_eq_1_iff order_refl)
  have \<open>isometry U\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: Uapply cinner_u)
  
  have 1: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
  proof -
    have *: \<open>U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U = butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun\<close> for \<xi> \<eta>
    proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
      fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>'c\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
        apply atomize_elim by auto
      have \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta>) *\<^sub>V \<Phi> (butterket \<xi>1 \<xi>0) *\<^sub>V rep_c \<alpha>\<close>
        unfolding cblinfun_apply_cblinfun_compose \<xi>1\<alpha> Uapply u_def by simp
      also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta> o\<^sub>C\<^sub>L butterket \<xi>1 \<xi>0) *\<^sub>V rep_c \<alpha>\<close>
        by (metis (no_types, lifting) assms butterfly_comp_butterfly lift_cblinfun_comp(4) register_mult)
      also have \<open>\<dots> = U* *\<^sub>V \<Phi> (of_bool (\<eta>=\<xi>1) *\<^sub>C butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>\<close>
        by (simp add: cinner_ket)
      also have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C U* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V rep_c \<alpha>\<close>
        by (simp add: complex_vector.linear_scale)
      also have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
        unfolding Uapply u_def by simp
      also from \<open>isometry U\<close> have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C ket (\<xi>, \<alpha>)\<close>
        unfolding cblinfun_apply_cblinfun_compose[symmetric] by simp
      also have \<open>\<dots> = (butterket \<xi> \<eta> *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
        by (simp add: tensor_ell2_scaleC1 tensor_ell2_ket)
      also have \<open>\<dots> = (butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
        by (simp add: \<xi>1\<alpha> tensor_op_ket)
      finally show \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = (butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
        by -
    qed

    have cont1: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. U* o\<^sub>C\<^sub>L \<Phi> a o\<^sub>C\<^sub>L U)\<close>
      apply (subst asm_rl[of \<open>(\<lambda>a. U* o\<^sub>C\<^sub>L \<Phi> a o\<^sub>C\<^sub>L U) = (\<lambda>x. x o\<^sub>C\<^sub>L U) o (\<lambda>x. U* o\<^sub>C\<^sub>L x) o \<Phi>\<close>])
      apply (auto intro!: continuous_map_compose[where X'=weak_star_topology])
      using assms register_def continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star by blast+

    have *: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> if \<open>\<theta> \<in> cspan {butterket \<xi> \<eta> | \<xi> \<eta>. True}\<close> for \<theta>
      apply (rule complex_vector.linear_eq_on[where x=\<theta>, OF _ _ that])
        apply (intro \<open>clinear \<Phi>\<close>
          clinear_compose[OF _ clinear_cblinfun_compose_left, unfolded o_def]
          clinear_compose[OF _ clinear_cblinfun_compose_right, unfolded o_def])
       apply simp
      using * by blast
    have \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> 
      if \<open>\<theta> \<in> (weak_star_topology closure_of (cspan {butterket \<xi> \<eta> | \<xi> \<eta>. True}))\<close> for \<theta>
      apply (rule closure_of_eqI[OF _ _ that])
      using * cont1 amplification_weak_star_cont by auto
    with butterkets_weak_star_dense show ?thesis
      by auto
  qed
  have \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b = u (\<xi>, inv rep_c b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_rep_c that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>1) *\<^sub>S \<top>\<close>
        unfolding cblinfun_compose_image[symmetric] register_mult[OF assms]
        by simp
      also have \<open>\<dots> \<le> \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<top>\<close>
        by (meson cblinfun_image_mono top_greatest)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S S \<xi>0\<close>
        by (simp add: S_def P'_def P_def)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S ccspan (B \<xi>0)\<close>
        by (simp add: cspanB)
      also have \<open>\<dots> = ccspan (\<Phi> (butterket \<xi> \<xi>0) ` B \<xi>0)\<close>
        by (meson cblinfun_image_ccspan)
      also have \<open>\<dots> \<le> U *\<^sub>S \<top>\<close>
        by (rule ccspan_leqI, use * in auto)
      finally show ?thesis by -
    qed
    then have \<open>ccspan {\<Phi> (butterket \<xi> \<xi>) *\<^sub>V \<alpha> |\<xi> \<alpha>. True} \<le> U *\<^sub>S \<top>\<close>
      apply (rule_tac ccspan_leqI)
      using cblinfun_apply_in_image less_eq_ccsubspace.rep_eq by blast
    moreover have \<open>ccspan {\<Phi> (butterket \<xi> \<xi>) *\<^sub>V \<alpha> |\<xi> \<alpha>. True} = \<top>\<close>
    proof -
      define Q where \<open>Q = Proj (- ccspan {\<Phi> (butterket \<xi> \<xi>) *\<^sub>V \<alpha> |\<xi> \<alpha>. True})\<close>
      have \<open>has_sum_in weak_star_topology (\<lambda>\<xi>. Q o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<xi>)) UNIV (Q o\<^sub>C\<^sub>L id_cblinfun)\<close>
        apply (rule has_sum_in_comm_additive[where g=\<open>cblinfun_compose Q\<close> and T=weak_star_topology, unfolded o_def])
        using sumP'id2
        by (auto simp add: continuous_map_left_comp_weak_star P'_def P_def cblinfun_compose_add_right)
      moreover have \<open>Q o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<xi>) = 0\<close> for \<xi>
        apply (auto intro!: equal_ket simp: Q_def Proj_ortho_compl cblinfun.diff_left)
        apply (subst Proj_fixes_image)
        by (auto intro!: ccspan_superset[THEN set_mp])
      ultimately have \<open>Q = 0\<close>
        apply (rule_tac has_sum_in_unique)
        by auto
      then show ?thesis
        apply (auto simp: Q_def)
        by (smt (verit, del_insts) Proj_ortho_compl Proj_range cblinfun_image_id right_minus_eq)
    qed
    ultimately have \<open>U *\<^sub>S \<top> = \<top>\<close>
      by (simp add: top.extremum_unique)
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (rule surj_isometry_is_unitary)
  qed

  have \<open>\<Phi> \<theta> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close> for \<theta>
  proof -
    from \<open>unitary U\<close>
    have \<open>\<Phi> \<theta> = (U o\<^sub>C\<^sub>L U*) o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L U*)\<close>
      by simp
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (U*  o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L U*\<close>
      by (simp add: cblinfun_assoc_left)
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close>
      using 1 by simp
    finally show ?thesis
      by -
  qed

  with \<open>unitary U\<close> show \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. \<Phi> \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: sandwich_def)
qed

lemma register_decomposition_converse: 
  assumes \<open>unitary U\<close>
  shows \<open>register (\<lambda>x. sandwich U (id_cblinfun \<otimes>\<^sub>o x))\<close>
  using _ unitary_sandwich_register apply (rule register_comp[unfolded o_def])
  using assms by auto

lemma register_inj: \<open>inj F\<close> if [simp]: \<open>register F\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F. inj F\<close>
    using register_decomposition[OF \<open>register F\<close>] 
  proof (rule with_type_mp)
    fix rep :: \<open>'c \<Rightarrow> 'd\<close> and abs and S
    assume \<open>type_definition rep abs S\<close>
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>unitary U\<close> and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
      apply atomize_elim by auto
    have \<open>inj (sandwich U)\<close>
      by (smt (verit, best) \<open>unitary U\<close> cblinfun_assoc_left inj_onI sandwich_def cblinfun_compose_id_right cblinfun_compose_id_left unitary_def)
    moreover have \<open>inj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (rule inj_tensor_left, simp)
    ultimately show \<open>inj F\<close>
      unfolding F
      by (smt (z3) inj_def)
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show \<open>inj F\<close>
    by -
qed


lemma weak_star_clinear_eq_butterfly_ketI:
  fixes F G :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
    and \<open>continuous_map weak_star_topology T F\<close> and \<open>continuous_map weak_star_topology T G\<close>
    and \<open>hausdorff T\<close>
  assumes "\<And>i j. F (butterfly (ket i) (ket j)) = G (butterfly (ket i) (ket j))"
  shows "F = G"
proof -
  have FG: \<open>F x = G x\<close> if \<open>x \<in> cspan {butterket i j |i j. True}\<close> for x
    by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(6) complex_vector.linear_eq_on mem_Collect_eq that)
  show ?thesis
    apply (rule ext)
    using \<open>hausdorff T\<close> FG
    apply (rule closure_of_eqI[where f=F and g=G and S=\<open>cspan {butterket i j| i j. True}\<close>])
    using assms butterkets_weak_star_dense by auto
qed

lemma clinear_register: \<open>register F \<Longrightarrow> clinear F\<close>
  using bounded_clinear.clinear register_bounded_clinear by blast

lemma weak_star_cont_register: \<open>register F \<Longrightarrow> continuous_map weak_star_topology weak_star_topology F\<close>
  using register_def by blast

lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  from register_decomposition
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
        \<exists>U. unitary U \<and> F = sandwich U\<close>
  proof (rule with_type_mp)
    show [simp]: \<open>register F\<close>
      using assms iso_register_is_register by blast 

    assume register_decomposition:
      \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>

    let ?ida = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

    from register_decomposition
    obtain V :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
      and FV: \<open>F \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o ?ida)\<close> for \<theta>
      by auto

    have \<open>surj F\<close>
      by (meson assms iso_register_inv_comp2 surj_iff)
    have surj_tensor: \<open>surj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. a \<otimes>\<^sub>o ?ida)\<close>
      apply (rule surj_from_comp[where g=\<open>sandwich V\<close>])
      using \<open>surj F\<close> apply (auto simp: FV)
      by (meson \<open>unitary V\<close> register_inj unitary_sandwich_register)
    then obtain a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close> 
      where a: \<open>a \<otimes>\<^sub>o ?ida = selfbutterket undefined \<otimes>\<^sub>o selfbutterket undefined\<close>
      by (smt (verit, best) surjD)

    then have \<open>a \<noteq> 0\<close>
      apply (auto simp: tensor_ell2_ket)
      by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_nonzero orthogonal_ket)

    obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C selfbutterket undefined\<close>
      apply atomize_elim
      using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
    then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (selfbutterket undefined *\<^sub>V ket undefined)\<close>
      by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C selfbutterket undefined\<close> scaleC_cblinfun.rep_eq)
    then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
      by (metis butterfly_apply cinner_ket_same id_cblinfun_apply ket_nonzero scaleC_cancel_right scaleC_one)
    then have \<open>\<gamma> = 1\<close>
      by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero)

    define T U where \<open>T = CBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
    have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
      unfolding T_def
      apply (subst bounded_clinear_CBlinfun_apply)
      by (auto intro!: bounded_clinear_tensor_ell22)
    have \<open>sandwich T (butterket i j) = butterket i j \<otimes>\<^sub>o id_cblinfun\<close> for i j
      by (simp add: T sandwich_def cblinfun_comp_butterfly butterfly_comp_cblinfun \<gamma> \<open>\<gamma> = 1\<close>)
    then have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by auto

    have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: Misc.sandwich_def FV)
    also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: T \<gamma> \<open>\<gamma> = 1\<close>)
    also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
      by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
    finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by (auto simp: clinear_register weak_star_cont_register simp flip: sandwich_def)

    have \<open>isometry T\<close>
      apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
      by (auto simp: T)
    moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
    proof -
      have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
      proof -
        have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
          by (simp add: T tensor_ell2_scaleC1 tensor_ell2_scaleC2)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (selfbutterket undefined *\<^sub>V \<xi>)\<close>
          by simp
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (?ida *\<^sub>V \<xi>)\<close>
          by (simp add: \<gamma> \<open>\<gamma> = 1\<close>)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<xi>\<close>
          by simp
        finally show ?thesis
          by (metis range_eqI)
      qed

      have \<open>\<top> \<le> ccspan {ket x | x. True}\<close>
        by (simp add: full_SetCompr_eq)
      also have \<open>\<dots> \<le> ccspan {\<phi> \<otimes>\<^sub>s \<xi> | \<phi> \<xi>. True}\<close>
        apply (rule ccspan_mono)
        by (auto simp flip: tensor_ell2_ket)
      also from 1 have \<open>\<dots> \<le> ccspan (range ((*\<^sub>V) T))\<close>
        by (auto intro!: ccspan_mono)
      also have \<open>\<dots> = T *\<^sub>S \<top>\<close>
        by (metis (mono_tags, opaque_lifting) calculation cblinfun_image_ccspan cblinfun_image_mono eq_iff top_greatest)
      finally show \<open>T *\<^sub>S \<top> = \<top>\<close>
        using top.extremum_uniqueI by blast
    qed

    ultimately have \<open>unitary T\<close>
      by (rule surj_isometry_is_unitary)
    then have \<open>unitary U\<close>
      by (simp add: U_def \<open>unitary V\<close>)

    from F_rep \<open>unitary U\<close> show \<open>\<exists>U. unitary U \<and> F = Misc.sandwich U\<close>
      by (auto simp: sandwich_def[abs_def])
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show ?thesis
    by -
qed

lemma complement_exists:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         \<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof (use register_decomposition[OF \<open>register F\<close>] in \<open>rule with_type_mp\<close>)
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  assume register_decomposition: \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
  then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    by auto
  define G :: \<open>'c update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      apply (auto simp: register_pair_apply F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: unitary_sandwich_register)
    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have \<open>I o (F;G) = id\<close> and FGI: \<open>(F;G) o I = id\<close>
       apply (auto intro!:ext simp: I_def[abs_def] FG sandwich_def)
       apply (metis (no_types, opaque_lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
      by (metis (no_types, lifting) \<open>unitary U\<close> cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD2)
    then show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show \<open>\<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    apply (rule_tac exI[of _ G]) by auto
qed

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

(* TODO move *)
lemma norm_isometry_o: \<open>norm (U o\<^sub>C\<^sub>L A) = norm A\<close> if \<open>isometry U\<close>
  by (smt (verit, del_insts) cblinfun_compose_id_left compatible_ac_rules(2) isometryD isometry_partial_isometry mult_cancel_left2 mult_cancel_right1 norm_adj norm_cblinfun_compose norm_eq_zero norm_le_zero_iff norm_partial_isometry that)

(* TODO move *)
lemma norm_isometry_o': \<open>norm (A o\<^sub>C\<^sub>L U) = norm A\<close> if \<open>isometry (U*)\<close>
  by (smt (verit, ccfv_threshold) adj_0 cblinfun_assoc_right(1) cblinfun_compose_id_right cblinfun_compose_zero_right double_adj isometryD isometry_partial_isometry mult_cancel_left2 norm_adj norm_cblinfun_compose norm_partial_isometry norm_zero that)

lemma register_norm: \<open>norm (F a) = norm a\<close> if \<open>register F\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
    (* using complement_exists that by blast *)
    using register_decomposition that by blast
  then have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         norm (F a) = norm a\<close>
  proof (rule with_type_mp) 
    fix Rep :: \<open>'c \<Rightarrow> 'b ell2\<close> and Abs
    assume \<open>type_definition Rep Abs (register_decomposition_basis F)\<close>
    assume \<open>(\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary U\<close>
      and FU: \<open>F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by metis
    show \<open>norm (F a) = norm a\<close>
      using \<open>unitary U\<close> by (simp add: FU sandwich_def norm_isometry_o norm_isometry_o' tensor_op_norm)
  qed
  (* note this[cancel_with_type] *)
  then show ?thesis
    sorry
qed

lemma commutant_exchange:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>iso_register F\<close>
  shows \<open>commutant (F ` X) = F ` commutant X\<close>
proof (rule Set.set_eqI)
  fix x :: \<open>'b update\<close>
  from assms
  obtain G where \<open>F o G = id\<close> and \<open>G o F = id\<close> and [simp]: \<open>register G\<close>
    using iso_register_def by blast
  from assms have [simp]: \<open>register F\<close>
    using iso_register_def by blast
  have \<open>x \<in> commutant (F ` X) \<longleftrightarrow> (\<forall>y \<in> F ` X. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> F ` X. G x o\<^sub>C\<^sub>L G y = G y o\<^sub>C\<^sub>L G x)\<close>
    by (metis (no_types, opaque_lifting) \<open>F \<circ> G = id\<close> \<open>G o F = id\<close> \<open>register G\<close> comp_def eq_id_iff register_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> X. G x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L G x)\<close>
    by (simp add: \<open>G \<circ> F = id\<close> pointfree_idE)
  also have \<open>\<dots> \<longleftrightarrow> G x \<in> commutant X\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by (metis (no_types, opaque_lifting) \<open>G \<circ> F = id\<close> \<open>F \<circ> G = id\<close> image_iff pointfree_idE)
  finally show \<open>x \<in> commutant (F ` X) \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by -
qed

lemma commutant_tensor1: \<open>commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)) = range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  fix \<gamma> :: 'a
  assume \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
  then have comm: \<open>(a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V \<psi> = x *\<^sub>V (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>\<close> for a \<psi>
    by (metis (mono_tags, lifting) commutant_def mem_Collect_eq rangeI cblinfun_apply_cblinfun_compose)

  define op where \<open>op = classical_operator (\<lambda>i. Some (\<gamma>,i::'b))\<close>
  have [simp]: \<open>classical_operator_exists (\<lambda>i. Some (\<gamma>,i))\<close>
    apply (rule classical_operator_exists_inj)
    using inj_map_def by blast
  define x' where \<open>x' = op* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L op\<close>
  have x': \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close> for j l
    by (simp add: x'_def op_def classical_operator_ket cinner_adj_right)

  have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l)) = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close> for i j k l
  proof -
    have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l))
        = cinner ((butterket i \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      unfolding comm by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close>
      by (simp add: comp_tensor_op tensor_op_ket tensor_op_scaleC_left cinner_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket j) (x' *\<^sub>V ket l)\<close>
      by (simp add: x')
    also have \<open>\<dots> = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close>
      apply (simp add: tensor_op_ket)
      by (simp flip: tensor_ell2_ket)
    finally show ?thesis by -
  qed
  then have \<open>x = (id_cblinfun \<otimes>\<^sub>o x')\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then show \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by auto
next
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  assume \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
  then obtain b where x: \<open>x = id_cblinfun \<otimes>\<^sub>o b\<close>
    by auto
  then show \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: x commutant_def comp_tensor_op)
qed

lemma complement_range:
  assumes [simp]: \<open>compatible F G\<close> and [simp]: \<open>iso_register (F;G)\<close>
  shows \<open>range G = commutant (range F)\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms compatible_def by metis+
  have [simp]: \<open>(F;G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
    using Laws_Quantum.register_pair_apply assms by blast
  have [simp]: \<open>range F = (F;G) ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  have [simp]: \<open>range G = (F;G) ` range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by force
  show \<open>range G = commutant (range F)\<close>
    by (simp add: commutant_exchange commutant_tensor1)
qed

(* lemma TMP: \<open>isCont f a \<longleftrightarrow> filterlim f (nhds a) (nhds (f a))\<close>
  apply rule
  defer
  by - *)

(* definition Collect_in where \<open>Collect_in S P = {x\<in>S. P x}\<close> for S and P

lemma Collect_in_parametric[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set R ===> (R ===> (\<longleftrightarrow>)) ===> rel_set R) Collect_in Collect_in\<close>
  apply (auto intro!: simp: rel_fun_def rel_set_def Collect_in_def)
  by blast+

term Set.filter *)

definition \<open>opensets = Collect open\<close>
  \<comment> \<open>This behaves more nicely with the @{method transfer}-method (and friends) than \<^const>\<open>open\<close>.
      So when rewriting a subgoal, using, e.g., \<^term>\<open>\<exists>U\<in>opensets. xxx\<close> instead of \<^term>\<open>\<exists>U. open U \<longrightarrow> xxx\<close> can make @{method transfer} work better. \<close>

lemma opensets_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>(rel_set R ===> (\<longleftrightarrow>)) open open\<close>
  shows \<open>(rel_set (rel_set R)) opensets opensets\<close>
  using assms apply (simp add: opensets_def rel_set_def )
  apply auto
sorry


(* TODO move *)
(* TODO reprove concrete nhds transfer rules with this (or drop them?) *)
lemma nhds_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>(rel_set R ===> (\<longleftrightarrow>)) open open\<close>
  shows \<open>(R ===> rel_filter R) nhds nhds\<close>
(* proof -
  have \<open>(R ===> rel_filter R) (\<lambda>a. \<Sqinter> (principal ` Set.filter ((\<in>) a) opensets)) (\<lambda>a. \<Sqinter> (principal ` Set.filter ((\<in>) a) opensets))\<close>
  show ?thesis
    unfolding nhds_def
    apply transfer_prover_start


         apply transfer_step
  apply transfer_step
      apply transfer_step
  apply transfer_step
  apply transfer_step
     apply (rule RelI)

     apply transfer_step



  term nhds *)
  sorry

lemma at_within_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>(rel_set R ===> (\<longleftrightarrow>)) open open\<close>
  shows \<open>(R ===> rel_set R ===> rel_filter R) at_within at_within\<close>
  unfolding at_within_def
  apply transfer_prover_start
  apply transfer_step
  apply transfer_step
      apply transfer_step
  apply transfer_step
  apply transfer_step


    apply transfer_step
  apply transfer_step

  
  sorry


  term at_within



lemma transfer_nhds_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_weak_star ===> rel_set cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star) (at_within_in weak_star_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: weak_star_topology_topspace)
  by transfer_prover


lemma same_range_equivalent:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G :: \<open>'b update \<Rightarrow> 'c update\<close>
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes \<open>range F = range G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  have G_rangeF[simp]: \<open>G x \<in> range F\<close> for x
    by (simp add: assms)
  have F_rangeG[simp]: \<open>F x \<in> range G\<close> for x
    by (simp add: assms(3)[symmetric])
  have [simp]: \<open>inj F\<close> and [simp]: \<open>inj G\<close>
    by (simp_all add: register_inj)
  have [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
    by (simp_all add: register_bounded_clinear)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    by (simp_all add: bounded_clinear.clinear)
  define I J where \<open>I x = inv F (G x)\<close> and \<open>J y = inv G (F y)\<close> for x y
  have addI: \<open>I (x + y) = I x + I y\<close> for x y
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_add)
  have addJ: \<open>J (x + y) = J x + J y\<close> for x y
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_add)
  have scaleI: \<open>I (r *\<^sub>C x) = r *\<^sub>C I x\<close> for r x
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_scale)
  have scaleJ: \<open>J (r *\<^sub>C x) = r *\<^sub>C J x\<close> for r x
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_scale)
  have unitalI: \<open>I id_cblinfun = id_cblinfun\<close>
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F])
     apply auto
    by (metis register_of_id G_rangeF assms(2))
  have unitalJ: \<open>J id_cblinfun = id_cblinfun\<close>
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G])
     apply auto
    by (metis register_of_id F_rangeG assms(1))
  have multI: \<open>I (a o\<^sub>C\<^sub>L b) = I a o\<^sub>C\<^sub>L I b\<close> for a b
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_mult[symmetric, OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: register_mult)
  have multJ: \<open>J (a o\<^sub>C\<^sub>L b) = J a o\<^sub>C\<^sub>L J b\<close> for a b
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_mult[symmetric, OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: register_mult)
  have adjI: \<open>I (a*) = (I a)*\<close> for a
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_adjoint[OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    using assms(2) register_adjoint by blast
  have adjJ: \<open>J (a*) = (J a)*\<close> for a
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_adjoint[OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    using assms(1) register_adjoint by blast
  have normI: \<open>norm (I a) = norm a\<close> for a
    unfolding I_def
    by (metis G_rangeF assms(1) assms(2) f_inv_into_f register_norm)
  have normJ: \<open>norm (J a) = norm a\<close> for a
    unfolding J_def
    by (metis F_rangeG assms(1) assms(2) f_inv_into_f register_norm)
  have weak_star_I: \<open>continuous_map weak_star_topology weak_star_topology I\<close>
  proof -
    include lifting_syntax
    define I' where \<open>I' = to_weak_star o I o from_weak_star\<close>
    have [transfer_rule]: \<open>(cr_cblinfun_weak_star ===> cr_cblinfun_weak_star) I I'\<close>
      by (metis (no_types, lifting) I'_def UNIV_I cr_cblinfun_weak_star_def o_def rel_funI to_weak_star_inverse)
    have \<open>I' \<midarrow>a\<rightarrow> I' a\<close> for a
      apply (transfer)
      sorry

      sorry
    then have \<open>isCont I' a\<close> for a
      by (simp add: continuous_within)
    then have \<open>continuous_on UNIV I'\<close>
      using continuous_at_imp_continuous_on by blast
    then have \<open>continuous_map euclidean euclidean I'\<close>
      using continuous_map_iff_continuous2 by blast
    then show ?thesis
      by transfer
  qed
  have weak_star_J: \<open>continuous_map weak_star_topology weak_star_topology J\<close>
    sorry

  from addI scaleI unitalI multI adjI normI weak_star_I
  have \<open>register I\<close>
    unfolding register_def by (auto intro!: bounded_clinearI[where K=1])
  from addJ scaleJ unitalJ multJ adjJ normJ weak_star_J
  have \<open>register J\<close>
    unfolding register_def by (auto intro!: bounded_clinearI[where K=1])

  have \<open>I o J = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj F\<close>])
    by auto
  have \<open>J o I = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj G\<close>])
    by auto

  from \<open>I o J = id\<close> \<open>J o I = id\<close> \<open>register I\<close> \<open>register J\<close>
  have \<open>iso_register I\<close>
    using iso_register_def by blast

  have \<open>F o I = G\<close>
    unfolding I_def o_def
    by (subst Hilbert_Choice.f_inv_into_f[where f=F], auto)

  with \<open>iso_register I\<close> show ?thesis
    unfolding equivalent_registers_def by auto
qed

lemma complement_unique:
  assumes "compatible F G" and \<open>iso_register (F;G)\<close>
  assumes "compatible F H" and \<open>iso_register (F;H)\<close>
  shows \<open>equivalent_registers G H\<close>
  by (metis assms compatible_def complement_range same_range_equivalent)

end
