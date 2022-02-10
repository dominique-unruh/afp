section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum Tensor_Product.With_Type Quantum_Extra Tensor_Product.Weak_Star_Topology
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")

(* typedef ('a::finite,'b::finite) complement_domain = \<open>{..< if CARD('b) div CARD('a) \<noteq> 0 then CARD('b) div CARD('a) else 1}\<close>
  by auto

instance complement_domain :: (finite, finite) finite
proof intro_classes
  have \<open>inj Rep_complement_domain\<close>
    by (simp add: Rep_complement_domain_inject inj_on_def)
  moreover have \<open>finite (range Rep_complement_domain)\<close>
    by (metis finite_lessThan type_definition.Rep_range type_definition_complement_domain)
  ultimately show \<open>finite (UNIV :: ('a,'b) complement_domain set)\<close>
    using finite_image_iff by blast
qed

lemma CARD_complement_domain: 
  assumes \<open>CARD('b::finite) = n * CARD('a::finite)\<close>
  shows \<open>CARD(('a,'b) complement_domain) = n\<close>
proof -
  from assms have \<open>n > 0\<close>
    by (metis zero_less_card_finite zero_less_mult_pos2)
  have *: \<open>inj Rep_complement_domain\<close>
    by (simp add: Rep_complement_domain_inject inj_on_def)
  moreover have \<open>card (range (Rep_complement_domain :: ('a,'b) complement_domain \<Rightarrow> _)) = n\<close>
    apply (subst type_definition.Rep_range[OF type_definition_complement_domain])
    using assms \<open>n > 0\<close> by simp
  ultimately show ?thesis
    by (metis card_image)
qed *)

(* lemma transfer_subset[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>(rel_set R ===> rel_set R ===> (\<longleftrightarrow>)) (\<subseteq>) (\<subseteq>)\<close>
  using assms apply (auto simp: rel_fun_def rel_set_def bi_unique_def)
  by (metis in_mono)+ *)

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

lemma finite_subsets_at_top_parametric[transfer_rule]:
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
qed

lemma sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> rel_set R ===> cr_cblinfun_weak_star) sum sum\<close>
proof (intro rel_funI, rename_tac f g A B)
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
qed

definition \<open>has_sum_in T f A x \<longleftrightarrow> limitin T (sum f) x (finite_subsets_at_top A)\<close>

lemma has_sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star ===> (\<longleftrightarrow>)) (has_sum_in weak_star_topology) has_sum\<close>
  unfolding has_sum_def has_sum_in_def
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: filterlim_weak_star_topology)

definition \<open>summable_on_in T f A \<longleftrightarrow> (\<exists>x. has_sum_in T f A x)\<close>

lemma summable_on_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> (\<longleftrightarrow>)) (summable_on_in weak_star_topology) Infinite_Sum.summable_on\<close>
  unfolding summable_on_def summable_on_in_def
  by transfer_prover

definition \<open>infsum_in T f A = (if summable_on_in T f A then (THE l. has_sum_in T f A l) else 0)\<close>

lemma has_sum_in_infsum_in: \<open>summable_on_in T f A \<Longrightarrow> has_sum_in T f A (infsum_in F f A)\<close>
  sorry

lemma infsum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star) (infsum_in weak_star_topology) infsum\<close>
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
      by (simp add: infsum_def False infsum_in_def zero_cblinfun_weak_star.transfer)
  qed
qed


(* ML Thm.rule_attribute
attribute_setup forget_lifting = \<open>Scan.lift Args.name >> (fn name => Thm.declaration_attribute (fn _ => 
  Context.map_proof (fn ctxt => Lifting_Setup.lifting_forget name ctxt)))\<close> *)

definition \<open>register_decomposition_basis \<Phi> = (SOME B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = \<Phi> (selfbutterket undefined) *\<^sub>S \<top>)\<close> 
  for \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>

(* attribute_setup filtered = \<open>Args.context -- Scan.lift Parse.term >> (fn (ctxt,t) => let
  val no_thm = @{lemma True by simp}
  (* From Find_Theorems *)
  fun matches_subterm ctxt (pat, obj) =
    let
      val thy = Proof_Context.theory_of ctxt;
      fun matches obj ctxt' = Pattern.matches thy (pat, obj) orelse
        (case obj of
          Abs (_, T, t) =>
            let val ((_, t'), ctxt'') = Variable.dest_abs obj ctxt'
            in matches t' ctxt'' end
        | t $ u => matches t ctxt' orelse matches u ctxt'
        | _ => false);
    in matches obj ctxt end;
  val pat = Proof_Context.read_term_pattern ctxt t
  fun filter context thm = let
    val ctxt = Context.proof_of context
    val match = matches_subterm ctxt (pat, Thm.prop_of thm)
    val result = if match then thm else no_thm
    in result end
  in
    Thm.rule_attribute [] filter end)\<close> *)

lemma bounded_clinear_cblinfun_compose_left: \<open>bounded_clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose)
lemma bounded_clinear_cblinfun_compose_right: \<open>bounded_clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose)
lemma clinear_cblinfun_compose_left: \<open>clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose bounded_clinear.clinear)
lemma clinear_cblinfun_compose_right: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_clinear.clinear bounded_clinear_cblinfun_compose_right)

definition hausdorff where \<open>hausdorff T \<longleftrightarrow> (\<forall>x \<in> topspace T. \<forall>y \<in> topspace T. x \<noteq> y \<longrightarrow> (\<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>

lemma hausdorff_weak_star[simp]: \<open>hausdorff weak_star_topology\<close>
  sorry

lemma closure_of_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::t2_space\<close> and T :: \<open>'a topology\<close> and U :: \<open>'b topology\<close>
  assumes haus: \<open>hausdorff T\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes xS: \<open>x \<in> T closure_of S\<close>
  assumes cont: \<open>continuous_map T U f\<close> \<open>continuous_map T U g\<close>
  shows \<open>f x = g x\<close>
    (* Like on_closure_eqI *)
  sorry

lemma limitin_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>F \<noteq> \<bottom>\<close>
  assumes \<open>limitin T f l F\<close>
  assumes \<open>limitin T f l' F\<close>
  shows \<open>l = l'\<close>
  sorry

lemma has_sum_in_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>has_sum_in T f A l'\<close>
  shows \<open>l = l'\<close>
  using assms(1) _ assms(2,3)[unfolded has_sum_in_def] 
  apply (rule limitin_unique)
  by simp


lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
  sorry (* By transferring orthonormal_basis_exists? *)

lemma orthogonal_projectors_orthogonal_spaces:
  fixes S T :: \<open>'a::chilbert_space set\<close>
  shows \<open>(\<forall>x\<in>S. \<forall>y\<in>T. is_orthogonal x y) \<longleftrightarrow> Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close>
proof (intro ballI iffI)
  fix x y assume \<open>Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close> \<open>x \<in> S\<close> \<open>y \<in> T\<close>
  then show \<open>is_orthogonal x y\<close>
    by (smt (verit, del_insts) Proj_idempotent Proj_range adj_Proj cblinfun.zero_left cblinfun_apply_cblinfun_compose cblinfun_fixes_range ccspan_superset cinner_adj_right cinner_zero_right in_mono)
next 
  assume \<open>\<forall>x\<in>S. \<forall>y\<in>T. is_orthogonal x y\<close>
  then show \<open>Proj (ccspan S) o\<^sub>C\<^sub>L Proj (ccspan T) = 0\<close>
    sorry
qed

(* TODO move *)
lemma cblinfun_image_bot_zero[simp]: \<open>A *\<^sub>S \<top> = \<bottom> \<longleftrightarrow> A = 0\<close>
proof (rule iffI, rule ccontr)
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
qed simp

(* lemma register_inj:
  assumes \<open>register F\<close>
  shows \<open>inj F\<close>
(* TODO: is there a proof that does not use register_decomposition? *)
  by - *)

(* TODO move *)
lemma closed_space_as_set[simp]: \<open>closed (space_as_set S)\<close>
  apply transfer by (simp add: closed_csubspace.closed)

(* TODO move *)
lemma Proj_fixes_image: \<open>Proj S *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set S\<close>
  by (simp add: Proj.rep_eq closed_csubspace_def projection_fixes_image that)

(* TODO move *)
lemma has_sum_in_comm_additive:
  fixes f :: \<open>'a \<Rightarrow> 'b :: comm_monoid_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: comm_monoid_add\<close>
  assumes \<open>continuous_map T U g\<close>
  assumes \<open>\<And>x y. g (x+y) = g x + g y\<close>
  assumes \<open>has_sum_in T f A l\<close>
  shows \<open>has_sum_in U (g o f) A (g l)\<close>
  sorry

(* TODO move *)
lemma has_sum_in_0[simp]: \<open>has_sum_in weak_star_topology (\<lambda>_. 0) A 0\<close>
  sorry

(* TODO move *)
lemma trace_butterfly_comp': \<open>trace (a o\<^sub>C\<^sub>L butterfly x y) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
  by (simp add: cblinfun_comp_butterfly trace_butterfly)

(* TODO move *)
lemma has_sum_in_weak_star:
  \<open>has_sum_in weak_star_topology f A l \<longleftrightarrow> 
     (\<forall>t. trace_class t \<longrightarrow> has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) A (trace (t o\<^sub>C\<^sub>L l)))\<close>
  apply (simp add: has_sum_def has_sum_in_def limitin_weak_star_topology)
  sorry

lemma trace_has_sum:
  assumes \<open>is_onb E\<close>
  assumes \<open>trace_class t\<close>
  shows \<open>has_sum (\<lambda>e. e \<bullet>\<^sub>C (t *\<^sub>V e)) E (trace t)\<close>
  sorry

(* TODO move *)
lemma infsum_butterfly_ket: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (ket i) (ket i)) UNIV id_cblinfun\<close>
proof (rule has_sum_in_weak_star[THEN iffD2, rule_format])
  fix t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume [simp]: \<open>trace_class t\<close>
  from trace_has_sum[OF is_onb_ket \<open>trace_class t\<close>]
  have \<open>has_sum (\<lambda>i. ket i \<bullet>\<^sub>C (t *\<^sub>V ket i)) UNIV (trace t)\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def)
  then show \<open>has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L selfbutterket i)) UNIV (trace (t o\<^sub>C\<^sub>L id_cblinfun))\<close>
    by (simp add: trace_butterfly_comp')
qed

lemma butterkets_weak_star_dense:
  \<open>weak_star_topology closure_of cspan {butterket \<xi> \<eta> |\<xi> \<eta>. True} = UNIV\<close>
  sorry

(* TODO move *)
lemma amplification_weak_star_cont:
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
(* TODO: How is this proven? *)
  sorry

lemma register_decomposition:
  fixes \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c = register_decomposition_basis \<Phi>.
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
  \<comment> \<open>Proof based on @{cite daws21unitalanswer}\<close>
proof (rule with_typeI)
  note [[simproc del: compatibility_warn]]
  define \<xi>0 :: 'a where \<open>\<xi>0 = undefined\<close>

(*   define \<Phi>' where \<open>\<Phi>' = to_weak_star o \<Phi> o from_weak_star\<close>
  have [transfer_rule]: \<open>(rel_fun cr_cblinfun_weak_star cr_cblinfun_weak_star) \<Phi> \<Phi>'\<close>
    unfolding \<Phi>'_def
    apply transfer_prover_start
         apply transfer_step+
    by simp
  have cont_\<Phi>': \<open>continuous_on UNIV \<Phi>'\<close>
    unfolding continuous_map_iff_continuous2[symmetric]
    apply transfer
    using assms register_def by blast *)

  have [simp]: \<open>bounded_clinear \<Phi>\<close> (* TODO needed? *)
    using assms register_def by blast
  have [simp]: \<open>clinear \<Phi>\<close>
    by (simp add: bounded_clinear.clinear)

  define P where \<open>P i = selfbutterket i\<close> for i :: 'a

  (* note [[forget_lifting "Complex_Bounded_Linear_Function0.cblinfun.lifting"]] *)
  note blinfun_cblinfun_eq_bi_unique[transfer_rule del]
  note cblinfun.bi_unique[transfer_rule del]
  note cblinfun.left_unique[transfer_rule del]
  note cblinfun.right_unique[transfer_rule del]
  note cblinfun.right_total[transfer_rule del]
  note id_cblinfun.transfer[transfer_rule del]
  (* note transfer_raw[filtered pcr_cblinfun, transfer_rule del] *)

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>is_Proj (P' i)\<close> for i
    by (simp add: P_def P'_def butterfly_is_Proj register_projector)
(*   have sumP'id: \<open>has_sum (\<lambda>i. to_weak_star (P' i)) UNIV id_weak_star\<close> (* TODO: alternatively, we could formulate this with has_sum_in *)
  proof -
    have *: \<open>has_sum (\<lambda>i. to_weak_star (P i)) UNIV id_weak_star\<close>
      unfolding P_def sorry (* TODO: need thm for that *)
    have \<open>has_sum (\<lambda>i. to_weak_star (P' i)) UNIV (to_weak_star (\<Phi> id_cblinfun))\<close>
    proof (insert *, unfold P'_def, transfer fixing: \<Phi> P)
      assume \<open>has_sum_in weak_star_topology P UNIV id_cblinfun\<close>
      then have \<open>limitin weak_star_topology (sum P) id_cblinfun (finite_subsets_at_top UNIV)\<close>
        using has_sum_in_def by blast
      then have \<open>limitin weak_star_topology (\<Phi> o sum P) id_cblinfun (finite_subsets_at_top UNIV)\<close>
        by (metis (no_types, lifting) assms continuous_map_limit register_def)
      then have \<open>limitin weak_star_topology (\<lambda>F. (\<Sum>i\<in>F. \<Phi> (P i))) id_cblinfun (finite_subsets_at_top UNIV)\<close>
        apply (rule limitin_transform_eventually[rotated])
        apply (rule eventually_finite_subsets_at_top_weakI)
        by (simp add: complex_vector.linear_sum)
      then show \<open>has_sum_in weak_star_topology (\<lambda>i. \<Phi> (P i)) UNIV (\<Phi> id_cblinfun)\<close>
        by (simp add: has_sum_in_def)
    qed
    also have \<open>to_weak_star (\<Phi> id_cblinfun) = to_weak_star id_cblinfun\<close>
      by simp
    also have \<open>\<dots> = id_weak_star\<close>
      apply transfer by simp
    finally show ?thesis
      by -
  qed *)
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
(*   have B\<^sub>0_nonempty: \<open>B\<^sub>0 \<noteq> {}\<close>
  proof -
    have \<open>P \<xi>0 \<noteq> 0\<close>
      by (metis P_def class_field.zero_not_one divisors_zero norm_butterfly norm_eq_zero norm_ket)
    then have \<open>P' \<xi>0 \<noteq> 0\<close>
      unfolding P'_def using register_inj[OF \<open>register \<Phi>\<close>]
      using \<open>clinear \<Phi>\<close> complex_vector.linear_inj_iff_eq_0 by blast
    then have \<open>S \<xi>0 \<noteq> 0\<close>
      by (simp add: S_def)
    then show \<open>B\<^sub>0 \<noteq> {}\<close>
      using \<open>ccspan B\<^sub>0 = S \<xi>0\<close>[symmetric]
      by auto
  qed *)

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
      by (meson orthogonal_projectors_orthogonal_spaces that(1) that(2))
  qed

  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>

  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding cspanB S_def
    using proj_P' Proj_on_own_range'[symmetric] is_Proj_algebraic by blast

(*   have \<open>(\<Sum>i\<in>UNIV. P' i) = Proj (ccspan B')\<close> (* TODO used? *)
(* TODO: w.r.t weak* (?) *)
(* TODO: needs new proof *)
    by - *)

(*   proof (unfold B'_def, use finite[of UNIV] in induction)
    case empty
    show ?case by auto
  next
    case (insert j M)
    have \<open>(\<Sum>i\<in>insert j M. P' i) = P' j + (\<Sum>i\<in>M. P' i)\<close>
      by (meson insert.hyps(1) insert.hyps(2) sum.insert)
    also have \<open>\<dots> = Proj (ccspan (B j)) + Proj (ccspan (\<Union>i\<in>M. B i))\<close>
      unfolding P'B insert.IH[symmetric] by simp
    also have \<open>\<dots> = Proj (ccspan (B j \<union> (\<Union>i\<in>M. B i)))\<close>
      apply (rule Proj_orthog_ccspan_union[symmetric])
      using orthoBiBj insert.hyps(2) by auto
    also have \<open>\<dots> = Proj (ccspan (\<Union>i\<in>insert j M. B i))\<close>
      by auto
    finally show ?case
      by simp
  qed *)

(*   with sumP'id 
  have ccspanB': \<open>ccspan B' = \<top>\<close>  (* TODO used? *)
(* TODO possibly drop sumP'id and prove this one directly? Or new proof. *)
    by (metis Proj_range cblinfun_image_id) x *)

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
    have \<open>id_cblinfun = 0\<close>
      apply simp
      using has_sum_in_0 has_sum_in_unique hausdorff_weak_star id_cblinfun_not_0 by blast
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
        by (simp add: tensor_ell2_scaleC1)
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
  have \<open>\<forall>\<^sub>\<tau> 'c = register_decomposition_basis F. inj F\<close>
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

lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  have [simp]: \<open>register F\<close>
    using assms iso_register_is_register by blast 

  let ?ida = \<open>id_cblinfun :: ('a, 'b) complement_domain ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

  from register_decomposition[OF \<open>register F\<close>]
  obtain V :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
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
    apply auto
    by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_nonzero orthogonal_ket)x

  obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C selfbutterket undefined\<close>
    apply atomize_elim
    using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
  then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (selfbutterket undefined *\<^sub>V ket undefined)\<close>
    by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C selfbutterket undefined\<close> scaleC_cblinfun.rep_eq)
  then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
    by (metis butterfly_apply cinner_scaleC_right id_cblinfun_apply cinner_ket_same mult.right_neutral scaleC_one)x
  then have \<open>\<gamma> = 1\<close>
    by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero)

  define T U where \<open>T = CBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
  have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
    unfolding T_def
    apply (subst bounded_clinear_CBlinfun_apply)
    by (auto intro!: bounded_clinear_finite_dim clinear_tensor_ell22)
  have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
    apply (rule fun_cong[where x=a])
    apply (rule clinear_eq_butterfly_ketI)
      apply auto
    by (metis (no_types, opaque_lifting) Misc.sandwich_def T \<gamma> \<open>\<gamma> = 1\<close> adj_cblinfun_compose butterfly_adjoint cblinfun_comp_butterfly scaleC_one tensor_butterfly)

  have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: Misc.sandwich_def FV)
  also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: T \<gamma> \<open>\<gamma> = 1\<close>)
  also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
    by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
  finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac clinear_eq_butterfly_ketI)
      apply auto
    by (metis (no_types, lifting) cblinfun_apply_clinear clinear_iff sandwich_apply)

  have \<open>isometry T\<close>
    apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: T)
  moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
  proof -
    have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
    proof -
      have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
        by (simp add: T tensor_ell2_scaleC2)
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

  from F_rep \<open>unitary U\<close> show ?thesis
    by (auto simp: sandwich_def[abs_def])
qed

lemma complement_exists:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<exists>G :: ('a, 'b) complement_domain update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  obtain U :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    apply atomize_elim using assms by (rule register_decomposition)
  define G :: \<open>(('a, 'b) complement_domain) update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
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
    by (auto simp: compatible_def \<open>register F\<close> \<open>register G\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      apply (auto simp: register_pair_apply F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right clinearI)
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
  ultimately show ?thesis
    apply (rule_tac exI[of _ G]) by (auto)
qed

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

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

  obtain x' where x': \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close> for j l
  proof atomize_elim
    obtain \<psi> where \<psi>: \<open>cinner (ket j) (\<psi> l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close> for l j
      apply (atomize_elim, rule choice, rule allI)
      apply (rule_tac x=\<open>Abs_ell2 (\<lambda>j. cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l)))\<close> in exI)
      by (simp add: cinner_ket_left Abs_ell2_inverse)
    obtain x' where \<open>x' *\<^sub>V ket l = \<psi> l\<close> for l
      apply atomize_elim
      apply (rule exI[of _ \<open>cblinfun_extension (range ket) (\<lambda>l. \<psi> (inv ket l))\<close>])
      apply (subst cblinfun_extension_apply)
        apply (rule cblinfun_extension_exists_finite_dim)
      by (auto simp add: inj_ket cindependent_ket)
    with \<psi> have \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close> for j l
      by auto
    then show \<open>\<exists>x'. \<forall>j l. cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close>
      by auto
  qed

  have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l)) = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close> for i j k l
  proof -
    have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l))
        = cinner ((butterket i \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      unfolding comm by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close>
      by (simp add: comp_tensor_op tensor_op_ket tensor_op_scaleC_left)
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

  from addI scaleI unitalI multI adjI
  have \<open>register I\<close>
    unfolding register_def by (auto intro!: clinearI)
  from addJ scaleJ unitalJ multJ adjJ
  have \<open>register J\<close>
    unfolding register_def by (auto intro!: clinearI)

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
