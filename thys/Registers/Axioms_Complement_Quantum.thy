section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum Quantum_Extra Tensor_Product.Weak_Star_Topology
    Tensor_Product.Partial_Trace
    With_Type.With_Type
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")
hide_const (open) Order.top
declare [[eta_contract]]

ctr parametricity in plus_ow_def[unfolded make_parametricity_proof_friendly]
ctr parametricity in neutral_ow_def[unfolded make_parametricity_proof_friendly]
ctr parametricity in zero_ow_def[unfolded make_parametricity_proof_friendly]
ctr parametricity in SML_Semigroups.semigroup_add_ow_def[unfolded SML_Semigroups.semigroup_add_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in SML_Semigroups.ab_semigroup_add_ow_def[unfolded SML_Semigroups.ab_semigroup_add_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in SML_Monoids.comm_monoid_add_ow_def[unfolded SML_Monoids.comm_monoid_add_ow_axioms_def make_parametricity_proof_friendly]

definition \<open>the_default def S = (if card S = 1 then (THE x. x \<in> S) else def)\<close>

lemma \<open>the_default def {x} = x\<close>
  unfolding the_default_def by auto

lemma \<open>the_default def {} = def\<close>
  unfolding the_default_def by auto

lemma the_default_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(T ===> rel_set T ===> T) the_default the_default\<close>
proof (intro rel_funI, rename_tac def def' S S')
  fix def def' assume [transfer_rule]: \<open>T def def'\<close>
  fix S S' assume [transfer_rule]: \<open>rel_set T S S'\<close>
  have card_eq: \<open>card S = card S'\<close>
    by transfer_prover
  show \<open>T (the_default def S) (the_default def' S')\<close>
  proof (cases \<open>card S = 1\<close>)
    case True
    define theS theS' where [no_atp]: \<open>theS = (THE x. x \<in> S)\<close> and [no_atp]: \<open>theS' = (THE x. x \<in> S')\<close>
    from True have cardS': \<open>card S' = 1\<close>
      by (simp add: card_eq)
    from True have \<open>theS \<in> S\<close>
      unfolding theS_def
      apply (rule_tac theI')
      by (simp add: card_eq_Suc_0_ex1)
    moreover from cardS' have \<open>theS' \<in> S'\<close>
      unfolding theS'_def
      apply (rule_tac theI')
      by (simp add: card_eq_Suc_0_ex1)
    ultimately have \<open>T theS theS'\<close>
      using \<open>rel_set T S S'\<close> True cardS'
      apply (auto simp: rel_set_def)
      by (metis card_eq_Suc_0_ex1)
    then show ?thesis
      by (simp add: True cardS' the_default_def theS_def theS'_def)
  next
    case False
    then have cardS': \<open>card S' \<noteq> 1\<close>
      by (simp add: card_eq)
    show ?thesis
      using False cardS' \<open>T def def'\<close>
      by (auto simp add: the_default_def)
  qed
qed

definition \<open>sum_ow z plus f S = 
  (if finite S then the_default z (Collect (fold_graph (plus o f) z S)) else z)\<close>
  for U z plus S

lemma semigroup_ow_typeclass[simp, iff]: \<open>semigroup_ow V (+)\<close>
  if \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: semigroup_add set\<close>
  by (auto simp: semigroup_ow_def Groups.add_ac that)

lemma abel_semigroup_ow_typeclass[simp, iff]: \<open>abel_semigroup_ow V (+)\<close>
  if \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: ab_semigroup_add set\<close>
  by (auto simp: abel_semigroup_ow_def abel_semigroup_ow_axioms_def Groups.add_ac that)

lemma neutral_ow_typeclass[simp, iff]: \<open>neutral_ow V 0\<close> 
  if \<open>0 \<in> V\<close> for V :: \<open>'a::zero set\<close>
  by (auto simp: neutral_ow_def that)

lemma comm_monoid_ow_typeclass[simp, iff]: \<open>comm_monoid_ow V (+) 0\<close> 
  if \<open>0 \<in> V\<close> and \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: comm_monoid_add set\<close>
  by (auto simp: comm_monoid_ow_def comm_monoid_ow_axioms_def that)

ctr parametricity in semigroup_ow_def[unfolded abel_semigroup_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in abel_semigroup_ow_def[unfolded abel_semigroup_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in comm_monoid_ow_def[unfolded comm_monoid_ow_axioms_def make_parametricity_proof_friendly]

definition \<open>rel_pred T P Q = rel_set T (Collect P) (Collect Q)\<close>

(* Exists as comp_fun_commute_on.fold_graph_finite, but the comp_fun_commute_on is not needed. *)
lemma fold_graph_finite:
  assumes "fold_graph f z A y"
  shows "finite A"
  using assms by induct simp_all

lemma fold_graph_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close>
  shows \<open>((T ===> U ===> U) ===> U ===> rel_set T ===> rel_pred U)
          fold_graph fold_graph\<close>
proof (intro rel_funI, rename_tac f f' z z' A A')
  fix f f' assume [transfer_rule, simp]: \<open>(T ===> U ===> U) f f'\<close>
  fix z z' assume [transfer_rule, simp]: \<open>U z z'\<close>
  fix A A' assume [transfer_rule, simp]: \<open>rel_set T A A'\<close>
  have one_direction: \<open>\<exists>y'. fold_graph f' z' A' y' \<and> U y y'\<close> if \<open>fold_graph f z A y\<close> 
    and [transfer_rule]: \<open>U z z'\<close> \<open>(T ===> U ===> U) f f'\<close> \<open>rel_set T A A'\<close> \<open>bi_unique T\<close>
    for f f' z z' A A' y and U :: \<open>'c1 \<Rightarrow> 'd1 \<Rightarrow> bool\<close> and T :: \<open>'a1 \<Rightarrow> 'b1 \<Rightarrow> bool\<close>
    using \<open>fold_graph f z A y\<close>  \<open>rel_set T A A'\<close>
  proof (induction arbitrary: A')
    case emptyI
    then show ?case
      by (metis \<open>U z z'\<close> empty_iff equals0I fold_graph.intros(1) rel_setD2)
  next
    case (insertI x A y)
    from insertI have foldA: \<open>fold_graph f z A y\<close> and T_xA[transfer_rule]: \<open>rel_set T (insert x A) A'\<close> and xA: \<open>x \<notin> A\<close>
      by simp_all
    define DT RT where \<open>DT = Collect (Domainp T)\<close> and \<open>RT = Collect (Rangep T)\<close>
    from T_xA have \<open>x \<in> DT\<close>
      by (metis DT_def Domainp.simps ctr_simps_mem_Collect_eq mem_simps(1) rel_setD1)
    then obtain x' where [transfer_rule]: \<open>T x x'\<close>
      unfolding DT_def by blast
    have \<open>x' \<in> A'\<close>
      apply transfer by simp
    define A'' where \<open>A'' = A' - {x'}\<close>
    then have A'_def: \<open>A' = insert x' A''\<close>
      using \<open>x' \<in> A'\<close> by fastforce
    have \<open>x' \<notin> A''\<close>
      unfolding A''_def by simp
    have [transfer_rule]: \<open>rel_set T A A''\<close>
      apply (subst asm_rl[of \<open>A = (insert x A) - {x}\<close>])
      using insertI.hyps apply blast
      unfolding A''_def
      by transfer_prover
    from insertI.IH[OF this]
    obtain y'' where foldA'': \<open>fold_graph f' z' A'' y''\<close> and [transfer_rule]: \<open>U y y''\<close>
      by auto
    define y' where \<open>y' = f' x' y''\<close>
    have \<open>fold_graph f' z' A' y'\<close>
      unfolding A'_def y'_def
      using \<open>x' \<notin> A''\<close> foldA''
      by (rule fold_graph.intros)
    moreover have \<open>U (f x y) y'\<close>
      unfolding y'_def by transfer_prover
    ultimately show ?case
      by auto
  qed

  show \<open>rel_pred U (fold_graph f z A) (fold_graph f' z' A')\<close>
    apply (auto simp: rel_pred_def rel_set_def)
     apply (rule one_direction[of f z A _ U z' T f'])
         apply auto[5]
    apply (rule one_direction[of f' z' A' _ \<open>U\<inverse>\<inverse>\<close> z \<open>T\<inverse>\<inverse>\<close> f, simplified])
    by (auto simp flip: conversep_rel_fun)
qed

lemma Collect_parametric[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_pred T ===> rel_set T) Collect Collect\<close>
  by (auto simp: rel_pred_def)

lemma sum_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_unique U\<close>
  shows \<open>(T ===> (V ===> T ===> T) ===> (U ===> V) ===> rel_set U ===> T)
            sum_ow sum_ow\<close>
  unfolding sum_ow_def
  by transfer_prover

lemma the_default_The: \<open>the_default z S = (THE x. x \<in> S)\<close> if \<open>card S = 1\<close>
  by (simp add: that the_default_def)

lemma (in comm_monoid_set) comp_fun_commute_onI: \<open>Finite_Set.comp_fun_commute_on UNIV ((\<^bold>*) \<circ> g)\<close>
  apply (rule Finite_Set.comp_fun_commute_on.intro)
  by (simp add: o_def left_commute)

lemma (in comm_monoid_set) F_via_the_default: \<open>F g A = the_default def (Collect (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A))\<close>
  if \<open>finite A\<close>
proof -
  have \<open>y = x\<close> if \<open>fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A x\<close> and \<open>fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A y\<close> for x y
    using that apply (rule Finite_Set.comp_fun_commute_on.fold_graph_determ[rotated 2, where S=UNIV])
    by (simp_all add: comp_fun_commute_onI)
  then have \<open>Ex1 (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A)\<close>
    by (meson finite_imp_fold_graph that)
  then have \<open>card (Collect (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A)) = 1\<close>
    using card_eq_Suc_0_ex1 by fastforce
  then show ?thesis
    using that by (auto simp add: the_default_The eq_fold Finite_Set.fold_def)
qed

(* lemma sum_ow_typeclass: \<open>sum_ow 0 plus = sum\<close> *)

lemma sum_ud[ud_with]: \<open>sum = sum_ow 0 plus\<close>
  apply (auto intro!: ext simp: sum_def sum_ow_def comm_monoid_set.F_via_the_default)
   apply (subst comm_monoid_set.F_via_the_default)
    apply (auto simp add: sum.comm_monoid_set_axioms)
  by (metis comm_monoid_add_class.sum_def sum.infinite)

declare sum_with[ud_with del]

definition \<open>has_sum_ow U plus zero open f A x =
        filterlim (sum_ow zero plus f) (nhds_ow U (\<lambda>S. open S) x)
         (finite_subsets_at_top A)\<close>
  for U plus zero "open" f A x

lemma has_sum_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set T ===> (V ===> T ===> T) ===> T ===> (rel_set T ===> (=)) ===> (U ===> V) ===> rel_set U ===> T ===> (=))
            has_sum_ow has_sum_ow\<close>
  unfolding has_sum_ow_def
  by transfer_prover

lemma has_sum_ud[ud_with]: \<open>has_sum = has_sum_ow UNIV plus (0::'a::{comm_monoid_add,topological_space}) open\<close>
  by (auto intro!: ext simp: has_sum_def has_sum_ow_def ud_with)

lemma has_sum_ow_topology:
  assumes \<open>l \<in> topspace T\<close>
  assumes \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x + y \<in> topspace T\<close>
  shows \<open>has_sum_ow (topspace T) (+) 0 (openin T) f S l \<longleftrightarrow> has_sum_in T f S l\<close>
  using assms apply (simp add: has_sum_ow_def has_sum_in_def nhds_ow_topology sum_ud[symmetric])
  by (metis filterlim_nhdsin_iff_limitin)

definition \<open>at_within_ow U open a s = nhds_ow U open a \<sqinter> principal (s - {a})\<close>
  for U "open" a s

(* TODO: add to make_parametricity_proof_friendly *)
definition \<open>transfer_inf_principal F M = F \<sqinter> principal M\<close>

lemma transfer_inf_principal_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_filter T ===> rel_set T ===> rel_filter T) transfer_inf_principal transfer_inf_principal\<close>
proof -
  have *: \<open>transfer_inf_principal F M = transfer_bounded_filter_Inf M {F}\<close> for F :: \<open>'z filter\<close> and M
    by (simp add: transfer_inf_principal_def[abs_def] transfer_bounded_filter_Inf_def)
  show ?thesis
    unfolding * by transfer_prover
qed

lemma at_within_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>((rel_set T) ===> (rel_set T ===> (=)) ===> T ===> rel_set T ===> rel_filter T)
            at_within_ow at_within_ow\<close>
  unfolding at_within_ow_def make_parametricity_proof_friendly transfer_inf_principal_def[symmetric]
  by transfer_prover

lemma at_within_ud[ud_with]: \<open>at_within = at_within_ow UNIV open\<close>
  by (auto intro!: ext simp: at_within_def at_within_ow_def ud_with)

lemma at_within_ow_topology:
  \<open>at_within_ow (topspace T) (openin T) a S = nhdsin T a \<sqinter> principal (S - {a})\<close> 
  if \<open>a \<in> topspace T\<close>
  using that unfolding at_within_ow_def by (simp add: nhds_ow_topology)

(* lemma class_comm_monoid_add_ud[ud_with]: \<open>class.comm_monoid_add = comm_monoid_add_ow UNIV\<close> *)
  (* by (auto intro!: ext simp: class.comm_monoid_add_def SML_Monoids.comm_monoid_add_ow class.comm_monoid_add_axioms_def ud_with) *)
declare SML_Monoids.comm_monoid_add_ow[ud_with]

(* TODO move *)
lemma has_sum_in_comm_additive_general:
  fixes f :: \<open>'a \<Rightarrow> 'b :: comm_monoid_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: comm_monoid_add\<close>
  assumes T0[simp]: \<open>0 \<in> topspace T\<close> and Tplus[simp]: \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x+y \<in> topspace T\<close>
  assumes Uplus[simp]: \<open>\<And>x y. x \<in> topspace U \<Longrightarrow> y \<in> topspace U \<Longrightarrow> x+y \<in> topspace U\<close>
  assumes grange: \<open>g ` topspace T \<subseteq> topspace U\<close>
  assumes g0: \<open>g 0 = 0\<close>
  assumes frange: \<open>f ` S \<subseteq> topspace T\<close>
  assumes gcont: \<open>filterlim g (nhdsin U (g l)) (atin T l)\<close>
  assumes gadd: \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> g (x+y) = g x + g y\<close>
  assumes sumf: \<open>has_sum_in T f S l\<close>
  shows \<open>has_sum_in U (g o f) S (g l)\<close>
proof -
  define f' where \<open>f' x = (if x \<in> S then f x else 0)\<close> for x
  have \<open>topspace T \<noteq> {}\<close>
    using T0 by blast
  then have \<open>topspace U \<noteq> {}\<close>
    using grange by blast
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'b) Abs. type_definition Rep Abs (topspace T)"
    then interpret T: local_typedef \<open>topspace T\<close> \<open>TYPE('t)\<close>
      by unfold_locales
    assume "\<exists>(Rep :: 'u \<Rightarrow> 'c) Abs. type_definition Rep Abs (topspace U)"
    then interpret U: local_typedef \<open>topspace U\<close> \<open>TYPE('u)\<close>
      by unfold_locales

    note [[show_types]]
    note has_sum_comm_additive_general
    note this[unfolded ud_with]
    note this[unoverload_type 'b, unoverload_type 'c]
    note this[where 'b='t and 'c='u and 'a='a]
    note this[unfolded ud_with]
    thm this[no_vars]
    note this[untransferred]
    note this[where f=g and g=f' and zero=0 and zeroa=0 and plus=plus and plusa=plus
        and ?open=\<open>openin U\<close> and opena=\<open>openin T\<close> and x=l and S=S and T=\<open>topspace T\<close>]
    note this[simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have f'T[simp]: \<open>f' x \<in> topspace T\<close> for x
    using frange f'_def by force
  have [simp]: \<open>l \<in> topspace T\<close>
    using sumf has_sum_in_topspace by blast
  have [simp]: \<open>x \<in> topspace T \<Longrightarrow> g x \<in> topspace U\<close> for x
    using grange by auto
  have sumf'T: \<open>(\<Sum>x\<in>F. f' x) \<in> topspace T\<close> if \<open>finite F\<close> for F
    using that apply induction
    by auto
  have [simp]: \<open>(\<Sum>x\<in>F. f x) \<in> topspace T\<close> if \<open>F \<subseteq> S\<close> for F
    using that apply (induction F rule:infinite_finite_induct)
      apply auto
    by (metis Tplus f'T f'_def)
  have sum_gf: \<open>(\<Sum>x\<in>F. g (f' x)) = g (\<Sum>x\<in>F. f' x)\<close> 
    if \<open>finite F\<close> and \<open>F \<subseteq> S\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. g (f' x)) = (\<Sum>x\<in>F. g (f x))\<close>
      apply (rule sum.cong)
      using frange that by (auto simp: f'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f x)\<close>
      using \<open>finite F\<close> \<open>F \<subseteq> S\<close> apply induction
      using g0 frange apply auto
      apply (subst gadd)
      by (auto simp: f'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f' x)\<close>
      apply (rule arg_cong[where f=g])
      apply (rule sum.cong)
      using that by (auto simp: f'_def)
    finally show ?thesis
      by -
  qed
  from sumf have sumf': \<open>has_sum_in T f' S l\<close>
    apply (rule has_sum_in_cong[THEN iffD2, rotated])
    unfolding f'_def by auto
  have [simp]: \<open>g l \<in> topspace U\<close>
    using grange by auto
  from gcont have contg': \<open>filterlim g (nhdsin U (g l)) (nhdsin T l \<sqinter> principal (topspace T - {l}))\<close>
    apply (rule filterlim_cong[THEN iffD1, rotated -1])
      apply (rule refl)
     apply (simp add: atin_def)
    by (auto intro!: exI simp add: eventually_atin)
  from T0 grange g0 have [simp]: \<open>0 \<in> topspace U\<close>
    by auto

  have [simp]: 
    \<open>SML_Monoids.comm_monoid_add_ow (topspace T) (+) 0\<close>
    \<open>SML_Monoids.comm_monoid_add_ow (topspace U) (+) 0\<close>
    by (simp_all add: SML_Monoids.comm_monoid_add_ow_def SML_Semigroups.ab_semigroup_add_ow_def
        SML_Semigroups.semigroup_add_ow_def plus_ow_def semigroup_add_ow_axioms_def zero_ow_def
        neutral_ow_def SML_Semigroups.ab_semigroup_add_ow_axioms_def SML_Monoids.comm_monoid_add_ow_axioms_def
        Groups.add_ac)

  have \<open>has_sum_ow (topspace U) (+) 0 (openin U) (g \<circ> f') S (g l)\<close>
    apply (rule *)
    by (auto simp: topological_space_ow_from_topology sum_gf sumf'
        sum_ud[symmetric] at_within_ow_topology has_sum_ow_topology
        contg' sumf'T)

  then have \<open>has_sum_in U (g \<circ> f') S (g l)\<close>
    apply (rule has_sum_ow_topology[THEN iffD1, rotated -1])
    by simp_all
  then have \<open>has_sum_in U (g \<circ> f') S (g l)\<close>
    by simp
  then show ?thesis
    apply (rule has_sum_in_cong[THEN iffD1, rotated])
    unfolding f'_def using frange grange by auto
qed

lemma continuous_map_is_continuous_at_point:
  assumes \<open>continuous_map T U f\<close>
  shows \<open>filterlim f (nhdsin U (f l)) (atin T l)\<close>
  by (metis assms atin_degenerate bot.extremum continuous_map_atin filterlim_iff_le_filtercomap filterlim_nhdsin_iff_limitin)

lemma has_sum_in_comm_additive:
  fixes f :: \<open>'a \<Rightarrow> 'b :: ab_group_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: ab_group_add\<close>
  assumes \<open>topspace T = UNIV\<close> and \<open>topspace U = UNIV\<close>
  assumes \<open>Modules.additive g\<close>
  assumes gcont: \<open>continuous_map T U g\<close>
  assumes sumf: \<open>has_sum_in T f S l\<close>
  shows \<open>has_sum_in U (g o f) S (g l)\<close>
  apply (rule has_sum_in_comm_additive_general[where T=T and U=U])
  using assms
  by (auto simp: additive.zero Modules.additive_def intro!: continuous_map_is_continuous_at_point)


lemma infsum_butterfly_ket_a: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (a *\<^sub>V ket i) (ket i)) UNIV a\<close>
proof -
  have \<open>has_sum_in weak_star_topology ((\<lambda>b. a o\<^sub>C\<^sub>L b) \<circ> (\<lambda>i. selfbutterket i)) UNIV (a o\<^sub>C\<^sub>L id_cblinfun)\<close>
    apply (rule has_sum_in_comm_additive)
    by (auto intro!: infsum_butterfly_ket continuous_map_is_continuous_at_point limitin_continuous_map
        continuous_map_left_comp_weak_star  cblinfun_compose_add_right
        simp: Modules.additive_def)
  then show ?thesis
    by (auto simp: o_def cblinfun_comp_butterfly)
qed


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


lemma map_filter_on_id: \<open>map_filter_on S (\<lambda>x. x) F = F\<close> if \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
  using that
  by (auto intro!: filter_eq_iff[THEN iffD2] simp: eventually_map_filter_on eventually_frequently_simps)

lemma inverse_real_inverse: \<open>inverse_real_inst.inverse_real = inverse\<close>
  by (simp add: HOL.nitpick_unfold)

lemma top_filter_parametric':
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  shows \<open>rel_filter r (principal (Collect S)) \<top>\<close>
proof (rule rel_filter.intros)
  define Z where \<open>Z = principal {(x,y). r x y}\<close>
  show \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: eventually_principal Z_def)
  show \<open>map_filter_on {(x, y). r x y} fst Z = principal (Collect S)\<close>
    using \<open>Domainp r = S\<close> by (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
  show \<open>map_filter_on {(x, y). r x y} snd Z = \<top>\<close>
    apply (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
    by (metis assms(2) right_totalE)
qed


lemma Inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes \<open>Domainp r = S\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_set (rel_filter r) ===> rel_filter r)
     (\<lambda>M. inf (Inf M) (principal (Collect S)))
     Inf\<close>
proof (rule rel_funI)
  fix Fs Gs
  assume asm[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  show \<open>rel_filter r (inf (Inf Fs) (principal (Collect S))) (Inf Gs)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by (metis asm empty_iff equals0I rel_setD2)
    show ?thesis
      using assms by (simp add: True \<open>Gs = {}\<close> top_filter_parametric')
  next
    case False
    then have \<open>Gs \<noteq> {}\<close>
      by (metis asm ex_in_conv rel_setD1)
    have dom: \<open>Domainp (rel_filter r) F = (F \<le> principal (Collect S))\<close> for F
      by (simp add: Domainp_rel_filter assms(1))
    have 1: \<open>(rel_filter r)
       (Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F})
       (Inf Gs)\<close> (is \<open>(rel_filter r) ?I _\<close>)
      unfolding Inf_filter_def[abs_def]
      by transfer_prover
    have \<open>F \<le> principal (Collect S)\<close> if \<open>F \<in> Fs\<close> for F
      by (meson DomainPI asm dom rel_setD1 that)
    have \<open>?I = (inf (Inf Fs) (principal (Collect S)))\<close>
      unfolding dom Inf_filter_def
      apply auto
      apply (rule antisym)
      apply auto
        apply (simp add: Collect_mono_iff Sup_subset_mono)
      apply (metis (no_types, lifting) Sup_least mem_Collect_eq)
      by (smt (verit, del_insts) Collect_mono False Sup_subset_mono \<open>\<And>Fa. Fa \<in> Fs \<Longrightarrow> Fa \<le> principal (Collect S)\<close> bot.extremum_unique dual_order.refl inf.bounded_iff order_trans subsetI)
    show ?thesis
      using "1" \<open>Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F} = inf (Inf Fs) (principal (Collect S))\<close> by fastforce
  qed
qed



lemma inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_filter r ===> rel_filter r ===> rel_filter r)
     inf inf\<close>
proof (rule rel_funI, rule rel_funI, rename_tac F1 F2 G1 G2)
  fix F1 F2 G1 G2
  assume asmF[transfer_rule]: \<open>rel_filter r F1 F2\<close>
  assume asmG[transfer_rule]: \<open>rel_filter r G1 G2\<close>
  then have *: \<open>G1 \<le> principal (Collect (Domainp r))\<close>
    by (meson Domainp.intros Domainp_rel_filter)
  have \<open>rel_filter r (Inf {F1,G1} \<sqinter> principal (Collect (Domainp r))) (Inf {F2,G2})\<close>
    by transfer_prover
  with * show \<open>rel_filter r (inf F1 G1) (inf F2 G2)\<close>
    by (auto simp: inf_assoc inf.absorb_iff1)
qed



lemma convergent_ow_typeclass2[simp]:
  assumes \<open>open V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. f \<longlonglongrightarrow> l \<and> l \<in> V)\<close>
  by (simp add: limitin_canonical_iff_gen assms)

lemma convergent_on_typeclass3[simp]:
  assumes \<open>open V\<close> \<open>closed V\<close> \<open>range f \<subseteq> V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> convergent f\<close>
  apply (simp add: assms)
  by (meson assms(2) assms(3) closed_sequentially convergent_def range_subsetD)

(* 
(* TODO: Should we use sum_with from ETTS instead? *)
definition sum_with where \<open>sum_with plus zero f A = (if finite A then foldr (\<lambda>i s. plus (f i) s) (SOME l. set l = A \<and> distinct l) zero else zero)\<close>
  for plus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and zero :: 'a

 *)

(* lemma sum_with[unoverload_def]: \<open>sum \<equiv> sum_with plus 0\<close>
proof (rule eq_reflection, rule ext, rule ext, rename_tac f A)
  fix f :: \<open>'a \<Rightarrow> 'b\<close> and A
  show \<open>sum f A = sum_with (+) 0 f A\<close>
  proof (cases \<open>finite A\<close>)
    case True
    define l where \<open>l = (SOME l. set l = A \<and> distinct l)\<close>
    with True have \<open>set l = A\<close> and \<open>distinct l\<close>
       apply (metis (mono_tags, lifting) finite_distinct_list someI_ex)
      by (metis (mono_tags, lifting) True finite_distinct_list l_def someI_ex)
    then have \<open>sum f A = foldr (\<lambda>i s. plus (f i) s) l 0\<close>
      apply (induction l arbitrary: A)
      by auto
    also have \<open>\<dots> = sum_with (+) 0 f A\<close>
      by (simp add: True l_def sum_with_def)
    finally show ?thesis 
      by -
  next
    case False
    then show ?thesis 
      by (simp add: sum_with_def)
  qed
qed *)

(* 
lemma sum_with_typeclass: \<open>sum_with plus 0 f A = sum f A\<close>
proof (cases \<open>finite A\<close>)
  case True
  define l where \<open>l = (SOME l. set l = A \<and> distinct l)\<close>
  with True have \<open>set l = A\<close> and \<open>distinct l\<close>
  apply (metis (mono_tags, lifting) finite_distinct_list verit_sko_ex)
  by (metis (mono_tags, lifting) True finite_distinct_list l_def someI2)
  show ?thesis
    apply (simp add: sum_with_def flip: l_def)
    using \<open>set l = A\<close> \<open>distinct l\<close>
    apply (induction l arbitrary: A)
    by auto
next
  case False
  then show ?thesis 
    by (simp add: sum_with_def)
qed
 *)

(* unoverload_definition nhds_def
unoverload_definition has_sum_def
unoverload_definition at_within_def *)

(* lemma sum_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> ((=) ===> T) ===> rel_set (=) ===> T) 
    sum_with
    sum_with"
  unfolding sum_with_def
  by transfer_prover *)

(* (* TODO: we already have (different but roughly equivalent) nhds-stuff in Tmp_Move *)
definition \<open>nhds_with_on A open a =
        (\<Sqinter> (principal ` {x. (open x \<and> a \<in> x) \<and> x \<subseteq> A}) \<sqinter> principal A)\<close>
  for A "open" a *)

(* lemma nhds_with_on_topology: \<open>nhds_with_on (topspace T) (openin T) a = 
      (if a\<in>topspace T then nhdsin T a else principal (topspace T))\<close>
proof (rule filter_eq_iff[THEN iffD2, rule_format])
  fix P
  show \<open>eventually P (nhds_with_on (topspace T) (openin T) a) = eventually P (if a\<in>topspace T then nhdsin T a else principal (topspace T))\<close>
  proof (cases \<open>a \<in> topspace T\<close>)
    case True
    have \<open>eventually P (nhds_with_on (topspace T) (openin T) a)\<close>
      if \<open>eventually P (nhdsin T a)\<close>
    proof -
      from that 
      obtain S where \<open>openin T S\<close> and \<open>a \<in> S\<close> and \<open>\<forall>x\<in>S. P x\<close>
        using True by (auto simp add: eventually_nhdsin)

      show ?thesis
        apply (simp add: nhds_with_on_def)  
        apply (subst INF_inf_const2[symmetric])
        using True apply blast
        apply (rule eventually_INF1[where i=S])
        using \<open>openin T S\<close> and \<open>a \<in> S\<close> and \<open>\<forall>x\<in>S. P x\<close>
        by (auto simp: eventually_principal openin_subset)
    qed
    moreover have \<open>eventually P (nhdsin T a)\<close> if \<open>eventually P (nhds_with_on (topspace T) (openin T) a)\<close>
    proof -
      from that
      have \<open>eventually P (\<Sqinter>U\<in>{U. openin T U \<and> a \<in> U \<and> U \<subseteq> topspace T}. principal (U \<inter> topspace T))\<close>
        unfolding nhds_with_on_def
        apply (subst (asm) INF_inf_const2[symmetric])
        using True by auto
      then have *: \<open>eventually P F\<close>
        if \<open>\<And>U. openin T U \<Longrightarrow> a \<in> U \<Longrightarrow> U \<subseteq> topspace T \<Longrightarrow> F \<le> principal (U \<inter> topspace T)\<close> for F
        using that by (simp add: Inf_filter_def eventually_Sup)
      show \<open>eventually P (nhdsin T a)\<close>
        apply (rule * )
        by (simp add: INF_lower Int_absorb2 nhdsin_def)
    qed
    ultimately show ?thesis
        using True by fastforce
  next
    case False
    have aux: \<open>Inf X = top\<close> if \<open>X = {}\<close> for X :: \<open>'a filter set\<close>
      using that by simp
    show ?thesis 
      using False apply (simp add: nhds_with_on_def)
      apply (subst aux)
      by auto
  qed
qed *)

(* lemma nhds_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows \<open>((rel_set T ===> (=)) ===> T ===> rel_filter T) 
          (nhds_with_on (Collect (Domainp T))) nhds.with\<close>
  unfolding nhds.with_def
  apply transfer_prover_start
        apply transfer_step+
  by (auto intro!: ext simp: nhds_with_on_def Ball_Collect)
 *)

(* definition \<open>at_within_with_on A open a s =
   nhds_with_on A (\<lambda>S. open S) a \<sqinter> principal (s - {a})\<close>
  for A "open" a s

lemma at_within_with_on_topology: \<open>at_within_with_on (topspace T) (openin T) a S
    = (if a \<in> topspace T then nhdsin T a \<sqinter> principal (S - {a}) else principal (topspace T \<inter> S))\<close>
  by (auto simp add: at_within_with_on_def nhds_with_on_topology)
 *)

(* lemma at_within_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows \<open>((rel_set T ===> (=)) ===> T ===> rel_set T ===> rel_filter T)
         (at_within_with_on (Collect (Domainp T))) at_within.with\<close>
  unfolding at_within.with_def
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: at_within_with_on_def[abs_def])
 *)

(*
definition \<open>has_sum_with_on D plus zero open f A x =
        filterlim (sum_with plus zero f) (nhds_with_on D (\<lambda>S. open S) x)
         (finite_subsets_at_top A)\<close>
  for D plus zero "open" f A x

 *)

(* lemma has_sum_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> (rel_set T ===> (=)) ===> ((=) ===> T) ===> rel_set (=) ===> T ===> (=)) 
    (has_sum_with_on (Collect (Domainp T)))
    has_sum.with"
  unfolding has_sum.with_def
  apply transfer_prover_start
      apply transfer_step+
  by (auto intro!: ext simp add: has_sum_with_on_def) *)

(* 
lemma [simp]: \<open>plus_ow (topspace U) (+)\<close>
  apply (simp add: plus_ow_def)

lemma semigroup_add_ow_from_typeclass[simp]: \<open>SML_Semigroups.semigroup_add_ow (topspace U) (+)\<close>
  apply (simp add: SML_Semigroups.semigroup_add_ow_def semigroup_add_ow_axioms_def)

lemma ab_semigroup_add_ow_from_typeclass[simp]: \<open>SML_Semigroups.ab_semigroup_add_ow (topspace U) (+)\<close>
  apply (simp add: SML_Semigroups.ab_semigroup_add_ow_def SML_Semigroups.ab_semigroup_add_ow_axioms_def)

lemma comm_monoid_add_ow_from_typeclass[simp]: \<open>SML_Monoids.comm_monoid_add_ow (topspace U) (+) 0\<close>
  apply (simp add: SML_Monoids.comm_monoid_add_ow_def)
  try0
  by - *)



lemma cmod_distrib_plus: \<open>a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> cmod (a + b) = cmod a + cmod b\<close>
  by (simp add: cmod_Re)

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
  have sumP'id2: \<open>has_sum_in weak_star_topology (\<lambda>i. P' i) UNIV id_cblinfun\<close>
  proof -
    from infsum_butterfly_ket
    have \<open>has_sum_in weak_star_topology (\<Phi> o selfbutterket) UNIV (\<Phi> id_cblinfun)\<close>
      apply (rule has_sum_in_comm_additive[rotated -1])
      using assms 
         apply simp_all
       apply (auto simp: complex_vector.linear_add register_def Modules.additive_def 
          intro!: continuous_map_is_continuous_at_point complex_vector.linear_0 \<open>clinear \<Phi>\<close>)
      using assms preregister_def register_preregister by blast

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
      using * cont1 left_amplification_weak_star_cont by auto
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
        by (auto simp add: continuous_map_left_comp_weak_star P'_def P_def cblinfun_compose_add_right Modules.additive_def)
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

lemma register_norm: \<open>norm (F a) = norm a\<close> if \<open>register F\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
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
      using \<open>unitary U\<close> by (simp add: FU sandwich_def norm_isometry_compose norm_isometry_o' tensor_op_norm)
  qed
  note this[cancel_with_type]
  then show ?thesis
    by simp
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

lemma continuous_map_iff_preserves_convergence:
  assumes \<open>\<And>F a. a \<in> topspace T \<Longrightarrow> limitin T id a F \<Longrightarrow> limitin U f (f a) F\<close>
  shows \<open>continuous_map T U f\<close>
  apply (rule continuous_map_atin[THEN iffD2], intro ballI)
  using assms
  by (simp add: limitin_continuous_map)

lemma isCont_iff_preserves_convergence:
  assumes \<open>\<And>F. (id \<longlongrightarrow> a) F \<Longrightarrow> (f \<longlongrightarrow> f a) F\<close>
  shows \<open>isCont f a\<close>
  using assms
  by (simp add: isCont_def Lim_at_id)


lemma register_inv_weak_star_continuous:
  assumes \<open>register F\<close>
  shows \<open>continuous_map (subtopology weak_star_topology (range F)) weak_star_topology (inv F)\<close>
proof (rule continuous_map_iff_preserves_convergence, rename_tac K a)
  fix K a
  assume limit_id: \<open>limitin (subtopology weak_star_topology (range F)) id a K\<close>
  from register_decomposition
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
        limitin weak_star_topology (inv F) (inv F a) K\<close>
  proof (rule with_type_mp)
    from assms show \<open>register F\<close> by -
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where \<open>unitary U\<close> and FU: \<open>F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    define \<delta> :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where \<open>\<delta> = selfbutter (ket (undefined))\<close>
    then have [simp]: \<open>trace_class \<delta>\<close>
      by simp
    define u where \<open>u t = U o\<^sub>C\<^sub>L (from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L U*\<close> for t
    have [simp]: \<open>trace_class (u t)\<close> for t
      unfolding u_def
      apply (rule trace_class_comp_left)
      apply (rule trace_class_comp_right)
      by (simp add: trace_class_tensor)
    have uF: \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (u t o\<^sub>C\<^sub>L F a)\<close> for t a 
    proof -
      have \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (from_trace_class t o\<^sub>C\<^sub>L a) * trace (\<delta> o\<^sub>C\<^sub>L id_cblinfun)\<close>
        by (simp add: \<delta>_def trace_butterfly)
      also have \<open>\<dots> = trace ((from_trace_class t o\<^sub>C\<^sub>L a) \<otimes>\<^sub>o (\<delta> o\<^sub>C\<^sub>L id_cblinfun))\<close>
        by (simp add: trace_class_comp_left trace_tensor)
      also have \<open>\<dots> = trace ((from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> = trace (U* o\<^sub>C\<^sub>L u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        using \<open>unitary U\<close>
        by (simp add: u_def lift_cblinfun_comp[OF unitaryD1] cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*)\<close>
        apply (subst (2) circularity_of_trace)
        by (simp_all add: trace_class_comp_left cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L F a)\<close>
        by (simp add: Misc.sandwich_def FU cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    from limit_id
    have \<open>a \<in> range F\<close> and KrangeF: \<open>\<forall>\<^sub>F a in K. a \<in> range F\<close> and limit_id': \<open>limitin weak_star_topology id a K\<close>
      unfolding limitin_subtopology by auto
    from \<open>a \<in> range F\<close> have FiFa: \<open>F (inv F a) = a\<close>
      by (simp add: f_inv_into_f)
    from KrangeF
    have *: \<open>\<forall>\<^sub>F x in K. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F x)) = trace (from_trace_class t o\<^sub>C\<^sub>L x)\<close> for t
      apply (rule eventually_mono)
      by (simp add: f_inv_into_f)
    from limit_id' have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L a)) K\<close> for t
      unfolding limitin_weak_star_topology' by simp
    then have *: \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      unfolding FiFa using * by (rule tendsto_cong[THEN iffD2, rotated])
    have \<open>((\<lambda>a'. trace (u t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (u t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      using *[of \<open>Abs_trace_class (u t)\<close>]
      by (simp add: Abs_trace_class_inverse)
    then have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L inv F a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L inv F a)) K\<close> for t
      by (simp add: uF[symmetric])
    then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
      by (simp add: limitin_weak_star_topology')
  qed
  note this[cancel_with_type]
  then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
    by -
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
  have normI: \<open>norm (I a) = norm a\<close> for a
    unfolding I_def
    by (metis G_rangeF assms(1) assms(2) f_inv_into_f register_norm)
  have normJ: \<open>norm (J a) = norm a\<close> for a
    unfolding J_def
    by (metis F_rangeG assms(1) assms(2) f_inv_into_f register_norm)
  have weak_star_I: \<open>continuous_map weak_star_topology weak_star_topology I\<close>
  proof -
    have \<open>continuous_map weak_star_topology weak_star_topology G\<close>
      by (simp add: weak_star_cont_register)
    then have \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range G)) G\<close>
      by (simp add: continuous_map_into_subtopology)
    moreover have \<open>continuous_map (subtopology weak_star_topology (range F)) weak_star_topology (inv F)\<close>
      using \<open>register F\<close> register_inv_weak_star_continuous by blast
    ultimately show \<open>continuous_map weak_star_topology weak_star_topology I\<close>
      unfolding \<open>range F = range G\<close> I_def
      by (rule continuous_map_compose[unfolded o_def])
  qed
  have weak_star_J: \<open>continuous_map weak_star_topology weak_star_topology J\<close>
  proof -
    have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
      by (simp add: weak_star_cont_register)
    then have \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range F)) F\<close>
      by (simp add: continuous_map_into_subtopology)
    moreover have \<open>continuous_map (subtopology weak_star_topology (range G)) weak_star_topology (inv G)\<close>
      using \<open>register G\<close> register_inv_weak_star_continuous by blast
    ultimately show \<open>continuous_map weak_star_topology weak_star_topology J\<close>
      unfolding \<open>range F = range G\<close> J_def
      by (rule continuous_map_compose[unfolded o_def])
  qed

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
