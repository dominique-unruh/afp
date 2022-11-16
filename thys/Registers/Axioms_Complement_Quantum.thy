section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum (* With_Type.With_Type_Inst_Complex_Bounded_Operators *) Quantum_Extra Tensor_Product.Weak_Star_Topology
    Tensor_Product.Partial_Trace TAS_Topology
    With_Type.With_Type
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")
hide_const (open) Order.top

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

lemma map_filter_on_id: \<open>map_filter_on S (\<lambda>x. x) F = F\<close> if \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
  using that
  by (auto intro!: filter_eq_iff[THEN iffD2] simp: eventually_map_filter_on eventually_frequently_simps)

lemma inverse_real_inverse: \<open>inverse_real_inst.inverse_real = inverse\<close>
  by (simp add: HOL.nitpick_unfold)

lemma is_onb_def_no_ccsubspace: 
  \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = UNIV\<close>
  unfolding is_onb_def apply transfer by simp

unoverload_definition is_ortho_set_def
unoverload_definition complex_vector.subspace_def
unoverload_definition complex_vector.span_def
unoverload_definition is_onb_def_no_ccsubspace

definition \<open>uniformity_dist_on A dist uniformity \<longleftrightarrow>
        uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>A\<times>A. dist x y < e})\<close>
  for dist uniformity

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


lemma Domainp_rel_filter:
  assumes \<open>Domainp r = S\<close>
  shows \<open>Domainp (rel_filter r) F \<longleftrightarrow> (F \<le> principal (Collect S))\<close>
proof (intro iffI, elim Domainp.cases, hypsubst)
  fix G 
  assume \<open>rel_filter r F G\<close>
  then obtain Z where rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    and ZF: "map_filter_on {(x, y). r x y} fst Z = F" 
    and "map_filter_on {(x, y). r x y} snd Z = G"
    using rel_filter.simps by blast
  show \<open>F \<le> principal (Collect S)\<close>
    using rZ apply (auto simp flip: ZF assms intro!: filter_leI 
        simp: eventually_principal eventually_map_filter_on)
    by (smt (verit, best) DomainPI case_prod_beta eventually_elim2)
next
  assume asm: \<open>F \<le> principal (Collect S)\<close>
  define Z where \<open>Z = inf (filtercomap fst F) (principal {(x, y). r x y})\<close>
  have rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: Z_def eventually_inf_principal)
  moreover 
  have \<open>(\<forall>\<^sub>F x in Z. P (fst x) \<and> (case x of (x, xa) \<Rightarrow> r x xa)) = eventually P F\<close> for P
    using asm apply (auto simp add: le_principal Z_def eventually_inf_principal eventually_filtercomap)
    by (smt (verit, del_insts) DomainpE assms eventually_elim2)
  then have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    by (simp add: filter_eq_iff eventually_map_filter_on rZ)
  ultimately show \<open>Domainp (rel_filter r) F\<close>
    by (auto simp: Domainp_iff intro!: exI rel_filter.intros)
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

lemma class_uniformity_dist_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (=)) 
    (uniformity_dist_on (Collect (Domainp T)))
    class.uniformity_dist"
  unfolding class.uniformity_dist_def 
  apply transfer_prover_start
  apply transfer_step+
  apply (intro ext)
  apply (simp add: case_prod_unfold pred_prod_beta uniformity_dist_on_def
        flip: INF_inf_const2)
  apply (rule arg_cong[where f=\<open>\<lambda>\<gamma>. _ = (INF x\<in>_. principal (\<gamma> x))\<close>])
  by (auto intro!: ext simp: prod.Domainp_rel)

definition \<open>open_uniformity_on A open uniformity \<longleftrightarrow>
  (\<forall>U\<subseteq>A. open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U))\<close>
  for A "open" uniformity

schematic_goal class_open_uniformity_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_filter (rel_prod T T) ===> (=)) 
    (open_uniformity_on (Collect (Domainp T)))
    class.open_uniformity"
  unfolding class.open_uniformity_def
  apply transfer_prover_start
  apply transfer_step+
  apply (auto intro!: ext simp: open_uniformity_on_def)
  by blast+

definition \<open>metric_space_on A dist uniformity open \<longleftrightarrow>
        uniformity_dist_on A dist uniformity \<and>
        open_uniformity_on A open uniformity \<and>
        (\<forall>x\<in>A. (\<forall>y\<in>A. (dist x y = 0) \<longleftrightarrow> (x = y))) \<and>
        (\<forall>x\<in>A. (\<forall>y\<in>A. (\<forall>z\<in>A. dist x y \<le> dist x z + dist y z)))\<close>
  for A dist uniformity "open"

lemma class_metric_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    (metric_space_on (Collect (Domainp T)))
    class.metric_space"
  unfolding class.metric_space_def class.metric_space_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: metric_space_on_def[abs_def])

attribute_setup axiom = \<open>Scan.lift Parse.name >> (fn name => Thm.rule_attribute [] 
    (fn context => fn _ => Thm.axiom (Context.theory_of context) name))\<close>


definition \<open>nhds_on A open a = (\<Sqinter> (principal ` {S. S \<subseteq> A \<and> open S \<and> a \<in> S})) \<sqinter> principal A\<close>
  for A "open" a

lemma nhds_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> T ===> rel_filter T) 
    (nhds_on (Collect (Domainp T)))
    topological_space.nhds"
  unfolding [[axiom Topological_Spaces.topological_space.nhds_def_raw]]
  apply transfer_prover_start
        apply transfer_step+
  apply (intro ext)
  apply (simp add: nhds_on_def[abs_def])
  apply (simp add: case_prod_unfold pred_prod_beta uniformity_dist_on_def
        flip: )
  by (smt (verit) Collect_cong mem_Collect_eq subset_eq)


definition \<open>convergent_on A open X = (\<exists>L\<in>A. filterlim X (nhds_on A open L) sequentially)\<close>
  for A "open" X

lemma convergent_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> ((=) ===> T) ===> (=)) 
    (convergent_on (Collect (Domainp T)))
    topological_space.convergent"
  unfolding [[axiom Topological_Spaces.topological_space.convergent_def_raw]]
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: convergent_on_def[abs_def])

lemma cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> rel_filter T ===> (=)) 
    uniform_space.cauchy_filter
    uniform_space.cauchy_filter"
  unfolding [[axiom Topological_Spaces.uniform_space.cauchy_filter_def_raw]]
  by transfer_prover

lemma Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> ((=) ===> T) ===> (=)) 
    uniform_space.Cauchy
    uniform_space.Cauchy"
  unfolding [[axiom Topological_Spaces.uniform_space.Cauchy_uniform_raw]]
  using filtermap_parametric[transfer_rule] apply fail?
  by transfer_prover

definition \<open>complete_space_on A dist uniformity open \<longleftrightarrow>
        metric_space_on A dist uniformity open \<and>
        (\<forall>X. (\<forall>n. X n \<in> A) \<longrightarrow>
            uniform_space.Cauchy uniformity X \<longrightarrow> convergent_on A open X)\<close>
  for A dist uniformity "open"

lemma complete_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    (complete_space_on (Collect (Domainp T)))
    class.complete_space"
  unfolding class.complete_space_def class.complete_space_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: complete_space_on_def[abs_def])

definition \<open>scaleC_on A scaleR scaleC \<longleftrightarrow> (\<forall>r. \<forall>a\<in>A. scaleR r a = scaleC (complex_of_real r) a)\<close>
  for scaleR scaleC

lemma scaleC_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (=))  
    (scaleC_on (Collect (Domainp T)))
    class.scaleC"
  unfolding class.scaleC_def fun_eq_iff
  thm ext
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: scaleC_on_def[abs_def])

definition \<open>semigroup_add_on A plus \<longleftrightarrow>
        (\<forall>a\<in>A.
           \<forall>b\<in>A. \<forall>c\<in>A. plus (plus a b) c = plus a (plus b c))\<close>
  for A plus

lemma semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (=))  
    (semigroup_add_on (Collect (Domainp T)))
    class.semigroup_add"
  unfolding class.semigroup_add_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: semigroup_add_on_def[abs_def])

definition \<open>ab_semigroup_add_on A plus \<longleftrightarrow>
        semigroup_add_on A plus \<and>
        (\<forall>a\<in>A. \<forall>b\<in>A. plus a b = plus b a)\<close>
  for A plus

lemma ab_semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (=))  
    (ab_semigroup_add_on (Collect (Domainp T)))
    class.ab_semigroup_add"
  unfolding class.ab_semigroup_add_def class.ab_semigroup_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: ab_semigroup_add_on_def[abs_def])

definition \<open>comm_monoid_add_on A plus zero \<longleftrightarrow>
        ab_semigroup_add_on A plus \<and> (\<forall>a\<in>A. plus zero a = a)\<close>
  for A plus zero

lemma comm_monoid_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> (=))  
    (comm_monoid_add_on (Collect (Domainp T)))
    class.comm_monoid_add"
  unfolding class.comm_monoid_add_def class.comm_monoid_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: comm_monoid_add_on_def[abs_def])

definition \<open>ab_group_add_on A plus zero minus uminus \<longleftrightarrow>
        comm_monoid_add_on A plus zero \<and>
        (\<forall>a\<in>A. plus (uminus a) a = zero) \<and>
        (\<forall>a\<in>A. \<forall>b\<in>A. minus a b = plus a (uminus b))\<close>
  for A plus zero minus uminus

lemma ab_group_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (=))  
    (ab_group_add_on (Collect (Domainp T)))
    class.ab_group_add"
  unfolding class.ab_group_add_def class.ab_group_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: ab_group_add_on_def[abs_def])

definition \<open>complex_vector_on A scaleR scaleC plus zero minus uminus \<longleftrightarrow>
        scaleC_on A scaleR scaleC \<and>
        ab_group_add_on A plus zero minus uminus \<and>
                 (\<forall>a. \<forall>x\<in>A. \<forall>y\<in>A. scaleC a (plus x y) = plus (scaleC a x) (scaleC a y)) \<and>
          (\<forall>a. \<forall>b. \<forall>x\<in>A. scaleC (a + b) x = plus (scaleC a x) (scaleC b x)) \<and>
         (\<forall>a. \<forall>b. \<forall>x\<in>A. scaleC a (scaleC b x) = scaleC (a * b) x) \<and> (\<forall>x\<in>A. scaleC 1 x = x)\<close>
  for A scaleR scaleC plus zero minus uminus

lemma complex_vector_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (=))  
    (complex_vector_on (Collect (Domainp T)))
    class.complex_vector"
  unfolding class.complex_vector_def class.complex_vector_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: complex_vector_on_def[abs_def])


definition \<open>sgn_div_norm_on A sgn norm scaleR
\<longleftrightarrow> (\<forall>x\<in>A. sgn x = scaleR (inverse (norm x)) x)\<close>
  for A sgn norm scaleR

lemma sgn_div_norm_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T) ===> (T ===> (=)) ===> ((=) ===> T ===> T) ===> (=))  
    (sgn_div_norm_on (Collect (Domainp T)))
    class.sgn_div_norm"
  unfolding class.sgn_div_norm_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: sgn_div_norm_on_def[abs_def])

definition \<open>dist_norm_on A minus dist norm \<longleftrightarrow>
  (\<forall>x\<in>A. \<forall>y\<in>A. dist x y = norm (minus x y))\<close>
  for A minus dist norm

lemma dist_norm_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=)) ===> (=))  
    (dist_norm_on (Collect (Domainp T)))
    class.dist_norm"
  unfolding class.dist_norm_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: dist_norm_on_def[abs_def])

definition \<open>complex_inner_on A scaleR scaleC plusa zeroa minus uminus dist norm sgn uniformity open cinner \<longleftrightarrow>
        (complex_vector_on A scaleR scaleC plusa zeroa minus uminus \<and>
         dist_norm_on A minus dist norm \<and>
         sgn_div_norm_on A sgn norm scaleR) \<and>
        uniformity_dist_on A dist uniformity \<and>
        open_uniformity_on A open uniformity \<and>
        ((\<forall>x\<in>A. \<forall>y\<in>A. cinner x y = cnj (cinner y x)) \<and>
         (\<forall>x\<in>A.
             \<forall>y\<in>A.
                \<forall>z\<in>A. cinner (plusa x y) z = cinner x z + cinner y z) \<and>
         (\<forall>r. \<forall>x\<in>A.
                 \<forall>y\<in>A. cinner (scaleC r x) y = cnj r * cinner x y)) \<and>
        (\<forall>x\<in>A. 0 \<le> cinner x x) \<and>
        (\<forall>x\<in>A. (cinner x x = 0) = (x = zeroa)) \<and>
        (\<forall>x\<in>A. norm x = sqrt (cmod (cinner x x)))\<close>
  for A scaleR scaleC plusa zeroa minus uminus dist norm sgn uniformity "open" cinner

lemma complex_inner_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
      ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
      ===> (T ===> T ===> (=)) ===> (=)) 
    (complex_inner_on (Collect (Domainp T)))
    class.complex_inner"
  unfolding class.complex_inner_def class.complex_inner_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: complex_inner_on_def[abs_def])

definition \<open>chilbert_space_on A scaleR scaleC plus zero minus uminus dist norm sgn uniformity open cinner \<longleftrightarrow>
        complex_inner_on A scaleR scaleC plus zero minus uminus dist norm sgn
         uniformity open cinner \<and>
        complete_space_on A dist uniformity open\<close>
  for  A scaleR scaleC plus zero minus uminus dist norm sgn uniformity "open" cinner

lemma class_chilbert_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
      ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
      ===> (T ===> T ===> (=)) ===> (=)) 
    (chilbert_space_on (Collect (Domainp T)))
    class.chilbert_space"
  unfolding class.chilbert_space_def
  apply transfer_prover_start
  apply transfer_step+
  by (simp add: chilbert_space_on_def[abs_def])

lemma is_ortho_set_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> T ===> rel_set T ===> (=)) 
    is_ortho_set.with
    is_ortho_set.with"
  unfolding is_ortho_set.with_def
  by transfer_prover

lemma csubspace_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(T ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> (=)) 
    csubspace.with
    csubspace.with"
  unfolding csubspace.with_def 
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: complex_inner_on_def[abs_def])


definition \<open>hull_on A S s = \<Inter> {x. (S x \<and> s \<subseteq> x) \<and> x \<subseteq> A} \<inter> A\<close>

lemma hull_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T ===> rel_set T) 
    (hull_on (Collect (Domainp T)))
    (hull)"
  unfolding hull_def
  apply transfer_prover_start
      apply transfer_step+
  apply (intro ext)
  by (auto simp: hull_on_def)

definition \<open>cspan_on A zero plus scaleC = hull_on A (csubspace.with zero plus scaleC)\<close>
  for A zero plus scaleC

lemma cspan_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(T ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> rel_set T) 
    (cspan_on (Collect (Domainp T)))
    cspan.with"
  unfolding cspan.with_def
  apply transfer_prover_start
    apply transfer_step+
  by (auto intro!: ext simp: cspan_on_def)

definition \<open>is_onb_on A cinner zero norm open plus scaleC E \<longleftrightarrow>
        is_ortho_set.with cinner zero E \<and>
        (\<forall>b\<in>E. norm b = 1) \<and>
        closure_on_with A open (cspan_on A zero plus scaleC E) = A\<close>
  for A cinner zero norm "open" plus scaleC E

lemma is_onb_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> T ===> (T ===> (=)) ===> (rel_set T ===> (=))
     ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> (=)) 
    (is_onb_on (Collect (Domainp T)))
    is_onb.with"
  using right_total_UNIV_transfer[transfer_rule] apply fail?
  unfolding is_onb.with_def 
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: is_onb_on_def[abs_def])

lemma csubspace_nonempty: \<open>csubspace V \<Longrightarrow> V \<noteq> {}\<close>
  using complex_vector.subspace_0 by auto

lemma cspan_on_cspan: \<open>cspan_on V 0 (+) (*\<^sub>C) B = cspan B \<inter> V\<close> if \<open>csubspace V\<close> and \<open>B \<subseteq> V\<close>
proof -
  have \<open>\<Inter> {x. (csubspace x \<and> B \<subseteq> x) \<and> x \<subseteq> V} \<subseteq> cspan B\<close>
    apply (rule Inf_lower2[where u=\<open>cspan B \<inter> V\<close>])
    by (auto simp: complex_vector.subspace_inter that complex_vector.span_clauses)
  moreover have \<open>cspan B \<inter> V \<subseteq> \<Inter> {x. (csubspace x \<and> B \<subseteq> x) \<and> x \<subseteq> V}\<close>
    apply (rule Inf_greatest)
    using complex_vector.span_minimal by blast
  ultimately show ?thesis
    unfolding cspan_on_def hull_on_def csubspace.with[symmetric]
    by auto
qed

lemma closure_on_with_typeclass[simp]: 
  \<open>closure_on_with X (openin (top_of_set X)) S = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
proof -
  have \<open>closure_on_with X (openin (top_of_set X)) S = (top_of_set X) closure_of S \<union> S\<close>
    apply (simp add: closure_on_with_def closure_of_def)
    apply safe
     apply (meson openin_imp_subset)
    by auto
  also have \<open>\<dots> = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
    by (simp add: closure_of_subtopology)
  finally show ?thesis
    by -
qed

lemma scaleC_on_typeclass[simp]: \<open>scaleC_on V (*\<^sub>R) (*\<^sub>C)\<close>
  by (auto simp: scaleC_on_def scaleR_scaleC)

lemma semigroup_add_on_typeclass[simp]: \<open>semigroup_add_on V (+)\<close> for V :: \<open>_::semigroup_add set\<close>
  by (auto simp: semigroup_add_on_def ordered_field_class.sign_simps)

lemma ab_semigroup_add_on_typeclass[simp]: \<open>ab_semigroup_add_on V (+)\<close> for V :: \<open>_::ab_semigroup_add set\<close>
  by (auto simp: ab_semigroup_add_on_def Groups.add_ac)

lemma comm_monoid_add_on_typeclass[simp]: \<open>comm_monoid_add_on V (+) 0\<close> for V :: \<open>_::comm_monoid_add set\<close>
  by (auto simp: comm_monoid_add_on_def)

lemma ab_group_add_on_typeclass[simp]: \<open>ab_group_add_on V (+) 0 (-) uminus\<close> for V :: \<open>_::ab_group_add set\<close>
  by (auto simp: ab_group_add_on_def)

lemma complex_vector_on_typeclass[simp]: 
  (* assumes \<open>csubspace V\<close> *)
  \<open>complex_vector_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus\<close> for V :: \<open>_::complex_vector set\<close>
  by (auto simp add: complex_vector_on_def complex_vector.vector_space_assms)

lemma dist_norm_on_typeclass[simp]: \<open>dist_norm_on V (-) dist norm\<close> for V :: \<open>_::dist_norm set\<close>
  by (auto simp add: dist_norm_on_def dist_norm)

lemma sgn_div_norm_on_typeclass[simp]: \<open>sgn_div_norm_on V sgn norm (*\<^sub>R)\<close> for V :: \<open>_::sgn_div_norm set\<close>
  by (auto simp add: sgn_div_norm_on_def sgn_div_norm)

lemma uniformity_dist_on_typeclass[simp]: \<open>uniformity_dist_on V dist (uniformity_on V)\<close> for V :: \<open>_::uniformity_dist set\<close>
  apply (auto simp add: uniformity_dist_on_def uniformity_dist simp flip: INF_inf_const2)
  apply (subst asm_rl[of \<open>\<And>x. Restr {(xa, y). dist xa y < x} V = {(xa, y). xa \<in> V \<and> y \<in> V \<and> dist xa y < x}\<close>, rule_format])
  by auto

lemma open_uniformity_on_typeclass[simp]: 
  fixes V :: \<open>_::open_uniformity set\<close>
  assumes \<open>closed V\<close>
  shows \<open>open_uniformity_on V (openin (top_of_set V)) (uniformity_on V)\<close>
proof (unfold open_uniformity_on_def, intro allI impI iffI)
  fix U assume \<open>U \<subseteq> V\<close>
  assume \<open>openin (top_of_set V) U\<close>
  then obtain T where \<open>U = T \<inter> V\<close> and \<open>open T\<close>
    by (metis Int_ac(3) openin_open)
  with open_uniformity 
  have *: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> T\<close> if \<open>x \<in> T\<close> for x
    using that by blast
  have \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_inf_principal[THEN iffD2])
    using *[of x] apply (rule eventually_rev_mp)
    using \<open>U = T \<inter> V\<close> that by (auto intro!: always_eventually)
  then show \<open>\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close>
    by blast
next
  fix U assume \<open>U \<subseteq> V\<close>
  assume asm: \<open>\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close>
  from asm[rule_format]
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' \<in> V \<and> y \<in> V \<and> x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    unfolding eventually_inf_principal
    apply (rule eventually_rev_mp)
    using that by (auto intro!: always_eventually)
  then have xU: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_rev_mp)
    using that \<open>U \<subseteq> V\<close> by (auto intro!: always_eventually)
  have \<open>open (-V)\<close>
    using assms by auto
  with open_uniformity
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> -V\<close> if \<open>x \<in> -V\<close> for x
    using that by blast
  then have xV: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> -V\<close> for x
    apply (rule eventually_rev_mp)
     apply (rule that)
    apply (rule always_eventually)
    by auto
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U \<union> -V\<close> for x
    using xV[of x] xU[of x] that
    by auto
  then have \<open>open (U \<union> -V)\<close>
    using open_uniformity by blast
  then show \<open>openin (top_of_set V) U\<close>
    using \<open>U \<subseteq> V\<close>
    by (auto intro!: exI simp: openin_open)
qed

lemma complex_inner_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>closed V\<close>
  shows \<open>complex_inner_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  apply (auto simp: assms complex_inner_on_def cinner_simps)
  using norm_eq_sqrt_cinner by blast

lemma metric_space_on_typeclass[simp]:
  fixes V :: \<open>_::metric_space set\<close>
  assumes \<open>closed V\<close>
  shows \<open>metric_space_on V dist (uniformity_on V) (openin (top_of_set V))\<close>
  by (auto simp: assms metric_space_on_def class.metric_space_axioms_def dist_triangle2)

lemma nhds_on_topology[simp]: \<open>nhds_on (topspace T) (openin T) x = nhdsin T x\<close> if \<open>x \<in> topspace T\<close>
  using that apply (auto intro!: ext simp add: nhds_on_def[abs_def] nhdsin_def[abs_def])
   apply (subst INF_inf_const2[symmetric])
  using openin_subset by (auto intro!: INF_cong)

lemma convergent_on_topology[simp]:
  \<open>convergent_on (topspace T) (openin T) f \<longleftrightarrow> (\<exists>l. limitin T f l sequentially)\<close>
  by (auto simp: convergent_on_def simp flip: filterlim_nhdsin_iff_limitin)

lemma convergent_on_typeclass[simp]:
  \<open>convergent_on V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. limitin (top_of_set V) f l sequentially)\<close>
    by (simp add: flip: convergent_on_topology)

lemma convergent_on_typeclass2[simp]:
  assumes \<open>open V\<close>
  shows \<open>convergent_on V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. f \<longlonglongrightarrow> l \<and> l \<in> V)\<close>
  by (simp add: limitin_canonical_iff_gen assms)

lemma convergent_on_typeclass3[simp]:
  assumes \<open>open V\<close> \<open>closed V\<close> \<open>range f \<subseteq> V\<close>
  shows \<open>convergent_on V (openin (top_of_set V)) f \<longleftrightarrow> convergent f\<close>
  apply (simp add: assms)
  by (meson assms(2) assms(3) closed_sequentially convergent_def range_subsetD)

lemma complete_space_on_typeclass[simp]:
  fixes V :: \<open>_::uniform_space set\<close>
  assumes \<open>complete V\<close>
  shows \<open>complete_space_on V dist (uniformity_on V) (openin (top_of_set V))\<close>
proof -
  have \<open>\<exists>l. limitin (top_of_set V) X l sequentially\<close>
    if XV: \<open>\<And>n. X n \<in> V\<close> and cauchy: \<open>uniform_space.Cauchy (uniformity_on V) X\<close> for X
  proof -
    from cauchy
    have \<open>uniform_space.cauchy_filter (uniformity_on V) (filtermap X sequentially)\<close>
      by (simp add: [[axiom Topological_Spaces.uniform_space.Cauchy_uniform_raw]])
    then have \<open>cauchy_filter (filtermap X sequentially)\<close>
      by (auto simp: cauchy_filter_def [[axiom Topological_Spaces.uniform_space.cauchy_filter_def_raw]])
    then have \<open>Cauchy X\<close>
      by (simp add: Cauchy_uniform)
    with \<open>complete V\<close> XV obtain l where l: \<open>X \<longlonglongrightarrow> l\<close> \<open>l \<in> V\<close>
      apply atomize_elim
      by (meson completeE)
    with XV l show ?thesis
      by (auto intro!: exI[of _ l] simp: convergent_def limitin_subtopology)
  qed
  then show ?thesis
    by (auto simp: complete_space_on_def complete_imp_closed assms)
qed

lemma complet_space_as_set[simp]: \<open>complete (space_as_set V)\<close> for V :: \<open>_::cbanach ccsubspace\<close>
  by (simp add: complete_eq_closed)

lemma chilbert_space_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>complete V\<close>
  shows \<open>chilbert_space_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn
     (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  by (auto simp: chilbert_space_on_def assms complete_imp_closed)

lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and norm: \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
proof -
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (space_as_set V)"
    then interpret T: local_typedef \<open>space_as_set V\<close> \<open>TYPE('t)\<close>
      by unfold_locales

    note orthonormal_basis_exists[unfolded is_onb.with is_ortho_set.with]
    note this[unoverload_type 'a]
    note this[where 'a='t]
    note this[untransferred]
    note this[where plus=plus and scaleC=scaleC and scaleR=scaleR and zero=0 and minus=minus
        and uminus=uminus and sgn=sgn and S=S and norm=norm and cinner=cinner and dist=dist
        and ?open=\<open>openin (top_of_set (space_as_set V))\<close>
        and uniformity=\<open>uniformity_on (space_as_set V)\<close>]
    note this[simplified Domainp_rel_filter prod.Domainp_rel T.Domainp_cr_S]
  }    
  note * = this[cancel_type_definition]
  have 1: \<open>uniformity_on (space_as_set V)
    \<le> principal (Collect (pred_prod (\<lambda>x. x \<in> space_as_set V) (\<lambda>x. x \<in> space_as_set V)))\<close>
    by (auto simp: uniformity_dist intro!: le_infI2)
  have \<open>\<exists>B\<in>{A. \<forall>x\<in>A. x \<in> space_as_set V}.
     S \<subseteq> B \<and> is_onb_on {x. x \<in> space_as_set V} (\<bullet>\<^sub>C) 0 norm (openin (top_of_set (space_as_set V))) (+) (*\<^sub>C) B\<close>
    apply (rule * )
    using \<open>S \<subseteq> space_as_set V\<close> \<open>is_ortho_set S\<close>
    by (auto simp add: simp flip: is_ortho_set.with
        intro!: complex_vector.subspace_scale real_vector.subspace_scale csubspace_is_subspace
        csubspace_nonempty complex_vector.subspace_add complex_vector.subspace_diff
        complex_vector.subspace_neg sgn_in_spaceI 1 norm)
  then obtain B where \<open>B \<subseteq> space_as_set V\<close> and \<open>S \<subseteq> B\<close>
    and is_onb: \<open>is_onb_on (space_as_set V) (\<bullet>\<^sub>C) 0 norm (openin (top_of_set (space_as_set V))) (+) (*\<^sub>C) B\<close>
    by auto

  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>cspan B \<inter> space_as_set V = cspan B\<close>
    by (smt (verit) basic_trans_rules(8) ccspan.rep_eq ccspan_leqI ccspan_superset complex_vector.span_span inf_absorb1 less_eq_ccsubspace.rep_eq)
  then have [simp]: \<open>space_as_set V \<inter> cspan B = cspan B\<close>
    by blast
  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>space_as_set V \<inter> closure (cspan B) = closure (cspan B)\<close>
    by (metis Int_absorb1 ccspan.rep_eq ccspan_leqI less_eq_ccsubspace.rep_eq)
  have [simp]: \<open>closure X \<union> X = closure X\<close> for X :: \<open>'z::topological_space set\<close>
    using closure_subset by blast
  
  from is_onb have \<open>is_ortho_set B\<close>
    by (auto simp: is_onb_on_def is_ortho_set.with)

  moreover from is_onb have \<open>norm x = 1\<close> if \<open>x \<in> B\<close> for x
    by (auto simp: is_onb_on_def that)

  moreover from is_onb have \<open>closure (cspan B) = space_as_set V\<close>
    by (simp add: is_onb_on_def \<open>B \<subseteq> space_as_set V\<close> cspan_on_cspan closure_on_with_typeclass)
  then have \<open>ccspan B = V\<close>
    by (simp add: ccspan.abs_eq space_as_set_inverse)

  ultimately show ?thesis
    using \<open>S \<subseteq> B\<close> by auto
qed

definition \<open>sum_with plus zero f A = (if finite A then foldr (\<lambda>i s. plus (f i) s) (SOME l. set l = A \<and> distinct l) zero else zero)\<close>
  for plus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and zero :: 'a

lemma sum_with[unoverload_def]: \<open>sum \<equiv> sum_with plus 0\<close>
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
qed

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


unoverload_definition nhds_def
unoverload_definition has_sum_def
unoverload_definition at_within_def

lemma sum_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> ((=) ===> T) ===> rel_set (=) ===> T) 
    sum_with
    sum_with"
  unfolding sum_with_def
  by transfer_prover

definition \<open>nhds_with_on A open a =
        (\<Sqinter> (principal ` {x. (open x \<and> a \<in> x) \<and> x \<subseteq> A}) \<sqinter> principal A)\<close>
  for A "open" a

lemma nhds_with_on_topology: \<open>nhds_with_on (topspace T) (openin T) a = 
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
        apply (rule *)
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
qed

lemma nhds_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows \<open>((rel_set T ===> (=)) ===> T ===> rel_filter T) 
          (nhds_with_on (Collect (Domainp T))) nhds.with\<close>
  unfolding nhds.with_def
  apply transfer_prover_start
        apply transfer_step+
  by (auto intro!: ext simp: nhds_with_on_def Ball_Collect)

definition \<open>at_within_with_on A open a s =
   nhds_with_on A (\<lambda>S. open S) a \<sqinter> principal (s - {a})\<close>
  for A "open" a s

lemma at_within_with_on_topology: \<open>at_within_with_on (topspace T) (openin T) a S
    = (if a \<in> topspace T then nhdsin T a \<sqinter> principal (S - {a}) else principal (topspace T \<inter> S))\<close>
  by (auto simp add: at_within_with_on_def nhds_with_on_topology)

lemma at_within_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows \<open>((rel_set T ===> (=)) ===> T ===> rel_set T ===> rel_filter T)
         (at_within_with_on (Collect (Domainp T))) at_within.with\<close>
  unfolding at_within.with_def
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: at_within_with_on_def[abs_def])

definition \<open>has_sum_with_on D plus zero open f A x =
        filterlim (sum_with plus zero f) (nhds_with_on D (\<lambda>S. open S) x)
         (finite_subsets_at_top A)\<close>
  for D plus zero "open" f A x

lemma has_sum_with_on_topology:
  assumes \<open>l \<in> topspace T\<close>
  shows \<open>has_sum_with_on (topspace T) (+) 0 (openin T) f S l = has_sum_in T f S l\<close>
  using assms apply (simp add: has_sum_with_on_def has_sum_in_def nhds_with_on_topology
      sum_with_typeclass[abs_def])
  by (metis filterlim_nhdsin_iff_limitin)

lemma has_sum_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> (rel_set T ===> (=)) ===> ((=) ===> T) ===> rel_set (=) ===> T ===> (=)) 
    (has_sum_with_on (Collect (Domainp T)))
    has_sum.with"
  unfolding has_sum.with_def
  apply transfer_prover_start
      apply transfer_step+
  by (auto intro!: ext simp add: has_sum_with_on_def)

unoverload_definition Modules.additive_def

definition \<open>additive_with_on A plus1 plus2 f =
        (\<forall>x\<in>A. \<forall>y\<in>A. f (plus1 x y) = plus2 (f x) (f y))\<close>
  for A plus1 plus2 f

lemma additive_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  assumes [transfer_rule]: "right_total U" "bi_unique U"
  shows "((T ===> T ===> T) ===> (U ===> U ===> U) ===> (T ===> U) ===> (=)) 
    (additive_with_on (Collect (Domainp T)))
    additive.with"
  unfolding additive.with_def additive_with_on_def
  by transfer_prover

lemma continuous_map_is_continuous_at_point:
  assumes \<open>continuous_map T U f\<close>
  shows \<open>filterlim f (nhdsin U (f l)) (atin T l)\<close>
  by (metis assms atin_degenerate bot.extremum continuous_map_atin filterlim_iff_le_filtercomap filterlim_nhdsin_iff_limitin)

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
  define g' where \<open>g' x = (if x \<in> topspace T then g x else 0)\<close> for x
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

    note has_sum_comm_additive_general[unfolded sum_with has_sum.with at_within.with nhds.with
        additive.with]
    note this[unoverload_type 'b, unoverload_type 'c]
    note this[where 'b='t and 'c='u and 'a='a]
    note this[untransferred]
    note this[where f=g' and g=f' and zero=0 and zeroa=0 and plus=plus and plusa=plus
        and ?open=\<open>openin U\<close> and opena=\<open>openin T\<close> and x=l and S=S and T=\<open>topspace T\<close>]
    note this[simplified]
  }    
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have f'T[simp]: \<open>f' x \<in> topspace T\<close> for x
    using frange f'_def by force
  have [simp]: \<open>l \<in> topspace T\<close>
    using sumf has_sum_in_topspace by blast
  have [simp]: \<open>x \<in> topspace T \<Longrightarrow> g' x \<in> topspace U\<close> for x
    using grange g'_def by auto
  have sumf'T: \<open>(\<Sum>x\<in>F. f' x) \<in> topspace T\<close> if \<open>finite F\<close> for F
    using that apply induction
    by auto
  have [simp]: \<open>(\<Sum>x\<in>F. f x) \<in> topspace T\<close> if \<open>F \<subseteq> S\<close> for F
    using that apply (induction F rule:infinite_finite_induct)
      apply auto
    by (metis Tplus f'T f'_def)
  have sum_gf: \<open>(\<Sum>x\<in>F. g' (f' x)) = g' (\<Sum>x\<in>F. f' x)\<close> 
    if \<open>finite F\<close> and \<open>F \<subseteq> S\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. g' (f' x)) = (\<Sum>x\<in>F. g (f x))\<close>
      apply (rule sum.cong)
      using frange that by (auto simp: f'_def g'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f x)\<close>
      using \<open>finite F\<close> \<open>F \<subseteq> S\<close> apply induction
      using g0 frange apply auto
      apply (subst gadd)
      by (auto simp: f'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f' x)\<close>
      apply (rule arg_cong[where f=g])
      apply (rule sum.cong)
      using that by (auto simp: f'_def)
    also have \<open>\<dots> = g' (\<Sum>x\<in>F. f' x)\<close>
      using g'_def sumf'T that(1) by simp
    finally show ?thesis
      by -
  qed
  from sumf have sumf': \<open>has_sum_in T f' S l\<close>
    apply (rule has_sum_in_cong[THEN iffD2, rotated])
    unfolding f'_def by auto
  have [simp]: \<open>g' l = g l\<close>
    by (simp add: g'_def)
  have [simp]: \<open>g l \<in> topspace U\<close>
    using grange by auto
  from gcont have contg': \<open>filterlim g' (nhdsin U (g l)) (nhdsin T l \<sqinter> principal (topspace T - {l}))\<close>
    apply (rule filterlim_cong[THEN iffD1, rotated -1])
      apply (rule refl)
     apply (simp add: atin_def)
    by (auto intro!: exI simp add: g'_def eventually_atin)
  from T0 grange g0 have [simp]: \<open>0 \<in> topspace U\<close>
    by auto

  have \<open>has_sum_with_on (topspace U) (+) 0 (openin U) (g' \<circ> f') S (g' l)\<close>
    apply (rule *)
    by (auto simp: topological_space_on_with_from_topology sum_gf sumf'
        nhds_with_on_topology sum_with_typeclass has_sum_with_on_topology
        at_within_with_on_topology contg' sumf'T)

  then have \<open>has_sum_in U (g' \<circ> f') S (g' l)\<close>
    apply (rule has_sum_with_on_topology[THEN iffD1, rotated])
    by simp
  then have \<open>has_sum_in U (g' \<circ> f') S (g l)\<close>
    by simp
  then show ?thesis
    apply (rule has_sum_in_cong[THEN iffD1, rotated])
    unfolding f'_def g'_def using frange grange by auto
qed

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
  have \<open>has_sum_in weak_star_topology ((\<lambda>b. a o\<^sub>C\<^sub>L b) \<circ> (\<lambda>i. Misc.selfbutterket i)) UNIV (a o\<^sub>C\<^sub>L id_cblinfun)\<close>
    apply (rule has_sum_in_comm_additive)
    by (auto intro!: infsum_butterfly_ket continuous_map_is_continuous_at_point limitin_continuous_map
        continuous_map_left_comp_weak_star  cblinfun_compose_add_right
        simp: Modules.additive_def)
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

(* (* TODO: remove (use continuous_map_pullback_both from Misc_Tensor_Product instead) *)
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
qed *)

lemma min_power_distrib_left: \<open>(min x y) ^ n = min (x ^ n) (y ^ n)\<close> if \<open>x \<ge> 0\<close> and \<open>y \<ge> 0\<close> for x y :: \<open>_ :: linordered_semidom\<close>
  by (metis linorder_le_cases min.absorb_iff2 min.order_iff power_mono that(1) that(2))

lemma norm_abs_op[simp]: \<open>norm (abs_op a) = norm a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have \<open>(norm (abs_op a))\<^sup>2 = norm (abs_op a* o\<^sub>C\<^sub>L abs_op a)\<close>
    by simp
  also have \<open>\<dots> = norm (a* o\<^sub>C\<^sub>L a)\<close>
    by (simp add: abs_op_def positive_cblinfun_squareI)
  also have \<open>\<dots> = (norm a)\<^sup>2\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma trace_norm_geq_cinner_abs_op: \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) \<le> trace_norm t\<close> if \<open>trace_class t\<close> and \<open>norm \<psi> = 1\<close>
proof -
  have \<open>\<exists>B. {\<psi>} \<subseteq> B \<and> is_onb B\<close>
    apply (rule orthonormal_basis_exists)
    using \<open>norm \<psi> = 1\<close>
    by auto
  then obtain B where \<open>is_onb B\<close> and \<open>\<psi> \<in> B\<close>
    by auto

  have \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) = (\<Sum>\<^sub>\<infinity>\<psi>\<in>{\<psi>}. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    by simp
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<psi>\<in>B. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    apply (rule infsum_mono_neutral_complex)
    using \<open>\<psi> \<in> B\<close> \<open>is_onb B\<close> that
    by (auto simp add: trace_exists cinner_pos_if_pos)
  also have \<open>\<dots> = trace_norm t\<close>
    using \<open>is_onb B\<close> that
    by (metis trace_abs_op trace_alt_def trace_class_abs_op)
  finally show ?thesis
    by -
qed

lemma norm_leq_trace_norm: \<open>norm t \<le> trace_norm t\<close> if \<open>trace_class t\<close> 
  for t :: \<open>'a::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> (* TODO get rid of "not_singleton" *)
proof (rule field_le_epsilon)
  fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>

  define \<delta> :: real where 
    \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (norm (sqrt_op (abs_op t)) + 1)))\<close>
  have \<open>\<delta> > 0\<close>
    using \<open>\<epsilon> > 0\<close> apply (auto simp add: \<delta>_def)
    by (smt (verit) norm_not_less_zero zero_less_divide_iff)
  have \<delta>_small: \<open>\<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta> \<le> \<epsilon>\<close>
  proof -
    define n where \<open>n = norm (sqrt_op (abs_op t))\<close>
    then have \<open>n \<ge> 0\<close>
      by simp
    have \<delta>: \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (n + 1)))\<close>
      by (simp add: \<delta>_def n_def)

    have \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon> / 2 + 2 * n * \<delta>\<close>
      apply (rule add_right_mono)
      apply (subst \<delta>) apply (subst min_power_distrib_left)
      using \<open>\<epsilon> > 0\<close> \<open>n \<ge> 0\<close> by auto
    also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * n * (\<epsilon> / (4 * (n + 1)))\<close>
      apply (intro add_left_mono mult_left_mono)
      by (simp_all add: \<delta> \<open>n \<ge> 0\<close>)
    also have \<open>\<dots> = \<epsilon> / 2 + 2 * (n / (n+1)) * (\<epsilon> / 4)\<close>
      by simp
    also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * 1 * (\<epsilon> / 4)\<close>
      apply (intro add_left_mono mult_left_mono mult_right_mono)
      using \<open>n \<ge> 0\<close> \<open>\<epsilon> > 0\<close> by auto
    also have \<open>\<dots> = \<epsilon>\<close>
      by simp
    finally show \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon>\<close>
      by -
  qed

  from \<open>\<delta> > 0\<close> obtain \<psi> where \<psi>\<epsilon>: \<open>norm (sqrt_op (abs_op t)) - \<delta> \<le> norm (sqrt_op (abs_op t) *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim by (rule cblinfun_norm_approx_witness)

  have aux1: \<open>2 * complex_of_real x = complex_of_real (2 * x)\<close> for x
    by simp

  have \<open>complex_of_real (norm t) = norm (abs_op t)\<close>
    by simp
  also have \<open>\<dots> = (norm (sqrt_op (abs_op t)))\<^sup>2\<close>
    by (simp flip: norm_AadjA)
  also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) + \<delta>)\<^sup>2\<close>
    by (smt (verit) \<psi>\<epsilon> complex_of_real_mono norm_triangle_ineq4 norm_triangle_sub pos2 power_strict_mono)
  also have \<open>\<dots> = (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) * \<delta>\<close>
    by (simp add: power2_sum)
  also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta>\<close>
    apply (rule complex_of_real_mono_iff[THEN iffD2])
    by (smt (z3) \<open>0 < \<delta>\<close> \<open>norm \<psi> = 1\<close> more_arith_simps(11) mult_less_cancel_right_disj norm_cblinfun one_power2 power2_eq_square)
  also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<epsilon>\<close>
    apply (rule complex_of_real_mono_iff[THEN iffD2])
    using \<delta>_small by auto
  also have \<open>\<dots> = ((sqrt_op (abs_op t) *\<^sub>V \<psi>) \<bullet>\<^sub>C (sqrt_op (abs_op t) *\<^sub>V \<psi>)) + \<epsilon>\<close>
    by (simp add: cdot_square_norm)
  also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>)) + \<epsilon>\<close>
    by (simp flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<le> trace_norm t + \<epsilon>\<close>
    using \<open>norm \<psi> = 1\<close> \<open>trace_class t\<close> by (auto simp add: trace_norm_geq_cinner_abs_op)
  finally show \<open>norm t \<le> trace_norm t + \<epsilon>\<close>
    using complex_of_real_mono_iff by blast
qed


lemma cmod_distrib_plus: \<open>a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> cmod (a + b) = cmod a + cmod b\<close>
  by (simp add: cmod_Re)

(* lemma abs_op_increasing[simp]: \<open>a \<le> abs_op a\<close> (* WRONG unless a is Hermitian *)
  by -

definition \<open>pos_part_op a = (abs_op a + a) /\<^sub>R 2\<close>
definition \<open>neg_part_op a = (abs_op a - a) /\<^sub>R 2\<close>

lemma op_decomp_pos_neg: \<open>pos_part_op a - neg_part_op a = a\<close>
  apply (auto simp: pos_part_op_def neg_part_op_def)
  by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(2) Extra_Ordered_Fields.sign_simps(8) arithmetic_simps(50) cblinfun_assoc_left(3) ordered_field_class.sign_simps(11) scaleR_2 scaleR_half_double scaleR_left_commute scaleR_right_diff_distrib verit_minus_simplify(1))

lemma abs_op_decomp_pos_neg: \<open>pos_part_op a + neg_part_op a = abs_op a\<close>
  apply (auto simp: pos_part_op_def neg_part_op_def)
  by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(2) Extra_Ordered_Fields.sign_simps(8) add_diff_cancel_left' scaleR_half_double scaleR_right_distrib)

lemma pos_part_op_leq_abs_op: \<open>pos_part_op a \<le> abs_op a\<close>
proof -
  have \<open>pos_part_op a - abs_op a = (a - abs_op a) /\<^sub>R 2\<close>
    apply (auto simp: pos_part_op_def)
    by (metis (no_types, lifting) Extra_Ordered_Fields.sign_simps(7) add_diff_cancel_left' scaleR_half_double scaleR_right_diff_distrib)
  also have \<open>\<dots> \<le> (abs_op a - abs_op a) /\<^sub>R 2\<close>
    apply (intro scaleR_left_mono diff_right_mono)
    by auto
  also have \<open>\<dots> = 0\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma pos_part_op_uminus[simp]: \<open>pos_part_op (-a) = neg_part_op a\<close>
  by (simp add: pos_part_op_def neg_part_op_def)

lemma neg_part_op_uminus[simp]: \<open>neg_part_op (-a) = pos_part_op a\<close>
  by (simp add: pos_part_op_def neg_part_op_def)

lemma neg_part_op_leq_abs_op: \<open>neg_part_op a \<le> abs_op a\<close>
  using pos_part_op_leq_abs_op[of \<open>-a\<close>]
  by simp

lemma pos_part_op_pos[simp]: \<open>pos_part_op a \<ge> 0\<close>
  by (metis abs_op_decomp_pos_neg le_add_same_cancel2 neg_part_op_leq_abs_op)

lemma neg_part_op_pos[simp]: \<open>neg_part_op a \<ge> 0\<close>
  by (metis pos_part_op_pos pos_part_op_uminus) *)

(* FALSE for non hermitian a! See quicksheets 2022, p.217 *)
(* lemma cmod_cinner_leq_cmod_cinner_abs: \<open>cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>)) \<le> cmod (\<psi> \<bullet>\<^sub>C (abs_op a *\<^sub>V \<psi>))\<close>
proof -
  have \<open>cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>)) = cmod (\<psi> \<bullet>\<^sub>C (pos_part_op a *\<^sub>V \<psi>) - \<psi> \<bullet>\<^sub>C (neg_part_op a *\<^sub>V \<psi>))\<close>
    by (metis cinner_simps(3) minus_cblinfun.rep_eq op_decomp_pos_neg)
  also have \<open>\<dots> \<le> cmod (\<psi> \<bullet>\<^sub>C (pos_part_op a *\<^sub>V \<psi>)) + cmod (\<psi> \<bullet>\<^sub>C (neg_part_op a *\<^sub>V \<psi>))\<close>
    using norm_triangle_ineq4 by blast
  also have \<open>\<dots> = cmod (\<psi> \<bullet>\<^sub>C (pos_part_op a *\<^sub>V \<psi>) + \<psi> \<bullet>\<^sub>C (neg_part_op a *\<^sub>V \<psi>))\<close>
    by (intro cmod_distrib_plus[symmetric] cinner_pos_if_pos pos_part_op_pos neg_part_op_pos)
  also have \<open>\<dots> = cmod (\<psi> \<bullet>\<^sub>C (abs_op a *\<^sub>V \<psi>))\<close>
    by (metis abs_op_decomp_pos_neg cblinfun.add_left cinner_simps(2))
  finally show ?thesis
    by -
qed *)


lemma ket_pair_split: \<open>ket x = tensor_ell2 (ket (fst x)) (ket (snd x))\<close>
  by (simp add: tensor_ell2_ket)

(* TODO better name *)
lemma trace_partial_trace_compose: \<open>trace (from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) = trace (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
proof -
  define s where \<open>s = trace (from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x)\<close>
  define s' where \<open>s' e = ket e \<bullet>\<^sub>C ((from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) *\<^sub>V ket e)\<close> for e
  define u where \<open>u j = Abs_trace_class ((tensor_ell2_right (ket j))* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (tensor_ell2_right (ket j)))\<close> for j
  define u' where \<open>u' e j = ket e \<bullet>\<^sub>C (from_trace_class (u j) *\<^sub>V x *\<^sub>V ket e)\<close> for e j
  have \<open>has_sum u UNIV (partial_trace t)\<close>
    using partial_trace_has_sum[of t]
    by (simp add: u_def[abs_def])
  then have \<open>has_sum ((\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) o u) UNIV (from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e)\<close> for e 
  proof (rule has_sum_comm_additive[rotated -1])
    show \<open>Modules.additive (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e)\<close>
      by (simp add: Modules.additive_def cblinfun.add_left plus_trace_class.rep_eq)
    have bounded_clinear: \<open>bounded_clinear (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e)\<close>
    proof (rule bounded_clinearI[where K=\<open>norm (x *\<^sub>V ket e)\<close>])
      show \<open>from_trace_class (b1 + b2) *\<^sub>V x *\<^sub>V ket e = from_trace_class b1 *\<^sub>V x *\<^sub>V ket e + from_trace_class b2 *\<^sub>V x *\<^sub>V ket e\<close> for b1 b2
        by (simp add: plus_cblinfun.rep_eq plus_trace_class.rep_eq)
      show \<open>from_trace_class (r *\<^sub>C b) *\<^sub>V x *\<^sub>V ket e = r *\<^sub>C (from_trace_class b *\<^sub>V x *\<^sub>V ket e)\<close> for b r
        by (simp add: scaleC_trace_class.rep_eq)
      show \<open>norm (from_trace_class t *\<^sub>V x *\<^sub>V ket e) \<le> norm t * norm (x *\<^sub>V ket e)\<close> for t
      proof -
        have \<open>norm (from_trace_class t *\<^sub>V x *\<^sub>V ket e) \<le> norm (from_trace_class t) * norm (x *\<^sub>V ket e)\<close>
          by (simp add: norm_cblinfun)
        also have \<open>\<dots> \<le> norm t * norm (x *\<^sub>V ket e)\<close>
          by (auto intro!: mult_right_mono simp add: norm_leq_trace_norm norm_trace_class.rep_eq)
        finally show ?thesis
          by -
      qed
    qed
    have \<open>isCont (\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) (partial_trace t)\<close>
      using bounded_clinear clinear_continuous_at by auto
    then show \<open>(\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) \<midarrow>partial_trace t\<rightarrow> from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e\<close>
      by (simp add: isCont_def)
  qed
  then have \<open>has_sum ((\<lambda>v. ket e \<bullet>\<^sub>C v) o ((\<lambda>u. from_trace_class u *\<^sub>V x *\<^sub>V ket e) o u)) UNIV (ket e \<bullet>\<^sub>C (from_trace_class (partial_trace t) *\<^sub>V x *\<^sub>V ket e))\<close> for e 
  proof (rule has_sum_comm_additive[rotated -1])
    show \<open>Modules.additive (\<lambda>v. ket e \<bullet>\<^sub>C v)\<close>
      by (simp add: Modules.additive_def cinner_simps(2))
    have bounded_clinear: \<open>bounded_clinear (\<lambda>v. ket e \<bullet>\<^sub>C v)\<close>
      using bounded_clinear_cinner_right by auto
    then have \<open>isCont (\<lambda>v. ket e \<bullet>\<^sub>C v) l\<close> for l
      by simp
    then show \<open>(\<lambda>v. ket e \<bullet>\<^sub>C v) \<midarrow>l\<rightarrow> ket e \<bullet>\<^sub>C l\<close> for l
      by (simp add: isContD)
  qed
  then have has_sum_u': \<open>has_sum (\<lambda>j. u' e j) UNIV (s' e)\<close> for e 
    by (simp add: o_def u'_def s'_def)
  then have infsum_u': \<open>s' e = infsum (u' e) UNIV\<close> for e
    by (metis infsumI)
(*   have abs_sum_s': \<open>s' abs_summable_on UNIV\<close> (* TODO needed? *)
    by - *)
  have tc_u_x[simp]: \<open>trace_class (from_trace_class (u j) o\<^sub>C\<^sub>L x)\<close> for j
    by (simp add: trace_class_comp_left)

  have summable_u'_pairs: \<open>(\<lambda>(e, j). u' e j) summable_on UNIV \<times> UNIV\<close>
  proof -
    have \<open>trace_class (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
      by (simp add: trace_class_comp_left)
    from trace_exists[OF is_onb_ket this]
    have \<open>(\<lambda>ej. ket ej \<bullet>\<^sub>C (from_trace_class t *\<^sub>V (x \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket ej)) summable_on UNIV\<close>
      by (simp_all add: summable_on_reindex o_def)
    then show ?thesis
      by (simp_all add: o_def u'_def[abs_def] u_def
          trace_class_comp_left trace_class_comp_right Abs_trace_class_inverse tensor_ell2_right_apply 
          ket_pair_split tensor_op_ell2 case_prod_unfold cinner_adj_right)
  qed

  have u'_tensor: \<open>u' e j = ket (e,j) \<bullet>\<^sub>C ((from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun)) *\<^sub>V ket (e,j))\<close> for e j
    by (simp add: u'_def u_def tensor_op_ell2 tensor_ell2_right_apply  Abs_trace_class_inverse
        trace_class_comp_left trace_class_comp_right cinner_adj_right
        flip: tensor_ell2_ket)

  have \<open>has_sum (\<lambda>e. e \<bullet>\<^sub>C ((from_trace_class (partial_trace t) o\<^sub>C\<^sub>L x) *\<^sub>V e)) (range ket) s\<close>
    unfolding s_def
    apply (rule trace_has_sum)
    by (auto simp: trace_class_comp_left)
  then have \<open>has_sum s' UNIV s\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def s'_def[abs_def])
  then have \<open>s = infsum s' UNIV\<close>
    by (simp add: infsumI)
  also have \<open>\<dots> = infsum (\<lambda>e. infsum (u' e) UNIV) UNIV\<close>
    using infsum_u' by presburger
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(e, j)\<in>UNIV. u' e j)\<close>
    apply (subst infsum_Sigma'_banach)
     apply (rule summable_u'_pairs)
    by simp
  also have \<open>\<dots> = trace (from_trace_class t o\<^sub>C\<^sub>L (x \<otimes>\<^sub>o id_cblinfun))\<close>
    unfolding u'_tensor 
    by (simp add: trace_ket_sum cond_case_prod_eta trace_class_comp_left)
  finally show ?thesis
    by (simp add: s_def)
qed

(* TODO move *)
lemma amplification_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
proof (unfold weak_star_topology_def', rule continuous_map_pullback_both)
  show \<open>S \<subseteq> f -` UNIV\<close> for S :: \<open>'x set\<close> and f :: \<open>'x \<Rightarrow> 'y\<close>
    by simp
  define g' :: \<open>(('b ell2, 'a ell2) trace_class \<Rightarrow> complex) \<Rightarrow> (('b \<times> 'c) ell2, ('a \<times> 'c) ell2) trace_class \<Rightarrow> complex\<close> where
    \<open>g' \<tau> t = \<tau> (partial_trace t)\<close> for \<tau> t
  have \<open>continuous_on UNIV g'\<close>
    by (simp add: continuous_on_coordinatewise_then_product g'_def)
  then show \<open>continuous_map euclidean euclidean g'\<close>
    using continuous_map_iff_continuous2 by blast
  show \<open>g' (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) =
         (\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x \<otimes>\<^sub>o id_cblinfun))\<close> for x
    by (auto intro!: ext simp: g'_def trace_partial_trace_compose)
qed

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
      using assms 
      by (auto simp: complex_vector.linear_add register_def Modules.additive_def
          intro!: continuous_map_is_continuous_at_point complex_vector.linear_0 \<open>clinear \<Phi>\<close>)
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
  sorry
(*   unfolding at_within_def
  apply transfer_prover_start
  apply transfer_step
  apply transfer_step
      apply transfer_step
  apply transfer_step
  apply transfer_step


    apply transfer_step
  apply transfer_step

  
  sorry


  term at_within *)



(* lemma transfer_nhds_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_weak_star ===> rel_set cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star)
     (at_within_in weak_star_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: weak_star_topology_topspace)
  by transfer_prover *)

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
      where \<open>unitary U\<close> and \<open>F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    define \<delta> :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where \<open>\<delta> = selfbutter (ket (undefined))\<close>
    define u where \<open>u t = U o\<^sub>C\<^sub>L (from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L U*\<close> for t
    have [simp]: \<open>trace_class (u t)\<close> for t
      unfolding u_def
      apply (rule trace_class_comp_left)
      apply (rule trace_class_comp_right)
      (* See Lemma 31 in register paper *)
      sorry
    have uF: \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (u t o\<^sub>C\<^sub>L F a)\<close> for t a 
      (* See Lemma 38 in register paper *)
      sorry
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
