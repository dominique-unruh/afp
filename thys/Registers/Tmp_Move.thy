(* Collecting stuff to move here *)
theory Tmp_Move
  imports
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    "HOL-Types_To_Sets.T2_Spaces"
begin

declare [[show_sorts=false]]
\<comment> \<open>\<^theory>\<open>HOL-Types_To_Sets.T2_Spaces\<close> leaves @{attribute show_sorts} enabled.\<close>

unbundle lattice_syntax

subsection \<open>Retrieving axioms\<close>

attribute_setup axiom = \<open>Scan.lift Parse.name >> (fn name => Thm.rule_attribute [] 
    (fn context => fn _ => Thm.axiom (Context.theory_of context) name))\<close>
  \<comment> \<open>Retrieves an axiom by name. E.g., write @{thm [source] [[axiom HOL.refl]]}.
      The fully qualified name is required.\<close>

subsection \<open>\<open>csubspace.with\<close>\<close>

unoverload_definition complex_vector.subspace_def

lemma csubspace_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(T ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> (=)) 
    csubspace.with
    csubspace.with"
  unfolding csubspace.with_def 
  apply transfer_prover_start
       apply transfer_step+
  by simp

lemma csubspace_nonempty: \<open>csubspace V \<Longrightarrow> V \<noteq> {}\<close>
  using complex_vector.subspace_0 by auto

subsection \<open>\<open>is_ortho_set.with\<close>\<close>

unoverload_definition is_ortho_set_def

lemma is_ortho_set_with_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> T ===> rel_set T ===> (=)) 
    is_ortho_set.with
    is_ortho_set.with"
  unfolding is_ortho_set.with_def
  by transfer_prover

subsection \<open>\<open>class.semigroup_add\<close>\<close>


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

lemma semigroup_add_on_typeclass[simp]: \<open>semigroup_add_on V (+)\<close> for V :: \<open>_::semigroup_add set\<close>
  by (auto simp: semigroup_add_on_def ordered_field_class.sign_simps)

subsection \<open>\<open>class.ab_semigroup_add\<close>\<close>

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

lemma ab_semigroup_add_on_typeclass[simp]: \<open>ab_semigroup_add_on V (+)\<close> for V :: \<open>_::ab_semigroup_add set\<close>
  by (auto simp: ab_semigroup_add_on_def Groups.add_ac)

subsection \<open>\<open>class.comm_monoid_add\<close>\<close>

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

lemma comm_monoid_add_on_typeclass[simp]: \<open>comm_monoid_add_on V (+) 0\<close> for V :: \<open>_::comm_monoid_add set\<close>
  by (auto simp: comm_monoid_add_on_def)

subsection \<open>\<open>class.ab_group_add\<close>\<close>

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

lemma ab_group_add_on_typeclass[simp]: \<open>ab_group_add_on V (+) 0 (-) uminus\<close> for V :: \<open>_::ab_group_add set\<close>
  by (auto simp: ab_group_add_on_def)

subsection \<open>\<open>class.scaleC\<close>\<close>

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

lemma scaleC_on_typeclass[simp]: \<open>scaleC_on V (*\<^sub>R) (*\<^sub>C)\<close>
  by (auto simp: scaleC_on_def scaleR_scaleC)

subsection \<open>\<open>class.complex_vector\<close>\<close>

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

lemma complex_vector_on_typeclass[simp]: 
  \<open>complex_vector_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus\<close> for V :: \<open>_::complex_vector set\<close>
  by (auto simp add: complex_vector_on_def complex_vector.vector_space_assms)


subsection \<open>class.open_uniformity\<close>

definition \<open>open_uniformity_on A open uniformity \<longleftrightarrow>
  (\<forall>U\<subseteq>A. open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U))\<close>
  for A "open" uniformity

lemma class_open_uniformity_transfer[transfer_rule]:
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

subsection \<open>\<open>class.uniformity_dist\<close>\<close>

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

definition \<open>uniformity_dist_on A dist uniformity \<longleftrightarrow>
        uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>A\<times>A. dist x y < e})\<close>
  for dist uniformity

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

lemma uniformity_dist_on_typeclass[simp]: \<open>uniformity_dist_on V dist (uniformity_on V)\<close> for V :: \<open>_::uniformity_dist set\<close>
  apply (auto simp add: uniformity_dist_on_def uniformity_dist simp flip: INF_inf_const2)
  apply (subst asm_rl[of \<open>\<And>x. Restr {(xa, y). dist xa y < x} V = {(xa, y). xa \<in> V \<and> y \<in> V \<and> dist xa y < x}\<close>, rule_format])
  by auto

subsection \<open>\<open>class.sgn_div_norm\<close>\<close>

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

lemma sgn_div_norm_on_typeclass[simp]: \<open>sgn_div_norm_on V sgn norm (*\<^sub>R)\<close> for V :: \<open>_::sgn_div_norm set\<close>
  by (auto simp add: sgn_div_norm_on_def sgn_div_norm)

subsection \<open>\<open>class.dist_norm\<close>\<close>

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

lemma dist_norm_on_typeclass[simp]: \<open>dist_norm_on V (-) dist norm\<close> for V :: \<open>_::dist_norm set\<close>
  by (auto simp add: dist_norm_on_def dist_norm)

subsection \<open>\<open>class.complex_inner\<close>\<close>


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


lemma complex_inner_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>closed V\<close>
  shows \<open>complex_inner_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  apply (auto simp: assms complex_inner_on_def cinner_simps)
  using norm_eq_sqrt_cinner by blast

subsection \<open>\<open>class.metric_space\<close>\<close>

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

lemma metric_space_on_typeclass[simp]:
  fixes V :: \<open>_::metric_space set\<close>
  assumes \<open>closed V\<close>
  shows \<open>metric_space_on V dist (uniformity_on V) (openin (top_of_set V))\<close>
  by (auto simp: assms metric_space_on_def class.metric_space_axioms_def dist_triangle2)

subsection \<open>\<open>topological_space.nhds\<close>\<close>

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

lemma nhds_on_topology[simp]: \<open>nhds_on (topspace T) (openin T) x = nhdsin T x\<close> if \<open>x \<in> topspace T\<close>
  using that apply (auto intro!: ext simp add: nhds_on_def[abs_def] nhdsin_def[abs_def])
   apply (subst INF_inf_const2[symmetric])
  using openin_subset by (auto intro!: INF_cong)

subsection \<open>\<open>filterlim\<close>\<close>

(* TODO: duplicated with Misc_Tensor_Product *)
lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover


subsection \<open>\<open>topological_space.convergent\<close>\<close>

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

(* TODO: Duplicated with Misc_Tensor_Product *)
lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin 
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)


lemma convergent_on_topology[simp]:
  \<open>convergent_on (topspace T) (openin T) f \<longleftrightarrow> (\<exists>l. limitin T f l sequentially)\<close>
  by (auto simp: convergent_on_def simp flip: filterlim_nhdsin_iff_limitin)

lemma convergent_on_typeclass[simp]:
  \<open>convergent_on V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. limitin (top_of_set V) f l sequentially)\<close>
  by (simp add: flip: convergent_on_topology)

subsection \<open>\<open>uniform_space.cauchy_filter\<close>\<close>

lemma cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> rel_filter T ===> (=)) 
    uniform_space.cauchy_filter
    uniform_space.cauchy_filter"
  unfolding [[axiom Topological_Spaces.uniform_space.cauchy_filter_def_raw]]
  by transfer_prover

subsection \<open>\<open>uniform_space.Cauchy\<close>\<close>


lemma Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> ((=) ===> T) ===> (=)) 
    uniform_space.Cauchy
    uniform_space.Cauchy"
  unfolding [[axiom Topological_Spaces.uniform_space.Cauchy_uniform_raw]]
  using filtermap_parametric[transfer_rule] apply fail?
  by transfer_prover

subsection \<open>\<open>class.complete_space\<close>\<close>

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

lemma complete_space_as_set[simp]: \<open>complete (space_as_set V)\<close> for V :: \<open>_::cbanach ccsubspace\<close>
  by (simp add: complete_eq_closed)

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

subsection \<open>\<open>class.chilbert_space\<close>\<close>

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

lemma chilbert_space_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>complete V\<close>
  shows \<open>chilbert_space_on V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn
     (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  by (auto simp: chilbert_space_on_def assms complete_imp_closed)

subsection \<open>\<open>hull\<close>\<close>

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


subsection \<open>\<open>cspan.with\<close>\<close>


unoverload_definition complex_vector.span_def

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

lemma cspan_on_typeclass: \<open>cspan_on V 0 (+) (*\<^sub>C) B = cspan B \<inter> V\<close> if \<open>csubspace V\<close> and \<open>B \<subseteq> V\<close>
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

subsubsection \<open>\<^const>\<open>closure\<close>\<close>

unoverload_definition closure_def[unfolded islimpt_def]

definition closure_on_with where \<open>closure_on_with A opn S = 
  S \<union> {x\<in>A. \<forall>T\<subseteq>A. x \<in> T \<longrightarrow> opn T \<longrightarrow> (\<exists>y\<in>S. y \<in> T \<and> y \<noteq> x)}\<close>

lemma closure_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T ===> rel_set T)
         (closure_on_with (Collect (Domainp T))) closure.with"
  unfolding closure.with_def closure_on_with_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Pow_def Ball_Collect[symmetric] Ball_def Bex_def mem_Collect_eq
  by blast

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

subsection \<open>\<open>is_onb.with\<close>\<close>

lemma is_onb_def_no_ccsubspace:
  \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = UNIV\<close>
  unfolding is_onb_def apply transfer by simp

unoverload_definition is_onb_def_no_ccsubspace

definition \<open>is_onb_on A cinner zero norm open plus scaleC E \<longleftrightarrow>
        is_ortho_set.with cinner zero E \<and>
        (\<forall>b\<in>E. norm b = 1) \<and>
        closure_on_with A open (cspan_on A zero plus scaleC E) = A\<close>
  for A cinner zero norm "open" plus scaleC E

lemma is_onb_with_transfer[transfer_rule]:
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


subsection \<open>Transferring a theorem\<close>

(* The original theorem: *)
print_statement orthonormal_basis_exists

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
    by (simp add: is_onb_on_def \<open>B \<subseteq> space_as_set V\<close> cspan_on_typeclass closure_on_with_typeclass)
  then have \<open>ccspan B = V\<close>
    by (simp add: ccspan.abs_eq space_as_set_inverse)

  ultimately show ?thesis
    using \<open>S \<subseteq> B\<close> by auto
qed


end
