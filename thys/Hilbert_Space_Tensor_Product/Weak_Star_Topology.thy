section \<open>\<open>Weak_Star_Topology\<close> -- Weak* topology on complex bounded operators\<close>

theory Weak_Star_Topology
  imports Trace_Class Weak_Operator_Topology
begin

definition weak_star_topology :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space) topology\<close>
  where \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) euclidean\<close>

lemma weak_star_topology_topspace[simp]:
  "topspace weak_star_topology = UNIV"
  unfolding weak_star_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma weak_star_topology_basis:
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  assumes tc: \<open>\<And>i. i \<in> I \<Longrightarrow> trace_class (t i)\<close>
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  have "open {g::('b\<Rightarrow>\<^sub>C\<^sub>L'a)\<Rightarrow>complex. \<forall>i\<in>I. g (t i) \<in> U i}"
    by (rule product_topology_basis'[OF assms(1,2)])
  moreover have "{a. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L a) \<in> U i}
                = (\<lambda>a t. if trace_class t then trace (t o\<^sub>C\<^sub>L a) else 0) -` \<dots> \<inter> UNIV"
    using tc by auto
  ultimately show ?thesis
    unfolding weak_star_topology_def 
    apply (subst openin_pullback_topology)
    by (meson open_openin)
qed

lemma wot_weaker_than_weak_star:
  "continuous_map weak_star_topology cweak_operator_topology (\<lambda>f. f)"
proof -
  let ?t = \<open>(\<lambda>(x::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0)\<close>
  let ?g = \<open>(\<lambda>a (x::'b, y::'a). x \<bullet>\<^sub>C (a *\<^sub>V y))\<close>
  have *: \<open>continuous_map euclidean euclidean (\<lambda>f (x::'b, y::'a). f (butterfly y x))\<close>
    apply simp
    apply (rule continuous_on_coordinatewise_then_product)
    by auto
  have *: \<open>continuous_map (pullback_topology UNIV ?t euclidean) euclidean ((\<lambda>f (x,y). f (butterfly y x)) \<circ> ?t)\<close>
    apply (rule continuous_map_pullback)
    using * by simp
  have *: \<open>continuous_map (pullback_topology UNIV ?t euclidean) euclidean
             (?g \<circ> (\<lambda>f. f))\<close>
    apply (subst asm_rl[of \<open>?g \<circ> (\<lambda>f. f) = (\<lambda>f (x,y). f (butterfly y x)) o ?t\<close>])
    using * by (auto intro!: ext simp: trace_butterfly_comp)
   show ?thesis
    unfolding cweak_operator_topology_def weak_star_topology_def
    apply (rule continuous_map_pullback')
    using * by auto
qed

(* TODO: Analogous lemmas for the other _weaker_ theorems *)
lemma wot_weaker_than_weak_star':
  \<open>openin cweak_operator_topology U \<Longrightarrow> openin weak_star_topology U\<close>
  using wot_weaker_than_weak_star[where 'a='a and 'b='b]
  by (auto simp: continuous_map_def weak_star_topology_topspace)

lemma weak_star_topology_continuous_duality:
  assumes \<open>trace_class t\<close>
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L x))"
proof -
  have "continuous_map weak_star_topology euclidean ((\<lambda>f. f t) o (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0))"
    unfolding weak_star_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  with assms
  show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_weak_star_topo_iff_coordinatewise:
  fixes f :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  shows "continuous_map T weak_star_topology f
    \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x)))"
proof (auto)
  fix t :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>trace_class t\<close>
  assume "continuous_map T weak_star_topology f"
  with continuous_map_compose[OF this weak_star_topology_continuous_duality, OF \<open>trace_class t\<close>]
  have "continuous_map T euclidean ((\<lambda>x. trace (t o\<^sub>C\<^sub>L x)) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))"
    unfolding comp_def by auto
next
  assume \<open>\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close>
  then have \<open>continuous_map T euclidean (\<lambda>x. if trace_class t then trace (t o\<^sub>C\<^sub>L f x) else 0)\<close> for t
    apply (cases \<open>trace_class t\<close>) by auto
  then have *: "continuous_map T euclidean ((\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) o f)"
    by (auto simp flip: euclidean_product_topology simp: o_def)
  show "continuous_map T weak_star_topology f"
    unfolding weak_star_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: *)
qed

lemma weak_star_topology_weaker_than_euclidean:
  "continuous_map euclidean weak_star_topology (\<lambda>f. f)"
  apply (subst continuous_on_weak_star_topo_iff_coordinatewise)
  by (auto intro!: linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_trace_duality)


typedef (overloaded) ('a,'b) cblinfun_weak_star = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> 
  morphisms from_weak_star to_weak_star ..
setup_lifting type_definition_cblinfun_weak_star

lift_definition id_weak_star :: \<open>('a::complex_normed_vector, 'a) cblinfun_weak_star\<close> is id_cblinfun .

instantiation cblinfun_weak_star :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_weak_star :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is uminus .
lift_definition zero_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star\<close> is 0 .
lift_definition minus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is minus .
lift_definition plus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is plus .
lift_definition scaleR_cblinfun_weak_star :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_space begin
lift_definition open_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star set \<Rightarrow> bool\<close> is \<open>openin weak_star_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_weak_star set)\<close>
    apply transfer
    by (metis weak_star_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_weak_star set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_weak_star set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star) (nhdsin weak_star_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: weak_star_topology_topspace)
  by transfer_prover


lemma limitin_weak_star_topology:
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>j. trace (t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L l)) F)\<close>
  by (simp add: weak_star_topology_def limitin_pullback_topology tendsto_coordinatewise)


lemma filterlim_weak_star_topology:
  \<open>filterlim f (nhdsin weak_star_topology l) = limitin weak_star_topology f l\<close>
  by (auto simp: weak_star_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

instance cblinfun_weak_star :: (chilbert_space, chilbert_space) t2_space
proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_weak_star\<close>
  assume \<open>a \<noteq> b\<close>
  then have \<open>Abs_cblinfun_wot (from_weak_star a) \<noteq> Abs_cblinfun_wot (from_weak_star b)\<close>
    by (simp add: Abs_cblinfun_wot_inject from_weak_star_inject)
  from hausdorff[OF this]

  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    apply transfer using wot_weaker_than_weak_star' by auto
qed

lemma Domainp_cr_cblinfun_weak_star[simp]: \<open>Domainp cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_weak_star.left_total left_totalE)

lemma Rangep_cr_cblinfun_weak_star[simp]: \<open>Rangep cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_weak_star_def)


lemma transfer_euclidean_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_weak_star) weak_star_topology euclidean\<close>
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (openin weak_star_topology) (openin euclidean)\<close>
    apply (auto simp: rel_topology_def cr_cblinfun_weak_star_def rel_set_def intro!: rel_funI)
     apply transfer
     apply auto
     apply (meson openin_subopen subsetI)
    apply transfer
    apply auto
    by (meson openin_subopen subsetI)
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin weak_star_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_weak_star set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Rangep_set)
qed

lemma openin_weak_star_topology: \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` V)\<close>
  by (simp add: weak_star_topology_def openin_pullback_topology)

lemma weak_star_topology_plus_cont: \<open>LIM (x,y) nhdsin weak_star_topology a \<times>\<^sub>F nhdsin weak_star_topology b.
            x + y :> nhdsin weak_star_topology (a + b)\<close>
proof -
  have trace_plus: \<open>trace (t o\<^sub>C\<^sub>L (a + b)) = trace (t o\<^sub>C\<^sub>L a) + trace (t o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and a b
    by (auto simp: cblinfun_compose_add_right trace_plus that trace_class_comp_left)
  show ?thesis
    unfolding weak_star_topology_def
    apply (rule_tac pullback_topology_bi_cont[where f'=plus])
    by (auto simp: trace_plus case_prod_unfold tendsto_add_Pair)
qed

instance cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply transfer
    using weak_star_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have \<open>continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L - x))\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using weak_star_topology_continuous_duality[of \<open>-t\<close>]
    by (auto simp: cblinfun_compose_uminus_left cblinfun_compose_uminus_right intro!: that trace_class_uminus)
  then have *: \<open>continuous_map weak_star_topology weak_star_topology (uminus :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _)\<close>
    by (auto simp: continuous_on_weak_star_topo_iff_coordinatewise)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where s=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a::'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
proof -
  let ?t = \<open>\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0\<close>
  have *: \<open>open B \<Longrightarrow> open ((*\<^sub>V) b -` B)\<close> for B
    by (simp add: continuous_open_vimage)
  (* have **: \<open>((\<lambda>a. b *\<^sub>V a \<psi>) -` B \<inter> UNIV) = (Pi\<^sub>E UNIV (\<lambda>i. if i=\<psi> then (\<lambda>a. b *\<^sub>V a) -` B else UNIV))\<close>  *)
  have **: \<open>(\<lambda>f :: _ \<Rightarrow> complex. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0) -` B \<inter> UNIV
         = (Pi\<^sub>E UNIV (\<lambda>i. if i=t o\<^sub>C\<^sub>L b then B else UNIV))\<close> 
    if \<open>trace_class t\<close>
    for t and B
    apply (cases \<open>trace_class t\<close>)
    using that by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>f :: _ \<Rightarrow> complex. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0)\<close> for t
    apply (cases \<open>trace_class t\<close>)
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **, simp)
    apply (rule open_PiE)
    using * by auto
  have *: \<open>continuous_on UNIV (\<lambda>(f :: _ \<Rightarrow> complex) t. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0)\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    by (rule *)
  show ?thesis
    unfolding weak_star_topology_def
    apply (rule continuous_map_pullback')
     apply (subst asm_rl[of \<open>?t \<circ> (o\<^sub>C\<^sub>L) b = (\<lambda>f t. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0) \<circ> ?t\<close>])
      apply (auto simp: cblinfun_assoc_left(1) intro!: ext trace_class_comp_left)[1]
     apply (rule continuous_map_pullback)
    using * by auto
qed

lemma continuous_map_right_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>b::'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  define f and g where \<open>f x t = (if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0)\<close>
    and \<open>g f' t' = (if trace_class t' then f' (a o\<^sub>C\<^sub>L t') else 0)\<close> 
      for x :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'c\<close> and t :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and f' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> complex\<close> and t' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  have gf: \<open>((\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) \<circ> (\<lambda>b. b o\<^sub>C\<^sub>L a)) = g o f\<close>
    apply (auto intro!: ext simp add: o_def trace_class_comp_right f_def g_def)
    by (metis cblinfun_compose_assoc circularity_of_trace trace_class_comp_left)
  have cont: \<open>continuous_on UNIV (\<lambda>x. g x t)\<close> for t
    apply (cases \<open>trace_class t\<close>) by (auto simp: g_def)
  have \<open>continuous_map euclidean euclidean g\<close>
   by (auto intro!: continuous_on_coordinatewise_then_product cont)
  then have \<open>continuous_map (pullback_topology UNIV f euclidean) euclidean (g \<circ> f)\<close>
    by (rule continuous_map_pullback)
  then show ?thesis
    unfolding weak_star_topology_def gf[symmetric] f_def
    apply (rule continuous_map_pullback')
    by auto
qed

lemma continuous_map_scaleC_weak_star: \<open>continuous_map weak_star_topology weak_star_topology (scaleC c)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  by (rule continuous_map_left_comp_weak_star)

lemma continuous_scaleC_weak_star: \<open>continuous_on X (scaleC c :: (_,_) cblinfun_weak_star \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  by (rule continuous_map_scaleC_weak_star)

lemma weak_star_closure_is_csubspace[simp]:
  fixes A::"('a::chilbert_space, 'b::chilbert_space) cblinfun_weak_star set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof (rule complex_vector.subspaceI)
  show 0: \<open>0 \<in> closure A\<close>
    by (simp add: assms closure_def complex_vector.subspace_0)
  show \<open>x + y \<in> closure A\<close> if \<open>x \<in> closure A\<close> \<open>y \<in> closure A\<close> for x y
  proof -
    define FF where \<open>FF = ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
    have nt: \<open>FF \<noteq> bot\<close>
      by (simp add: prod_filter_eq_bot that(1) that(2) FF_def flip: closure_nhds_principal)
    have \<open>\<forall>\<^sub>F x in FF. fst x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter fst_conv inf_sup_ord(2) le_principal)
    moreover have \<open>\<forall>\<^sub>F x in FF. snd x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter snd_conv inf_sup_ord(2) le_principal)
    ultimately have FF_plus: \<open>\<forall>\<^sub>F x in FF. fst x + snd x \<in> A\<close>
      by (smt (verit, best) assms complex_vector.subspace_add eventually_elim2)

    have \<open>(fst \<longlongrightarrow> x) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_fst_prod_filter
      using le_inf_iff by blast
    moreover have \<open>(snd \<longlongrightarrow> y) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_snd_prod_filter
      using le_inf_iff by blast
    ultimately have \<open>(id \<longlongrightarrow> (x,y)) FF\<close>
      by (simp add: filterlim_def nhds_prod prod_filter_mono FF_def)

    moreover note tendsto_add_Pair[of x y]
    ultimately have \<open>(((\<lambda>x. fst x + snd x) o id) \<longlongrightarrow> (\<lambda>x. fst x + snd x) (x,y)) FF\<close>
      unfolding filterlim_def nhds_prod
      by (smt (verit, best) filterlim_compose filterlim_def filterlim_filtermap fst_conv snd_conv tendsto_compose_filtermap)

    then have \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> (x+y)) FF\<close>
      by simp
    then show \<open>x + y \<in> closure A\<close>
      using nt FF_plus by (rule limit_in_closure)
  qed
  show \<open>c *\<^sub>C x \<in> closure A\<close> if \<open>x \<in> closure A\<close> for x c
    using  that
    using image_closure_subset[where S=A and T=\<open>closure A\<close> and f=\<open>scaleC c\<close>, OF continuous_scaleC_weak_star]
    apply auto
    by (metis 0 assms closure_subset csubspace_scaleC_invariant imageI in_mono scaleC_eq_0_iff)
qed


lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (closedin weak_star_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] weak_star_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> rel_set cr_cblinfun_weak_star) (Abstract_Topology.closure_of weak_star_topology) closure\<close>
  apply (subst closure_of_hull[where X=weak_star_topology, unfolded weak_star_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma weak_star_closure_is_csubspace'[simp]:
  fixes A::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (weak_star_topology closure_of A)\<close>
  using weak_star_closure_is_csubspace[of \<open>to_weak_star ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_weak_star_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin weak_star_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>t. trace_class t \<Longrightarrow> has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L a i)) I (trace (t o\<^sub>C\<^sub>L b))\<close>
  shows \<open>b \<in> A\<close>
proof -
  have 1: \<open>range (sum a) \<subseteq> A\<close>
  proof -
    have \<open>sum a X \<in> A\<close> for X
      apply (induction X rule:infinite_finite_induct)
      by (auto simp add: subspace complex_vector.subspace_0 aA complex_vector.subspace_add)
    then show ?thesis
      by auto
  qed

  from has_sum
  have \<open>((\<lambda>F. \<Sum>i\<in>F. trace (t o\<^sub>C\<^sub>L a i)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L b)) (finite_subsets_at_top I)\<close> if \<open>trace_class t\<close> for t
    by (auto intro: that simp: has_sum_def)
  then have \<open>limitin weak_star_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_weak_star_topology cblinfun_compose_sum_right trace_sum trace_class_comp_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

unbundle no_cblinfun_notation

end
