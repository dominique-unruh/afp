section \<open>\<open>Weak_Operator_Topology\<close> -- Weak operator topology on complex bounded operators\<close>

theory Weak_Operator_Topology
  imports Misc_Tensor_Product Strong_Operator_Topology
begin

unbundle cblinfun_notation

definition cweak_operator_topology::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_inner) topology"
  where "cweak_operator_topology = pullback_topology UNIV (\<lambda>a (x,y). cinner x (a *\<^sub>V y)) euclidean"

lemma cweak_operator_topology_topspace[simp]:
  "topspace cweak_operator_topology = UNIV"
  unfolding cweak_operator_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma cweak_operator_topology_basis:
  fixes f::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner)" and U::"'i \<Rightarrow> complex set" and x::"'i \<Rightarrow> 'b" and y::\<open>'i \<Rightarrow> 'a\<close>
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
  shows "openin cweak_operator_topology {f. \<forall>i\<in>I. cinner (x i) (f *\<^sub>V y i) \<in> U i}"
proof -
  have "open {g::(('b\<times>'a)\<Rightarrow>complex). \<forall>i\<in>I. g (x i, y i) \<in> U i}"
    by (rule product_topology_basis'[OF assms])
  moreover have "{f. \<forall>i\<in>I. cinner (x i) (f *\<^sub>V y i) \<in> U i}
                = (\<lambda>f (x,y). cinner x (f *\<^sub>V y))-`\<dots> \<inter> UNIV"
    by auto
  ultimately show ?thesis
    unfolding cweak_operator_topology_def by (subst openin_pullback_topology) auto
qed

lemma wot_weaker_than_sot:
  "continuous_map cstrong_operator_topology cweak_operator_topology (\<lambda>f. f)"
proof -
  have *: \<open>continuous_on UNIV ((\<lambda>z. cinner x z) o (\<lambda>f. f y))\<close> for x :: 'b and y :: 'a
    apply (rule continuous_on_compose)
    by (auto intro: continuous_on_compose continuous_at_imp_continuous_on)
  have *: \<open>continuous_map euclidean euclidean (\<lambda>f (x::'b, y::'a). x \<bullet>\<^sub>C f y)\<close>
    apply simp
    apply (rule continuous_on_coordinatewise_then_product)
    using * by auto
  have *: \<open>continuous_map (pullback_topology UNIV (*\<^sub>V) euclidean) euclidean ((\<lambda>f (x::'b, a::'a). x \<bullet>\<^sub>C f a) \<circ> (*\<^sub>V))\<close>
    apply (rule continuous_map_pullback)
    using * by simp
  have *: \<open>continuous_map (pullback_topology UNIV (*\<^sub>V) euclidean) euclidean ((\<lambda>a (x::'b, y::'a). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (\<lambda>f. f))\<close>
     apply (subst asm_rl[of \<open>((\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (\<lambda>f. f)) = (\<lambda>f (a,b). cinner a (f b)) o (*\<^sub>V)\<close>])
     using * by auto
   show ?thesis
    unfolding cstrong_operator_topology_def cweak_operator_topology_def
    apply (rule continuous_map_pullback')
    using * by auto
qed


lemma cweak_operator_topology_weaker_than_euclidean:
  "continuous_map euclidean cweak_operator_topology (\<lambda>f. f)"
  by (metis (mono_tags, lifting) continuous_map_compose continuous_map_eq cstrong_operator_topology_weaker_than_euclidean wot_weaker_than_sot o_def)


(* TODO rename *)
lemma cweak_operator_topology_continuous_evaluation:
  "continuous_map cweak_operator_topology euclidean (\<lambda>f. cinner x (f *\<^sub>V y))"
proof -
  have "continuous_map cweak_operator_topology euclidean ((\<lambda>f. f (x,y)) o (\<lambda>a (x,y). cinner x (a *\<^sub>V y)))"
    unfolding cweak_operator_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_cweak_operator_topo_iff_coordinatewise:
  "continuous_map T cweak_operator_topology f
    \<longleftrightarrow> (\<forall>x y. continuous_map T euclidean (\<lambda>z.  cinner x (f z *\<^sub>V y)))"
proof (auto)
  fix x::'c and y::'b
  assume "continuous_map T cweak_operator_topology f"
  with continuous_map_compose[OF this cweak_operator_topology_continuous_evaluation]
  have "continuous_map T euclidean ((\<lambda>f. cinner x (f *\<^sub>V y)) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>z.  cinner x (f z *\<^sub>V y))"
    unfolding comp_def by auto
next
  assume *: \<open>\<forall>x y. continuous_map T euclidean (\<lambda>z. x \<bullet>\<^sub>C (f z *\<^sub>V y))\<close>
  then have *: "continuous_map T euclidean ((\<lambda>a (x,y). cinner x (a *\<^sub>V y)) o f)"
    by (auto simp flip: euclidean_product_topology)
  show "continuous_map T cweak_operator_topology f"
    unfolding cweak_operator_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: *)
qed














typedef (overloaded) ('a,'b) cblinfun_wot = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) set\<close> ..
setup_lifting type_definition_cblinfun_wot

instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) complex_vector begin
lift_definition scaleC_cblinfun_wot :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is uminus .
lift_definition zero_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot\<close> is 0 .
lift_definition minus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is minus .
lift_definition plus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is plus .
lift_definition scaleR_cblinfun_wot :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) topological_space begin
lift_definition open_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot set \<Rightarrow> bool\<close> is \<open>openin cweak_operator_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_wot set)\<close>
    apply transfer
    by (metis cweak_operator_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_wot set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_wot set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_cweak_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_wot ===> rel_filter cr_cblinfun_wot) (nhdsin cweak_operator_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: cweak_operator_topology_topspace)
  by transfer_prover

lemma limitin_cweak_operator_topology: 
  \<open>limitin cweak_operator_topology f l F \<longleftrightarrow> (\<forall>a b. ((\<lambda>i. a \<bullet>\<^sub>C (f i *\<^sub>V b)) \<longlongrightarrow> a \<bullet>\<^sub>C (l *\<^sub>V b)) F)\<close>
  by (simp add: cweak_operator_topology_def limitin_pullback_topology tendsto_coordinatewise)

lemma filterlim_cweak_operator_topology: \<open>filterlim f (nhdsin cweak_operator_topology l) = limitin cweak_operator_topology f l\<close>
  by (auto simp: cweak_operator_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

instance cblinfun_wot :: (complex_normed_vector, complex_inner) t2_space
proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_wot\<close>
  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
  proof transfer
    fix a b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume \<open>a \<noteq> b\<close>
    then obtain \<phi> \<psi> where \<open>\<phi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>) \<noteq> \<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)\<close>
      by (meson cblinfun_eqI cinner_extensionality)
    then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> and inU': \<open>\<phi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>) \<in> U'\<close> and inV': \<open>\<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>) \<in> V'\<close> and \<open>U' \<inter> V' = {}\<close>
      by (meson hausdorff)
    define U V :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> where \<open>U = {f. \<forall>i\<in>{()}. \<phi> \<bullet>\<^sub>C (f *\<^sub>V \<psi>) \<in> U'}\<close> and \<open>V = {f. \<forall>i\<in>{()}. \<phi> \<bullet>\<^sub>C (f *\<^sub>V \<psi>) \<in> V'}\<close>
    have \<open>openin cweak_operator_topology U\<close>
      unfolding U_def apply (rule cweak_operator_topology_basis)
      using \<open>open U'\<close> by auto
    moreover have \<open>openin cweak_operator_topology V\<close>
      unfolding V_def apply (rule cweak_operator_topology_basis)
      using \<open>open V'\<close> by auto
    ultimately show \<open>\<exists>U V. openin cweak_operator_topology U \<and> openin cweak_operator_topology V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
      apply (rule_tac exI[of _ U])
      apply (rule_tac exI[of _ V])
      using inU' inV' \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def)
  qed
qed

lemma Domainp_cr_cblinfun_wot[simp]: \<open>Domainp cr_cblinfun_wot = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_wot.left_total left_totalE)

lemma Rangep_cr_cblinfun_wot[simp]: \<open>Rangep cr_cblinfun_wot = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_wot_def)

lemma transfer_euclidean_cweak_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_wot) cweak_operator_topology euclidean\<close>
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_wot ===> (=)) (openin cweak_operator_topology) (openin euclidean)\<close>
    apply (auto simp: rel_topology_def cr_cblinfun_wot_def rel_set_def intro!: rel_funI)
     apply transfer
     apply auto
     apply (meson openin_subopen subsetI)
    apply transfer
    apply auto
    by (meson openin_subopen subsetI)
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin cweak_operator_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_wot) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_wot set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_wot) U\<close>
    by (simp add: Rangep_set)
qed

lemma openin_cweak_operator_topology: \<open>openin cweak_operator_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>a (x,y). cinner x (a *\<^sub>V y)) -` V)\<close>
  by (simp add: cweak_operator_topology_def openin_pullback_topology)

lemma cweak_operator_topology_plus_cont: \<open>LIM (x,y) nhdsin cweak_operator_topology a \<times>\<^sub>F nhdsin cweak_operator_topology b.
            x + y :> nhdsin cweak_operator_topology (a + b)\<close>
proof -
  show ?thesis
    unfolding cweak_operator_topology_def
    apply (rule_tac pullback_topology_bi_cont[where f'=plus])
    by (auto simp: case_prod_unfold tendsto_add_Pair cinner_add_right cblinfun.add_left)
qed

instance cblinfun_wot :: (complex_normed_vector, complex_inner) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_wot\<close>
    apply transfer
    using cweak_operator_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have *: \<open>continuous_map cweak_operator_topology cweak_operator_topology uminus\<close>
    apply (subst continuous_on_cweak_operator_topo_iff_coordinatewise)
    apply (rewrite at \<open>(\<lambda>z. x \<bullet>\<^sub>C (- z *\<^sub>V y))\<close> in \<open>\<forall>x y. \<hole>\<close> to \<open>(\<lambda>z. - x \<bullet>\<^sub>C (z *\<^sub>V y))\<close> DEADID.rel_mono_strong)
    by (auto simp: cweak_operator_topology_continuous_evaluation cblinfun.minus_left cblinfun.minus_right)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_wot\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where s=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_wot: 
  \<open>continuous_map cweak_operator_topology cweak_operator_topology (\<lambda>a::'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close>
proof -
  have **: \<open>((\<lambda>f::'b \<times> 'a \<Rightarrow> complex. f (b* *\<^sub>V x, y)) -` B \<inter> UNIV) 
          = (Pi\<^sub>E UNIV (\<lambda>z. if z = (b* *\<^sub>V x, y) then B else UNIV))\<close> 
    for x :: 'c and y :: 'a and B :: \<open>complex set\<close>
    by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>f::'b \<times> 'a \<Rightarrow> complex. f (b* *\<^sub>V x, y))\<close> for x y
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **)
    apply (rule open_PiE)
    by auto
  have *: \<open>continuous_on UNIV (\<lambda>(f::'b \<times> 'a \<Rightarrow> complex) (x, y). f (b* *\<^sub>V x, y))\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    using * by auto
  show ?thesis
    unfolding cweak_operator_topology_def
    apply (rule continuous_map_pullback')
     apply (subst asm_rl[of \<open>((\<lambda>(a::'a\<Rightarrow>\<^sub>C\<^sub>L'c) (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (o\<^sub>C\<^sub>L) b) = (\<lambda>f (x,y). f (b* *\<^sub>V x,y)) \<circ> (\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y))\<close>])
      apply (auto intro!: ext simp: cinner_adj_left)[1]
     apply (rule continuous_map_pullback)
    using * by auto
qed

lemma continuous_map_scaleC_wot: \<open>continuous_map cweak_operator_topology cweak_operator_topology 
                         (scaleC c :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> _)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  by (rule continuous_map_left_comp_wot)

lemma continuous_scaleC_wot: \<open>continuous_on X (scaleC c :: (_::complex_normed_vector,_::chilbert_space) cblinfun_wot \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  by (rule continuous_map_scaleC_wot)

lemma wot_closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector, 'b::chilbert_space) cblinfun_wot set"
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
    using image_closure_subset[where S=A and T=\<open>closure A\<close> and f=\<open>scaleC c\<close>, OF continuous_scaleC_wot]
    apply auto
    by (metis 0 assms closure_subset csubspace_scaleC_invariant imageI in_mono scaleC_eq_0_iff)
qed


lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> (=)) (closedin cweak_operator_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] cweak_operator_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> rel_set cr_cblinfun_wot) (Abstract_Topology.closure_of cweak_operator_topology) closure\<close>
  apply (subst closure_of_hull[where X=cweak_operator_topology, unfolded cweak_operator_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma wot_closure_is_csubspace'[simp]:
  fixes A::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (cweak_operator_topology closure_of A)\<close>
  using wot_closure_is_csubspace[of \<open>Abs_cblinfun_wot ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_cweak_operator_topology:
  fixes A :: \<open>('b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner) set\<close>
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin cweak_operator_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>\<phi> \<psi>. has_sum (\<lambda>i. \<phi> \<bullet>\<^sub>C (a i *\<^sub>V \<psi>)) I (\<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>))\<close>
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
  have \<open>((\<lambda>F. \<Sum>i\<in>F. \<phi> \<bullet>\<^sub>C (a i *\<^sub>V \<psi>)) \<longlongrightarrow> \<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) (finite_subsets_at_top I)\<close> for \<psi> \<phi>
    using has_sum_def by blast
  then have \<open>limitin cweak_operator_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_cweak_operator_topology cblinfun.sum_left cinner_sum_right)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

lemma limitin_adj_wot:
  assumes \<open>limitin cweak_operator_topology f l F\<close>
  shows \<open>limitin cweak_operator_topology (\<lambda>i. (f i)*) (l*) F\<close>
proof -
  from assms
  have \<open>((\<lambda>i. a \<bullet>\<^sub>C (f i *\<^sub>V b)) \<longlongrightarrow> a \<bullet>\<^sub>C (l *\<^sub>V b)) F\<close> for a b
    by (simp add: limitin_cweak_operator_topology)
  then have \<open>((\<lambda>i. cnj (a \<bullet>\<^sub>C (f i *\<^sub>V b))) \<longlongrightarrow> cnj (a \<bullet>\<^sub>C (l *\<^sub>V b))) F\<close> for a b
    using tendsto_cnj by blast
  then have \<open>((\<lambda>i. cnj (((f i)* *\<^sub>V a) \<bullet>\<^sub>C b)) \<longlongrightarrow> cnj ((l* *\<^sub>V a) \<bullet>\<^sub>C b)) F\<close> for a b
    by (simp add: cinner_adj_left)
  then have \<open>((\<lambda>i. b \<bullet>\<^sub>C ((f i)* *\<^sub>V a)) \<longlongrightarrow> b \<bullet>\<^sub>C (l* *\<^sub>V a)) F\<close> for a b
    by simp
  then show ?thesis
    by (simp add: limitin_cweak_operator_topology)
qed

lemma hausdorff_cweak_operator_topology[simp]: \<open>hausdorff cweak_operator_topology\<close>
proof (rule hausdorffI)
  fix A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> assume \<open>A \<noteq> B\<close>
  then obtain y where \<open>A *\<^sub>V y \<noteq> B *\<^sub>V y\<close>
    by (meson cblinfun_eqI)
  then obtain x where \<open>x \<bullet>\<^sub>C (A *\<^sub>V y) \<noteq> x \<bullet>\<^sub>C (B *\<^sub>V y)\<close>
    using cinner_extensionality by blast
  then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> and inside: \<open>x \<bullet>\<^sub>C (A *\<^sub>V y) \<in> U'\<close> \<open>x \<bullet>\<^sub>C (B *\<^sub>V y) \<in> V'\<close> and disj: \<open>U' \<inter> V' = {}\<close>
    by (meson separation_t2)
  define U'' V'' where \<open>U'' = Pi\<^sub>E UNIV (\<lambda>i. if i=(x,y) then U' else UNIV)\<close> and \<open>V'' = Pi\<^sub>E UNIV (\<lambda>i. if i=(x,y) then V' else UNIV)\<close>
  from \<open>open U'\<close> \<open>open V'\<close>
  have \<open>open U''\<close> and \<open>open V''\<close>
    by (auto simp: U''_def V''_def open_fun_def intro!: product_topology_basis)
  define U V :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> where \<open>U = (\<lambda>A (x, y). x \<bullet>\<^sub>C (A *\<^sub>V y)) -` U''\<close> and \<open>V = (\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) -` V''\<close>
  have openin: \<open>openin cweak_operator_topology U\<close> \<open>openin cweak_operator_topology V\<close>
    using U_def V_def \<open>open U''\<close> \<open>open V''\<close> openin_cweak_operator_topology by blast+
  have \<open>A \<in> U\<close> \<open>B \<in> V\<close>
    using inside by (auto simp: U_def V_def U''_def V''_def)
  have \<open>U \<inter> V = {}\<close>
    using disj apply (auto simp: U_def V_def U''_def V''_def PiE_def Pi_iff)
    by (metis disjoint_iff)
  show \<open>\<exists>U V. openin cweak_operator_topology U \<and> openin cweak_operator_topology V \<and> A \<in> U \<and> B \<in> V \<and> U \<inter> V = {}\<close>
    using \<open>A \<in> U\<close> \<open>B \<in> V\<close> \<open>U \<inter> V = {}\<close> openin by blast
qed

lemma hermitian_limit_hermitian_wot:
  assumes \<open>F \<noteq> \<bottom>\<close>
  assumes herm: \<open>\<And>i. (a i)* = a i\<close>
  assumes lim: \<open>limitin cweak_operator_topology a A F\<close>
  shows \<open>A* = A\<close>
  using hausdorff_cweak_operator_topology \<open>F \<noteq> \<bottom>\<close>
  apply (rule limitin_unique[of cweak_operator_topology])
  using lim apply (rule limitin_adj_wot)
  unfolding herm by (fact lim)

lemma wot_weaker_than_sot_openin:
  \<open>openin cweak_operator_topology x \<Longrightarrow> openin cstrong_operator_topology x\<close>
  using wot_weaker_than_sot unfolding continuous_map_def by auto

lemma wot_weaker_than_sot_limitin: \<open>limitin cweak_operator_topology a A F\<close> if \<open>limitin cstrong_operator_topology a A F\<close>
  using that unfolding filterlim_cweak_operator_topology[symmetric] filterlim_cstrong_operator_topology[symmetric]
  apply (rule filterlim_mono)
   apply (rule nhdsin_mono)
  by (auto simp: wot_weaker_than_sot_openin)

(* Logically belongs in Strong_Operator_Topology, but we use hermitian_tendsto_hermitian_wot in the proof. *)
lemma hermitian_limit_hermitian_sot:
  assumes \<open>F \<noteq> \<bottom>\<close>
  assumes \<open>\<And>i. (a i)* = a i\<close>
  assumes \<open>limitin cstrong_operator_topology a A F\<close>
  shows \<open>A* = A\<close>
  using assms(1,2) apply (rule hermitian_limit_hermitian_wot[where a=a and F=F])
  using assms(3) by (rule wot_weaker_than_sot_limitin)

lemma hermitian_sum_hermitian_sot:
  assumes herm: \<open>\<And>i. (a i)* = a i\<close>
  assumes sum: \<open>has_sum_in cstrong_operator_topology a X A\<close>
  shows \<open>A* = A\<close>
proof -
  from herm have herm_sum: \<open>(sum a F)* = sum a F\<close> for F
    by (simp add: sum_adj)
  show ?thesis
    using _ herm_sum sum[unfolded has_sum_in_def]
    apply (rule hermitian_limit_hermitian_sot)
    by simp
qed

end
