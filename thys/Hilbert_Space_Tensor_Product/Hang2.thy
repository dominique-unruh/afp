theory Strong_Operator_Topology
  imports Misc_Tensor_Product
begin

(* declare no_leading_Cons[rule del, simp del, iff] *)


unbundle cblinfun_notation

typedef (overloaded) ('a,'b) cblinfun_sot = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> ..
setup_lifting type_definition_cblinfun_sot

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_sot :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is uminus .
lift_definition zero_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot\<close> is 0 .
lift_definition minus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is minus .
lift_definition plus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is plus .
lift_definition scaleR_cblinfun_sot :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_space begin
lift_definition open_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot set \<Rightarrow> bool\<close> is \<open>openin cstrong_operator_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_sot set)\<close>
    apply transfer
    by (metis cstrong_operator_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_sot set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_sot set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_sot ===> rel_filter cr_cblinfun_sot) (nhdsin cstrong_operator_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: cstrong_operator_topology_topspace)
  by transfer_prover


lemma limitin_cstrong_operator_topology: 
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> (((*\<^sub>V) \<circ> f) \<longlongrightarrow> (*\<^sub>V) l) F\<close>
  by (simp add: cstrong_operator_topology_def limitin_pullback_topology)

(* TODO move *)
lemma limitin_product_topology:
  \<open>limitin (product_topology T I) f l F \<longleftrightarrow> l \<in> extensional I \<and> (\<forall>i\<in>I. limitin (T i) (\<lambda>j. f j i) (l i) F)\<close>
proof (intro iffI conjI ballI)
  assume asm: \<open>limitin (product_topology T I) f l F\<close>
  then have l_PiE: \<open>l \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))\<close>
    by (metis PiE_iff limitin_topspace topspace_product_topology)
  then show \<open>l \<in> extensional I\<close>
    using PiE_iff by blast

  fix i assume \<open>i \<in> I\<close>
  from l_PiE have l_topspace: \<open>l i \<in> topspace (T i)\<close>
    by (metis PiE_mem \<open>i \<in> I\<close>)

  from asm
  have eventually_prod: \<open>openin (product_topology T I) V \<Longrightarrow> l \<in> V \<Longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V)\<close> for V
    unfolding limitin_def by auto

  have eventually_U: \<open>\<forall>\<^sub>F x in F. f x i \<in> U\<close>
    if open_U: \<open>openin (T i) U\<close> and \<open>l i \<in> U\<close> for U
  proof -
    from open_U have U_topspace: \<open>U \<subseteq> topspace (T i)\<close>
      by (simp add: openin_closedin_eq)
    define V where \<open>V = {f \<in> \<Pi>\<^sub>E i\<in>I. topspace (T i). f i \<in> U}\<close>
    then have V_PiE: \<open>V = PiE I (\<lambda>j. if j = i then U else topspace (T j))\<close>
      apply auto
      apply (smt (verit, best) PiE_mem U_topspace subsetD)
      using PiE_mem \<open>i \<in> I\<close> by fastforce
    have \<open>openin (product_topology T I) V\<close>
      unfolding V_PiE apply (rule product_topology_basis)
      using open_U by auto
    moreover have \<open>l \<in> V\<close>
      using V_def l_PiE that(2) by blast
    ultimately have \<open>\<forall>\<^sub>F x in F. f x \<in> V\<close>
      by (rule eventually_prod)
    then show \<open>\<forall>\<^sub>F x in F. f x i \<in> U\<close>
      apply (rule eventually_mono)
      unfolding V_def by simp
  qed

  show \<open>limitin (T i) (\<lambda>j. f j i) (l i) F\<close>
    using l_topspace eventually_U unfolding limitin_def by simp
next
  assume asm: \<open>l \<in> extensional I \<and> (\<forall>i\<in>I. limitin (T i) (\<lambda>j. f j i) (l i) F)\<close>
  then have limit: \<open>limitin (T i) (\<lambda>j. f j i) (l i) F\<close> if \<open>i\<in>I\<close> for i
    using that by simp
  have l_topspace: \<open>l \<in> topspace (product_topology T I)\<close>
    by (metis PiE_iff asm limitin_topspace topspace_product_topology)
  have eventually_U: \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    if \<open>openin (product_topology T I) U\<close> and \<open>l \<in> U\<close> for U
  proof -
    from product_topology_open_contains_basis[OF that]
    obtain V where l_V: \<open>l \<in> Pi\<^sub>E I V\<close> and open_V: \<open>(\<forall>i. openin (T i) (V i))\<close>
      and finite_I0: \<open>finite {i. V i \<noteq> topspace (T i)}\<close> and \<open>Pi\<^sub>E I V \<subseteq> U\<close>
      by auto
    define I0 where \<open>I0 = {i\<in>I. V i \<noteq> topspace (T i)}\<close>
    have \<open>\<forall>\<^sub>F x in F. f x i \<in> V i\<close> if \<open>i\<in>I\<close> for i
      using limit[OF that] that unfolding limitin_def
      by (meson PiE_E open_V l_V)
    then have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>I0. f x i \<in> V i\<close>
      apply (subst eventually_ball_finite_distrib)
      by (simp_all add: I0_def finite_I0)
    have \<open>\<forall>i\<in>I-I0. f x i \<in> V i\<close> for x
      unfolding I0_def
      apply auto
      apply auto x
  qed

  show \<open>limitin (product_topology T I) f l F\<close>
    using l_topspace eventually_U unfolding limitin_def by simp
qed


lemma limitin_cstrong_operator_topology_XXX: 
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> xxx\<close>
  apply (simp add: cstrong_operator_topology_def limitin_pullback_topology 
flip: euclidean_product_topology)

  apply simp


lemma transfer_tendsto_cstrong_operator_topology[transfer_rule]: 
  includes lifting_syntax
  shows \<open>((R ===> cr_cblinfun_sot) ===> cr_cblinfun_sot ===> rel_filter R ===> (=)) (limitin cstrong_operator_topology) tendsto\<close>
  apply transfer_prover_start
    apply transfer_step
   apply transfer_step
  oops

lemma filterlim_cstrong_operator_topology: \<open>filterlim f (nhdsin cstrong_operator_topology l) = limitin cstrong_operator_topology f l\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin cstrong_operator_topology_topspace
  apply (intro ext)
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) t2_space
proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_sot\<close>
  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
  proof transfer
    fix a b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume \<open>a \<noteq> b\<close>
    then obtain \<psi> where \<open>a *\<^sub>V \<psi> \<noteq> b *\<^sub>V \<psi>\<close>
      by (meson cblinfun_eqI)
    then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> \<open>a *\<^sub>V \<psi> \<in> U'\<close> \<open>b *\<^sub>V \<psi> \<in> V'\<close> \<open>U' \<inter> V' = {}\<close>
      by (meson hausdorff)
    define U V where \<open>U = {f. \<forall>i\<in>{()}. f *\<^sub>V \<psi> \<in> U'}\<close> and \<open>V = {f. \<forall>i\<in>{()}. f *\<^sub>V \<psi> \<in> V'}\<close>
    have \<open>openin cstrong_operator_topology U\<close>
      unfolding U_def apply (rule cstrong_operator_topology_basis)
      using \<open>open U'\<close> by auto
    moreover have \<open>openin cstrong_operator_topology V\<close>
      unfolding V_def apply (rule cstrong_operator_topology_basis)
      using \<open>open V'\<close> by auto
    ultimately show \<open>\<exists>U V. openin cstrong_operator_topology U \<and> openin cstrong_operator_topology V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
      apply (rule_tac exI[of _ U])
      apply (rule_tac exI[of _ V])
      using  \<open>a *\<^sub>V \<psi> \<in> U'\<close> \<open>b *\<^sub>V \<psi> \<in> V'\<close> \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def)
  qed
qed

lemma transfer_euclidean_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_sot) cstrong_operator_topology euclidean\<close>
  apply (auto simp: rel_topology_def cr_cblinfun_sot_def rel_set_def
intro!: rel_funI)
   apply transfer
   apply auto
   apply (meson openin_subopen subsetI)
  apply transfer
  apply auto
  by (meson openin_subopen subsetI)

lemma openin_cstrong_operator_topology: \<open>openin cstrong_operator_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (*\<^sub>V) -` V)\<close>
  by (simp add: cstrong_operator_topology_def openin_pullback_topology)


lemma cstrong_operator_topology_plus_cont: \<open>LIM x nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b.
            fst x + snd x :> nhdsin cstrong_operator_topology (a + b)\<close>
proof -
  have 1: \<open>nhdsin cstrong_operator_topology a = filtercomap cblinfun_apply (nhds (cblinfun_apply a))\<close>
    for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (auto simp add: filter_eq_iff eventually_filtercomap eventually_nhds eventually_nhdsin
        cstrong_operator_topology_topspace openin_cstrong_operator_topology)

  have \<open>(((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) \<longlongrightarrow> (*\<^sub>V) (a + b))
     (nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b)\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>(*\<^sub>V) (a + b) \<in> S\<close>
    obtain U where \<open>(*\<^sub>V) (a + b) \<in> Pi\<^sub>E UNIV U\<close> and openU: \<open>\<forall>i. openin euclidean (U i)\<close>
      and finiteD: \<open>finite {i. U i \<noteq> topspace euclidean}\<close> and US: \<open>Pi\<^sub>E UNIV U \<subseteq> S\<close>
      using product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>(*\<^sub>V) (a + b) \<in> S\<close>]
      by auto

    define D where \<open>D = {i. U i \<noteq> UNIV}\<close>
    with finiteD have \<open>finite D\<close>
      by auto

    from openU have openU: \<open>open (U i)\<close> for i
      by auto

    have \<open>a *\<^sub>V i + b *\<^sub>V i \<in> U i\<close> for i
      by (metis PiE_mem \<open>(*\<^sub>V) (a + b) \<in> Pi\<^sub>E UNIV U\<close> iso_tuple_UNIV_I plus_cblinfun.rep_eq)

    then have \<open>\<forall>\<^sub>F x in nhds (a *\<^sub>V i) \<times>\<^sub>F nhds (b *\<^sub>V i).
            (fst x + snd x) \<in> U i\<close> for i
      using openU tendsto_add_Pair tendsto_def by fastforce

    then obtain Pa Pb where \<open>eventually (Pa i) (nhds (a *\<^sub>V i))\<close> and \<open>eventually (Pb i) (nhds (b *\<^sub>V i))\<close>
      and PaPb_plus: \<open>(\<forall>x y. Pa i x \<longrightarrow> Pb i y \<longrightarrow> fst (x, y) + snd (x, y) \<in> U i)\<close> 
    for i
      unfolding eventually_prod_filter
      by metis

    from \<open>\<And>i. eventually (Pa i) (nhds (a *\<^sub>V i))\<close>
    obtain Ua where \<open>open (Ua i)\<close> and a_Ua: \<open>a *\<^sub>V i \<in> Ua i\<close> and Ua_Pa: \<open>Ua i \<subseteq> Collect (Pa i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    from \<open>\<And>i. eventually (Pb i) (nhds (b *\<^sub>V i))\<close>
    obtain Ub where \<open>open (Ub i)\<close> and b_Ub: \<open>b *\<^sub>V i \<in> Ub i\<close> and Ub_Pb: \<open>Ub i \<subseteq> Collect (Pb i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    have UaUb_plus: \<open>x \<in> Ua i \<Longrightarrow> y \<in> Ub i \<Longrightarrow> x + y \<in> U i\<close> for i x y
      by (metis PaPb_plus Ua_Pa Ub_Pb fst_eqD mem_Collect_eq snd_conv subsetD)

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
    have a_Ua': \<open>a *\<^sub>V i \<in> Ua' i\<close> for i
      by (simp add: Ua'_def a_Ua)
    have b_Ub': \<open>b *\<^sub>V i \<in> Ub' i\<close> for i
      by (simp add: Ub'_def b_Ub)
    have UaUb'_plus: \<open>a \<in> Ua' i \<Longrightarrow> b \<in> Ub' i \<Longrightarrow> a + b \<in> U i\<close> for i a b
      apply (cases \<open>i \<in> D\<close>)
      using UaUb_plus by (auto simp add: Ua'_def  Ub'_def D_def)

    define Ua'' where \<open>Ua'' = Pi UNIV Ua'\<close>
    define Ub'' where \<open>Ub'' = Pi UNIV Ub'\<close>

    have \<open>open Ua''\<close>
      using finiteD Ua'_UNIV
      apply (auto simp add: openin_cstrong_operator_topology open_fun_def Ua''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ua'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have \<open>open Ub''\<close>
      using finiteD Ub'_UNIV
      apply (auto simp add: openin_cstrong_operator_topology open_fun_def Ub''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ub'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have a_Ua'': \<open>cblinfun_apply a \<in> Ua''\<close>
      by (simp add: Ua''_def a_Ua')
    have b_Ub'': \<open>cblinfun_apply b \<in> Ub''\<close>
      by (simp add: Ub''_def b_Ub')
    have UaUb''_plus: \<open>a \<in> Ua'' \<Longrightarrow> b \<in> Ub'' \<Longrightarrow> a i + b i \<in> U i\<close> for i a b
      using UaUb'_plus apply (auto simp add: Ua''_def  Ub''_def)
      by blast

    define Ua''' where \<open>Ua''' = cblinfun_apply -` Ua''\<close>
    define Ub''' where \<open>Ub''' = cblinfun_apply -` Ub''\<close>
    have \<open>openin cstrong_operator_topology Ua'''\<close>
      using \<open>open Ua''\<close> by (auto simp: openin_cstrong_operator_topology Ua'''_def)
    have \<open>openin cstrong_operator_topology Ub'''\<close>
      using \<open>open Ub''\<close> by (auto simp: openin_cstrong_operator_topology Ub'''_def)
    have a_Ua'': \<open>a \<in> Ua'''\<close>
      by (simp add: Ua'''_def a_Ua'')
    have b_Ub'': \<open>b \<in> Ub'''\<close>
      by (simp add: Ub'''_def b_Ub'')
    have UaUb'''_plus: \<open>a \<in> Ua''' \<Longrightarrow> b \<in> Ub''' \<Longrightarrow> a *\<^sub>V i + b *\<^sub>V i \<in> U i\<close> for i a b
      by (simp add: Ua'''_def UaUb''_plus Ub'''_def)

    define Pa' where \<open>Pa' a \<longleftrightarrow> a \<in> Ua'''\<close> for a
    define Pb' where \<open>Pb' b \<longleftrightarrow> b \<in> Ub'''\<close> for b

    have Pa'_nhd: \<open>eventually Pa' (nhdsin cstrong_operator_topology a)\<close>
      using \<open>openin cstrong_operator_topology Ua'''\<close>
      by (auto simp add: Pa'_def eventually_nhdsin intro!: exI[of _ \<open>Ua'''\<close>] a_Ua'')
    have Pb'_nhd: \<open>eventually Pb' (nhdsin cstrong_operator_topology b)\<close>
      using \<open>openin cstrong_operator_topology Ub'''\<close>
      by (auto simp add: Pb'_def eventually_nhdsin intro!: exI[of _ \<open>Ub'''\<close>] b_Ub'')
    have Pa'Pb'_plus: \<open>((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) (a, b) \<in> S\<close> if \<open>Pa' a\<close> \<open>Pb' b\<close> for a b
      using that UaUb'''_plus US
      by (auto simp add: Pa'_def Pb'_def PiE_UNIV_domain Pi_iff cblinfun.add_left[THEN ext])

    show \<open>\<forall>\<^sub>F x in nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b.
            ((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) x \<in> S\<close>
      using Pa'_nhd Pb'_nhd Pa'Pb'_plus
      unfolding eventually_prod_filter
      apply (rule_tac exI[of _ Pa'])
      apply (rule_tac exI[of _ Pb'])
      by simp
  qed
  then show ?thesis
    unfolding 1 filterlim_filtercomap_iff by -
qed

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_sot\<close>
    apply transfer
    by (rule cstrong_operator_topology_plus_cont)

  have *: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology uminus\<close>
    apply (subst continuous_on_cstrong_operator_topo_iff_coordinatewise)
    apply (rewrite at \<open>(\<lambda>y. - y *\<^sub>V x)\<close> in \<open>\<forall>x. \<hole>\<close> to \<open>(\<lambda>y. y *\<^sub>V - x)\<close> DEADID.rel_mono_strong)
    by (auto simp: cstrong_operator_topology_continuous_evaluation cblinfun.minus_left cblinfun.minus_right)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_sot\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where s=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_sot: 
  \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (\<lambda>a::'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close>
proof -
  have *: \<open>open B \<Longrightarrow> open ((*\<^sub>V) b -` B)\<close> for B
    by (simp add: continuous_open_vimage)
  have **: \<open>((\<lambda>a. b *\<^sub>V a \<psi>) -` B \<inter> UNIV) = (Pi\<^sub>E UNIV (\<lambda>i. if i=\<psi> then (\<lambda>a. b *\<^sub>V a) -` B else UNIV))\<close> 
    for \<psi> :: 'a and B
    by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>(a::'a \<Rightarrow> 'b). b *\<^sub>V  (a \<psi>))\<close> for \<psi>
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **)
    apply (rule open_PiE)
    using * by auto
  have *: \<open>continuous_on UNIV (\<lambda>(a::'a \<Rightarrow> 'b) \<psi>. b *\<^sub>V  a \<psi>)\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    by (rule *)
  show ?thesis
    unfolding cstrong_operator_topology_def
    apply (rule continuous_map_pullback')
     apply (subst asm_rl[of \<open>(*\<^sub>V) \<circ> (o\<^sub>C\<^sub>L) b = (\<lambda>a x. b *\<^sub>V (a x)) \<circ> (*\<^sub>V)\<close>])
      apply (auto intro!: ext)[1]
     apply (rule continuous_map_pullback)
    using * by auto
qed

lemma continuous_map_scaleC_sot: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (scaleC c)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  by (rule continuous_map_left_comp_sot)

lemma continuous_scaleC_sot: \<open>continuous_on X (scaleC c :: (_,_) cblinfun_sot \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  by (rule continuous_map_scaleC_sot)

lemma sot_closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun_sot set"
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
    using image_closure_subset[where S=A and T=\<open>closure A\<close> and f=\<open>scaleC c\<close>, OF continuous_scaleC_sot]
    apply auto
    by (metis 0 assms closure_subset csubspace_scaleC_invariant imageI in_mono scaleC_eq_0_iff)
qed


lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) (closedin cstrong_operator_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] cstrong_operator_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> rel_set cr_cblinfun_sot) (Abstract_Topology.closure_of cstrong_operator_topology) closure\<close>
  apply (subst closure_of_hull[where X=cstrong_operator_topology, unfolded cstrong_operator_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma sot_closure_is_csubspace'[simp]:
  fixes A::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (cstrong_operator_topology closure_of A)\<close>
  using sot_closure_is_csubspace[of \<open>Abs_cblinfun_sot ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_cstrong_operator_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin cstrong_operator_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>\<psi>. has_sum (\<lambda>i. a i *\<^sub>V \<psi>) I (b *\<^sub>V \<psi>)\<close>
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
  have \<open>((\<lambda>F. \<Sum>i\<in>F. a i *\<^sub>V \<psi>) \<longlongrightarrow> b *\<^sub>V \<psi>) (finite_subsets_at_top I)\<close> for \<psi>
    using has_sum_def by blast
  then have \<open>limitin cstrong_operator_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_cstrong_operator_topology tendsto_coordinatewise cblinfun.sum_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed


unbundle no_cblinfun_notation


end