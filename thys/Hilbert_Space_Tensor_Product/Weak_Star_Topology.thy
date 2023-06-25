section \<open>\<open>Weak_Star_Topology\<close> -- Weak* topology on complex bounded operators\<close>

theory Weak_Star_Topology
  imports Trace_Class Weak_Operator_Topology Misc_Tensor_Product_TTS
begin

definition weak_star_topology :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space) topology\<close>
  where \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))
                              (product_topology (\<lambda>_. euclidean)  (Collect trace_class))\<close>

(* lemma open_map_basisI:
  assumes \<open>\<And>U. openin\<close>
  shows \<open>open_map f T U\<close> *)

(* lift_definition map_topology :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a topology \<Rightarrow> 'b topology)\<close> is undefined . *)


lemma open_map_product_topology_reindex:
  fixes \<pi> :: \<open>'b \<Rightarrow> 'a\<close>
  assumes bij_\<pi>: \<open>bij_betw \<pi> B A\<close> and ST: \<open>\<And>x. x\<in>B \<Longrightarrow> S x = T (\<pi> x)\<close>
  assumes g_def: \<open>\<And>f. g f = restrict (f o \<pi>) B\<close>
  shows \<open>open_map (product_topology T A) (product_topology S B) g\<close>
proof -
  define \<pi>' g' where \<open>\<pi>' = inv_into B \<pi>\<close> and \<open>g' f = restrict (f \<circ> \<pi>') A\<close> for f :: \<open>'b \<Rightarrow> 'c\<close>
  have bij_g: \<open>bij_betw g (Pi\<^sub>E A V) (Pi\<^sub>E B (V \<circ> \<pi>))\<close> for V
    apply (rule bij_betw_byWitness[where f'=g'])
       apply (auto simp: g'_def g_def \<pi>'_def)
       apply (smt (verit, best) PiE_restrict bij_\<pi> bij_betw_imp_surj_on bij_betw_inv_into_right comp_eq_dest_lhs inv_into_into restrict_def restrict_ext)
      apply (smt (verit, ccfv_SIG) PiE_restrict bij_\<pi> bij_betwE bij_betw_inv_into_left comp_apply restrict_apply restrict_ext)
     apply (meson PiE_E bij_\<pi> bij_betw_apply)
    by (smt (verit, best) PiE_mem bij_\<pi> bij_betw_imp_surj_on bij_betw_inv_into_right comp_apply inv_into_into)
  have open_gU: \<open>openin (product_topology S B) (g ` U)\<close> if \<open>openin (product_topology T A) U\<close> for U
  proof -
    from product_topology_open_contains_basis[OF that]
    obtain V where xAV: \<open>x \<in> PiE A (V x)\<close> and openV: \<open>openin (T a) (V x a)\<close> and finiteV: \<open>finite {a. V x a \<noteq> topspace (T a)}\<close>
      and AVU: \<open>Pi\<^sub>E A (V x) \<subseteq> U\<close> if \<open>x \<in> U\<close> for x a
      apply atomize_elim
      apply (rule choice4)
      by meson
    define V' where \<open>V' x b = (if b \<in> B then V x (\<pi> b) else topspace (S b))\<close> for b x
    have PiEV': \<open>Pi\<^sub>E B (V x \<circ> \<pi>) = Pi\<^sub>E B (V' x)\<close> for x
      by (metis (mono_tags, opaque_lifting) PiE_cong V'_def comp_def)
    from xAV AVU have AVU': \<open>(\<Union>x\<in>U. Pi\<^sub>E A (V x)) = U\<close>
      by blast
    have openVb: \<open>openin (S b) (V' x b)\<close> if [simp]: \<open>x \<in> U\<close> for x b
      by (auto simp: ST V'_def intro!: openV)
    have \<open>bij_betw \<pi>' {a\<in>A. V x a \<noteq> topspace (T a)} {b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)}\<close> for x
      apply (rule bij_betw_byWitness[where f'=\<pi>])
         apply simp
         apply (metis \<pi>'_def bij_\<pi> bij_betw_inv_into_right)
      using \<pi>'_def bij_\<pi> bij_betw_imp_inj_on apply fastforce
       apply (smt (verit, best) ST \<pi>'_def bij_\<pi> bij_betw_imp_surj_on comp_apply f_inv_into_f image_Collect_subsetI inv_into_into mem_Collect_eq)
      using ST bij_\<pi> bij_betwE by fastforce

    then have \<open>finite {b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      apply (rule bij_betw_finite[THEN iffD1])
      using that finiteV
      by simp
    also have \<open>{b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)} = {b. V' x b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      by (auto simp: V'_def)
    finally have finiteV\<pi>: \<open>finite {b. V' x b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      using that by -
    from openVb finiteV\<pi>
    have \<open>openin (product_topology S B) (Pi\<^sub>E B (V' x))\<close> if [simp]: \<open>x \<in> U\<close> for x
      by (auto intro!: product_topology_basis)
    with bij_g PiEV' have \<open>openin (product_topology S B) (g ` (Pi\<^sub>E A (V x)))\<close> if \<open>x \<in> U\<close> for x
      by (metis bij_betw_imp_surj_on that)
    then have \<open>openin (product_topology S B) (\<Union>x\<in>U. (g ` (Pi\<^sub>E A (V x))))\<close>
      by blast
    with AVU' show \<open>openin (product_topology S B) (g ` U)\<close>
      by (metis image_UN)
  qed
  show \<open>open_map (product_topology T A) (product_topology S B) g\<close>
    by (simp add: open_gU open_map_def)
qed

lemma homeomorphic_map_product_topology_reindex:
  fixes \<pi> :: \<open>'b \<Rightarrow> 'a\<close>
  assumes big_\<pi>: \<open>bij_betw \<pi> B A\<close> and ST: \<open>\<And>x. x\<in>B \<Longrightarrow> S x = T (\<pi> x)\<close>
  assumes g_def: \<open>\<And>f. g f = restrict (f o \<pi>) B\<close>
  shows \<open>homeomorphic_map (product_topology T A) (product_topology S B) g\<close>
proof (rule bijective_open_imp_homeomorphic_map)
  show open_map: \<open>open_map (product_topology T A) (product_topology S B) g\<close>
    using assms by (rule open_map_product_topology_reindex)
  define \<pi>' g' where \<open>\<pi>' = inv_into B \<pi>\<close> and \<open>g' f = restrict (f \<circ> \<pi>') A\<close> for f :: \<open>'b \<Rightarrow> 'c\<close>
  have \<open>bij_betw \<pi>' A B\<close>
    by (simp add: \<pi>'_def big_\<pi> bij_betw_inv_into)

  have l1: \<open>x \<in> (\<lambda>x. restrict (x \<circ> \<pi>) B) ` (\<Pi>\<^sub>E i\<in>A. topspace (T i))\<close> if \<open>x \<in> (\<Pi>\<^sub>E i\<in>B. topspace (S i))\<close> for x
  proof -
    have \<open>g' x \<in> (\<Pi>\<^sub>E i\<in>A. topspace (T i))\<close>
      by (smt (z3) g'_def PiE_mem \<pi>'_def assms(1) assms(2) bij_betw_imp_surj_on bij_betw_inv_into_right comp_apply inv_into_into restrict_PiE_iff that)
    moreover have \<open>x = restrict (g' x \<circ> \<pi>) B\<close>
      by (smt (verit) PiE_restrict \<pi>'_def assms(1) bij_betwE bij_betw_inv_into_left comp_apply restrict_apply restrict_ext that g'_def)
    ultimately show ?thesis
      apply (rule_tac rev_image_eqI)
      by assumption+
  qed
  show topspace: \<open>g ` topspace (product_topology T A) = topspace (product_topology S B)\<close>
    apply (auto simp add: l1 g_def[abs_def])
    by (metis PiE_mem assms(1) assms(2) bij_betw_apply)

  show \<open>inj_on g (topspace (product_topology T A))\<close>
    apply (simp add: g_def[abs_def])
    by (smt (verit) PiE_ext assms(1) bij_betw_iff_bijections comp_apply inj_on_def restrict_apply') 
  
  have open_map_g': \<open>open_map (product_topology S B) (product_topology T A) g'\<close>
    using \<open>bij_betw \<pi>' A B\<close> apply (rule open_map_product_topology_reindex)
     apply (metis ST \<pi>'_def big_\<pi> bij_betw_imp_surj_on bij_betw_inv_into_right inv_into_into)
    using g'_def by blast
  have g'g: \<open>g' (g x) = x\<close> if \<open>x \<in> topspace (product_topology T A)\<close> for x
    using that
    apply (auto simp: g'_def g_def)
    by (smt (verit) PiE_restrict \<open>bij_betw \<pi>' A B\<close> \<pi>'_def big_\<pi> bij_betwE bij_betw_inv_into_right comp_def restrict_apply' restrict_ext)
  have gg': \<open>g (g' x) = x\<close> if \<open>x \<in> topspace (product_topology S B)\<close> for x
    apply (auto simp: g'_def g_def)
    by (metis (no_types, lifting) g'_def f_inv_into_f g'g g_def inv_into_into that topspace)

  from open_map_g'
  have \<open>openin (product_topology T A) (g' ` U)\<close> if \<open>openin (product_topology S B) U\<close> for U
    using open_map_def that by blast
  also have \<open>g' ` U = (g -` U) \<inter> (topspace (product_topology T A))\<close> if \<open>openin (product_topology S B) U\<close> for U
  proof -
    from that
    have U_top: \<open>U \<subseteq> topspace (product_topology S B)\<close>
      using openin_subset by blast
    from topspace
    have topspace': \<open>topspace (product_topology T A) = g' ` topspace (product_topology S B)\<close>
      by (metis (no_types, lifting) bij_betw_byWitness bij_betw_imp_surj_on g'g gg' open_map open_map_g' open_map_imp_subset_topspace)

    show ?thesis
      unfolding topspace'
      using U_top gg' 
      by auto
  qed
  finally have open_gU2: \<open>openin (product_topology T A) ((g -` U) \<inter> (topspace (product_topology T A)))\<close>
    if \<open>openin (product_topology S B) U\<close> for U
  using that by blast

  then show \<open>continuous_map (product_topology T A) (product_topology S B) g\<close>
    by (metis topspace continuous_map_alt open_gU2 openin_subset openin_topspace)
qed

lemma weak_star_topology_def':
  \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
proof -
  define f g where \<open>f x = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))\<close> and \<open>g f' = f' o from_trace_class\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and f' :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex\<close>
  have \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) (product_topology (\<lambda>_. euclidean) UNIV) g\<close>
    unfolding g_def[abs_def]
    apply (rule homeomorphic_map_product_topology_reindex[where \<pi>=from_trace_class])
      apply auto
    by (smt (verit, best) UNIV_I bij_betwI' from_trace_class from_trace_class_cases from_trace_class_inject)
  then have homeo_g: \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) euclidean g\<close>
    by (simp add: euclidean_product_topology)
  have \<open>weak_star_topology = pullback_topology UNIV f (product_topology (\<lambda>_. euclidean) (Collect trace_class))\<close>
    by (simp add: weak_star_topology_def pullback_topology_homeo_cong homeo_g f_def[abs_def])
  also have \<open>\<dots> = pullback_topology UNIV (g o f) euclidean\<close>
    apply (subst pullback_topology_homeo_cong)
      apply (auto simp add: homeo_g f_def[abs_def])
    by metis
  also have \<open>\<dots> = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
    by (auto simp: f_def[abs_def] g_def[abs_def] o_def)
  finally show ?thesis
    by -
qed

lemma weak_star_topology_topspace[simp]:
  "topspace weak_star_topology = UNIV"
  unfolding weak_star_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma weak_star_topology_basis':
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b,'a) trace_class"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (from_trace_class (t i) o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  have 1: "open {g. \<forall>i\<in>I. g (t i) \<in> U i}"
    using assms by (rule product_topology_basis')
  show ?thesis
    unfolding weak_star_topology_def'
    apply (subst openin_pullback_topology)
    apply (intro exI conjI)
    using 1 by auto
qed

lemma weak_star_topology_basis:
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  assumes tc: \<open>\<And>i. i \<in> I \<Longrightarrow> trace_class (t i)\<close>
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  obtain t' where tt': \<open>t i = from_trace_class (t' i)\<close> if \<open>i \<in> I\<close> for i
    apply atomize_elim 
    using tc apply (auto intro!: choice ext)
  by (metis from_trace_class_cases mem_Collect_eq)
  show ?thesis
    using assms by (auto simp: tt' o_def intro!: weak_star_topology_basis')
qed

lemma wot_weaker_than_weak_star:
  "continuous_map weak_star_topology cweak_operator_topology (\<lambda>f. f)"
  unfolding weak_star_topology_def cweak_operator_topology_def
proof (rule continuous_map_pullback_both)
  define g' :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex) \<Rightarrow> 'b \<times> 'a \<Rightarrow> complex\<close> where 
    \<open>g' f = (\<lambda>(x,y). f (butterfly y x))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (\<lambda>f. f) -` UNIV\<close>
    by simp
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>(xa, y). xa \<bullet>\<^sub>C (x *\<^sub>V y))\<close>
    if \<open>(\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) \<in> topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class))\<close>
    for x
    by (auto intro!: ext simp: g'_def trace_butterfly_comp)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) euclidean g'\<close>
    apply (subst euclidean_product_topology[symmetric])
    apply (rule continuous_map_coordinatewise_then_product)
     apply (auto simp: g'_def[abs_def])
    by (metis continuous_map_product_projection mem_Collect_eq trace_class_butterfly)
qed

(* TODO: Analogous lemmas for the other _weaker_ theorems *)
lemma wot_weaker_than_weak_star':
  \<open>openin cweak_operator_topology U \<Longrightarrow> openin weak_star_topology U\<close>
  using wot_weaker_than_weak_star[where 'a='a and 'b='b]
  by (auto simp: continuous_map_def weak_star_topology_topspace)

lemma weak_star_topology_continuous_duality':
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (from_trace_class t o\<^sub>C\<^sub>L x))"
proof -
  have "continuous_map weak_star_topology euclidean ((\<lambda>f. f t) o (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)))"
    unfolding weak_star_topology_def' apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma weak_star_topology_continuous_duality:
  assumes \<open>trace_class t\<close>
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L x))"
  by (metis assms from_trace_class_cases mem_Collect_eq weak_star_topology_continuous_duality')

lemma continuous_on_weak_star_topo_iff_coordinatewise:
  fixes f :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  shows "continuous_map T weak_star_topology f
    \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x)))"
proof auto
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
  then have \<open>continuous_map T euclidean (\<lambda>x. trace (from_trace_class t o\<^sub>C\<^sub>L f x))\<close> for t
    by auto
  then have *: "continuous_map T euclidean ((\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) o f)"
    by (auto simp flip: euclidean_product_topology simp: o_def)
  show "continuous_map T weak_star_topology f"
    unfolding weak_star_topology_def'
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

lemma limitin_weak_star_topology':
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. ((\<lambda>j. trace (from_trace_class t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L l)) F)\<close>
  by (simp add: weak_star_topology_def' limitin_pullback_topology tendsto_coordinatewise)

lemma limitin_weak_star_topology:
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>j. trace (t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L l)) F)\<close>
  by (smt (z3) eventually_mono from_trace_class from_trace_class_cases limitin_weak_star_topology' mem_Collect_eq tendsto_def)

lemma filterlim_weak_star_topology:
  \<open>filterlim f (nhdsin weak_star_topology l) = limitin weak_star_topology f l\<close>
  by (auto simp: weak_star_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

lemma openin_weak_star_topology': \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` V)\<close>
  by (simp add: weak_star_topology_def' openin_pullback_topology)

(* lemma openin_weak_star_topology: \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. trace (t o\<^sub>C\<^sub>L x)) -` V)\<close> *)

lemma hausdorff_weak_star[simp]: \<open>hausdorff weak_star_topology\<close>
  by (metis cweak_operator_topology_topspace hausdorff_cweak_operator_topology hausdorff_def weak_star_topology_topspace wot_weaker_than_weak_star')
(* proof (unfold hausdorff_def, intro ballI impI)
  fix x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> assume \<open>x \<noteq> y\<close>
  then obtain a b where \<open>a \<bullet>\<^sub>C (x *\<^sub>V b) \<noteq> a \<bullet>\<^sub>C (y *\<^sub>V b)\<close>
    by (meson cblinfun_eqI cinner_extensionality)
  then have \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<noteq> trace (butterfly b a o\<^sub>C\<^sub>L y)\<close>
    by (simp add: trace_butterfly_comp)
  then obtain U' V' where U': \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<in> U'\<close> and V': \<open>trace (butterfly b a o\<^sub>C\<^sub>L y) \<in> V'\<close> 
    and \<open>open U'\<close> and \<open>open V'\<close> and \<open>U' \<inter> V' = {}\<close>
    by (meson separation_t2)
  define U'' V'' where \<open>U'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> U'}\<close> and \<open>V'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> V'}\<close>
  have \<open>open U''\<close>
    unfolding U''_def apply (rule product_topology_basis')
    using \<open>open U'\<close> by auto
  have \<open>open V''\<close>
    unfolding V''_def apply (rule product_topology_basis')
    using \<open>open V'\<close> by auto
  define U V where \<open>U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U''\<close> and
    \<open>V = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` V''\<close>
  have openU: \<open>openin weak_star_topology U\<close>
    using U_def \<open>open U''\<close> openin_weak_star_topology by blast
  have openV: \<open>openin weak_star_topology V\<close>
    using V_def \<open>open V''\<close> openin_weak_star_topology by blast
  have \<open>x \<in> U\<close>
    by (auto simp: U_def U''_def U')
  have \<open>y \<in> V\<close>
    by (auto simp: V_def V''_def V')
  have \<open>U \<inter> V = {}\<close>
    using \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def U''_def V''_def)
  show \<open>\<exists>U V. openin weak_star_topology U \<and> openin weak_star_topology V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
    apply (rule exI[of _ U], rule exI[of _ V])
    using \<open>x \<in> U\<close> \<open>y \<in> V\<close> openU openV \<open>U \<inter> V = {}\<close> by auto
qed *)


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


lemma hausdorff_OFCLASS_t2_space: \<open>OFCLASS('a::topological_space, t2_space_class)\<close> if \<open>hausdorff (euclidean :: 'a topology)\<close>
proof intro_classes
  fix a b :: 'a
  assume \<open>a \<noteq> b\<close>
  from that
  show \<open>\<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    unfolding hausdorff_def
    using \<open>a \<noteq> b\<close> by auto
qed


instance cblinfun_weak_star :: (chilbert_space, chilbert_space) t2_space
  apply (rule hausdorff_OFCLASS_t2_space)
  apply transfer
  by (rule hausdorff_weak_star)
(* proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_weak_star\<close>
  assume \<open>a \<noteq> b\<close>
  then have \<open>Abs_cblinfun_wot (from_weak_star a) \<noteq> Abs_cblinfun_wot (from_weak_star b)\<close>
    by (simp add: Abs_cblinfun_wot_inject from_weak_star_inject)
  from hausdorff[OF this]

  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    apply transfer using wot_weaker_than_weak_star' by auto
qed *)

lemma weak_star_topology_plus_cont: \<open>LIM (x,y) nhdsin weak_star_topology a \<times>\<^sub>F nhdsin weak_star_topology b.
            x + y :> nhdsin weak_star_topology (a + b)\<close>
proof -
  have trace_plus: \<open>trace (t o\<^sub>C\<^sub>L (a + b)) = trace (t o\<^sub>C\<^sub>L a) + trace (t o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and a b
    by (auto simp: cblinfun_compose_add_right trace_plus that trace_class_comp_left)
  show ?thesis
    unfolding weak_star_topology_def'
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
proof (unfold weak_star_topology_def, rule continuous_map_pullback_both)
  define g' :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex) \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex)\<close> where
    \<open>g' f = (\<lambda>t\<in>Collect trace_class. f (t o\<^sub>C\<^sub>L b))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (o\<^sub>C\<^sub>L) b -` UNIV\<close>
    by simp
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L x)))\<close> for x
    by (auto intro!: ext simp: g'_def[abs_def] cblinfun_compose_assoc trace_class_comp_left)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class))
     (product_topology (\<lambda>_. euclidean) (Collect trace_class)) g'\<close>
    apply (rule continuous_map_coordinatewise_then_product)
     apply (auto simp: g'_def[abs_def])
    by (metis continuous_map_product_projection mem_Collect_eq trace_class_comp_left)
qed

lemma continuous_map_right_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>b::'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof (subst weak_star_topology_def, subst weak_star_topology_def, rule continuous_map_pullback_both)
  define g' :: \<open>('c \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> complex) \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex)\<close> where
    \<open>g' f = (\<lambda>t\<in>Collect trace_class. f (a o\<^sub>C\<^sub>L t))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (\<lambda>b. b o\<^sub>C\<^sub>L a) -` UNIV\<close>
    by simp
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L (x o\<^sub>C\<^sub>L a)))\<close> for x
    apply (auto intro!: ext simp: g'_def[abs_def] trace_class_comp_right)
    by (metis (no_types, lifting) cblinfun_compose_assoc circularity_of_trace trace_class_comp_right)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class))
     (product_topology (\<lambda>_. euclidean) (Collect trace_class)) g'\<close>
    apply (rule continuous_map_coordinatewise_then_product)
     apply (auto simp: g'_def[abs_def])
    by (metis continuous_map_product_projection mem_Collect_eq trace_class_comp_right)
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
  include lattice_syntax
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


lemma transfer_csubspace_cblinfun_weak_star[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma transfer_closed_cblinfun_weak_star[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (closedin weak_star_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] weak_star_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma transfer_closure_cblinfun_weak_star[transfer_rule]:
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
  assumes has_sum: \<open>\<And>t. trace_class t \<Longrightarrow> ((\<lambda>i. trace (t o\<^sub>C\<^sub>L a i)) has_sum trace (t o\<^sub>C\<^sub>L b)) I\<close>
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

lemma has_sum_in_weak_star:
  \<open>has_sum_in weak_star_topology f A l \<longleftrightarrow> 
     (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) has_sum trace (t o\<^sub>C\<^sub>L l)) A)\<close>
proof -
  have *: \<open>trace (t o\<^sub>C\<^sub>L sum f F) = sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) F\<close> if \<open>trace_class t\<close> 
    for t F
    by (simp_all add: cblinfun_compose_sum_right that trace_class_comp_left trace_sum)
  show ?thesis
    by (simp add: * has_sum_def has_sum_in_def limitin_weak_star_topology)
qed

(* TODO rename \<rightarrow> has_sum... *)
lemma infsum_butterfly_ket: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (ket i) (ket i)) UNIV id_cblinfun\<close>
proof (rule has_sum_in_weak_star[THEN iffD2, rule_format])
  fix t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume [simp]: \<open>trace_class t\<close>
  from trace_has_sum[OF is_onb_ket \<open>trace_class t\<close>]
  have \<open>((\<lambda>i. ket i \<bullet>\<^sub>C (t *\<^sub>V ket i)) has_sum trace t) UNIV\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def)
  then show \<open>((\<lambda>i. trace (t o\<^sub>C\<^sub>L selfbutterket i)) has_sum trace (t o\<^sub>C\<^sub>L id_cblinfun)) UNIV\<close>
    by (simp add: trace_butterfly_comp')
qed

lemma sandwich_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (sandwich A)\<close>
  using continuous_map_compose[OF continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star]
  by (auto simp: o_def sandwich_apply[abs_def])

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
    show \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV.
       (\<Sum>i\<in>F. butterfly (x *\<^sub>V ket i) (ket i)) \<in> Collect finite_rank\<close>
      by (auto intro!: finite_rank_sum simp: f_def)
    show \<open>finite_subsets_at_top UNIV \<noteq> \<bottom>\<close>
      by simp
  qed
  then show ?thesis
    by auto
qed


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

lemma continuous_map_scaleC_weak_star'[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. scaleC c (f x))\<close>
  using continuous_map_compose[OF assms continuous_map_scaleC_weak_star]
  by (simp add: o_def)

lemma continuous_map_uminus_weak_star[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. - f x)\<close>
  apply (subst scaleC_minus1_left[abs_def,symmetric])
  by (intro continuous_map_scaleC_weak_star' assms)

lemma continuous_map_add_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x + g x)\<close>
proof -
  have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close> if \<open>trace_class t\<close> for t
    using assms(1) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  moreover have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L g x))\<close> if \<open>trace_class t\<close> for t
    using assms(2) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  ultimately show ?thesis
    by (auto intro!: continuous_map_add simp add: continuous_on_weak_star_topo_iff_coordinatewise
        cblinfun_compose_add_right trace_class_comp_left trace_plus)
qed

lemma continuous_map_minus_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro assms continuous_intros)



unbundle no_cblinfun_notation

end
