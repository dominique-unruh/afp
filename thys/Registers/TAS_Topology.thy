theory TAS_Topology
  imports
    "HOL-Analysis.Abstract_Topology_2"
    Complex_Bounded_Operators.Extra_General
    Tensor_Product.Misc_Tensor_Product
    Tmp_Move
begin

subsection \<open>Transferring type classes\<close>

subsubsection \<open>\<^class>\<open>topological_space\<close>\<close>

(* (* TODO needed? *)
lemma topology_restrict_topspace[simp]: \<open>topology (\<lambda>U. U \<subseteq> topspace T \<and> openin T U) = T\<close>
  apply (subst asm_rl[of \<open>\<And>U. (U \<subseteq> topspace T \<and> openin T U) = openin T U\<close>, rule_format])
  using openin_subset apply blast
  by (metis openin_inverse)
 *)

ctr parametricity in topological_space_ow_def[unfolded make_parametricity_proof_friendly]

lemma class_topological_space_ud[ud_with]: \<open>class.topological_space = topological_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.topological_space_def topological_space_ow_def)

subsubsection \<open>\<^class>\<open>t2_space\<close>\<close>


lemma make_parametricity_proof_friendly_more: (* TODO put into make_parametricity_proof_friendly *)
  shows \<open>(\<exists>A\<subseteq>B. P A) \<longleftrightarrow> (\<exists>A\<in>Pow B. P A)\<close>
  by blast

locale t2_space_ow = topological_space_ow +
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. x \<noteq> y \<longrightarrow> (\<exists>S\<subseteq>U. \<exists>T\<subseteq>U. \<tau> S \<and> \<tau> T \<and> x \<in> S \<and> y \<in> T \<and> S \<inter> T = {})\<close>

ctr parametricity in t2_space_ow_def[unfolded t2_space_ow_axioms_def make_parametricity_proof_friendly  make_parametricity_proof_friendly_more]

lemma class_t2_space_ud[ud_with]: \<open>class.t2_space = t2_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.t2_space_def class.t2_space_axioms_def t2_space_ow_def
      t2_space_ow_axioms_def ud_with)

subsection \<open>Transferring constants\<close>

subsubsection \<open>\<^const>\<open>closed\<close>\<close>

definition \<open>islimptin T x S \<longleftrightarrow> x \<in> topspace T \<and> (\<forall>V. x \<in> V \<longrightarrow> openin T V \<longrightarrow> (\<exists>y\<in>S. y \<in> V \<and> y \<noteq> x))\<close>

lemma islimpt_ow_from_topology: \<open>islimpt_ow (topspace T) (openin T) x S \<longleftrightarrow> islimptin T x S \<or> x \<notin> topspace T\<close>
  apply (cases \<open>x \<in> topspace T\<close>)
   apply (simp_all add: islimpt_ow_def islimptin_def Pow_def)
  by blast+

subsubsection \<open>\<^const>\<open>continuous_on\<close>\<close>

definition \<open>transfer_vimage_into f U s = (f -` U) \<inter> s\<close> (* TODO: add to make_parametricity_proof_friendly *)

lemma transfer_vimage_into_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>((A ===> B) ===> rel_set B ===> rel_set A ===> rel_set A) transfer_vimage_into transfer_vimage_into\<close>
  unfolding transfer_vimage_into_def
  apply (auto intro!: rel_funI simp: rel_set_def)
  by (metis Int_iff apply_rsp' assms bi_unique_def vimage_eq)+

definition continuous_on_ow where \<open>continuous_on_ow A B opnA opnB s f 
  \<longleftrightarrow> (\<forall>U\<subseteq>B. opnB U \<longrightarrow> (\<exists>V\<subseteq>A. opnA V \<and> (V \<inter> s) = (f -` U) \<inter> s))\<close>
  for f :: \<open>'a \<Rightarrow> 'b\<close>

lemma continuous_on_ud[ud_with]: \<open>continuous_on s f \<longleftrightarrow> continuous_on_ow UNIV UNIV open open s f\<close>
  for f :: \<open>'a::topological_space \<Rightarrow> 'b::topological_space\<close>
  unfolding continuous_on_ow_def continuous_on_open_invariant by auto

lemma continuous_on_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>(rel_set A ===> rel_set B ===> (rel_set A ===> (\<longleftrightarrow>)) ===> (rel_set B ===> (\<longleftrightarrow>)) ===> rel_set A ===> (A ===> B) ===> (\<longleftrightarrow>)) continuous_on_ow continuous_on_ow\<close>
  unfolding continuous_on_ow_def make_parametricity_proof_friendly make_parametricity_proof_friendly_more transfer_vimage_into_def[symmetric]
  by transfer_prover

(* ctr parametricity in continuous_on_ow_def *)

lemma topological_space_ow_from_topology[simp]: \<open>topological_space_ow (topspace T) (openin T)\<close>
  by (auto intro!: topological_space_ow.intro)

lemma t2_space_ow_from_topology[simp, iff]: \<open>t2_space_ow (topspace T) (openin T)\<close> if \<open>hausdorff T\<close>
  using that
  apply (auto intro!: t2_space_ow.intro simp: t2_space_ow_axioms_def hausdorff_def)
  by (metis openin_subset)

lemma closure_ow_from_topology: \<open>closure_ow (topspace T) (openin T) S = T closure_of S\<close> if \<open>S \<subseteq> topspace T\<close>
  using that apply (auto simp: closure_ow_def islimpt_ow_from_topology in_closure_of)
  apply (meson in_closure_of islimptin_def)
  by (metis islimptin_def)

lemma continuous_on_ow_from_topology: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f \<longleftrightarrow> continuous_map T U f\<close>
  if \<open>f ` topspace T \<subseteq> topspace U\<close>
  apply (simp add: continuous_on_ow_def continuous_map_def)
  apply safe
  apply (meson image_subset_iff that)
  apply (smt (verit) Collect_mono_iff Int_def ctr_simps_mem_Collect_eq inf_absorb1 openin_subopen openin_subset vimage_eq)
  by blast

declare SML_Topological_Space.closure.with[ud_with del]
lemma closure_ud[ud_with]: \<open>closure = closure_ow UNIV open\<close>
  unfolding closure_def closure_ow_def islimpt_def islimpt_ow_def by auto

subsection \<open>Transferring results\<close>

attribute_setup protect = \<open>Scan.lift Parse.nat >> (fn num => 
  Thm.rule_attribute [] 
    (fn context => fn thm =>
       Goal.protect num thm))\<close> 

lemma closure_of_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close> and T :: \<open>'a topology\<close> and U :: \<open>'b topology\<close>
  assumes hausdorff: \<open>hausdorff U\<close>
  assumes f_eq_g: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes x: \<open>x \<in> T closure_of S\<close>
  assumes f: \<open>continuous_map T U f\<close> and g: \<open>continuous_map T U g\<close>
  shows \<open>f x = g x\<close>
proof -
  have \<open>topspace T \<noteq> {}\<close>
    by (metis assms(3) equals0D in_closure_of)
  have \<open>topspace U \<noteq> {}\<close>
    using \<open>topspace T \<noteq> {}\<close> assms(5) continuous_map_image_subset_topspace by blast

  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (topspace T)"
    then interpret T: local_typedef \<open>topspace T\<close> \<open>TYPE('t)\<close>
      by unfold_locales
    assume "\<exists>(Rep :: 'u \<Rightarrow> 'b) Abs. type_definition Rep Abs (topspace U)"
    then interpret U: local_typedef \<open>topspace U\<close> \<open>TYPE('u)\<close>
      by unfold_locales

    note on_closure_eqI
    note this[unfolded ud_with]
    note this[unoverload_type 'b, unoverload_type 'a]
    note this[unfolded ud_with]
    note this[where 'a='t and 'b='u]
    note this[untransferred]
    note this[where f=f and g=g and S=\<open>S \<inter> topspace T\<close> and x=x and ?open="openin T" and opena=\<open>openin U\<close>]
    note this[simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have 2: \<open>f ` topspace T \<subseteq> topspace U\<close>
  by (meson assms(4) continuous_map_image_subset_topspace)
  have 3: \<open>g ` topspace T \<subseteq> topspace U\<close>
    by (simp add: continuous_map_image_subset_topspace g)
  have 4: \<open>x \<in> topspace T\<close>
    by (meson assms(3) in_closure_of)
  have 5: \<open>topological_space_ow (topspace T) (openin T)\<close>
    by simp
  have 6: \<open>t2_space_ow (topspace U) (openin U)\<close>
    by (simp add: hausdorff)
  from x have \<open>x \<in> T closure_of (S \<inter> topspace T)\<close>
    by (metis closure_of_restrict inf_commute)
  then have 7: \<open>x \<in> closure_ow (topspace T) (openin T) (S \<inter> topspace T)\<close>
    by (simp add: closure_ow_from_topology)
  have 8: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f\<close>
     by (meson "2" continuous_on_ow_from_topology f)
  have 9: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) g\<close>
    by (simp add: "3" continuous_on_ow_from_topology g)

  show ?thesis
    apply (rule * )
    using 2 3 4 5 6 f_eq_g 7 8 9 by auto
qed

end
