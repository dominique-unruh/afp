theory TAS_Topology
  imports
    "HOL-Analysis.Abstract_Topology_2"
    "HOL-Types_To_Sets.T2_Spaces"
    Complex_Bounded_Operators.Extra_General
    Tensor_Product.Misc_Tensor_Product
    Tmp_Move
begin

subsection \<open>Transferring type classes\<close>

subsubsection \<open>\<^class>\<open>topological_space\<close>\<close>

lemma topology_restrict_topspace[simp]: \<open>topology (\<lambda>U. U \<subseteq> topspace T \<and> openin T U) = T\<close>
  apply (subst asm_rl[of \<open>\<And>U. (U \<subseteq> topspace T \<and> openin T U) = openin T U\<close>, rule_format])
  using openin_subset apply blast
  by (metis openin_inverse)


lemma topological_space_on_with_alt_def: "topological_space_on_with A opn \<longleftrightarrow> istopology (\<lambda>U. U \<subseteq> A \<and> opn U) \<and> opn A"
  unfolding topological_space_on_with_def istopology_def
  apply (safe intro!: ext)
       apply fastforce
      apply (simp add: subsetI)
     apply fastforce
    apply (simp add: subset_iff)
   apply (meson Ball_Collect)
  by (meson Pow_iff subset_iff)

lemma topological_space_on_with_class: \<open>class.topological_space opn \<longleftrightarrow> topological_space_on_with UNIV opn\<close>
  apply transfer
  by (simp add: top_set_def)

lemma topological_space_on_with_from_topology: \<open>topological_space_on_with (topspace T) (openin T)\<close>
  unfolding topological_space_on_with_alt_def
  apply (subst asm_rl[of \<open>\<And>U. (U \<subseteq> topspace T \<and> openin T U) = openin T U\<close>, rule_format])
  using openin_subset by auto

lemma topological_space_on_with_openin: \<open>topological_space_on_with A opn \<Longrightarrow> openin (topology (\<lambda>U. U \<subseteq> A \<and> opn U)) X \<longleftrightarrow> (X \<subseteq> A \<and> opn X)\<close>
  by (simp add: topological_space_on_with_alt_def)

lemma topological_space_on_with_topspace: \<open>topological_space_on_with A opn \<Longrightarrow> topspace (topology (\<lambda>U. U \<subseteq> A \<and> opn U)) = A\<close>
  apply (simp add: topspace_def topological_space_on_with_openin)
  by (smt (verit, ccfv_SIG) Sup_set_def cSup_eq_maximum mem_Collect_eq order_refl topological_space_on_with_alt_def)

subsubsection \<open>\<^class>\<open>t2_space\<close>\<close>


lemma topological_space_on_with_hausdorff:
  \<open>topological_space_on_with A opn \<Longrightarrow> hausdorff (topology (\<lambda>U. U \<subseteq> A \<and> opn U)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> 
              (\<exists>U\<subseteq>A. \<exists>V\<subseteq>A. opn U \<and> opn V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>
  apply (simp add: hausdorff_def topological_space_on_with_topspace topological_space_on_with_openin)
  by meson

lemma t2_space_on_with_alt_def: "t2_space_on_with A opn \<longleftrightarrow> topological_space_on_with A opn \<and>
  hausdorff (topology (\<lambda>U. U \<subseteq> A \<and> opn U))"
  unfolding t2_space_on_with_def Ball_Collect
  apply (safe intro!: ext)
   apply (subst topological_space_on_with_hausdorff, simp)
   apply (simp add: subset_iff)
  apply (subst (asm) topological_space_on_with_hausdorff, simp)
  by metis

lemma t2_space_on_with_from_topology:
  assumes \<open>hausdorff T\<close>
  shows \<open>t2_space_on_with (topspace T) (openin T)\<close>
  using assms by (simp add: t2_space_on_with_alt_def topological_space_on_with_from_topology)

subsection \<open>Transferring constants\<close>

subsubsection \<open>\<^const>\<open>closed\<close>\<close>

lemma closed_on_with_alt_def:
  shows "closed_on_with A opn S \<longleftrightarrow> (if topological_space_on_with A opn \<and> S\<subseteq>A then closedin (topology (\<lambda>U. U \<subseteq> A \<and> opn U)) S else opn (A-S))"
  by (auto simp add: closedin_def closed_on_with_def topological_space_on_with_openin
      topological_space_on_with_topspace Diff_eq inf_commute)


lemma closure_on_with_from_topology:
  assumes \<open>S \<subseteq> topspace T\<close>
  shows \<open>closure_on_with (topspace T) (openin T) S = T closure_of S\<close>
  unfolding closure_on_with_def closure_of_def
  using assms 
  apply safe
  by blast+

subsubsection \<open>\<^const>\<open>continuous_on\<close>\<close>

definition continuous_on_UNIV_with where \<open>continuous_on_UNIV_with opn1 opn2 f \<longleftrightarrow> (\<forall>S. opn2 S \<longrightarrow> opn1 (f -` S))\<close>

lemma continuous_on_UNIV_with: \<open>(continuous_on :: 'a::topological_space set \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> _) UNIV
 = continuous_on_UNIV_with open open\<close>
  apply (simp add: continuous_on_UNIV_with_def[abs_def])
  by (metis continuous_on_open_invariant open_vimage)

definition \<open>continuous_on_UNIV_on_with A B opnA opnB f \<longleftrightarrow>(\<forall>S\<subseteq>B. opnB S \<longrightarrow> opnA ((f -` S) \<inter> A))\<close>

lemma continuous_on_UNIV_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  assumes [transfer_rule]: "right_total U" "bi_unique U"
  shows \<open>((rel_set T ===> (=)) ===> (rel_set U ===> (=)) ===> (T ===> U) ===> (=))
         (continuous_on_UNIV_on_with (Collect (Domainp T)) (Collect (Domainp U))) continuous_on_UNIV_with\<close>
  unfolding continuous_on_UNIV_on_with_def continuous_on_UNIV_with_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Pow_def Ball_Collect[symmetric] Ball_def Bex_def mem_Collect_eq
  by blast

subsection \<open>Transferring results\<close>

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

    note on_closure_eqI[unfolded closure.with  continuous_on_UNIV_with,
        unoverload_type 'b, unoverload_type 'a, where 'a='t and 'b='u]
    note this[untransferred, where f=f and g=g and S=\<open>S \<inter> topspace T\<close> and x=x]
    note this[untransferred, simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have 2: \<open>f ` topspace T \<subseteq> topspace U\<close>
  by (meson assms(4) continuous_map_image_subset_topspace)
  have 3: \<open>g ` topspace T \<subseteq> topspace U\<close>
    by (simp add: continuous_map_image_subset_topspace g)
  have 4: \<open>x \<in> topspace T\<close>
    by (meson assms(3) in_closure_of)
  have 5: \<open>topological_space_on_with (topspace T) (openin T)\<close>
    by (simp add: topological_space_on_with_from_topology)
  have 6: \<open>t2_space_on_with (topspace U) (openin U)\<close>
    by (simp add: assms(1) t2_space_on_with_from_topology)
  from x have \<open>x \<in> T closure_of (S \<inter> topspace T)\<close>
    by (metis closure_of_restrict inf_commute)
  then have 7: \<open>x \<in> closure_on_with (topspace T) (openin T) (S \<inter> topspace T)\<close>
    by (auto simp: closure_on_with_from_topology)
  have 8: \<open>continuous_on_UNIV_on_with (topspace T) (topspace U) (openin T) (openin U) f\<close>
    using continuous_on_UNIV_on_with_def f by fastforce
  have 9: \<open>continuous_on_UNIV_on_with (topspace T) (topspace U) (openin T) (openin U) g\<close>
    using continuous_on_UNIV_on_with_def g by fastforce

  show ?thesis
    apply (rule * )
    using 2 3 4 5 6 f_eq_g 7 8 9 by auto
qed

end
