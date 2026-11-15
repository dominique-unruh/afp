theory Circle_Homology_Degree
  imports Circle_Radial_Retract "HOL-Homology.Homology"
begin

section \<open>Homology of the circle and the punctured plane\<close>

text \<open>
  The standard Isabelle homology library computes the reduced homology of an
  abstract sphere.  The geometric circle used by the preceding theories is
  identified with the one-sphere using the library's Euclidean-coordinate
  homeomorphism, and the radial deformation retract then transfers the result
  to the punctured plane.
\<close>

lemma reduced_homology_group_nsphere_one:
  "reduced_homology_group (int (1::nat)) (nsphere (1::nat)) \<cong> integer_group"
  by (metis reduced_homology_group_nsphere(1))

lemma reduced_homology_group_nsphere_one_other:
  "p \<noteq> int (1::nat) \<Longrightarrow>
     trivial_group (reduced_homology_group p (nsphere (1::nat)))"
  by (rule reduced_homology_group_nsphere(2))

lemma circle_homeomorphic_nsphere_one:
  "top_of_set circle homeomorphic_space nsphere 1"
proof -
  have independent_basis: "independent (Basis :: complex set)"
    by (rule independent_Basis)
  have orthogonal_basis: "pairwise orthogonal (Basis :: complex set)"
    by (rule orthogonal_Basis)
  have card_basis: "card (Basis :: complex set) = DIM(complex)"
    using dim_eq_card_independent [OF independent_basis]
    by (simp add: span_Basis)
  have dim_complex: "DIM(complex) = 2"
    by simp
  have nonzero_dim: "DIM(complex) \<noteq> 0"
    by (simp add: dim_complex)
  have norm_basis: "\<And>u. u \<in> (Basis :: complex set) \<Longrightarrow> norm u = 1"
    by (rule norm_Basis)
  obtain f g where
    hm: "homeomorphic_maps (nsphere (DIM(complex) - 1))
      (top_of_set (sphere 0 1 \<inter> span (Basis :: complex set))) f g"
  proof (rule homeomorphic_maps_nsphere_euclidean_sphere)
    show "independent (Basis :: complex set)"
      by (rule independent_basis)
    show "pairwise orthogonal (Basis :: complex set)"
      by (rule orthogonal_basis)
    show "card (Basis :: complex set) = DIM(complex)"
      by (rule card_basis)
    show "DIM(complex) \<noteq> 0"
      by (rule nonzero_dim)
    show "\<And>u. u \<in> (Basis :: complex set) \<Longrightarrow> norm u = 1"
      by (rule norm_basis)
  qed
  have hm': "homeomorphic_maps (nsphere 1)
      (top_of_set (sphere (0::complex) 1)) f g"
    using hm by (simp add: dim_complex)
  have hm'': "homeomorphic_maps (nsphere 1) (top_of_set circle) f g"
    using hm' by (simp add: circle_def)
  have "nsphere 1 homeomorphic_space top_of_set circle"
    by (rule homeomorphic_maps_imp_homeomorphic_space [OF hm''])
  then show ?thesis
    by (rule iffD1 [OF homeomorphic_space_sym])
qed

lemma reduced_homology_group_circle_one:
  "reduced_homology_group (int (1::nat)) (top_of_set circle) \<cong> integer_group"
proof -
  have h:
      "reduced_homology_group (int (1::nat)) (top_of_set circle) \<cong>
       reduced_homology_group (int (1::nat)) (nsphere (1::nat))"
    by (rule homeomorphic_space_imp_isomorphic_reduced_homology_groups
        [OF circle_homeomorphic_nsphere_one])
  then show ?thesis
    using reduced_homology_group_nsphere_one by (rule iso_trans)
qed

lemma reduced_homology_group_circle_transfer:
  "reduced_homology_group p (top_of_set circle) \<cong>
   reduced_homology_group p (nsphere (1::nat))"
  by (rule homeomorphic_space_imp_isomorphic_reduced_homology_groups
      [OF circle_homeomorphic_nsphere_one])

lemma reduced_homology_group_circle_other:
  "p \<noteq> int (1::nat) \<Longrightarrow>
   trivial_group (reduced_homology_group p (top_of_set circle))"
proof -
  assume p: "p \<noteq> int (1::nat)"
  have h:
      "reduced_homology_group p (top_of_set circle) \<cong>
       reduced_homology_group p (nsphere (1::nat))"
    by (rule reduced_homology_group_circle_transfer)
  have hn: "trivial_group (reduced_homology_group p (nsphere (1::nat)))"
    using p by (metis reduced_homology_group_nsphere(2))
  have gc: "group (reduced_homology_group p (top_of_set circle))"
    by simp
  have gs: "group (reduced_homology_group p (nsphere (1::nat)))"
    by simp
  have hi:
      "trivial_group (reduced_homology_group p (top_of_set circle)) \<longleftrightarrow>
       trivial_group (reduced_homology_group p (nsphere (1::nat)))"
    by (rule isomorphic_group_triviality [OF h gc gs])
  then show ?thesis
    using hn by blast
qed

lemma reduced_homology_group_punctured_plane_transfer:
  "reduced_homology_group p (top_of_set punctured_plane) \<cong>
   reduced_homology_group p (top_of_set circle)"
  using punctured_plane_homotopy_equivalent_circle
  by (rule homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups)

lemma reduced_homology_group_punctured_plane_one:
  "reduced_homology_group (int (1::nat)) (top_of_set punctured_plane) \<cong> integer_group"
proof -
  have h:
      "reduced_homology_group (int (1::nat)) (top_of_set punctured_plane) \<cong>
       reduced_homology_group (int (1::nat)) (top_of_set circle)"
    using punctured_plane_homotopy_equivalent_circle
    by (rule homotopy_equivalent_space_imp_isomorphic_reduced_homology_groups)
  then show ?thesis
    using reduced_homology_group_circle_one by (rule iso_trans)
qed

lemma reduced_homology_group_punctured_plane_other:
  "p \<noteq> int (1::nat) \<Longrightarrow>
   trivial_group (reduced_homology_group p (top_of_set punctured_plane))"
proof -
  assume p: "p \<noteq> int (1::nat)"
  have h:
      "reduced_homology_group p (top_of_set punctured_plane) \<cong>
       reduced_homology_group p (top_of_set circle)"
    by (rule reduced_homology_group_punctured_plane_transfer)
  have hc: "trivial_group (reduced_homology_group p (top_of_set circle))"
    by (rule reduced_homology_group_circle_other [OF p])
  have gp: "group (reduced_homology_group p (top_of_set punctured_plane))"
    by simp
  have gc: "group (reduced_homology_group p (top_of_set circle))"
    by simp
  have hi:
      "trivial_group (reduced_homology_group p (top_of_set punctured_plane)) \<longleftrightarrow>
       trivial_group (reduced_homology_group p (top_of_set circle))"
    by (rule isomorphic_group_triviality [OF h gp gc])
  then show ?thesis
    using hc by blast
qed

lemma circle_not_contractible:
  "\<not> contractible_space (top_of_set circle)"
proof
  assume c: "contractible_space (top_of_set circle)"
  have hc:
      "contractible_space (top_of_set circle) \<longleftrightarrow>
       contractible_space (nsphere (1::nat))"
    by (rule homeomorphic_space_contractibility [OF circle_homeomorphic_nsphere_one])
  have hns: "contractible_space (nsphere (1::nat))"
    using hc c by blast
  then show False
    using non_contractible_space_nsphere [of "1::nat"] by blast
qed

lemma punctured_plane_not_contractible:
  "\<not> contractible_space (top_of_set punctured_plane)"
proof
  assume c: "contractible_space (top_of_set punctured_plane)"
  have hc:
      "contractible_space (top_of_set punctured_plane) \<longleftrightarrow>
       contractible_space (top_of_set circle)"
    by (rule homotopy_equivalent_space_contractibility
        [OF punctured_plane_homotopy_equivalent_circle])
  have hcircle: "contractible_space (top_of_set circle)"
    using hc c by blast
  then show False
    using circle_not_contractible by blast
qed

section \<open>Brouwer degree\<close>

text \<open>
  The homology library defines the degree of a self-map of an abstract sphere
  through its action on the top reduced homology group.  We expose the basic
  calculational laws needed by later degree arguments.
\<close>

lemma Brouwer_degree_circle_identity:
  "Brouwer_degree2 1 id = 1"
  by (rule Brouwer_degree2_id)

lemma Brouwer_degree_circle_reflection:
  "Brouwer_degree2 1 (\<lambda>x i. if i = 0 then -x i else x i) = -1"
  by (rule Brouwer_degree2_reflection)

lemma Brouwer_degree_circle_compose:
  assumes "continuous_map (nsphere 1) (nsphere 1) f"
    and "continuous_map (nsphere 1) (nsphere 1) g"
  shows "Brouwer_degree2 1 (g \<circ> f) =
      Brouwer_degree2 1 g * Brouwer_degree2 1 f"
  by (rule Brouwer_degree2_compose [OF assms])

lemma Brouwer_degree_circle_homotopy_invariant:
  assumes "homotopic_with (\<lambda>x. True) (nsphere 1) (nsphere 1) f g"
  shows "Brouwer_degree2 1 f = Brouwer_degree2 1 g"
  by (rule Brouwer_degree2_homotopic [OF assms])

end
