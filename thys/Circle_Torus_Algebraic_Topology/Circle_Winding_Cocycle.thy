theory Circle_Winding_Cocycle
  imports Circle_Loop_Homology
begin

section \<open>Winding number annihilates singular boundaries\<close>

text \<open>The winding functional is extended linearly to singular chains.
  The boundary of each singular triangle has winding zero, because its
  boundary loop contracts in the triangle. This detects a nonzero first
  homology class without assuming a Hurewicz theorem.\<close>

definition winding_triangle :: "complex set" where
  "winding_triangle = {z. 0 \<le> Re z \<and> 0 \<le> Im z \<and> Re z + Im z \<le> 1}"

lemma convex_winding_triangle: "convex winding_triangle"
proof -
  have eq: "winding_triangle = {z. 0 \<le> Re z} \<inter> {z. 0 \<le> Im z} \<inter>
      {z. inner (1+\<i>) z \<le> 1}"
    by (auto simp: winding_triangle_def inner_complex_def)
  show ?thesis unfolding eq
    by (intro convex_Int convex_halfspace_Re_ge convex_halfspace_Im_ge convex_halfspace_le)
qed

definition triangle_coordinates :: "complex \<Rightarrow> nat \<Rightarrow> real" where
  "triangle_coordinates z i =
    (if i=0 then 1 - Re z - Im z else if i=1 then Re z else if i=2 then Im z else 0)"

lemma triangle_coordinates_mem:
  assumes "z \<in> winding_triangle"
  shows "triangle_coordinates z \<in> standard_simplex 2"
  using assms
  by (auto simp: winding_triangle_def triangle_coordinates_def standard_simplex_def
      sum.atMost_Suc numeral_2_eq_2 split: if_splits; linarith)

lemma triangle_coordinates_continuous:
  "continuous_map euclidean (powertop_real UNIV) triangle_coordinates"
  unfolding continuous_map_componentwise triangle_coordinates_def
  by (auto intro!: continuous_intros simp: if_distrib split: if_splits)

lemma singular_triangle_continuous:
  assumes "singular_simplex 2 (top_of_set circle) f"
  shows "continuous_on winding_triangle (f \<circ> triangle_coordinates)"
    "(f \<circ> triangle_coordinates) ` winding_triangle \<subseteq> circle"
proof -
  have c: "continuous_map (top_of_set winding_triangle)
      (subtopology (powertop_real UNIV) (standard_simplex 2)) triangle_coordinates"
    using triangle_coordinates_continuous triangle_coordinates_mem
    by (auto simp: continuous_map_in_subtopology intro: continuous_map_from_subtopology)
  have "continuous_map (top_of_set winding_triangle) (top_of_set circle) (f \<circ> triangle_coordinates)"
    using assms c unfolding singular_simplex_def by (blast intro: continuous_map_compose)
  then show "continuous_on winding_triangle (f \<circ> triangle_coordinates)"
    "(f \<circ> triangle_coordinates) ` winding_triangle \<subseteq> circle"
    by (auto simp: continuous_map_subtopology_eu)
qed

lemma triangle_winding_add:
  assumes cont: "continuous_on winding_triangle f" and im: "f ` winding_triangle \<subseteq> circle"
  shows "winding_number (f \<circ> linepath 1 \<i>) 0 -
      winding_number (f \<circ> linepath 0 \<i>) 0 +
      winding_number (f \<circ> linepath 0 1) 0 = 0"
proof -
  have verts: "(0::complex) \<in> winding_triangle" "1 \<in> winding_triangle" "\<i> \<in> winding_triangle"
    by (simp_all add: winding_triangle_def)
  have edges: "path_image (linepath 0 1) \<subseteq> winding_triangle"
    "path_image (linepath 1 \<i>) \<subseteq> winding_triangle"
    "path_image (linepath 0 \<i>) \<subseteq> winding_triangle"
    using convex_winding_triangle verts
    by (simp_all add: convex_contains_segment)
  have hom: "homotopic_paths winding_triangle (linepath 0 1 +++ linepath 1 \<i>) (linepath 0 \<i>)"
  proof (rule homotopic_paths_linear)
    show "path (linepath 0 1 +++ linepath 1 \<i>)" "path (linepath 0 \<i>)" by auto
    show "pathstart (linepath 0 \<i>) = pathstart (linepath 0 1 +++ linepath 1 \<i>)"
      "pathfinish (linepath 0 \<i>) = pathfinish (linepath 0 1 +++ linepath 1 \<i>)" by simp_all
    show "closed_segment ((linepath 0 1 +++ linepath 1 \<i>) t) (linepath 0 \<i> t) \<subseteq> winding_triangle"
      if "t \<in> {0..1}" for t
    proof -
      have jp: "path_image (linepath 0 1 +++ linepath 1 \<i>) \<subseteq> winding_triangle"
        by (rule subset_path_image_join) (use edges in auto)
      have mem: "(linepath 0 1 +++ linepath 1 \<i>) t \<in> winding_triangle"
        "linepath 0 \<i> t \<in> winding_triangle"
        using jp edges(3) that by (auto simp: path_image_def)
      show ?thesis using convex_winding_triangle mem
        by (meson convex_contains_segment)
    qed
  qed
  have mapped: "homotopic_paths (-{0}) (f \<circ> (linepath 0 1 +++ linepath 1 \<i>)) (f \<circ> linepath 0 \<i>)"
    by (rule homotopic_paths_continuous_image[OF hom cont])
       (use im in \<open>auto simp: circle_def\<close>)
  have p: "path (f \<circ> linepath 0 1)" "path (f \<circ> linepath 1 \<i>)"
    using cont edges by (intro path_continuous_image; auto intro: continuous_on_subset)+
  have images: "path_image (f \<circ> linepath 0 1) \<subseteq> circle"
    "path_image (f \<circ> linepath 1 \<i>) \<subseteq> circle"
    using subset_trans[OF image_mono[OF edges(1), of f] im]
      subset_trans[OF image_mono[OF edges(2), of f] im]
    by (simp_all add: path_image_def image_comp)
  have nz: "0 \<notin> path_image (f \<circ> linepath 0 1)" "0 \<notin> path_image (f \<circ> linepath 1 \<i>)"
    using images by (auto simp: circle_def sphere_def)
  have "winding_number (f \<circ> linepath 0 \<i>) 0 =
      winding_number (f \<circ> linepath 0 1) 0 + winding_number (f \<circ> linepath 1 \<i>) 0"
    using winding_number_homotopic_paths[OF mapped]
      winding_number_join[OF p(1) nz(1) p(2) nz(2)]
    by (simp add: path_compose_join pathstart_def pathfinish_def linepath_def)
  then show ?thesis by simp
qed

lemma singular_triangle_winding:
  assumes "singular_simplex 2 (top_of_set circle) f"
  shows "winding_number (singular_face 2 0 f \<circ> edge_coordinates) 0 -
      winding_number (singular_face 2 1 f \<circ> edge_coordinates) 0 +
      winding_number (singular_face 2 2 f \<circ> edge_coordinates) 0 = 0"
proof -
  have coords:
    "simplical_face 0 (edge_coordinates t) = triangle_coordinates (linepath 1 \<i> t)"
    "simplical_face 1 (edge_coordinates t) = triangle_coordinates (linepath 0 \<i> t)"
    "simplical_face 2 (edge_coordinates t) = triangle_coordinates (linepath 0 1 t)" for t
    by (auto simp: fun_eq_iff simplical_face_def edge_coordinates_def triangle_coordinates_def
        linepath_def scaleR_conv_of_real numeral_2_eq_2 split: if_splits; algebra)+
  have faces:
    "(singular_face 2 0 f \<circ> edge_coordinates) t =
       ((f \<circ> triangle_coordinates) \<circ> linepath 1 \<i>) t"
    "(singular_face 2 1 f \<circ> edge_coordinates) t =
       ((f \<circ> triangle_coordinates) \<circ> linepath 0 \<i>) t"
    "(singular_face 2 2 f \<circ> edge_coordinates) t =
       ((f \<circ> triangle_coordinates) \<circ> linepath 0 1) t"
    if "t \<in> {0..1}" for t
    using edge_coordinates_mem[OF that]
    by (simp_all add: singular_face_def coords[unfolded One_nat_def, simplified])
  have eq:
    "winding_number (singular_face 2 0 f \<circ> edge_coordinates) 0 =
       winding_number ((f \<circ> triangle_coordinates) \<circ> linepath 1 \<i>) 0"
    "winding_number (singular_face 2 1 f \<circ> edge_coordinates) 0 =
       winding_number ((f \<circ> triangle_coordinates) \<circ> linepath 0 \<i>) 0"
    "winding_number (singular_face 2 2 f \<circ> edge_coordinates) 0 =
       winding_number ((f \<circ> triangle_coordinates) \<circ> linepath 0 1) 0"
    by (intro winding_number_cong; use faces in auto)+
  show ?thesis
    unfolding eq by (rule triangle_winding_add[OF singular_triangle_continuous[OF assms]])
qed

definition complex_add_group :: "complex monoid" where
  "complex_add_group = \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>"

lemma comm_group_complex_add: "comm_group complex_add_group"
proof (rule comm_groupI)
  show "\<exists>y\<in>carrier complex_add_group. y \<otimes>\<^bsub>complex_add_group\<^esub> x = \<one>\<^bsub>complex_add_group\<^esub>"
    for x by (rule bexI[where x="-x"]) (simp_all add: complex_add_group_def)
qed (simp_all add: complex_add_group_def add.assoc add.commute)

lemma winding_chain_functional:
  obtains w :: "complex chain \<Rightarrow> complex" where
    "w 0 = 0" "\<And>a b. w (a+b) = w a + w b" "\<And>a b. w (a-b) = w a - w b"
    "\<And>f. w (frag_of f) = winding_number (f \<circ> edge_coordinates) 0"
    "\<And>c. singular_chain 2 (top_of_set circle) c \<Longrightarrow> w (chain_boundary 2 c) = 0"
proof -
  interpret C: comm_group complex_add_group by (rule comm_group_complex_add)
  obtain w where hom: "w \<in> hom (free_Abelian_group UNIV) complex_add_group"
    and gen: "\<And>f. w (frag_of f) = winding_number (f \<circ> edge_coordinates) 0"
    by (rule C.free_Abelian_group_universal[where S=UNIV and
          f="\<lambda>f. winding_number (f \<circ> edge_coordinates) 0"])
       (auto simp: complex_add_group_def)
  interpret W: group_hom "free_Abelian_group UNIV" complex_add_group w
    by (simp add: group_hom_def group_hom_axioms_def hom C.is_group)
  have zero: "w 0 = 0" using W.hom_one by (simp add: complex_add_group_def)
  have add: "w (a+b) = w a + w b" for a b
    using W.hom_mult[of a b] by (simp add: complex_add_group_def)
  have minus: "w (-a) = - w a" for a
    using add[of a "-a"] zero by (simp add: add_eq_0_iff)
  have diff: "w (a-b) = w a - w b" for a b
    by (subst diff_conv_add_uminus, subst add, subst minus)
       (rule diff_conv_add_uminus[symmetric])
  have boundary: "w (chain_boundary 2 c) = 0" if "singular_chain 2 (top_of_set circle) c" for c
  proof (rule free_Abelian_group_induct[OF that[unfolded singular_chain_def]])
    show "w (chain_boundary 2 0) = 0" by (simp add: zero)
    show "w (chain_boundary 2 (a-b)) = 0"
      if "Poly_Mapping.keys a \<subseteq> singular_simplex_set 2 (top_of_set circle)"
        "Poly_Mapping.keys b \<subseteq> singular_simplex_set 2 (top_of_set circle)"
        "w (chain_boundary 2 a) = 0" "w (chain_boundary 2 b) = 0" for a b
      using that by (simp add: chain_boundary_diff diff)
    show "w (chain_boundary 2 (frag_of f)) = 0"
      if "f \<in> singular_simplex_set 2 (top_of_set circle)" for f
      using that singular_triangle_winding[of f]
      by (simp add: chain_boundary_of sum.atMost_Suc numeral_2_eq_2
          add minus diff gen zero)
  qed
  show thesis by (rule that[OF zero add diff]) (use gen boundary in auto)
qed

theorem circle_standard_loop_homology_nontrivial:
  "circle_loop_homology (circlepath 0 1) \<noteq> \<one>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>"
proof
  assume eq: "circle_loop_homology (circlepath 0 1) = \<one>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>"
  have "singular_relboundary 1 (top_of_set circle) {} (frag_of (loop_simplex (circlepath 0 1)))"
    using eq by (simp add: circle_loop_homology_def homologous_rel_set_eq_relboundary
        one_relative_homology_group[where p=1, simplified])
  then obtain c where c: "singular_chain 2 (top_of_set circle) c"
    "chain_boundary 2 c = frag_of (loop_simplex (circlepath 0 1))"
    by (auto simp: singular_boundary numeral_2_eq_2)
  obtain w :: "complex chain \<Rightarrow> complex" where
    w: "\<And>f. w (frag_of f) = winding_number (f \<circ> edge_coordinates) 0"
    "\<And>c. singular_chain 2 (top_of_set circle) c \<Longrightarrow> w (chain_boundary 2 c) = 0"
    by (rule winding_chain_functional) blast
  have "winding_number (loop_simplex (circlepath 0 1) \<circ> edge_coordinates) 0 = 0"
    using w c by metis
  moreover have "winding_number (loop_simplex (circlepath 0 1) \<circ> edge_coordinates) 0 = 1"
    using winding_number_cong[of "loop_simplex (circlepath 0 1) \<circ> edge_coordinates" "circlepath 0 1" 0]
    by (simp add: loop_simplex_edge winding_number_circlepath_centre)
  ultimately show False by simp
qed

end
