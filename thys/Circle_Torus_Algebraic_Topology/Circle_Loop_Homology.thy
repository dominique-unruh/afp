theory Circle_Loop_Homology
  imports "Circle_Torus_Algebraic_Topology.Circle_Covering"
    "Circle_Torus_Algebraic_Topology.Circle_Homology_Degree"
begin

section \<open>Loops as singular cycles\<close>

definition edge_coordinates :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "edge_coordinates t i = (if i = 0 then 1-t else if i = 1 then t else 0)"

lemma edge_coordinates_mem:
  "t \<in> {0..1} \<Longrightarrow> edge_coordinates t \<in> standard_simplex 1"
  by (auto simp: edge_coordinates_def standard_simplex_def sum.atMost_Suc)

lemma edge_coordinates_continuous:
  "continuous_map euclideanreal (powertop_real UNIV) edge_coordinates"
  unfolding continuous_map_componentwise edge_coordinates_def
  by (auto intro!: continuous_intros simp: if_distrib split: if_splits)

definition loop_simplex :: "(real \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex" where
  "loop_simplex p = restrict (\<lambda>x. p (x 1)) (standard_simplex 1)"

lemma loop_simplex_singular:
  assumes "path p" "path_image p \<subseteq> S"
  shows "singular_simplex 1 (top_of_set S) (loop_simplex p)"
proof -
  have coord: "continuous_map (subtopology (powertop_real UNIV) (standard_simplex 1))
      (top_of_set {0..1}) (\<lambda>x. x 1)"
    by (auto simp: continuous_map_in_subtopology standard_simplex_def
        intro: continuous_map_from_subtopology continuous_map_product_projection)
  have p: "continuous_map (top_of_set {0..1}) (top_of_set S) p"
    using assms by (auto simp: continuous_map_subtopology_eu path_def path_image_def)
  show ?thesis
    unfolding loop_simplex_def singular_simplex_def
    using continuous_map_compose[OF coord p]
    by (simp add: o_def)
qed

lemma loop_simplex_edge:
  "t \<in> {0..1} \<Longrightarrow> loop_simplex p (edge_coordinates t) = p t"
  using edge_coordinates_mem[of t]
  by (auto simp: loop_simplex_def edge_coordinates_def)

lemma loop_simplex_boundary:
  "chain_boundary 1 (frag_of (loop_simplex p)) =
    frag_of (restrict (\<lambda>x. p 1) (standard_simplex 0)) -
    frag_of (restrict (\<lambda>x. p 0) (standard_simplex 0))"
proof -
  have strip: "singular_face 1 i (loop_simplex p) = singular_face 1 i (\<lambda>x. p (x 1))"
    if "i \<le> 1" for i
    unfolding loop_simplex_def by (rule singular_face_restrict) (use that in auto)
  have faces: "singular_face 1 0 (loop_simplex p) = restrict (\<lambda>x. p 1) (standard_simplex 0)"
    "singular_face 1 1 (loop_simplex p) = restrict (\<lambda>x. p 0) (standard_simplex 0)"
    by (simp_all only: strip[OF zero_le] strip[OF order_refl])
       (auto simp: singular_face_def simplical_face_def standard_simplex_0 fun_eq_iff restrict_def)
  show ?thesis
    by (simp add: chain_boundary_of sum.atMost_Suc faces[unfolded One_nat_def])
qed

lemma loop_simplex_cycle:
  assumes "is_loop p"
  shows "singular_relcycle 1 (top_of_set circle) {} (frag_of (loop_simplex p))"
  using loop_simplex_singular[OF is_loop_path[OF assms] is_loop_image[OF assms]] assms
  by (simp add: singular_cycle singular_chain_of loop_simplex_boundary[unfolded One_nat_def]
      is_loop_def pathstart_def pathfinish_def)

definition circle_loop_homology where
  "circle_loop_homology p = homologous_rel_set 1 (top_of_set circle) {} (frag_of (loop_simplex p))"

lemma circle_loop_homology_carrier:
  "is_loop p \<Longrightarrow> circle_loop_homology p \<in> carrier (homology_group 1 (top_of_set circle))"
  using loop_simplex_cycle
  by (auto simp: circle_loop_homology_def carrier_relative_homology_group[where p=1, simplified])

lemma loop_simplex_compose:
  "simplex_map 1 f (loop_simplex p) = loop_simplex (f \<circ> p)"
  by (auto simp: simplex_map_def loop_simplex_def fun_eq_iff)

lemma circle_loop_homology_natural:
  assumes "continuous_map (top_of_set circle) (top_of_set circle) f" "is_loop p"
  shows "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f
      (circle_loop_homology p) = circle_loop_homology (f \<circ> p)"
  unfolding circle_loop_homology_def
  using hom_induced_chain_map[OF assms(1) _ loop_simplex_cycle[OF assms(2)]]
  by (simp add: loop_simplex_compose[unfolded One_nat_def])

definition circle_loop_map where
  "circle_loop_map p = p \<circ> (\<lambda>z. Arg2pi z / (2*pi))"

lemma circle_loop_map_homotopic:
  assumes "homotopic_loops circle p q"
  shows "homotopic_with (\<lambda>h. True) (top_of_set circle) (top_of_set circle)
      (circle_loop_map p) (circle_loop_map q)"
  using homotopic_loops_imp_homotopic_circlemaps[OF assms]
  by (simp add: circle_loop_map_def circle_def)

lemma circle_loop_map_continuous:
  assumes "is_loop p"
  shows "continuous_map (top_of_set circle) (top_of_set circle) (circle_loop_map p)"
proof -
  have "homotopic_loops circle p p"
    using assms by (simp add: homotopic_loops_refl is_loop_def)
  then show ?thesis
    using circle_loop_map_homotopic homotopic_with_imp_continuous_maps by blast
qed

lemma circle_loop_map_parametrize:
  assumes "is_loop p" "t \<in> {0..1}"
  shows "circle_loop_map p (circlepath 0 1 t) = p t"
proof (cases "t = 1")
  case True
  have endpoint: "circlepath 0 1 1 = (1::complex)"
    using is_loop_circlepath by (simp add: is_loop_def pathfinish_def)
  have arg1: "Arg2pi 1 = 0" by (simp add: Arg2pi_eq_0)
  show ?thesis
    using assms(1) True endpoint
    by (simp add: circle_loop_map_def is_loop_def pathstart_def pathfinish_def arg1)
next
  case False
  have bounds: "0 \<le> 2*pi*t" "2*pi*t < 2*pi"
    using assms(2) False by (auto simp: mult_nonneg_nonneg)
  have arg: "Arg2pi (circlepath 0 1 t) = 2*pi*t"
    using bounds
    by (simp add: circlepath_def part_circlepath_def linepath_def
        scaleR_conv_of_real Arg2pi_exp mult_ac)
  show ?thesis by (simp add: circle_loop_map_def arg)
qed

lemma circle_loop_homology_map:
  assumes "is_loop p"
  shows "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} (circle_loop_map p)
      (circle_loop_homology (circlepath 0 1)) = circle_loop_homology p"
proof -
  have eq: "loop_simplex (circle_loop_map p \<circ> circlepath 0 1) = loop_simplex p"
    unfolding loop_simplex_def
    using circle_loop_map_parametrize[OF assms]
    by (auto simp: fun_eq_iff standard_simplex_def)
  show ?thesis
    using circle_loop_homology_natural[OF circle_loop_map_continuous[OF assms] is_loop_circlepath]
    by (simp add: circle_loop_homology_def eq)
qed

lemma circle_loop_homology_homotopic:
  assumes "is_loop p" "is_loop q" "homotopic_paths circle p q"
  shows "circle_loop_homology p = circle_loop_homology q"
proof -
  have hom: "homotopic_loops circle p q"
    using assms by (intro homotopic_paths_imp_homotopic_loops) (auto simp: is_loop_def)
  have eq: "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} (circle_loop_map p) =
      hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} (circle_loop_map q)"
    using circle_loop_map_homotopic[OF hom]
    by (intro homology_homotopy_axiom) simp
  show ?thesis
    using eq circle_loop_homology_map[OF assms(1)] circle_loop_homology_map[OF assms(2)]
    by simp
qed

end
