theory Circle_Torus_Algebraic_Topology
  imports Torus_Fundamental_Group Circle_SVK Circle_Homology_Action
begin

section \<open>Circle, torus, and punctured-plane invariants: collected results\<close>

text \<open>
  This theory collects the circle, torus, and punctured-plane results. Its
  component theories separate the reusable covering-space API, product and
  retract constructions, the Seifert--van Kampen interface, and the
  homology/degree consequences.
\<close>

theorem circle_fundamental_group_summary:
  "pi1_circle \<cong> Fundamental_Group_Circle.integer_group"
  by (rule pi1_circle_iso_integers)

theorem circle_reduced_homology_summary:
  "reduced_homology_group 1 (top_of_set circle) \<cong>
   Elementary_Groups.integer_group"
  using reduced_homology_group_circle_one by auto

theorem punctured_plane_homology_and_noncontractibility:
  "reduced_homology_group 1 (top_of_set punctured_plane) \<cong> integer_group \<and>
   \<not> contractible_space (top_of_set punctured_plane)"
  using reduced_homology_group_punctured_plane_one
    punctured_plane_not_contractible by auto

end
