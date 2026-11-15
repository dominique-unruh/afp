theory Circle_Radial_Retract
  imports Circle_Covering
begin

section \<open>The punctured plane retracts onto the circle\<close>

text \<open>
  The preceding circle entry already contains the analytic radial map
  \<open>retr\<close>.  We expose it here with the geometric name used by the later
  homotopy and homology developments, together with its subspace-topology
  interface.
\<close>

definition punctured_plane :: "complex set" where
  "punctured_plane = - {0}"

definition radial_retraction :: "complex \<Rightarrow> complex" where
  "radial_retraction z = retr z"

lemma punctured_plane_eq:
  "punctured_plane = - {0}"
  by (simp add: punctured_plane_def)

lemma radial_retraction_continuous:
  "continuous_on punctured_plane radial_retraction"
  using continuous_on_retr
  by (simp add: punctured_plane_def radial_retraction_def)

lemma radial_retraction_into_circle:
  "radial_retraction \<in> punctured_plane \<rightarrow> circle"
  unfolding radial_retraction_def punctured_plane_def
  by (rule retr_into_circle)

lemma radial_retraction_fixes:
  assumes "z \<in> circle"
  shows "radial_retraction z = z"
  using assms by (simp add: radial_retraction_def retr_fixes)

lemma radial_retraction_maps:
  "retraction_maps (top_of_set punctured_plane) (top_of_set circle)
      radial_retraction id"
  unfolding retraction_maps_def
proof (intro conjI)
  show "continuous_map (top_of_set punctured_plane)
      (top_of_set circle) radial_retraction"
    using radial_retraction_continuous radial_retraction_into_circle
    by (simp add: continuous_map_in_subtopology)
next
  show "continuous_map (top_of_set circle)
      (top_of_set punctured_plane) id"
    using zero_notin_circle
    by (auto simp: continuous_map_in_subtopology punctured_plane_def)
next
  show "\<forall>x \<in> topspace (top_of_set circle). radial_retraction (id x) = x"
    using radial_retraction_fixes by auto
qed

definition radial_homotopy :: "real \<times> complex \<Rightarrow> complex" where
  "radial_homotopy z =
     ((1 - fst z) * (1 / norm (snd z)) + fst z) *\<^sub>R snd z"

lemma radial_homotopy_coeff_pos:
  assumes "t \<in> {0..1}" "z \<in> punctured_plane"
  shows "0 < (1 - t) * (1 / norm z) + t"
proof -
  have z0: "z \<noteq> 0"
    using assms(2) by (simp add: punctured_plane_def)
  have nz: "0 < norm z"
    using z0 by simp
  have t0: "0 \<le> t" and t1: "t \<le> 1"
    using assms(1) by auto
  have ni: "0 < 1 / norm z"
    using nz by (simp add: nz)
  have prod: "0 \<le> (1 - t) * (1 / norm z)"
    using t1 ni by (intro mult_nonneg_nonneg) (linarith, linarith)
  show ?thesis
  proof (cases "t = 0")
    case True
    then show ?thesis using ni by simp
  next
    case False
    then have "0 < t" using t0 by linarith
    then show ?thesis using prod by linarith
  qed
qed

lemma radial_homotopy_into_punctured_plane:
  "radial_homotopy \<in> ({0..1} \<times> punctured_plane) \<rightarrow> punctured_plane"
proof
  fix x :: "real \<times> complex"
  assume x: "x \<in> ({0..1} \<times> punctured_plane)"
  obtain t :: real and z :: complex where xeq: "x = (t,z)"
    by (cases x) simp
  have tz: "(t,z) \<in> ({0..1} \<times> punctured_plane)"
    using x xeq by simp
  have tI: "t \<in> {0..1}" and zP: "z \<in> punctured_plane"
    using tz by auto
  have coeff: "0 < (1 - t) * (1 / norm z) + t"
    by (rule radial_homotopy_coeff_pos [OF tI zP])
  have nz: "0 < norm z"
    using zP by (simp add: punctured_plane_def)
  have hn: "0 < norm (radial_homotopy (t,z))"
    unfolding radial_homotopy_def
    using coeff nz
    by (simp add: norm_scaleR abs_of_pos coeff)
  have hne: "radial_homotopy (t,z) \<noteq> 0"
    using hn by auto
  show "radial_homotopy x \<in> punctured_plane"
    using hne xeq by (simp add: punctured_plane_def)
qed

lemma radial_homotopy_continuous:
  "continuous_on ({0..1} \<times> punctured_plane) radial_homotopy"
  unfolding radial_homotopy_def
  apply (intro continuous_intros)
  by (auto simp: punctured_plane_def)

lemma radial_homotopy_continuous_map:
  "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set punctured_plane))
      (top_of_set punctured_plane) radial_homotopy"
  using radial_homotopy_continuous radial_homotopy_into_punctured_plane
  by (simp add: continuous_map_in_subtopology prod_topology_subtopology_eu)

lemma radial_homotopy_zero:
  "radial_homotopy (0,z) = radial_retraction z"
  by (simp add: radial_homotopy_def radial_retraction_def retr_def
      scaleR_conv_of_real divide_inverse mult.commute)

lemma radial_homotopy_one:
  "radial_homotopy (1,z) = id z"
  by (simp add: radial_homotopy_def)

lemma radial_deformation:
  "homotopic_with (\<lambda>f. True) (top_of_set punctured_plane) (top_of_set punctured_plane)
      radial_retraction id"
  unfolding homotopic_with_def
proof (intro exI conjI)
  show "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set punctured_plane))
      (top_of_set punctured_plane) radial_homotopy"
    by (rule radial_homotopy_continuous_map)
  show "\<forall>x. radial_homotopy (0,x) = radial_retraction x"
    using radial_homotopy_zero by simp
  show "\<forall>x. radial_homotopy (1,x) = id x"
    using radial_homotopy_one by simp
  show "\<forall>t \<in> {0..1::real}. True"
    by simp
qed

lemma punctured_plane_homotopy_equivalent_circle:
  "top_of_set punctured_plane homotopy_equivalent_space top_of_set circle"
  by (rule deformation_retract_imp_homotopy_equivalent_space
      [OF radial_deformation radial_retraction_maps])

end
