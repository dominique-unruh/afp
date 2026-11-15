theory Circle_Loop_Concatenation
  imports Circle_Loop_Homology
begin

section \<open>Concatenation and addition of cycles\<close>

lemma homology_class_add:
  "homologous_rel_set 1 X {} (a+b) =
    homologous_rel_set 1 X {} a \<otimes>\<^bsub>homology_group 1 X\<^esub> homologous_rel_set 1 X {} b"
proof -
  have split: "\<exists>u v. homologous_rel 1 X {} a u \<and> homologous_rel 1 X {} b v \<and> x=u+v"
    if "homologous_rel 1 X {} (a+b) x" for x
    using that by (metis diff_add_cancel diff_diff_eq2 homologous_rel_def homologous_rel_refl)
  show ?thesis
    using split by (auto simp: mult_relative_homology_group[where p=1, simplified]
        intro: homologous_rel_add)
qed

definition join_simplex where
  "join_simplex p q = restrict (\<lambda>x. (p +++ q) (x 1 / 2 + x 2)) (standard_simplex 2)"

lemma join_simplex_singular:
  assumes "is_loop p" "is_loop q"
  shows "singular_simplex 2 (top_of_set circle) (join_simplex p q)"
proof -
  have coord: "continuous_map (subtopology (powertop_real UNIV) (standard_simplex 2))
      (top_of_set {0..1}) (\<lambda>x. x 1 / 2 + x 2)"
  proof (subst continuous_map_in_subtopology, intro conjI)
    show "continuous_map (subtopology (powertop_real UNIV) (standard_simplex 2)) euclideanreal
        (\<lambda>x. x 1 / 2 + x 2)"
      by (intro continuous_intros continuous_map_from_subtopology continuous_map_product_projection) auto
    have bounds: "(\<lambda>x. x 1 / 2 + x 2) ` topspace (subtopology (powertop_real UNIV) (standard_simplex 2)) \<subseteq> {0..1}"
    proof (rule image_subsetI)
      fix x assume "x \<in> topspace (subtopology (powertop_real UNIV) (standard_simplex 2))"
      then have x: "0 \<le> x 0" "0 \<le> x 1" "0 \<le> x 2" "x 0 + x 1 + x 2 = 1"
        by (auto simp: standard_simplex_def sum.atMost_Suc numeral_2_eq_2)
      show "x 1 / 2 + x 2 \<in> {0..1}" using x by auto
    qed
    show "(\<lambda>x. x 1 / 2 + x 2) \<in> topspace (subtopology (powertop_real UNIV) (standard_simplex 2)) \<rightarrow> {0..1}"
      using bounds by auto
  qed
  have p: "continuous_map (top_of_set {0..1}) (top_of_set circle) (p +++ q)"
    using is_loop_join[OF assms]
    by (auto simp: continuous_map_subtopology_eu is_loop_def path_def path_image_def)
  show ?thesis unfolding join_simplex_def singular_simplex_def
    using continuous_map_compose[OF coord p] by (simp add: o_def)
qed

lemma join_simplex_faces:
  assumes "is_loop p" "is_loop q"
  shows "singular_face 2 0 (join_simplex p q) = loop_simplex q"
    "singular_face 2 1 (join_simplex p q) = loop_simplex (p +++ q)"
    "singular_face 2 2 (join_simplex p q) = loop_simplex p"
proof -
  have strip: "singular_face 2 i (join_simplex p q) =
      singular_face 2 i (\<lambda>x. (p +++ q) (x 1 / 2 + x 2))"
    if "i \<le> 2" for i
    unfolding join_simplex_def by (rule singular_face_restrict) (use that in auto)
  have ends: "p 1 = q 0" using assms by (simp add: is_loop_def pathstart_def pathfinish_def)
  have glue: "(p +++ q) (s/2+t) = q t" if "s+t=1" "0 \<le> t" for s t
  proof (cases "t=0")
    case True then show ?thesis using that ends by (simp add: joinpaths_def)
  next
    case False
    have gt: "s/2+t > 1/2" using that False by linarith
    have eq: "s + 2*t - 1 = t" using that by linarith
    show ?thesis using gt by (simp add: joinpaths_def eq)
  qed
  show "singular_face 2 0 (join_simplex p q) = loop_simplex q"
    apply (subst strip)
     apply simp
    apply (simp only: singular_face_def loop_simplex_def)
    using ends
    by (auto simp: fun_eq_iff simplical_face_def standard_simplex_def sum.atMost_Suc
        numeral_2_eq_2 glue)
  show "singular_face 2 1 (join_simplex p q) = loop_simplex (p +++ q)"
    apply (subst strip)
     apply simp
    apply (simp only: singular_face_def loop_simplex_def)
    by (auto simp: simplical_face_def fun_eq_iff)
  show "singular_face 2 2 (join_simplex p q) = loop_simplex p"
    apply (subst strip)
     apply simp
    apply (simp only: singular_face_def loop_simplex_def)
    by (auto simp: fun_eq_iff simplical_face_def standard_simplex_def joinpaths_def numeral_2_eq_2)
qed

lemma circle_loop_homology_join:
  assumes "is_loop p" "is_loop q"
  shows "circle_loop_homology (p +++ q) =
    circle_loop_homology p \<otimes>\<^bsub>homology_group 1 (top_of_set circle)\<^esub> circle_loop_homology q"
proof -
  have boundary: "chain_boundary 2 (frag_of (join_simplex p q)) =
      frag_of (loop_simplex q) - frag_of (loop_simplex (p +++ q)) + frag_of (loop_simplex p)"
    using join_simplex_faces[OF assms]
    by (simp add: chain_boundary_of sum.atMost_Suc numeral_2_eq_2)
  have "homologous_rel 1 (top_of_set circle) {} (frag_of (loop_simplex (p +++ q)))
      (frag_of (loop_simplex p) + frag_of (loop_simplex q))"
    unfolding homologous_rel_def singular_boundary
    by (rule exI[where x="-frag_of (join_simplex p q)"])
       (simp add: singular_chain_minus singular_chain_of
        join_simplex_singular[OF assms, unfolded numeral_2_eq_2]
        chain_boundary_minus boundary[unfolded numeral_2_eq_2] algebra_simps)
  then show ?thesis
    by (simp add: circle_loop_homology_def
        homology_class_add[unfolded One_nat_def, symmetric] homologous_rel_set_eq)
qed

lemma circle_loop_homology_constant:
  "circle_loop_homology (linepath 1 1) = \<one>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>"
proof -
  interpret H: group "homology_group 1 (top_of_set circle)" by simp
  have eq: "(linepath (1::complex) 1 +++ linepath 1 1) = linepath 1 1"
    by (auto simp: fun_eq_iff joinpaths_def linepath_refl)
  show ?thesis
    using circle_loop_homology_join[OF is_loop_linepath_1 is_loop_linepath_1]
    by (simp add: eq H.l_cancel_one' circle_loop_homology_carrier)
qed

lemma circle_loop_homology_reverse:
  assumes "is_loop p"
  shows "circle_loop_homology (reversepath p) =
    inv\<^bsub>homology_group 1 (top_of_set circle)\<^esub> (circle_loop_homology p)"
proof -
  interpret H: group "homology_group 1 (top_of_set circle)" by simp
  have hom: "homotopic_paths circle (reversepath p +++ p) (linepath 1 1)"
    using homotopic_paths_linv[OF is_loop_path[OF assms] is_loop_image[OF assms]] assms
    by (simp add: is_loop_def)
  have eq: "circle_loop_homology (reversepath p) \<otimes>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>
      circle_loop_homology p = \<one>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>"
    using circle_loop_homology_homotopic[OF is_loop_join[OF is_loop_reversepath[OF assms] assms]
        is_loop_linepath_1 hom]
    by (simp add: circle_loop_homology_join is_loop_reversepath assms circle_loop_homology_constant)
  show ?thesis
    by (rule sym, rule H.inv_equality) (use eq assms in \<open>auto intro: circle_loop_homology_carrier\<close>)
qed

lemma circle_loop_homology_cpow:
  "circle_loop_homology (Fundamental_Group_Circle.cpow n) =
    circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> n"
proof (induction n)
  case 0 then show ?case by (simp add: circle_loop_homology_constant[simplified linepath_refl])
next
  case (Suc n)
  have step: "circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> Suc n =
      circle_loop_homology (circlepath 0 1) \<otimes>\<^bsub>homology_group 1 (top_of_set circle)\<^esub>
      (circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> n)"
    by (rule monoid.nat_pow_Suc2)
       (simp_all add: group.is_monoid circle_loop_homology_carrier is_loop_circlepath)
  then show ?case
    using Suc
    by (simp only: Fundamental_Group_Circle.cpow.simps
        circle_loop_homology_join[OF is_loop_circlepath is_loop_cpow] step)
qed

theorem circle_loop_homology_winding:
  assumes "is_loop p"
  shows "circle_loop_homology p =
    circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> wnd p"
proof (cases "0 \<le> wnd p")
  case True
  have eq: "circle_lift_endpoint p = circle_lift_endpoint (Fundamental_Group_Circle.cpow (nat (wnd p)))"
    by (simp add: circle_lift_endpoint_eq_wnd[OF assms] circle_lift_endpoint_cpow True)
  have hom: "homotopic_paths circle p (Fundamental_Group_Circle.cpow (nat (wnd p)))"
    by (rule circle_lift_endpoint_eq_homotopic[OF assms is_loop_cpow eq])
  show ?thesis
    using circle_loop_homology_homotopic[OF assms is_loop_cpow hom]
    by (simp add: circle_loop_homology_cpow int_pow_int[symmetric] True)
next
  case False
  have nonpos: "wnd p \<le> 0" using False by linarith
  have eq: "circle_lift_endpoint p = circle_lift_endpoint (reversepath (Fundamental_Group_Circle.cpow (nat (-wnd p))))"
    by (simp add: circle_lift_endpoint_eq_wnd[OF assms] circle_lift_endpoint_reverse is_loop_cpow
        circle_lift_endpoint_cpow nonpos)
  have hom: "homotopic_paths circle p (reversepath (Fundamental_Group_Circle.cpow (nat (-wnd p))))"
    by (rule circle_lift_endpoint_eq_homotopic[OF assms is_loop_reversepath[OF is_loop_cpow] eq])
  have class_eq: "circle_loop_homology p =
      inv\<^bsub>homology_group 1 (top_of_set circle)\<^esub>
        (circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> nat (-wnd p))"
    using circle_loop_homology_homotopic[OF assms is_loop_reversepath[OF is_loop_cpow] hom]
    by (simp only: circle_loop_homology_reverse[OF is_loop_cpow] circle_loop_homology_cpow)
  have neg: "wnd p < 0" using False by linarith
  have power: "circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> wnd p =
      inv\<^bsub>homology_group 1 (top_of_set circle)\<^esub>
        (circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub> nat (-wnd p))"
    by (rule trans[OF int_pow_def2]) (simp only: if_P[OF neg])
  show ?thesis using class_eq power by simp
qed

end
