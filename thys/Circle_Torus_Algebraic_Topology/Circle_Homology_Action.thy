theory Circle_Homology_Action
  imports Circle_Winding_Cocycle Circle_Loop_Concatenation
begin

section \<open>Winding number and the induced homology map\<close>

text \<open>An endomorphism of an infinite cyclic group is determined by its
  action on any nonzero element. Thus the nonzero standard-loop class and
  the loop winding formula suffice; we need not first prove that this class
  is a primitive generator. The final theorem applies to arbitrary continuous
  circle maps, using a rotation homotopy to normalize the basepoint.\<close>

lemma infinite_cyclic_hom_determined:
  assumes grp: "group G" and iso: "h \<in> iso G Elementary_Groups.integer_group"
    and hom: "F \<in> hom G G"
    and a: "a \<in> carrier G" "a \<noteq> \<one>\<^bsub>G\<^esub>"
    and image: "F a = a [^]\<^bsub>G\<^esub> (n::int)"
    and x: "x \<in> carrier G"
  shows "h (F x) = n * h x"
proof -
  interpret G: group G by (rule grp)
  interpret H: group_hom G Elementary_Groups.integer_group h
    using iso by (simp add: group_hom_def group_hom_axioms_def grp iso_def)
  interpret F: group_hom G G F
    by (simp add: group_hom_def group_hom_axioms_def grp hom)
  obtain k where inv: "group_isomorphisms G Elementary_Groups.integer_group h k"
    using iso G.iso_iff_group_isomorphisms by blast
  interpret K: group_hom Elementary_Groups.integer_group G k
    using inv by (auto simp: group_hom_def group_hom_axioms_def group_isomorphisms_def grp)
  have k1: "k 1 \<in> carrier G" using K.hom_closed[of 1] by simp
  have repr: "y = k 1 [^]\<^bsub>G\<^esub> h y" if "y \<in> carrier G" for y
  proof -
    have "k (h y) = y" using inv that by (simp add: group_isomorphisms_def)
    moreover have "k (h y) = k 1 [^]\<^bsub>G\<^esub> h y"
      using K.hom_int_pow[of 1 "h y"] by simp
    ultimately show ?thesis by simp
  qed
  have action: "h (F y) = h (F (k 1)) * h y" if "y \<in> carrier G" for y
    by (subst repr[OF that]) (simp add: F.hom_int_pow H.hom_int_pow k1 F.hom_closed)
  have inj: "inj_on h (carrier G)" 
    using iso by (simp add: iso_def bij_betw_def)
  then have ha: "h a \<noteq> 0"
    using H.inj_on_one_iff a by force
  have "h (F (k 1)) * h a = n * h a"
    using action[OF a(1)] image H.hom_int_pow[OF a(1), of n]
    by (auto simp: mult.commute)
  then have "h (F (k 1)) = n" using ha by simp
  then show ?thesis using action[OF x] by simp
qed

lemma circle_first_homology_iso:
  "homology_group 1 (top_of_set circle) \<cong> Elementary_Groups.integer_group"
  using reduced_homology_group_circle_one
  by (simp add: un_reduced_homology_group)

lemma circle_based_map_loop:
  assumes "continuous_map (top_of_set circle) (top_of_set circle) f" "f 1 = 1" "is_loop p"
  shows "is_loop (f \<circ> p)"
proof -
  have c: "continuous_on circle f" using assms(1) by (simp add: continuous_map_subtopology_eu)
  have path: "path (f \<circ> p)"
    by (rule path_continuous_image[OF is_loop_path[OF assms(3)]])
       (rule continuous_on_subset[OF c is_loop_image[OF assms(3)]])
  show ?thesis using assms path
    by (auto simp: continuous_map_subtopology_eu is_loop_def pathstart_def pathfinish_def path_image_def)
qed

theorem circle_homology_action_winding_based:
  assumes coordinates: "h \<in> iso (homology_group 1 (top_of_set circle)) Elementary_Groups.integer_group"
    and f: "continuous_map (top_of_set circle) (top_of_set circle) f" "f 1 = 1"
    and x: "x \<in> carrier (homology_group 1 (top_of_set circle))"
  shows "h (hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f x) =
    wnd (f \<circ> circlepath 0 1) * h x"
proof (rule infinite_cyclic_hom_determined[OF _ coordinates _ _ circle_standard_loop_homology_nontrivial _ x])
  show "group (homology_group 1 (top_of_set circle))" by simp
  show "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f \<in>
      hom (homology_group 1 (top_of_set circle)) (homology_group 1 (top_of_set circle))"
    by (rule hom_induced_empty_hom)
  show "circle_loop_homology (circlepath 0 1) \<in> carrier (homology_group 1 (top_of_set circle))"
    by (rule circle_loop_homology_carrier[OF is_loop_circlepath])
  show "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f
      (circle_loop_homology (circlepath 0 1)) =
      circle_loop_homology (circlepath 0 1) [^]\<^bsub>homology_group 1 (top_of_set circle)\<^esub>
        wnd (f \<circ> circlepath 0 1)"
    using circle_loop_homology_natural[OF f(1) is_loop_circlepath]
      circle_loop_homology_winding[OF circle_based_map_loop[OF f is_loop_circlepath]] by simp
qed

lemma circle_map_winding_homotopic:
  assumes "homotopic_with_canon (\<lambda>h. True) circle circle f g"
  shows "wnd (f \<circ> circlepath 0 1) = wnd (g \<circ> circlepath 0 1)"
proof -
  have param: "circlepath 0 1 = exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>)"
    by (auto simp: fun_eq_iff circlepath_def part_circlepath_def
        linepath_def scaleR_conv_of_real algebra_simps)
  have hom: "homotopic_loops circle (f \<circ> circlepath 0 1) (g \<circ> circlepath 0 1)"
    using homotopic_circlemaps_imp_homotopic_loops[where f=f and g=g and S=circle] assms
    by (simp add: circle_def param o_assoc)
  have "homotopic_loops (-{0}) (f \<circ> circlepath 0 1) (g \<circ> circlepath 0 1)"
    by (rule homotopic_loops_subset[OF hom]) (auto simp: circle_def sphere_def)
  then have "winding_number (f \<circ> circlepath 0 1) 0 = winding_number (g \<circ> circlepath 0 1) 0"
    by (rule winding_number_homotopic_loops)
  then show ?thesis by (simp add: wnd_def)
qed

lemma circle_map_based_normalization:
  assumes f: "continuous_map (top_of_set circle) (top_of_set circle) f"
  obtains g where "continuous_map (top_of_set circle) (top_of_set circle) g" "g 1 = 1"
    "homotopic_with_canon (\<lambda>h. True) circle circle f g"
proof -
  have fc: "continuous_on circle f" and fim: "f \<in> circle \<rightarrow> circle"
    using f by auto
  have one: "(1::complex) \<in> circle" by (simp add: circle_def)
  have f1: "norm (f 1) = 1" using fim one norm_of_circle by blast
  have nz: "f 1 \<noteq> 0" using f1 by auto
  have inv: "inverse (f 1) \<in> circle" using f1 by (simp add: circle_def sphere_def norm_inverse)
  have pc: "path_connected circle"
    unfolding circle_def by (rule path_connected_sphere) simp
  obtain r where r: "path r" "path_image r \<subseteq> circle"
    "pathstart r = 1" "pathfinish r = inverse (f 1)"
    using pc one inv unfolding path_connected_def by blast
  define g where "g z = inverse (f 1) * f z" for z
  define H where "H x = r (fst x) * f (snd x)" for x
  have rc: "continuous_on {0..1} r" using r(1) by (simp only: path_def)
  have rcomp: "continuous_on ({0..1} \<times> circle) (\<lambda>x. r (fst x))"
    by (rule continuous_on_compose2[OF rc]) (auto intro: continuous_on_fst)
  have fcomp: "continuous_on ({0..1} \<times> circle) (\<lambda>x. f (snd x))"
    by (rule continuous_on_compose2[OF fc]) (auto intro: continuous_on_snd)
  have hc: "continuous_on ({0..1} \<times> circle) H"
    unfolding H_def by (rule continuous_on_mult[OF rcomp fcomp])
  have rn: "norm (r t) = 1" if "t \<in> {0..1}" for t
    using r(2) that by (auto simp: path_image_def circle_def sphere_def subset_iff)
  have fn: "norm (f z) = 1" if "z \<in> circle" for z
    using fim that norm_of_circle by blast
  have hi: "H \<in> ({0..1} \<times> circle) \<rightarrow> circle"
  proof (rule Pi_I)
    fix x :: "real \<times> complex" assume x: "x \<in> {0..1} \<times> circle"
    have xt: "fst x \<in> {0..1}" and xz: "snd x \<in> circle" using x by auto
    have "norm (H x) = 1"
      unfolding H_def by (simp add: norm_mult rn[OF xt] fn[OF xz])
    then show "H x \<in> circle" by (simp add: circle_def sphere_def)
  qed
  have cm: "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set circle)) (top_of_set circle) H"
    using hc hi by (simp add: continuous_map_in_subtopology prod_topology_subtopology_eu)
  have hom: "homotopic_with_canon (\<lambda>h. True) circle circle f g"
    unfolding homotopic_with_def
    by (rule exI[where x=H])
       (use cm r in \<open>auto simp: H_def g_def pathstart_def pathfinish_def\<close>)
  have gc: "continuous_map (top_of_set circle) (top_of_set circle) g"
    using hom homotopic_with_imp_continuous_maps by blast
  show thesis by (rule that[OF gc _ hom]) (simp add: g_def nz)
qed

theorem circle_homology_action_winding:
  assumes coordinates: "h \<in> iso (homology_group 1 (top_of_set circle)) Elementary_Groups.integer_group"
    and f: "continuous_map (top_of_set circle) (top_of_set circle) f"
    and x: "x \<in> carrier (homology_group 1 (top_of_set circle))"
  shows "h (hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f x) =
    wnd (f \<circ> circlepath 0 1) * h x"
proof -
  obtain g where g: "continuous_map (top_of_set circle) (top_of_set circle) g" "g 1 = 1"
    and hom: "homotopic_with_canon (\<lambda>h. True) circle circle f g"
    by (rule circle_map_based_normalization[OF f])
  have eq: "hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} f =
      hom_induced 1 (top_of_set circle) {} (top_of_set circle) {} g"
    by (rule homology_homotopy_axiom) (use hom in simp)
  show ?thesis
    using circle_homology_action_winding_based[OF coordinates g x]
      circle_map_winding_homotopic[OF hom] eq by simp
qed

end
