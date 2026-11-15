theory Torus_Fundamental_Group
  imports "Circle_Torus_Algebraic_Topology.Circle_Product"
begin

section \<open>The fundamental group of the torus\<close>

text \<open>Elements are homotopy classes of loops based at \<open>(1,1)\<close>.
  Multiplication is induced by path concatenation. The two lift endpoints
  give an explicit isomorphism to the product of the additive integer groups.\<close>

definition torus_class where
  "torus_class p = {q. torus_loop q \<and> homotopic_paths (circle \<times> circle) p q}"

definition torus_classes where
  "torus_classes = {torus_class p |p. torus_loop p}"

definition torus_rep where
  "torus_rep A = (SOME p. torus_loop p \<and> torus_class p = A)"

lemma torus_class_mem:
  "torus_loop p \<Longrightarrow> torus_class p \<in> torus_classes"
  by (auto simp: torus_classes_def)

lemma torus_class_self:
  "torus_loop p \<Longrightarrow> p \<in> torus_class p"
  by (simp add: torus_class_def torus_loop_def)

lemma torus_class_eq_iff:
  assumes "torus_loop p" "torus_loop q"
  shows "torus_class p = torus_class q \<longleftrightarrow>
    torus_lift_endpoint p = torus_lift_endpoint q"
proof
  assume "torus_class p = torus_class q"
  then have "q \<in> torus_class p"
    using torus_class_self[OF assms(2)] by simp
  then show "torus_lift_endpoint p = torus_lift_endpoint q"
    using assms by (simp add: torus_class_def torus_loop_homotopic_iff)
next
  assume "torus_lift_endpoint p = torus_lift_endpoint q"
  with assms show "torus_class p = torus_class q"
    by (auto simp: torus_class_def torus_loop_homotopic_iff)
qed

lemma torus_rep_props:
  assumes "A \<in> torus_classes"
  shows "torus_loop (torus_rep A) \<and> torus_class (torus_rep A) = A"
proof -
  have "\<exists>p. torus_loop p \<and> torus_class p = A"
    using assms by (auto simp: torus_classes_def)
  then show ?thesis unfolding torus_rep_def by (rule someI_ex)
qed

definition torus_degree where
  "torus_degree A = torus_lift_endpoint (torus_rep A)"

lemma torus_degree_class:
  assumes "torus_loop p"
  shows "torus_degree (torus_class p) = torus_lift_endpoint p"
  using torus_rep_props[OF torus_class_mem[OF assms]] assms
  by (auto simp: torus_degree_def torus_class_eq_iff)

lemma torus_degree_inj: "inj_on torus_degree torus_classes"
proof (rule inj_onI)
  fix A B
  assume A: "A \<in> torus_classes" and B: "B \<in> torus_classes"
    and eq: "torus_degree A = torus_degree B"
  have "torus_class (torus_rep A) = torus_class (torus_rep B)"
    apply (rule iffD2[OF torus_class_eq_iff])
    using torus_rep_props[OF A] torus_rep_props[OF B] eq
    by (auto simp: torus_degree_def)
  then show "A = B" using torus_rep_props A B by metis
qed

lemma torus_endpoint_product:
  "torus_lift_endpoint (product_path p q) =
    (circle_lift_endpoint p, circle_lift_endpoint q)"
  by (simp add: torus_lift_endpoint_def product_path_def o_def)

lemma circle_endpoint_surj:
  obtains p where "is_loop p" "circle_lift_endpoint p = n"
proof -
  have "n \<in> deg ` carrier pi1_circle" by (subst deg_surj) simp
  then obtain A where A: "A \<in> carrier pi1_circle" "deg A = n"
    by blast
  have L: "is_loop (rep A)" and C: "loop_class (rep A) = A"
    using A rep_props by auto
  have "circle_lift_endpoint (rep A) = n"
    using A C circle_lift_endpoint_eq_wnd[OF L] deg_class[OF L] by simp
  then show thesis using that L by blast
qed

lemma torus_degree_surj: "torus_degree ` torus_classes = UNIV"
proof (rule UNIV_eq_I[THEN sym])
  fix z :: "int \<times> int"
  obtain p where p: "is_loop p" "circle_lift_endpoint p = fst z"
    by (rule circle_endpoint_surj)
  obtain q where q: "is_loop q" "circle_lift_endpoint q = snd z"
    by (rule circle_endpoint_surj)
  have L: "torus_loop (product_path p q)"
    by (rule torus_loop_product[OF p(1) q(1)])
  have "torus_degree (torus_class (product_path p q)) = z"
    by (simp add: torus_degree_class[OF L] torus_endpoint_product p q)
  then show "z \<in> torus_degree ` torus_classes"
    using torus_class_mem[OF L] by blast
qed

definition pi1_torus :: "(real \<Rightarrow> complex \<times> complex) set monoid" where
  "pi1_torus = \<lparr>carrier = torus_classes,
    mult = (\<lambda>A B. torus_class (torus_rep A +++ torus_rep B)),
    one = torus_class (product_path (linepath 1 1) (linepath 1 1))\<rparr>"

lemma torus_mult_class:
  assumes "torus_loop p" "torus_loop q"
  shows "torus_class p \<otimes>\<^bsub>pi1_torus\<^esub> torus_class q = torus_class (p +++ q)"
proof -
  have p: "torus_loop (torus_rep (torus_class p))"
    "torus_lift_endpoint (torus_rep (torus_class p)) = torus_lift_endpoint p"
    using torus_rep_props[OF torus_class_mem[OF assms(1)]] assms(1)
    by (auto simp: torus_class_eq_iff)
  have q: "torus_loop (torus_rep (torus_class q))"
    "torus_lift_endpoint (torus_rep (torus_class q)) = torus_lift_endpoint q"
    using torus_rep_props[OF torus_class_mem[OF assms(2)]] assms(2)
    by (auto simp: torus_class_eq_iff)
  show ?thesis
    unfolding pi1_torus_def
    using assms p q
    by (simp add: torus_class_eq_iff torus_loop_join torus_lift_endpoint_join)
qed

lemma torus_mult_closed:
  assumes "A \<in> torus_classes" "B \<in> torus_classes"
  shows "A \<otimes>\<^bsub>pi1_torus\<^esub> B \<in> torus_classes"
  using torus_rep_props assms
  by (auto simp: pi1_torus_def intro: torus_class_mem torus_loop_join)

lemma torus_degree_mult:
  assumes "A \<in> torus_classes" "B \<in> torus_classes"
  shows "torus_degree (A \<otimes>\<^bsub>pi1_torus\<^esub> B) = torus_degree A + torus_degree B"
proof -
  have A: "torus_loop (torus_rep A)" and B: "torus_loop (torus_rep B)"
    using torus_rep_props assms by blast+
  have "torus_degree (A \<otimes>\<^bsub>pi1_torus\<^esub> B) =
      torus_lift_endpoint (torus_rep A +++ torus_rep B)"
    by (simp only: pi1_torus_def monoid.select_convs
        torus_degree_class[OF torus_loop_join[OF A B]])
  then show ?thesis
    by (simp add: torus_lift_endpoint_join[OF A B] torus_degree_def)
qed

lemma torus_one_closed: "\<one>\<^bsub>pi1_torus\<^esub> \<in> torus_classes"
  by (simp add: pi1_torus_def torus_class_mem torus_loop_product)

lemma torus_degree_one: "torus_degree \<one>\<^bsub>pi1_torus\<^esub> = 0"
  by (simp add: pi1_torus_def torus_degree_class torus_loop_product
      torus_endpoint_product circle_lift_endpoint_linepath zero_prod_def)

theorem group_pi1_torus: "group pi1_torus"
proof (rule groupI)
  show "x \<otimes>\<^bsub>pi1_torus\<^esub> y \<in> carrier pi1_torus"
    if "x \<in> carrier pi1_torus" "y \<in> carrier pi1_torus" for x y
    using that torus_mult_closed by (simp add: pi1_torus_def)
  show "\<one>\<^bsub>pi1_torus\<^esub> \<in> carrier pi1_torus"
    using torus_one_closed by (simp add: pi1_torus_def)
  show "(x \<otimes>\<^bsub>pi1_torus\<^esub> y) \<otimes>\<^bsub>pi1_torus\<^esub> z =
      x \<otimes>\<^bsub>pi1_torus\<^esub> (y \<otimes>\<^bsub>pi1_torus\<^esub> z)"
    if "x \<in> carrier pi1_torus" "y \<in> carrier pi1_torus" "z \<in> carrier pi1_torus" for x y z
  proof -
    have C: "x \<in> torus_classes" "y \<in> torus_classes" "z \<in> torus_classes"
      using that by (simp_all add: pi1_torus_def)
    show ?thesis
      by (rule inj_onD[OF torus_degree_inj])
        (simp_all add: torus_degree_mult torus_mult_closed C add.assoc)
  qed
  show "\<one>\<^bsub>pi1_torus\<^esub> \<otimes>\<^bsub>pi1_torus\<^esub> x = x"
    if "x \<in> carrier pi1_torus" for x
  proof -
    have C: "x \<in> torus_classes" using that by (simp add: pi1_torus_def)
    show ?thesis
      by (rule inj_onD[OF torus_degree_inj])
        (simp_all add: torus_degree_mult torus_mult_closed torus_one_closed torus_degree_one C)
  qed
  show "\<exists>y\<in>carrier pi1_torus. y \<otimes>\<^bsub>pi1_torus\<^esub> x = \<one>\<^bsub>pi1_torus\<^esub>"
    if "x \<in> carrier pi1_torus" for x
  proof -
    have C: "x \<in> torus_classes" using that by (simp add: pi1_torus_def)
    have "- torus_degree x \<in> torus_degree ` torus_classes"
      by (simp add: torus_degree_surj)
    then obtain y where Y: "y \<in> torus_classes" "torus_degree y = - torus_degree x"
      by (auto simp: image_iff)
    have "y \<otimes>\<^bsub>pi1_torus\<^esub> x = \<one>\<^bsub>pi1_torus\<^esub>"
      by (rule inj_onD[OF torus_degree_inj])
        (simp_all add: torus_degree_mult torus_mult_closed torus_one_closed torus_degree_one C Y)
    with Y show ?thesis by (auto simp: pi1_torus_def)
  qed
qed

lemma torus_inverse_class:
  assumes "torus_loop p"
  shows "inv\<^bsub>pi1_torus\<^esub> (torus_class p) = torus_class (reversepath p)"
proof (rule group.inv_equality[OF group_pi1_torus])
  have C: "torus_class p \<in> torus_classes" "torus_class (reversepath p) \<in> torus_classes"
    using assms by (auto intro: torus_class_mem torus_loop_reverse)
  show "torus_class (reversepath p) \<otimes>\<^bsub>pi1_torus\<^esub> torus_class p = \<one>\<^bsub>pi1_torus\<^esub>"
    by (rule inj_onD[OF torus_degree_inj])
      (simp_all add: torus_degree_mult C torus_degree_class torus_loop_reverse assms
        torus_lift_endpoint_reverse torus_degree_one torus_mult_closed torus_one_closed)
  show "torus_class p \<in> carrier pi1_torus" "torus_class (reversepath p) \<in> carrier pi1_torus"
    using C by (simp_all add: pi1_torus_def)
qed

theorem torus_degree_iso:
  "torus_degree \<in> iso pi1_torus
    (Fundamental_Group_Circle.integer_group \<times>\<times> Fundamental_Group_Circle.integer_group)"
proof (rule isoI)
  show "torus_degree \<in> hom pi1_torus
    (Fundamental_Group_Circle.integer_group \<times>\<times> Fundamental_Group_Circle.integer_group)"
    using torus_degree_mult
    by (auto simp: hom_def pi1_torus_def DirProd_def plus_prod_def split: prod.splits)
  show "bij_betw torus_degree (carrier pi1_torus)
    (carrier (Fundamental_Group_Circle.integer_group \<times>\<times> Fundamental_Group_Circle.integer_group))"
    using torus_degree_inj torus_degree_surj
    by (simp add: bij_betw_def pi1_torus_def DirProd_def)
qed

theorem pi1_torus_iso_integer_product:
  "pi1_torus \<cong>
    (Fundamental_Group_Circle.integer_group \<times>\<times> Fundamental_Group_Circle.integer_group)"
  by (rule is_isoI[OF torus_degree_iso])

end
