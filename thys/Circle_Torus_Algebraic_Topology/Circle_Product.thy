theory Circle_Product
  imports Circle_Covering Covering_Spaces
begin

section \<open>Product paths and torus loops\<close>

text \<open>
  The product construction is the first genuinely functorial extension of the
  circle calculation.  We keep the path-level presentation explicit: this
  makes the two integer coordinates available independently of the quotient
  presentation constructed in the torus fundamental-group theory.
\<close>

definition product_path ::
  "(real \<Rightarrow> 'a::topological_space) \<Rightarrow>
   (real \<Rightarrow> 'b::topological_space) \<Rightarrow>
   (real \<Rightarrow> 'a \<times> 'b)"
where
  "product_path p q = (\<lambda>t. (p t, q t))"

lemma path_product_path:
  assumes "path p" "path q"
  shows "path (product_path p q)"
  using assms unfolding product_path_def path_def
  by (intro continuous_on_Pair)

lemma path_image_product_path:
  "path_image (product_path p q) \<subseteq> path_image p \<times> path_image q"
  by (auto simp: product_path_def path_image_def)

lemma pathstart_product_path [simp]:
  "pathstart (product_path p q) = (pathstart p, pathstart q)"
  by (simp add: product_path_def pathstart_def)

lemma pathfinish_product_path [simp]:
  "pathfinish (product_path p q) = (pathfinish p, pathfinish q)"
  by (simp add: product_path_def pathfinish_def)

definition torus_loop :: "(real \<Rightarrow> complex \<times> complex) \<Rightarrow> bool"
where
  "torus_loop p \<longleftrightarrow>
     path p \<and> path_image p \<subseteq> circle \<times> circle \<and>
     pathstart p = (1, 1) \<and> pathfinish p = (1, 1)"

lemma torus_loopD:
  assumes "torus_loop p"
  shows "path p" "path_image p \<subseteq> circle \<times> circle"
    "pathstart p = (1, 1)" "pathfinish p = (1, 1)"
  using assms unfolding torus_loop_def by blast+

lemma torus_loop_fst:
  assumes "torus_loop p"
  shows "is_loop (fst \<circ> p)"
  using torus_loopD [OF assms]
  by (auto simp: is_loop_def path_def path_image_def pathstart_def
      pathfinish_def continuous_on_fst)

lemma torus_loop_snd:
  assumes "torus_loop p"
  shows "is_loop (snd \<circ> p)"
  using torus_loopD [OF assms]
  by (auto simp: is_loop_def path_def path_image_def pathstart_def
      pathfinish_def continuous_on_snd)

lemma torus_loop_product:
  assumes "is_loop p" "is_loop q"
  shows "torus_loop (product_path p q)"
proof -
  have im: "path_image (product_path p q) \<subseteq>
      path_image p \<times> path_image q"
    by (rule path_image_product_path)
  show ?thesis
    using assms im unfolding torus_loop_def
    by (auto simp: is_loop_def path_product_path)
qed

definition torus_lift_endpoint ::
  "(real \<Rightarrow> complex \<times> complex) \<Rightarrow> int \<times> int"
where
  "torus_lift_endpoint p =
     (circle_lift_endpoint (fst \<circ> p),
      circle_lift_endpoint (snd \<circ> p))"

lemma torus_lift_endpoint_fst [simp]:
  "fst (torus_lift_endpoint p) = circle_lift_endpoint (fst \<circ> p)"
  by (simp add: torus_lift_endpoint_def)

lemma torus_lift_endpoint_snd [simp]:
  "snd (torus_lift_endpoint p) = circle_lift_endpoint (snd \<circ> p)"
  by (simp add: torus_lift_endpoint_def)

lemma torus_loop_join:
  assumes "torus_loop p" "torus_loop q"
  shows "torus_loop (p +++ q)"
proof -
  have tp: "path p" "path_image p \<subseteq> circle \<times> circle"
      "pathstart p = (1, 1)" "pathfinish p = (1, 1)"
    using torus_loopD [OF assms(1)] by blast+
  have tq: "path q" "path_image q \<subseteq> circle \<times> circle"
      "pathstart q = (1, 1)" "pathfinish q = (1, 1)"
    using torus_loopD [OF assms(2)] by blast+
  have conn: "pathfinish p = pathstart q"
    using tp(4) tq(3) by simp
  have pp: "path (p +++ q)"
    by (rule path_join_imp [OF tp(1) tq(1) conn])
  have pi: "path_image (p +++ q) \<subseteq> circle \<times> circle"
    by (rule subset_path_image_join)
       (use tp(2) tq(2) in auto)
  show ?thesis
    using pp pi tp tq
    unfolding torus_loop_def by simp
qed

lemma torus_loop_reverse:
  assumes "torus_loop p"
  shows "torus_loop (reversepath p)"
  using torus_loopD [OF assms]
  by (simp add: torus_loop_def)

lemma product_path_join:
  "product_path (p +++ r) (q +++ s) =
    product_path p q +++ product_path r s"
  by (rule ext) (simp add: product_path_def joinpaths_def)

lemma product_path_reverse:
  "product_path (reversepath p) (reversepath q) =
    reversepath (product_path p q)"
  by (rule ext) (simp add: product_path_def reversepath_def)

lemma torus_lift_endpoint_join:
  assumes "torus_loop p" "torus_loop q"
  shows "torus_lift_endpoint (p +++ q) =
    torus_lift_endpoint p + torus_lift_endpoint q"
proof -
  have hp1: "is_loop (fst \<circ> p)" by (rule torus_loop_fst [OF assms(1)])
  have hq1: "is_loop (fst \<circ> q)" by (rule torus_loop_fst [OF assms(2)])
  have hp2: "is_loop (snd \<circ> p)" by (rule torus_loop_snd [OF assms(1)])
  have hq2: "is_loop (snd \<circ> q)" by (rule torus_loop_snd [OF assms(2)])
  have fcomp: "fst \<circ> (p +++ q) = (fst \<circ> p) +++ (fst \<circ> q)"
    by (rule path_compose_join)
  have scomp: "snd \<circ> (p +++ q) = (snd \<circ> p) +++ (snd \<circ> q)"
    by (rule path_compose_join)
  show ?thesis
    unfolding torus_lift_endpoint_def
    by (simp add: fcomp scomp circle_lift_endpoint_join [OF hp1 hq1]
      circle_lift_endpoint_join [OF hp2 hq2])
qed

lemma torus_lift_endpoint_reverse:
  assumes "torus_loop p"
  shows "torus_lift_endpoint (reversepath p) =
    - torus_lift_endpoint p"
proof -
  have hp1: "is_loop (fst \<circ> p)" by (rule torus_loop_fst [OF assms])
  have hp2: "is_loop (snd \<circ> p)" by (rule torus_loop_snd [OF assms])
  have fcomp:
      "fst \<circ> reversepath p = reversepath (fst \<circ> p)"
    by (rule path_compose_reversepath)
  have scomp:
      "snd \<circ> reversepath p = reversepath (snd \<circ> p)"
    by (rule path_compose_reversepath)
  show ?thesis
    unfolding torus_lift_endpoint_def
    by (simp add: fcomp scomp circle_lift_endpoint_reverse [OF hp1]
      circle_lift_endpoint_reverse [OF hp2])
qed

lemma homotopic_paths_product:
  fixes S :: "'a::topological_space set" and T :: "'b::topological_space set"
    and p q :: "real \<Rightarrow> 'a" and r s :: "real \<Rightarrow> 'b"
  assumes h1: "homotopic_paths S p q"
    and h2: "homotopic_paths T r s"
  shows "homotopic_paths (S \<times> T)
    (product_path p r) (product_path q s)"
proof -
  obtain h where conth: "continuous_on ({0..1} \<times> {0..1}) h"
    and him: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> S"
    and h0: "\<forall>x \<in> {0..1}. h (0,x) = p x"
    and h1x: "\<forall>x \<in> {0..1}. h (1,x) = q x"
    and hendraw: "\<forall>t \<in> {0..1::real}.
      pathstart (h \<circ> Pair t) = pathstart p \<and>
      pathfinish (h \<circ> Pair t) = pathfinish p"
    using homotopic_paths [THEN iffD1, OF h1] by blast
  have hend: "\<And>t. t \<in> {0..1} \<Longrightarrow>
      h (t,0) = p 0 \<and> h (t,1) = p 1"
    using hendraw by (auto simp: pathstart_def pathfinish_def)
  obtain k where contk: "continuous_on ({0..1} \<times> {0..1}) k"
    and kim: "k \<in> ({0..1} \<times> {0..1}) \<rightarrow> T"
    and k0: "\<forall>x \<in> {0..1}. k (0,x) = r x"
    and k1: "\<forall>x \<in> {0..1}. k (1,x) = s x"
    and kendraw: "\<forall>t \<in> {0..1::real}.
      pathstart (k \<circ> Pair t) = pathstart r \<and>
      pathfinish (k \<circ> Pair t) = pathfinish r"
    using homotopic_paths [THEN iffD1, OF h2] by blast
  have kend: "\<And>t. t \<in> {0..1} \<Longrightarrow>
      k (t,0) = r 0 \<and> k (t,1) = r 1"
    using kendraw by (auto simp: pathstart_def pathfinish_def)
  define H where "H = (\<lambda>z. (h z, k z))"
  have Hc: "continuous_on ({0..1} \<times> {0..1}) H"
    unfolding H_def
    by (intro continuous_on_Pair conth contk)
  have Him: "H \<in> ({0..1} \<times> {0..1}) \<rightarrow> S \<times> T"
    using him kim unfolding H_def by auto
  have H0: "\<forall>x \<in> {0..1}.
      H (0, x) = product_path p r x"
    using h0 k0 unfolding H_def product_path_def by auto
  have Htop: "\<forall>x \<in> {0..1}.
      H (1, x) = product_path q s x"
    using h1x k1 unfolding H_def product_path_def by auto
  have Hends: "\<forall>t \<in> {0..1::real}.
      pathstart (H \<circ> Pair t) =
        pathstart (product_path p r) \<and>
      pathfinish (H \<circ> Pair t) =
        pathfinish (product_path p r)"
    using hend kend
    by (auto simp: H_def product_path_def pathstart_def pathfinish_def o_def)
  show ?thesis
    apply (rule homotopic_paths [THEN iffD2])
    apply (rule exI[of _ H])
    using Hc Him H0 Htop Hends by blast
qed

lemma torus_loop_homotopic_iff:
  assumes p: "torus_loop p" and q: "torus_loop q"
  shows "homotopic_paths (circle \<times> circle) p q \<longleftrightarrow>
    torus_lift_endpoint p = torus_lift_endpoint q"
proof
  assume h: "homotopic_paths (circle \<times> circle) p q"
  have hf: "homotopic_paths circle (fst \<circ> p) (fst \<circ> q)"
    apply (rule homotopic_paths_continuous_image [OF h])
    apply (intro continuous_intros)
    by auto
  have hs: "homotopic_paths circle (snd \<circ> p) (snd \<circ> q)"
    apply (rule homotopic_paths_continuous_image [OF h])
    apply (intro continuous_intros)
    by auto
  have ef: "circle_lift_endpoint (fst \<circ> p) =
      circle_lift_endpoint (fst \<circ> q)"
    by (rule circle_lift_endpoint_homotopic
      [OF torus_loop_fst [OF p] torus_loop_fst [OF q] hf])
  have es: "circle_lift_endpoint (snd \<circ> p) =
      circle_lift_endpoint (snd \<circ> q)"
    by (rule circle_lift_endpoint_homotopic
      [OF torus_loop_snd [OF p] torus_loop_snd [OF q] hs])
  show "torus_lift_endpoint p = torus_lift_endpoint q"
    using ef es unfolding torus_lift_endpoint_def by simp
next
  assume e: "torus_lift_endpoint p = torus_lift_endpoint q"
  have ef: "circle_lift_endpoint (fst \<circ> p) =
      circle_lift_endpoint (fst \<circ> q)"
    using e unfolding torus_lift_endpoint_def by simp
  have es: "circle_lift_endpoint (snd \<circ> p) =
      circle_lift_endpoint (snd \<circ> q)"
    using e unfolding torus_lift_endpoint_def by simp
  have hf: "homotopic_paths circle (fst \<circ> p) (fst \<circ> q)"
    by (rule circle_lift_endpoint_eq_homotopic
      [OF torus_loop_fst [OF p] torus_loop_fst [OF q] ef])
  have hs: "homotopic_paths circle (snd \<circ> p) (snd \<circ> q)"
    by (rule circle_lift_endpoint_eq_homotopic
      [OF torus_loop_snd [OF p] torus_loop_snd [OF q] es])
  have hp: "homotopic_paths (circle \<times> circle)
      (product_path (fst \<circ> p) (snd \<circ> p))
      (product_path (fst \<circ> q) (snd \<circ> q))"
    by (rule homotopic_paths_product [OF hf hs])
  show "homotopic_paths (circle \<times> circle) p q"
    using hp by (simp add: product_path_def)
qed

end
