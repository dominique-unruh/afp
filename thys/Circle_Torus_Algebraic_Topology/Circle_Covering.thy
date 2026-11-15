theory Circle_Covering
  imports
    "Fundamental_Group_Circle.Fundamental_Group_Circle"
    "HOL-Analysis.Further_Topology"
begin

section \<open>Covering-space lifts for the circle\<close>

text \<open>
  This theory complements the winding-number proof in
  the circle entry with the real-lift description of
  based circle loops.  The covering-space API used below is the one from the standard
  Isabelle analysis library; in particular, the exponential covering of the
  punctured plane supplies the analytic lifting argument.
\<close>

definition circle_cover :: "real \<Rightarrow> complex" where
  "circle_cover t = circlepath 0 1 t"

lemma circle_cover_exp:
  "circle_cover t = exp (2 * of_real pi * \<i> * of_real t)"
  by (simp add: circle_cover_def circlepath)

lemma path_circle_cover [simp]: "path circle_cover"
  unfolding circle_cover_def
  by (simp only: path_circlepath)

lemma circle_cover_into_circle: "circle_cover ` UNIV \<subseteq> circle"
  unfolding circle_cover_exp circle_def
  by (auto simp: dist_norm norm_exp norm_mult)

lemma circle_cover_periodic_int:
  "circle_cover (t + of_int n) = circle_cover t"
  unfolding circle_cover_exp
  by (simp add: algebra_simps exp_add)

lemma circle_cover_fiber:
  "circle_cover s = circle_cover t \<longleftrightarrow> (\<exists>n::int. s = t + of_int n)"
  unfolding circle_cover_exp
proof -
  have hexp: "exp (2 * of_real pi * \<i> * of_real s) =
      exp (2 * of_real pi * \<i> * of_real t) \<longleftrightarrow>
      (\<exists>n::int. 2 * of_real pi * \<i> * of_real s =
        2 * of_real pi * \<i> * of_real t + (of_int (2 * n) * pi) * \<i>)"
    by (rule exp_eq)
  show "exp (2 * of_real pi * \<i> * of_real s) =
      exp (2 * of_real pi * \<i> * of_real t) \<longleftrightarrow>
      (\<exists>n::int. s = t + of_int n)"
  proof
    assume h0: "exp (2 * of_real pi * \<i> * of_real s) =
        exp (2 * of_real pi * \<i> * of_real t)"
    then obtain n h where h:
        "2 * of_real pi * \<i> * of_real s =
          2 * of_real pi * \<i> * of_real t + (of_int (2 * n) * pi) * \<i>"
      using hexp by blast
    have h': "s = t + of_int n"
    proof -
      have h'':
          "Im (2 * of_real pi * \<i> * of_real s) =
            Im (2 * of_real pi * \<i> * of_real t +
              (of_int (2 * n) * pi) * \<i>)"
        using arg_cong [OF h, of Im] by blast
      have h''':
          "2 * pi * s = 2 * pi * t + of_int (2 * n) * pi"
        using h'' by (simp add: algebra_simps)
      have hcancel:
          "2 * pi * s = 2 * pi * (t + of_int n)"
        using h''' by (simp add: algebra_simps)
      have hpi: "2 * pi \<noteq> 0" by (simp add: pi_gt_zero)
      show ?thesis
        using hcancel hpi by (simp add: mult_left_cancel)
    qed
    then show "\<exists>n::int. s = t + of_int n" by blast
  next
    assume h0: "\<exists>n::int. s = t + of_int n"
    then obtain n h where h: "s = t + of_int n" by blast
    have h': "2 * of_real pi * \<i> * of_real s =
        2 * of_real pi * \<i> * of_real t + (of_int (2 * n) * pi) * \<i>"
      using h by (simp add: algebra_simps)
    then show "exp (2 * of_real pi * \<i> * of_real s) =
        exp (2 * of_real pi * \<i> * of_real t)"
      using hexp by blast
  qed
qed

lemma circle_cover_eq_iff:
  "circle_cover s = circle_cover t \<longleftrightarrow> s - t \<in> \<int>"
proof
  show "circle_cover s = circle_cover t \<Longrightarrow> s - t \<in> \<int>"
  proof -
    assume h: "circle_cover s = circle_cover t"
    obtain n where n: "s = t + of_int n"
      using h circle_cover_fiber [of s t] by blast
    have "s - t = of_int n" using n by linarith
    then show "s - t \<in> \<int>" by (simp add: Ints_def)
  qed
next
  show "s - t \<in> \<int> \<Longrightarrow> circle_cover s = circle_cover t"
  proof -
    assume h: "s - t \<in> \<int>"
    obtain n::int where n: "s - t = of_int n"
      using h by (auto simp: Ints_def)
    have "s = t + of_int n" using n by linarith
    then show "circle_cover s = circle_cover t"
      using circle_cover_fiber [of s t] by (blast dest: iffD2)
  qed
qed

lemma circle_cover_one [simp]: "circle_cover 0 = (1::complex)"
  by (simp add: circle_cover_exp)

lemma circle_cover_Arg:
  "z \<in> circle \<Longrightarrow> circle_cover (Arg z / (2 * pi)) = z"
proof -
  assume z: "z \<in> circle"
  have ze: "exp (\<i> * Arg z) = z"
    using z by (simp add: circle_def complex_norm_eq_1_exp_eq)
  have harg:
      "2 * of_real pi * \<i> * of_real (Arg z / (2 * pi)) = \<i> * Arg z"
    by (simp add: algebra_simps)
  have hcover:
      "circle_cover (Arg z / (2 * pi)) = exp (\<i> * Arg z)"
    unfolding circle_cover_exp
    using harg by simp
  show "circle_cover (Arg z / (2 * pi)) = z"
    using hcover ze by (rule trans)
qed

lemma circle_cover_mem: "z \<in> circle \<Longrightarrow> z \<in> circle_cover ` UNIV"
proof -
  assume hz: "z \<in> circle"
  have hc: "circle_cover (Arg z / (2 * pi)) = z"
    by (rule circle_cover_Arg [OF hz])
  show "z \<in> circle_cover ` UNIV"
    by (rule image_eqI[where x="Arg z / (2 * pi)"])
       (auto simp add: hc)
qed

lemma circle_cover_range: "circle_cover ` UNIV = circle"
proof (rule subset_antisym)
  show "circle_cover ` UNIV \<subseteq> circle"
    by (rule circle_cover_into_circle)
  show "circle \<subseteq> circle_cover ` UNIV"
    by (rule subsetI) (rule circle_cover_mem)
qed

lemma circle_cover_surjective: "circle_cover ` UNIV = circle"
  by (rule circle_cover_range)

section \<open>Path lifting\<close>

definition circle_path_lift :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "circle_path_lift p q \<longleftrightarrow>
     path q \<and> pathstart q = 0 \<and>
     (\<forall>t \<in> {0..1}. circle_cover (q t) = p t)"

lemma circle_path_lift_exists:
  assumes ppath: "path p"
      and pimage: "path_image p \<subseteq> circle"
      and pstart: "pathstart p = 1"
  shows "\<exists>q. circle_path_lift p q"
proof -
  have pnonzero: "0 \<notin> path_image p"
    using pimage zero_notin_circle by blast
  obtain h where hpath: "path h" and himage: "path_image h \<subseteq> UNIV"
      and hstart: "pathstart h = 0"
      and hexp: "\<And>t. t \<in> {0..1} \<Longrightarrow> exp (h t) = p t"
    using covering_space_lift_path_strong
      [OF covering_space_exp_punctured_plane, of 0 p] ppath pimage pstart pnonzero
    by (auto simp: circle_subset_punctured)
  define r where "r \<equiv> \<lambda>t. Im (h t) / (2 * pi)"
  have rpath: "path r"
    unfolding r_def path_def
    using hpath by (intro continuous_intros) (auto simp add: path_def pi_gt_zero)
  have rstart: "pathstart r = 0"
    unfolding r_def pathstart_def
    using hstart by (simp add: pathstart_def)
  have rcover: "circle_cover (r t) = p t" if "t \<in> {0..1}" for t
  proof -
    have pt: "p t \<in> circle"
      using pimage that by (auto simp: path_image_def)
    have nexp: "norm (exp (h t)) = 1"
      using hexp that by (simp add: norm_of_circle [OF pt])
    have hre: "Re (h t) = 0"
      by (rule norm_exp_imaginary [OF nexp])
    have heq: "2 * of_real pi * \<i> * of_real (Im (h t) / (2 * pi)) = h t"
      apply (rule complex_eqI)
       apply (simp add: hre)
      apply (simp add: algebra_simps pi_gt_zero)
    done
    show ?thesis
      unfolding circle_cover_exp r_def
      using heq hexp that by simp
  qed
  have "circle_path_lift p r"
    unfolding circle_path_lift_def
    using rpath rstart rcover by blast
  then show ?thesis by blast
qed

definition circle_lift_exp :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> complex)" where
  "circle_lift_exp q t = \<i> * of_real (2 * pi * q t)"

lemma path_circle_lift_exp:
  assumes "path q"
  shows "path (circle_lift_exp q)"
  unfolding circle_lift_exp_def path_def
  using assms by (intro continuous_intros) (auto simp: path_def)

lemma pathstart_circle_lift_exp:
  assumes "pathstart q = 0"
  shows "pathstart (circle_lift_exp q) = 0"
  using assms by (simp add: circle_lift_exp_def pathstart_def)

lemma circle_lift_exp_map:
  "exp (circle_lift_exp q t) = circle_cover (q t)"
  unfolding circle_lift_exp_def circle_cover_exp
  by (simp add: algebra_simps)

lemma circle_path_lift_unique:
  assumes l1: "circle_path_lift p q1"
      and l2: "circle_path_lift p q2"
      and ppath: "path p"
      and pimage: "path_image p \<subseteq> circle"
  shows "\<forall>t \<in> {0..1}. q1 t = q2 t"
proof -
  have q1path: "path q1"
    using l1 by (simp add: circle_path_lift_def)
  have q1start: "pathstart q1 = 0"
    using l1 by (simp add: circle_path_lift_def)
  have q2path: "path q2"
    using l2 by (simp add: circle_path_lift_def)
  have q2start: "pathstart q2 = 0"
    using l2 by (simp add: circle_path_lift_def)
  have pnonzero: "path_image p \<subseteq> - {0}"
    using pimage circle_subset_punctured by blast
  have qeq: "q1 t = q2 t" if "t \<in> {0..1}" for t
  proof -
    have heq:
        "circle_lift_exp q1 t = circle_lift_exp q2 t"
      proof (rule covering_space_lift_unique
          [OF covering_space_exp_punctured_plane, of
            "circle_lift_exp q1" 0 "circle_lift_exp q2" "{0..1}" p t])
        show "circle_lift_exp q1 0 = circle_lift_exp q2 0"
          using q1start q2start by (simp add: circle_lift_exp_def pathstart_def)
        show "continuous_on {0..1} p"
          using ppath by (simp add: path_def)
        show "p \<in> {0..1} \<rightarrow> - {0}"
          using pnonzero by (auto simp: path_image_def)
        show "continuous_on {0..1} (circle_lift_exp q1)"
          unfolding circle_lift_exp_def
          using q1path unfolding path_def
          by (intro continuous_intros) (auto simp: path_def)
        show "circle_lift_exp q1 \<in> {0..1} \<rightarrow> UNIV"
          by simp
        show "\<And>x. x \<in> {0..1} \<Longrightarrow>
            p x = exp (circle_lift_exp q1 x)"
          using l1 by (auto simp: circle_path_lift_def circle_lift_exp_map)
        show "continuous_on {0..1} (circle_lift_exp q2)"
          unfolding circle_lift_exp_def
          using q2path unfolding path_def
          by (intro continuous_intros) (auto simp: path_def)
        show "circle_lift_exp q2 \<in> {0..1} \<rightarrow> UNIV"
          by simp
        show "\<And>x. x \<in> {0..1} \<Longrightarrow>
            p x = exp (circle_lift_exp q2 x)"
          using l2 by (auto simp: circle_path_lift_def circle_lift_exp_map)
        show "connected ({0..1}::real set)"
          by (simp add: connected_Icc)
        show "0 \<in> ({0..1}::real set)"
          by simp
        show "t \<in> ({0..1}::real set)"
          using that .
      qed
    have him: "2 * pi * q1 t = 2 * pi * q2 t"
      using arg_cong [OF heq, of Im] by (simp add: circle_lift_exp_def)
    have hpi: "2 * pi \<noteq> 0"
      by (simp add: pi_gt_zero)
    then show ?thesis
      using him by (simp add: mult_left_cancel)
  qed
  show ?thesis
    using qeq by blast
qed

definition circle_lift :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> real)" where
  "circle_lift p = (SOME q. circle_path_lift p q)"

lemma circle_lift_spec:
  assumes "path p" "path_image p \<subseteq> circle" "pathstart p = 1"
  shows "circle_path_lift p (circle_lift p)"
proof -
  have "\<exists>q. circle_path_lift p q"
    using assms by (rule circle_path_lift_exists)
  then show ?thesis
    unfolding circle_lift_def
    by (rule someI_ex)
qed

lemma circle_lift_unique:
  assumes l1: "circle_path_lift p q1"
      and l2: "circle_path_lift p q2"
      and ppath: "path p" and pimage: "path_image p \<subseteq> circle"
  shows "\<forall>t \<in> {0..1}. q1 t = q2 t"
  using circle_path_lift_unique [OF l1 l2 ppath pimage] .

definition circle_lift_endpoint :: "(real \<Rightarrow> complex) \<Rightarrow> int" where
  "circle_lift_endpoint p =
     (SOME n::int. circle_lift p 1 = of_int n)"

lemma circle_lift_endpoint_spec:
  assumes loop: "is_loop p"
  shows "circle_lift p 1 = of_int (circle_lift_endpoint p)"
proof -
  have lp: "circle_path_lift p (circle_lift p)"
    using loop by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have hp1: "circle_cover (circle_lift p 1) = p 1"
    using lp by (simp add: circle_path_lift_def)
  have hpend: "p 1 = 1"
    using loop by (simp add: is_loop_def pathfinish_def)
  have hcover: "circle_cover (circle_lift p 1) = 1"
    using hp1 hpend by simp
  have hzero: "circle_cover 0 = (1::complex)"
    by (rule circle_cover_one)
  have heqcover: "circle_cover (circle_lift p 1) = circle_cover 0"
    using hcover hzero by simp
  have hfiber: "\<exists>n::int. circle_lift p 1 = 0 + of_int n"
    using circle_cover_fiber [of "circle_lift p 1" 0] heqcover by blast
  obtain n::int where n: "circle_lift p 1 = 0 + of_int n"
    using hfiber by blast
  have ex: "\<exists>n::int. circle_lift p 1 = of_int n"
    using n by (intro exI[of _ n]) simp
  show ?thesis
    unfolding circle_lift_endpoint_def
    by (rule someI_ex [OF ex])
qed

lemma circle_lift_endpoint_integer:
  assumes "is_loop p"
  shows "circle_lift p 1 \<in> \<int>"
  using circle_lift_endpoint_spec [OF assms]
  by (simp add: Ints_def)

lemma path_add_const:
  fixes q :: "real \<Rightarrow> real" and a :: real
  assumes "path q"
  shows "path (\<lambda>t. q t + a)"
proof -
  have hpath: "path ((\<lambda>x. a + x) \<circ> q)"
    using path_translation_eq [of a q] assms by simp
  then show ?thesis
    by (simp add: comp_def add.commute)
qed

lemma pathstart_add_const:
  fixes q :: "real \<Rightarrow> real" and a :: real
  assumes "pathstart q = 0"
  shows "pathstart (\<lambda>t. q t + a) = a"
proof -
  have q0: "q 0 = 0"
    using assms by (simp add: pathstart_def)
  show ?thesis
    unfolding pathstart_def
    using q0 by simp
qed

lemma circle_path_lift_join:
  assumes lp: "circle_path_lift p P"
      and lq: "circle_path_lift q Q"
      and endpoint: "P 1 = of_int n"
  shows "circle_path_lift (p +++ q) (P +++ (\<lambda>t. Q t + P 1))"
proof -
  have Ppath: "path P"
    using lp by (simp add: circle_path_lift_def)
  have Pstart: "pathstart P = 0"
    using lp by (simp add: circle_path_lift_def)
  have Qpath: "path Q"
    using lq by (simp add: circle_path_lift_def)
  have Qstart: "pathstart Q = 0"
    using lq by (simp add: circle_path_lift_def)
  have Qshiftpath: "path (\<lambda>t. Q t + P 1)"
    by (rule path_add_const [OF Qpath])
  have Qshiftstart: "pathstart (\<lambda>t. Q t + P 1) = P 1"
    by (rule pathstart_add_const [OF Qstart])
  have Pfinish: "pathfinish P = P 1"
    by (simp add: pathfinish_def)
  have connect: "pathfinish P = pathstart (\<lambda>t. Q t + P 1)"
    using Pfinish Qshiftstart by simp
  have joinedpath: "path (P +++ (\<lambda>t. Q t + P 1))"
    by (rule path_join_imp [OF Ppath Qshiftpath connect])
  have P0: "P 0 = 0"
    using Pstart by (simp add: pathstart_def)
  have joinedstart: "pathstart (P +++ (\<lambda>t. Q t + P 1)) = 0"
    by (simp add: pathstart_join pathstart_def joinpaths_def P0)
  have cover_join:
      "circle_cover ((P +++ (\<lambda>t. Q t + P 1)) t) = (p +++ q) t"
    if "t \<in> {0..1}" for t
  proof (cases "t \<le> 1/2")
    case True
    have ti: "2 * t \<in> {0..1}"
      using that True by auto
    have hP: "circle_cover (P (2 * t)) = p (2 * t)"
      using lp ti by (simp add: circle_path_lift_def)
    then show ?thesis
      by (simp only: joinpaths_def if_P True)
  next
    case False
    have ti: "2 * t - 1 \<in> {0..1}"
      using that False by auto
    have hQ: "circle_cover (Q (2 * t - 1)) = q (2 * t - 1)"
      using lq ti by (simp add: circle_path_lift_def)
    have hperiod:
        "circle_cover (Q (2 * t - 1) + P 1) =
          circle_cover (Q (2 * t - 1))"
      using endpoint by (simp add: circle_cover_periodic_int)
    have notnorm: "\<not> t * 2 \<le> 1"
      using False by linarith
    show ?thesis
      using hQ hperiod notnorm by (simp add: joinpaths_def)
  qed
  show ?thesis
    unfolding circle_path_lift_def
    using joinedpath joinedstart cover_join by blast
qed

lemma circle_lift_endpoint_join:
  assumes p: "is_loop p" and q: "is_loop q"
  shows "circle_lift_endpoint (p +++ q) =
    circle_lift_endpoint p + circle_lift_endpoint q"
proof -
  have lp: "circle_path_lift p (circle_lift p)"
    using p by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have lq: "circle_path_lift q (circle_lift q)"
    using q by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ep: "circle_lift p 1 = of_int (circle_lift_endpoint p)"
    by (rule circle_lift_endpoint_spec [OF p])
  have eq: "circle_lift q 1 = of_int (circle_lift_endpoint q)"
    by (rule circle_lift_endpoint_spec [OF q])
  have lj:
      "circle_path_lift (p +++ q)
        (circle_lift p +++ (\<lambda>t. circle_lift q t + circle_lift p 1))"
    by (rule circle_path_lift_join [OF lp lq ep])
  have pj: "is_loop (p +++ q)"
    by (rule is_loop_join [OF p q])
  have lcj: "circle_path_lift (p +++ q) (circle_lift (p +++ q))"
    using pj by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ppath: "path (p +++ q)"
    using pj by (rule is_loop_path)
  have pimage: "path_image (p +++ q) \<subseteq> circle"
    using pj by (rule is_loop_image)
  have leq:
      "circle_lift (p +++ q) 1 =
        (circle_lift p +++ (\<lambda>t. circle_lift q t + circle_lift p 1)) 1"
    using circle_path_lift_unique [OF lcj lj ppath pimage]
      by simp
  have cend:
      "(circle_lift p +++ (\<lambda>t. circle_lift q t + circle_lift p 1)) 1 =
        circle_lift q 1 + circle_lift p 1"
    by (simp add: joinpaths_def)
  have ej: "circle_lift (p +++ q) 1 =
      of_int (circle_lift_endpoint (p +++ q))"
    by (rule circle_lift_endpoint_spec [OF pj])
  have hreal:
      "real_of_int (circle_lift_endpoint (p +++ q)) =
        real_of_int (circle_lift_endpoint q) +
        real_of_int (circle_lift_endpoint p)"
  proof -
    have "of_int (circle_lift_endpoint (p +++ q)) =
        circle_lift (p +++ q) 1"
      using ej by simp
    also have "\<dots> =
        (circle_lift p +++ (\<lambda>t. circle_lift q t + circle_lift p 1)) 1"
      using leq .
    also have "\<dots> = circle_lift q 1 + circle_lift p 1"
      using cend .
    also have "\<dots> =
        of_int (circle_lift_endpoint q) + of_int (circle_lift_endpoint p)"
      using ep eq by simp
    finally show ?thesis .
  qed
  have hint:
      "real_of_int (circle_lift_endpoint (p +++ q)) =
        real_of_int (circle_lift_endpoint p + circle_lift_endpoint q)"
    using hreal by (simp add: add.commute)
  then show ?thesis
    by (metis of_int_eq_iff)
qed

lemma circle_path_lift_reverse:
  assumes lp: "circle_path_lift p P"
      and endpoint: "P 1 = of_int n"
  shows "circle_path_lift (reversepath p) (\<lambda>t. P (1 - t) - P 1)"
proof -
  have Ppath: "path P"
    using lp by (simp add: circle_path_lift_def)
  have Rpath: "path (reversepath P)"
    using Ppath by (simp add: path_reversepath)
  have Cpath: "path (\<lambda>t. reversepath P t + (- P 1))"
    by (rule path_add_const [OF Rpath])
  have Cpath': "path (\<lambda>t. P (1 - t) - P 1)"
    by (rule path_eq [OF Cpath])
       (simp only: reversepath_def diff_conv_add_uminus)
  have Cstart: "pathstart (\<lambda>t. P (1 - t) - P 1) = 0"
    by (simp add: pathstart_def)
  have cover_reverse:
      "circle_cover ((\<lambda>t. P (1 - t) - P 1) t) = (reversepath p) t"
    if "t \<in> {0..1}" for t
  proof -
    have ti: "1 - t \<in> {0..1}"
      using that by auto
    have hP: "circle_cover (P (1 - t)) = p (1 - t)"
      using lp ti by (simp add: circle_path_lift_def)
    have hshift:
        "P (1 - t) - P 1 = P (1 - t) + of_int (- n)"
      using endpoint by (simp only: endpoint diff_conv_add_uminus of_int_minus)
    have hperiod':
        "circle_cover (P (1 - t) + of_int (- n)) = circle_cover (P (1 - t))"
      by (rule circle_cover_periodic_int [of "P (1 - t)" "- n"])
    have hperiod:
        "circle_cover (P (1 - t) - P 1) = circle_cover (P (1 - t))"
      using hshift hperiod' by (simp only: hshift)
    show ?thesis
      using hP hperiod by (simp add: reversepath_def)
  qed
  show ?thesis
    unfolding circle_path_lift_def
    using Cpath' Cstart cover_reverse by blast
qed

lemma circle_lift_endpoint_reverse:
  assumes loop: "is_loop p"
  shows "circle_lift_endpoint (reversepath p) =
    - circle_lift_endpoint p"
proof -
  have lp: "circle_path_lift p (circle_lift p)"
    using loop by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ep: "circle_lift p 1 = of_int (circle_lift_endpoint p)"
    by (rule circle_lift_endpoint_spec [OF loop])
  have lr:
      "circle_path_lift (reversepath p)
        (\<lambda>t. circle_lift p (1 - t) - circle_lift p 1)"
    by (rule circle_path_lift_reverse [OF lp ep])
  have rloop: "is_loop (reversepath p)"
    by (rule is_loop_reversepath [OF loop])
  have lrc: "circle_path_lift (reversepath p) (circle_lift (reversepath p))"
    using rloop by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have rpath: "path (reversepath p)"
    using rloop by (rule is_loop_path)
  have rimage: "path_image (reversepath p) \<subseteq> circle"
    using rloop by (rule is_loop_image)
  have er:
      "circle_lift (reversepath p) 1 =
        of_int (circle_lift_endpoint (reversepath p))"
    by (rule circle_lift_endpoint_spec [OF rloop])
  have p0: "circle_lift p 0 = 0"
    using lp by (simp add: circle_path_lift_def pathstart_def)
  have eq:
      "circle_lift (reversepath p) 1 =
        (\<lambda>t. circle_lift p (1 - t) - circle_lift p 1) 1"
    using circle_path_lift_unique [OF lrc lr rpath rimage] by simp
  have hreal:
      "real_of_int (circle_lift_endpoint (reversepath p)) =
        - real_of_int (circle_lift_endpoint p)"
    using er eq ep p0 by simp
  have hint:
      "real_of_int (circle_lift_endpoint (reversepath p)) =
        real_of_int (- circle_lift_endpoint p)"
    using hreal by simp
  then show ?thesis
    by (metis of_int_eq_iff)
qed

lemma continuous_on_circle_cover: "continuous_on UNIV circle_cover"
  unfolding circle_cover_exp
  by (intro continuous_intros)

lemma circle_lift_endpoint_homotopic:
  assumes p: "is_loop p" and q: "is_loop q"
      and hom: "homotopic_paths circle p q"
  shows "circle_lift_endpoint p = circle_lift_endpoint q"
proof -
  have lp: "circle_path_lift p (circle_lift p)"
    using p by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have lq: "circle_path_lift q (circle_lift q)"
    using q by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ppath: "path p"
    by (rule is_loop_path [OF p])
  have qpath: "path q"
    by (rule is_loop_path [OF q])
  have Ppath: "path (circle_lift p)"
    using lp by (simp add: circle_path_lift_def)
  have Qpath: "path (circle_lift q)"
    using lq by (simp add: circle_path_lift_def)
  have pimage: "path_image p \<subseteq> - {0}"
    using is_loop_image [OF p] circle_subset_punctured by blast
  have qimage: "path_image q \<subseteq> - {0}"
    using is_loop_image [OF q] circle_subset_punctured by blast
  have hcomplex_finish:
      "pathfinish (circle_lift_exp (circle_lift p)) =
        pathfinish (circle_lift_exp (circle_lift q))"
  proof (rule covering_space_monodromy
      [OF covering_space_exp_punctured_plane, of p q
        "circle_lift_exp (circle_lift p)"
        "circle_lift_exp (circle_lift q)"])
    show "path p"
      by (rule ppath)
    show "path_image p \<subseteq> - {0}"
      by (rule pimage)
    show "path q"
      by (rule qpath)
    show "path_image q \<subseteq> - {0}"
      by (rule qimage)
    show "homotopic_paths (- {0}) p q"
      using hom circle_subset_punctured by (rule homotopic_paths_subset)
    show "path (circle_lift_exp (circle_lift p))"
      by (rule path_circle_lift_exp [OF Ppath])
    show "path_image (circle_lift_exp (circle_lift p)) \<subseteq> UNIV"
      by simp
    show "\<And>t. t \<in> {0..1} \<Longrightarrow>
        exp (circle_lift_exp (circle_lift p) t) = p t"
      using lp by (auto simp: circle_path_lift_def circle_lift_exp_map)
    show "path (circle_lift_exp (circle_lift q))"
      by (rule path_circle_lift_exp [OF Qpath])
    show "path_image (circle_lift_exp (circle_lift q)) \<subseteq> UNIV"
      by simp
    show "\<And>t. t \<in> {0..1} \<Longrightarrow>
        exp (circle_lift_exp (circle_lift q) t) = q t"
      using lq by (auto simp: circle_path_lift_def circle_lift_exp_map)
    show "pathstart (circle_lift_exp (circle_lift p)) =
        pathstart (circle_lift_exp (circle_lift q))"
      using lp lq by (simp add: circle_path_lift_def
        pathstart_circle_lift_exp)
  qed
  have hcomplex:
      "circle_lift_exp (circle_lift p) 1 =
        circle_lift_exp (circle_lift q) 1"
    using hcomplex_finish by (simp add: pathfinish_def)
  have hreal:
      "circle_lift p 1 = circle_lift q 1"
    using arg_cong [OF hcomplex, of Im]
    by (simp add: circle_lift_exp_def)
  have ep: "circle_lift p 1 = of_int (circle_lift_endpoint p)"
    by (rule circle_lift_endpoint_spec [OF p])
  have eq: "circle_lift q 1 = of_int (circle_lift_endpoint q)"
    by (rule circle_lift_endpoint_spec [OF q])
  have hreal_int:
      "real_of_int (circle_lift_endpoint p) =
        real_of_int (circle_lift_endpoint q)"
    using hreal ep eq by simp
  then show ?thesis
    by (metis of_int_eq_iff)
qed

lemma circle_lift_endpoint_eq_homotopic:
  assumes p: "is_loop p" and q: "is_loop q"
      and eq: "circle_lift_endpoint p = circle_lift_endpoint q"
  shows "homotopic_paths circle p q"
proof -
  have lp: "circle_path_lift p (circle_lift p)"
    using p by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have lq: "circle_path_lift q (circle_lift q)"
    using q by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have Ppath: "path (circle_lift p)"
    using lp by (simp add: circle_path_lift_def)
  have Qpath: "path (circle_lift q)"
    using lq by (simp add: circle_path_lift_def)
  have Pstart: "pathstart (circle_lift p) = 0"
    using lp by (simp add: circle_path_lift_def)
  have Qstart: "pathstart (circle_lift q) = 0"
    using lq by (simp add: circle_path_lift_def)
  have ep: "circle_lift p 1 = of_int (circle_lift_endpoint p)"
    by (rule circle_lift_endpoint_spec [OF p])
  have eq': "circle_lift q 1 = of_int (circle_lift_endpoint q)"
    by (rule circle_lift_endpoint_spec [OF q])
  have Pfinish: "pathfinish (circle_lift p) = pathfinish (circle_lift q)"
    using ep eq' eq by (simp add: pathfinish_def)
  have hlin:
      "homotopic_paths (UNIV::real set) (circle_lift p) (circle_lift q)"
  proof (rule homotopic_paths_linear [OF Ppath Qpath])
    show "pathstart (circle_lift q) = pathstart (circle_lift p)"
      using Pstart Qstart by simp
    show "pathfinish (circle_lift q) = pathfinish (circle_lift p)"
      using Pfinish by simp
    show "\<And>t. t \<in> {0..1} \<Longrightarrow>
        closed_segment (circle_lift p t) (circle_lift q t) \<subseteq> (UNIV::real set)"
      by simp
  qed
  have cover_fun: "circle_cover \<in> (UNIV::real set) \<rightarrow> circle"
    using circle_cover_into_circle
    by (auto simp: image_subset_iff_funcset)
  have himg:
      "homotopic_paths circle
        (circle_cover \<circ> circle_lift p)
        (circle_cover \<circ> circle_lift q)"
    by (rule homotopic_paths_continuous_image
      [OF hlin continuous_on_circle_cover cover_fun])
  have hpcomp:
      "homotopic_paths circle p (circle_cover \<circ> circle_lift p)"
  proof (rule homotopic_paths_eq)
    show "path p"
      by (rule is_loop_path [OF p])
    show "path_image p \<subseteq> circle"
      by (rule is_loop_image [OF p])
    show "\<And>t. t \<in> {0..1} \<Longrightarrow>
        p t = (circle_cover \<circ> circle_lift p) t"
      using lp by (auto simp: circle_path_lift_def)
  qed
  have hqcomp:
      "homotopic_paths circle q (circle_cover \<circ> circle_lift q)"
  proof (rule homotopic_paths_eq)
    show "path q"
      by (rule is_loop_path [OF q])
    show "path_image q \<subseteq> circle"
      by (rule is_loop_image [OF q])
    show "\<And>t. t \<in> {0..1} \<Longrightarrow>
        q t = (circle_cover \<circ> circle_lift q) t"
      using lq by (auto simp: circle_path_lift_def)
  qed
  show ?thesis
    by (meson hpcomp himg hqcomp homotopic_paths_sym homotopic_paths_trans)
qed

theorem circle_lift_endpoint_eq_iff:
  assumes p: "is_loop p" and q: "is_loop q"
  shows "circle_lift_endpoint p = circle_lift_endpoint q \<longleftrightarrow>
    homotopic_paths circle p q"
proof
  assume "circle_lift_endpoint p = circle_lift_endpoint q"
  then show "homotopic_paths circle p q"
    by (rule circle_lift_endpoint_eq_homotopic [OF p q])
next
  assume "homotopic_paths circle p q"
  then show "circle_lift_endpoint p = circle_lift_endpoint q"
    by (rule circle_lift_endpoint_homotopic [OF p q])
qed

lemma circle_path_lift_circlepath:
  "circle_path_lift (circlepath 0 1) id"
  unfolding circle_path_lift_def circle_cover_def
  by (simp add: path_def pathstart_def)

lemma circle_lift_endpoint_circlepath:
  "circle_lift_endpoint (circlepath 0 1) = 1"
proof -
  have loop: "is_loop (circlepath 0 1)"
    by (rule is_loop_circlepath)
  have chosen: "circle_path_lift (circlepath 0 1)
      (circle_lift (circlepath 0 1))"
    using loop by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ppath: "path (circlepath 0 1)"
    by (rule is_loop_path [OF loop])
  have pimage: "path_image (circlepath 0 1) \<subseteq> circle"
    by (rule is_loop_image [OF loop])
  have heq:
      "circle_lift (circlepath 0 1) 1 = id 1"
    using circle_path_lift_unique
      [OF chosen circle_path_lift_circlepath ppath pimage] by simp
  have ep:
      "circle_lift (circlepath 0 1) 1 =
        of_int (circle_lift_endpoint (circlepath 0 1))"
    by (rule circle_lift_endpoint_spec [OF loop])
  have hreal:
      "real_of_int (circle_lift_endpoint (circlepath 0 1)) = 1"
    using ep heq by simp
  have hint:
      "real_of_int (circle_lift_endpoint (circlepath 0 1)) =
        real_of_int 1"
    using hreal by simp
  then show ?thesis
    by (metis of_int_eq_iff)
qed

lemma circle_path_lift_linepath:
  "circle_path_lift (linepath (1::complex) 1) (\<lambda>t. 0)"
  unfolding circle_path_lift_def
  by (simp add: circle_cover_one path_def pathstart_def)

lemma circle_lift_endpoint_linepath:
  "circle_lift_endpoint (linepath (1::complex) 1) = 0"
proof -
  have loop: "is_loop (linepath (1::complex) 1)"
    by (rule is_loop_linepath_1)
  have chosen:
      "circle_path_lift (linepath (1::complex) 1)
        (circle_lift (linepath 1 1))"
    using loop by (intro circle_lift_spec) (simp_all add: is_loop_def)
  have ppath: "path (linepath (1::complex) 1)"
    by (rule is_loop_path [OF loop])
  have pimage: "path_image (linepath (1::complex) 1) \<subseteq> circle"
    by (rule is_loop_image [OF loop])
  have heq:
      "circle_lift (linepath (1::complex) 1) 1 = (\<lambda>t. 0) 1"
    using circle_path_lift_unique
      [OF chosen circle_path_lift_linepath ppath pimage] by simp
  have ep:
      "circle_lift (linepath (1::complex) 1) 1 =
        of_int (circle_lift_endpoint (linepath 1 1))"
    by (rule circle_lift_endpoint_spec [OF loop])
  have hreal:
      "real_of_int (circle_lift_endpoint (linepath 1 1)) = 0"
    using ep heq by simp
  have hint:
      "real_of_int (circle_lift_endpoint (linepath 1 1)) =
        real_of_int 0"
    using hreal by simp
  then show ?thesis
    by (metis of_int_eq_iff)
qed

lemma circle_lift_endpoint_cpow:
  "circle_lift_endpoint (cpow n) = int n"
proof (induction n)
  case 0
  have h: "circle_lift_endpoint (linepath (1::complex) 1) = 0"
    by (rule circle_lift_endpoint_linepath)
  then show ?case by (simp add: cpow.simps(1) linepath_refl)
next
  case (Suc n)
  have h:
      "circle_lift_endpoint (cpow (Suc n)) =
        circle_lift_endpoint (circlepath 0 1) +
        circle_lift_endpoint (cpow n)"
    unfolding cpow.simps(2)
    by (rule circle_lift_endpoint_join)
      (rule is_loop_circlepath, rule is_loop_cpow)
  then show ?case
    by (simp add: circle_lift_endpoint_circlepath Suc.IH)
qed

lemma circle_lift_endpoint_eq_wnd:
  assumes loop: "is_loop p"
  shows "circle_lift_endpoint p = wnd p"
proof -
  have class_of:
      "loop_class p \<in> carrier pi1_circle"
    using loop by (simp add: carrier_pi1)
  show ?thesis
  proof (cases "wnd p \<ge> 0")
    case True
    define r where "r = cpow (nat (wnd p))"
    have rloop: "is_loop r"
      unfolding r_def by (rule is_loop_cpow)
    have deg_eq: "deg (loop_class p) = deg (loop_class r)"
      using loop rloop by (simp add: deg_class r_def wnd_cpow True)
    have rcarrier: "loop_class r \<in> carrier pi1_circle"
      using rloop by (simp add: carrier_pi1)
    have rclass: "loop_class p = loop_class r"
    proof (rule inj_onD [OF deg_inj])
      show "loop_class p \<in> carrier pi1_circle"
        by (rule class_of)
      show "loop_class r \<in> carrier pi1_circle"
        by (rule rcarrier)
      show "deg (loop_class p) = deg (loop_class r)"
        by (rule deg_eq)
    qed
    have hom: "homotopic_paths circle p r"
      using loop_class_eq_iff [OF loop rloop] rclass by blast
    have endpoint_eq:
        "circle_lift_endpoint p = circle_lift_endpoint r"
      by (rule circle_lift_endpoint_homotopic [OF loop rloop hom])
    then show ?thesis
      using endpoint_eq r_def circle_lift_endpoint_cpow True by simp
  next
    case False
    define r where "r = reversepath (cpow (nat (- wnd p)))"
    have rloop: "is_loop r"
      unfolding r_def by (simp add: is_loop_cpow)
    have wr: "wnd r = wnd p"
    proof -
      have h:
          "wnd (reversepath (cpow (nat (- wnd p)))) =
            - int (nat (- wnd p))"
        by (simp add: wnd_reversepath is_loop_cpow wnd_cpow)
      then show ?thesis
        unfolding r_def
        using False by simp
    qed
    have deg_eq: "deg (loop_class p) = deg (loop_class r)"
      using loop rloop
      by (simp add: deg_class wr)
    have rcarrier: "loop_class r \<in> carrier pi1_circle"
      using rloop by (simp add: carrier_pi1)
    have rclass: "loop_class p = loop_class r"
    proof (rule inj_onD [OF deg_inj])
      show "loop_class p \<in> carrier pi1_circle"
        by (rule class_of)
      show "loop_class r \<in> carrier pi1_circle"
        by (rule rcarrier)
      show "deg (loop_class p) = deg (loop_class r)"
        by (rule deg_eq)
    qed
    have hom: "homotopic_paths circle p r"
      using loop_class_eq_iff [OF loop rloop] rclass by blast
    have endpoint_eq:
        "circle_lift_endpoint p = circle_lift_endpoint r"
      by (rule circle_lift_endpoint_homotopic [OF loop rloop hom])
    have er:
        "circle_lift_endpoint r =
          - circle_lift_endpoint (cpow (nat (- wnd p)))"
      unfolding r_def
      by (rule circle_lift_endpoint_reverse [OF is_loop_cpow])
    then show ?thesis
      using endpoint_eq er circle_lift_endpoint_cpow False by simp
  qed
qed

lemma circle_lift_endpoint_eq_deg:
  assumes "is_loop p"
  shows "circle_lift_endpoint p = deg (loop_class p)"
  using circle_lift_endpoint_eq_wnd [OF assms]
    deg_class [OF assms] by simp

end
