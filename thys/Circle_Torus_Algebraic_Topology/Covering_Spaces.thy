theory Covering_Spaces
  imports "HOL-Analysis.Homeomorphism"
begin

section \<open>Generic pointed path lifts\<close>

text \<open>
  The standard analysis library contains the point-set definition of a covering
  space and its lifting theorems.  This theory packages those results in a
  small interface that can be reused without exposing the implementation of a
  particular covering map.  The domain and codomain of the covering are
  real-normed vector spaces, exactly as required by the analytic covering-space
  API.
\<close>

definition covering_path_lift ::
  "'a::real_normed_vector set \<Rightarrow>
   ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
   (real \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "covering_path_lift C p g a h \<longleftrightarrow>
     path h \<and> path_image h \<subseteq> C \<and> pathstart h = a \<and>
     (\<forall>t \<in> {0..1}. p (h t) = g t)"

lemma covering_path_liftI:
  assumes "path h" "path_image h \<subseteq> C" "pathstart h = a"
    and "\<And>t. t \<in> {0..1} \<Longrightarrow> p (h t) = g t"
  shows "covering_path_lift C p g a h"
  using assms unfolding covering_path_lift_def by blast

lemma covering_path_liftD:
  assumes "covering_path_lift C p g a h"
  shows "path h" "path_image h \<subseteq> C" "pathstart h = a"
    and "\<And>t. t \<in> {0..1} \<Longrightarrow> p (h t) = g t"
  using assms unfolding covering_path_lift_def by blast+

lemma covering_path_lift_exists:
  assumes cov: "covering_space C p S" and ac: "a \<in> C"
    and pg: "path g" and ig: "path_image g \<subseteq> S"
    and start: "pathstart g = p a"
  shows "\<exists>h. covering_path_lift C p g a h"
proof -
  obtain h where "path h" "path_image h \<subseteq> C" "pathstart h = a"
    and eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p (h t) = g t"
    using covering_space_lift_path_strong [OF cov ac pg ig start]
    by blast
  then show ?thesis by (intro exI) (rule covering_path_liftI)
qed

lemma covering_path_lift_unique:
  assumes cov: "covering_space C p S"
    and pg: "path g" and ig: "path_image g \<subseteq> S"
    and h1: "covering_path_lift C p g a h1"
    and h2: "covering_path_lift C p g a h2"
  shows "\<And>t. t \<in> {0..1} \<Longrightarrow> h1 t = h2 t"
proof -
  have cg: "continuous_on {0..1} g"
    using pg unfolding path_def by blast
  have ig': "g \<in> {0..1} \<rightarrow> S"
    using ig unfolding path_image_def by auto
  have h1d: "path h1" "path_image h1 \<subseteq> C" "pathstart h1 = a"
    and h1eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p (h1 t) = g t"
    using covering_path_liftD [OF h1] by blast+
  have h2d: "path h2" "path_image h2 \<subseteq> C" "pathstart h2 = a"
    and h2eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p (h2 t) = g t"
    using covering_path_liftD [OF h2] by blast+
  have ch1: "continuous_on {0..1} h1"
    using h1d(1) unfolding path_def by blast
  have ch2: "continuous_on {0..1} h2"
    using h2d(1) unfolding path_def by blast
  have ih1: "h1 \<in> {0..1} \<rightarrow> C"
    using h1d(2) unfolding path_image_def by auto
  have ih2: "h2 \<in> {0..1} \<rightarrow> C"
    using h2d(2) unfolding path_image_def by auto
  have connected01: "connected ({0..1}::real set)"
    by simp
  have eq0: "h1 0 = h2 0"
    using h1d(3) h2d(3) unfolding pathstart_def by simp
  have h1eq': "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = p (h1 t)"
    using h1eq by (metis)
  have h2eq': "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = p (h2 t)"
    using h2eq by (metis)
  show "h1 t = h2 t" if "t \<in> {0..1}" for t
    apply (rule covering_space_lift_unique
      [of C p S h1 0 h2 "{0..1}" g t])
    using cov eq0 cg ig' ch1 ih1 h1eq' ch2 ih2 h2eq' connected01 that
    by simp_all
qed

definition covering_path_lift_choice ::
  "'a::real_normed_vector set \<Rightarrow>
   ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
   (real \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a)"
where
  "covering_path_lift_choice C p g a = (SOME h. covering_path_lift C p g a h)"

lemma covering_path_lift_choice_spec:
  assumes "covering_space C p S" "a \<in> C" "path g"
    "path_image g \<subseteq> S" "pathstart g = p a"
  shows "covering_path_lift C p g a (covering_path_lift_choice C p g a)"
  unfolding covering_path_lift_choice_def
  using someI_ex [OF covering_path_lift_exists [OF assms(1-5)]] .

lemma covering_path_lift_choice_unique:
  assumes cov: "covering_space C p S" and ac: "a \<in> C"
    and pg: "path g" and ig: "path_image g \<subseteq> S"
    and start: "pathstart g = p a"
    and h: "covering_path_lift C p g a h"
  shows "\<And>t. t \<in> {0..1} \<Longrightarrow>
      covering_path_lift_choice C p g a t = h t"
proof -
  have choice: "covering_path_lift C p g a
      (covering_path_lift_choice C p g a)"
    by (rule covering_path_lift_choice_spec [OF cov ac pg ig start])
  show "covering_path_lift_choice C p g a t = h t"
    if "t \<in> {0..1}" for t
    using covering_path_lift_unique [OF cov pg ig choice h that] .
qed

definition covering_lift_endpoint ::
  "'a::real_normed_vector set \<Rightarrow>
   ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
   (real \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "covering_lift_endpoint C p g a = covering_path_lift_choice C p g a 1"

lemma covering_lift_endpoint_eq:
  assumes cov: "covering_space C p S" and ac: "a \<in> C"
    and pg: "path g" and ig: "path_image g \<subseteq> S"
    and start: "pathstart g = p a"
    and h: "covering_path_lift C p g a h"
  shows "covering_lift_endpoint C p g a = h 1"
  unfolding covering_lift_endpoint_def
  by (rule covering_path_lift_choice_unique [OF cov ac pg ig start h]) simp

lemma covering_lift_endpoint_fiber:
  assumes cov: "covering_space C p S" and ac: "a \<in> C"
    and pg: "path g" and ig: "path_image g \<subseteq> S"
    and start: "pathstart g = p a"
  shows "covering_lift_endpoint C p g a \<in> C"
    and "p (covering_lift_endpoint C p g a) = pathfinish g"
proof -
  have h: "covering_path_lift C p g a
      (covering_path_lift_choice C p g a)"
    by (rule covering_path_lift_choice_spec [OF cov ac pg ig start])
  have hd: "path (covering_path_lift_choice C p g a)"
      "path_image (covering_path_lift_choice C p g a) \<subseteq> C"
      "pathstart (covering_path_lift_choice C p g a) = a"
    and heq: "\<And>t. t \<in> {0..1} \<Longrightarrow>
      p (covering_path_lift_choice C p g a t) = g t"
    using covering_path_liftD [OF h] by blast+
  show "covering_lift_endpoint C p g a \<in> C"
    using hd(2) unfolding covering_lift_endpoint_def path_image_def by auto
  show "p (covering_lift_endpoint C p g a) = pathfinish g"
    using heq [of 1] unfolding covering_lift_endpoint_def pathfinish_def by simp
qed

lemma covering_lift_endpoint_homotopic:
  assumes cov: "covering_space C p S"
    and pg1: "path g1" and ig1: "path_image g1 \<subseteq> S"
    and pg2: "path g2" and ig2: "path_image g2 \<subseteq> S"
    and hom: "homotopic_paths S g1 g2"
    and ac: "a \<in> C"
    and start1: "pathstart g1 = p a" and start2: "pathstart g2 = p a"
  shows "covering_lift_endpoint C p g1 a =
      covering_lift_endpoint C p g2 a"
proof -
  have h1: "covering_path_lift C p g1 a
      (covering_path_lift_choice C p g1 a)"
    by (rule covering_path_lift_choice_spec [OF cov ac pg1 ig1 start1])
  have h2: "covering_path_lift C p g2 a
      (covering_path_lift_choice C p g2 a)"
    by (rule covering_path_lift_choice_spec [OF cov ac pg2 ig2 start2])
  have f1: "pathfinish (covering_path_lift_choice C p g1 a) =
      pathfinish (covering_path_lift_choice C p g2 a)"
    by (rule covering_space_monodromy [OF cov pg1 ig1 pg2 ig2 hom])
      (use covering_path_liftD [OF h1] covering_path_liftD [OF h2] in auto)
  show ?thesis
    using f1 unfolding covering_lift_endpoint_def pathfinish_def by simp
qed

section \<open>Pointed covering spaces\<close>

text \<open>
  A pointed covering packages the sheet chosen above the base point.  The
  locale is deliberately lightweight: later developments can instantiate it
  with the exponential circle cover, universal covers, or covering graphs.
\<close>

locale pointed_covering_space =
  fixes C :: "'a::real_normed_vector set"
    and p :: "'a \<Rightarrow> 'b::real_normed_vector"
    and S :: "'b set"
    and a0 :: "'a"
  assumes covering: "covering_space C p S"
    and basepoint: "a0 \<in> C"
begin

lemma continuous:
  "continuous_on C p"
  using covering_space_imp_continuous [OF covering] .

lemma surjective:
  "p ` C = S"
  using covering_space_imp_surjective [OF covering] .

abbreviation lift_endpoint where
  "lift_endpoint g \<equiv> covering_lift_endpoint C p g a0"

lemma lift_endpoint_homotopic:
  assumes "path g1" "path_image g1 \<subseteq> S"
    "path g2" "path_image g2 \<subseteq> S"
    "homotopic_paths S g1 g2"
    "pathstart g1 = p a0" "pathstart g2 = p a0"
  shows "lift_endpoint g1 = lift_endpoint g2"
  using covering_lift_endpoint_homotopic [OF covering assms(1-5) basepoint assms(6-7)] .

end

end
