theory Girth_Chromatic_Misc
imports
  Main
  "HOL-Library.Extended_Real"
begin

section \<open>Auxilliary lemmas and setup\<close>

text \<open>
  This section contains facts about general concepts which are not directly
  connected to the proof of the Chromatic-Girth theorem. At some point in time,
  most of them could be moved to the Isabelle base library.

  Also, a little bit of setup happens.
\<close>

subsection \<open>Numbers\<close>

lemma enat_in_Inf:
  fixes S :: "enat set"
  assumes "Inf S \<noteq> top"
  shows "Inf S \<in> S"
  using assms wellorder_InfI by auto

lemma enat_in_INF:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "(INF x\<in>S. f x) \<noteq> top"
  obtains x where "x \<in> S" and "(INF x\<in>S. f x) = f x"
  by (meson assms enat_in_Inf imageE)

lemma enat_less_INF_I:
  fixes f :: "'a \<Rightarrow> enat"
  assumes not_inf: "x \<noteq> \<infinity>" and less: "\<And>y. y \<in> S \<Longrightarrow> x < f y"
  shows "x < (INF y\<in>S. f y)"
  using assms by (auto simp: Suc_ile_eq[symmetric] INF_greatest)

lemma enat_le_Sup_iff:
  "enat k \<le> Sup M \<longleftrightarrow> k = 0 \<or> (\<exists>m \<in> M. enat k \<le> m)" (is "?L \<longleftrightarrow> ?R")
proof cases
  assume "k = 0" then show ?thesis by (auto simp: enat_0)
next
  assume "k \<noteq> 0"
  show ?thesis
  proof
    assume ?L
    then have "\<lbrakk>enat k \<le> (if finite M then Max M else \<infinity>); M \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m\<in>M. enat k \<le> m"
      by (metis Max_in Sup_enat_def finite_enat_bounded linorder_linear)
    with \<open>k \<noteq> 0\<close> and \<open>?L\<close> show ?R
      unfolding Sup_enat_def
      by (cases "M={}") (auto simp add: enat_0[symmetric])
  next
    assume ?R then show ?L
      by (auto simp: enat_0 intro: complete_lattice_class.Sup_upper2)
  qed
qed

lemma enat_neq_zero_cancel_iff[simp]:
  "0 \<noteq> enat n \<longleftrightarrow> 0 \<noteq> n"
  "enat n \<noteq> 0 \<longleftrightarrow> n \<noteq> 0"
by (auto simp: enat_0[symmetric])


lemma natceiling_lessD: "nat(ceiling x) < n \<Longrightarrow> x < real n"
  by linarith

lemma le_natceiling_iff:
  fixes n :: nat and r :: real
  shows "n \<le> r \<Longrightarrow> n \<le> nat(ceiling r)"
  by linarith

lemma natceiling_le_iff:
  fixes n :: nat and r :: real
  shows "r \<le> n \<Longrightarrow> nat(ceiling r) \<le> n"
  by linarith

lemma dist_real_noabs_less:
  fixes a b c :: real assumes "dist a b < c" shows "a - b < c"
using assms by (simp add: dist_real_def)

subsection \<open>Lists and Sets\<close>

lemma list_set_tl: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  by (cases xs) auto

lemma list_exhaust3:
  obtains "xs = []" | x where "xs = [x]" | x y ys where "xs = x # y # ys"
  by (metis list.exhaust)

lemma card_Ex_subset:
  "k \<le> card M \<Longrightarrow> \<exists>N. N \<subseteq> M \<and> card N = k"
  by (induct rule: inc_induct) (auto simp: card_Suc_eq)



subsection \<open>Limits and eventually\<close>

text \<open>
  We employ filters and the @{term eventually} predicate to deal with the
  @{term "\<exists>N. \<forall>n\<ge>N. P n"} cases. To make this more convenient, introduce
  a shorter syntax.
\<close>

abbreviation evseq :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>\<infinity>" 10) where
  "evseq P \<equiv> eventually P sequentially"

lemma LIMSEQ_neg_powr:
  assumes s: "s < 0"
  shows "(%x. (real x) powr s) \<longlonglongrightarrow> 0"
  by (simp add: filterlim_real_sequentially s tendsto_neg_powr)

lemma LIMSEQ_inv_powr:
  assumes "0 < c" "0 < d"
  shows "(\<lambda>n :: nat. (c / n) powr d) \<longlonglongrightarrow> 0"
proof (rule tendsto_zero_powrI)
  from \<open>0 < c\<close> have "\<And>x. 0 < x \<Longrightarrow> 0 < c / x" by simp
  then show "\<forall>\<^sup>\<infinity>n. 0 \<le> c / real n"
    using assms(1) by auto
  show "(\<lambda>x. c / real x) \<longlonglongrightarrow> 0"
    by (simp add: lim_const_over_n)
qed (use assms in force)+

end
