section \<open>\<open>Weak_Star_Topology\<close> -- Weak* topology on complex bounded operators\<close>

theory Weak_Star_Topology
  imports Trace_Class Weak_Operator_Topology
begin

definition weak_star_topology :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space) topology\<close>
  where \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))
                              (product_topology (\<lambda>_. euclidean)  (Collect trace_class))\<close>

(* TODO move *)
lemma trace_class_from_trace_class[simp]: \<open>trace_class (from_trace_class t)\<close>
  using from_trace_class by blast

(* TODO move *)
lemma from_trace_class_0[simp]: \<open>from_trace_class 0 = 0\<close>
  by (simp add: zero_trace_class.rep_eq)

(* TODO move *)
lemma pullback_topology_twice:
  assumes \<open>(f -` B) \<inter> A = C\<close>
  shows \<open>pullback_topology A f (pullback_topology B g T) = pullback_topology C (g o f) T\<close>
(* TODO pretty proof *)
proof -
  have aux: \<open>S = A \<longleftrightarrow> S = B\<close> if \<open>A = B\<close> for A B S :: 'z
    using that by simp
  have *: \<open>(\<exists>V. (openin T U \<and> V = g -` U \<inter> B) \<and> S = f -` V \<inter> A) = (openin T U \<and> S = (g \<circ> f) -` U \<inter> C)\<close> for S U
    apply (cases \<open>openin T U\<close>)
     apply (simp_all add: vimage_comp)
    apply (rule aux)
    apply auto
    using assms
    apply auto
    by -
  then have *: \<open>(\<exists>V. (\<exists>U. openin T U \<and> V = g -` U \<inter> B) \<and> S = f -` V \<inter> A) = (\<exists>U. openin T U \<and> S = (g \<circ> f) -` U \<inter> C)\<close> for S
    by metis
  show ?thesis
  apply (simp add: topology_eq openin_pullback_topology)
    apply (intro allI)
    by (rule *)
qed

lemma pullback_topology_homeo_cong:
  assumes \<open>homeomorphic_map T S g\<close>
  assumes \<open>range f \<subseteq> topspace T\<close>
  shows \<open>pullback_topology A f T = pullback_topology A (g o f) S\<close>
proof -
  have \<open>\<exists>Us. openin S Us \<and> f -` Ut \<inter> A = (g \<circ> f) -` Us \<inter> A\<close> if \<open>openin T Ut\<close> for Ut
    apply (rule exI[of _ \<open>g ` Ut\<close>])
    using assms that apply auto
    using homeomorphic_map_openness_eq apply blast
    by (smt (verit, best) homeomorphic_map_maps homeomorphic_maps_map openin_subset rangeI subsetD)
  moreover have \<open>\<exists>Ut. openin T Ut \<and> (g \<circ> f) -` Us \<inter> A = f -` Ut \<inter> A\<close> if \<open>openin S Us\<close> for Us
    apply (rule exI[of _ \<open>(g -` Us) \<inter> topspace T\<close>])
    using assms that apply auto
    by (meson continuous_map_open homeomorphic_imp_continuous_map)
  ultimately show ?thesis
    by (auto simp: topology_eq openin_pullback_topology)
qed

(* lemma open_map_basisI:
  assumes \<open>\<And>U. openin\<close>
  shows \<open>open_map f T U\<close> *)

(* lift_definition map_topology :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a topology \<Rightarrow> 'b topology)\<close> is undefined . *)

lemma homeomorphic_map_product_topology_reindex:
  fixes \<pi> :: \<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>bij_betw \<pi> B A\<close> and \<open>\<And>x. x\<in>B \<Longrightarrow> S x = T (\<pi> x)\<close>
  defines \<open>\<And>f. g f \<equiv> restrict (f o \<pi>) B\<close>
  shows \<open>homeomorphic_map (product_topology T A) (product_topology S B) g\<close>
proof (rule bijective_open_imp_homeomorphic_map)
  have g_topspace: \<open>g x \<in> topspace (product_topology S B)\<close> if \<open>x \<in> topspace (product_topology T A)\<close> for x
    using that apply (auto simp add: g_def[abs_def])
    by (metis PiE_mem assms(1) assms(2) bij_betwE)
  have l1: \<open>x \<in> (\<lambda>x. restrict (x \<circ> \<pi>) B) ` (\<Pi>\<^sub>E i\<in>A. topspace (T i))\<close> if \<open>x \<in> (\<Pi>\<^sub>E i\<in>B. topspace (S i))\<close> for x
    by -
  have open_gU: \<open>openin (product_topology T A) {x \<in> topspace (product_topology T A). g x \<in> U}\<close> 
    if \<open>openin (product_topology S B) U\<close> for U
    using that unfolding openin_product_topology_alt
    apply auto
    by -
  have open_gU2: \<open>openin (product_topology S B) (g ` U)\<close> if \<open>openin (product_topology T A) U\<close> for U
    by -
  show \<open>continuous_map (product_topology T A) (product_topology S B) g\<close>
   by (smt (verit, best) Collect_cong continuous_map_def g_topspace open_gU)
  show \<open>open_map (product_topology T A) (product_topology S B) g\<close>
    by (simp add: open_gU2 open_map_def)
  show \<open>g ` topspace (product_topology T A) = topspace (product_topology S B)\<close>
    apply (auto simp add: l1 topspace_product_topology g_def[abs_def])
    by (metis PiE_mem assms(1) assms(2) bij_betw_apply)
  show \<open>inj_on g (topspace (product_topology T A))\<close>
    apply (simp add: topspace_product_topology g_def[abs_def])
    by (smt (verit) PiE_ext assms(1) bij_betw_iff_bijections comp_apply inj_on_def restrict_apply') 
qed

(* lemma product_topology_parametric[transfer_rule]:
  includes lifting_syntax
(* TODO assms *)
  shows \<open>((R ===> (=)) ===> rel_set R ===> (=)) product_topology product_topology\<close> (* TODO: more general: S instead of (=) *)
  sorry *)

lemma weak_star_topology_def':
  \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
proof -
  define f g where \<open>f x = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))\<close> and \<open>g f' = f' o from_trace_class\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and f' :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex\<close>
  have \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) (product_topology (\<lambda>_. euclidean) UNIV) g\<close>
    unfolding g_def[abs_def]
    apply (rule homeomorphic_map_product_topology_reindex)
    apply (smt (verit, best) Abs_trace_class_inverse UNIV_I bij_betwI' from_trace_class from_trace_class_inject)
    by simp
  then have homeo_g: \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) euclidean g\<close>
    by (simp add: euclidean_product_topology)
  have \<open>weak_star_topology = pullback_topology UNIV f (product_topology (\<lambda>_. euclidean) (Collect trace_class))\<close>
    by (simp add: weak_star_topology_def pullback_topology_homeo_cong homeo_g f_def[abs_def])
  also have \<open>\<dots> = pullback_topology UNIV (g o f) euclidean\<close>
    apply (subst pullback_topology_homeo_cong)
      apply (auto simp add: homeo_g f_def[abs_def])
    by metis
  also have \<open>\<dots> = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
    by (auto simp: f_def[abs_def] g_def[abs_def] o_def)
  finally show ?thesis
    by -
qed

  have \<open>bij_betw g (extensional (Collect trace_class)) UNIV\<close>
sorry

    by (smt (verit, best) Abs_trace_class_inverse comp_eq_elim extensionalityI g_def inj_on_def)
  have 1:  \<open>product_topology (\<lambda>_. euclidean) (Collect trace_class) = pullback_topology (extensional (Collect trace_class)) g euclidean\<close>
  proof -
    have \<open>\<exists>U. open U \<and> S = g -` U \<inter> extensional (Collect trace_class)\<close> if \<open>openin (product_topology (\<lambda>_. euclidean) (Collect trace_class)) S\<close> for S
    proof (rule exI[of _ \<open>g ` S\<close>], intro conjI)
      show \<open>open (g ` S)\<close>
        apply (simp add: g_def open_fun_def)
sorry

        by -
      from openin_subset[OF that]
      have \<open>S \<subseteq> extensional (Collect trace_class)\<close>
        by (auto simp: PiE_def subsetD)
      show \<open>S = g -` g ` S \<inter> extensional (Collect trace_class)\<close>
        sledgehammer
        sorry
    qed
    moreover have \<open>openin (product_topology (\<lambda>_. euclidean) (Collect trace_class)) (g -` U)\<close> if \<open>open U\<close> for U
      by -
     show ?thesis
       apply (auto simp add: topology_eq openin_pullback_topology)
       by -
  qed
  have 2: \<open>g o f = (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x))\<close>
    unfolding f_def[abs_def] g_def[abs_def] by force
  show ?thesis
    by (simp add: weak_star_topology_def 1 pullback_topology_twice flip: f_def[abs_def] 2)



  include lifting_syntax
  have [transfer_rule]: \<open>rel_set cr_trace_class (Collect trace_class) UNIV\<close>
    by auto
  show ?thesis
    unfolding weak_star_topology_def
    apply (rule sym)
    apply (subst euclidean_product_topology[symmetric])
    apply (transfer_prover_start)
    apply transfer_step
    apply transfer_step
         apply transfer_step
        apply (rule transfer_raw(2))
  thm transfer_raw(2)[where R=cr_trace_class]
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step

proof -
  have \<open>undefined = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
    apply (subst euclidean_product_topology[symmetric])
    apply (transfer_start)
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
    apply transfer_step
       defer
       apply transfer_step
       apply transfer_step
     defer
    apply simp
      apply transfer_step

  apply (rule topology_eq[THEN iffD2])
  unfolding weak_star_topology_def
  sorry
(* proof -
  define Abs where \<open>Abs t = (if trace_class t then Abs_trace_class t else 0)\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  have [simp]: \<open>trace_class t \<Longrightarrow> from_trace_class (Abs t) = t\<close> for t
    by (simp add: Abs_trace_class_inverse local.Abs_def)
  have [simp]: \<open>\<not> trace_class t \<Longrightarrow> Abs t = 0\<close> for t
    by (simp add: local.Abs_def)

  have \<open>\<exists>Ua. open Ua \<and>
              (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U = (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` Ua\<close> 
    if \<open>open U\<close> for U :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex) set\<close>
  proof (rule exI[of _ \<open>{f o from_trace_class | f. f \<in> U \<and> (\<forall>t. \<not> trace_class t \<longrightarrow> f t = 0)}\<close>], intro conjI set_eqI iffI)
    from \<open>open U\<close>
    have \<open>openin (product_topology (\<lambda>_. euclidean) UNIV) U\<close>
      by (simp add: open_fun_def)
(*      obtain V where \<open>\<forall>x\<in>U. finite {i \<in> UNIV. V i \<noteq> topspace euclidean} \<and> (\<forall>i \<in> UNIV. openin euclidean (V i)) \<and> x \<in> Pi\<^sub>E UNIV V \<and> Pi\<^sub>E UNIV V \<subseteq> U\<close>
       apply atomize_elim unfolding PiE_def Pi_def
       thm bchoice[where S=U]
       apply (rule bchoice[where S=U])
      unfolding openin_product_topology_alt
      apply auto
sledgehammer
sorry

sorry
  then have 
      by -
 *)    have \<open>open {f. f \<in> U \<and> (\<forall>t. \<not> trace_class t \<longrightarrow> f t = 0)}\<close>
      sorry
    then show \<open>open {f \<circ> from_trace_class |f. f \<in> U \<and> (\<forall>t. \<not> trace_class t \<longrightarrow> f t = 0)}\<close>
sorry
  next
    fix x
    assume asm: \<open>x \<in> (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U\<close>
    show \<open>x \<in> (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -`
              {f \<circ> from_trace_class |f. f \<in> U \<and> (\<forall>t. \<not> trace_class t \<longrightarrow> f t = 0)}\<close>
      apply (intro vimageI2 image_eqI)
      using asm 
      by (auto intro!: exI[of _ \<open>\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0\<close>])
  next
    fix x
    assume asm: \<open>x \<in> (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -`
             {f \<circ> from_trace_class |f. f \<in> U \<and> (\<forall>t. \<not> trace_class t \<longrightarrow> f t = 0)}\<close>
    then obtain f where f_tc: \<open>(\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) = f \<circ> from_trace_class\<close>
      and \<open>f \<in> U\<close> and f0: \<open>\<not> trace_class t \<Longrightarrow> f t = 0\<close> for t
      by auto
    have \<open>(\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) 
            = (\<lambda>t. if trace_class t then (f o from_trace_class) (Abs_trace_class t) else 0)\<close>
      by (metis (mono_tags, lifting) Abs_trace_class_inverse f_tc mem_Collect_eq)
    also have \<open>\<dots> = f\<close>
      apply (auto intro!: ext)
      using f0 by (auto simp add: Abs_trace_class_inverse)
    also have \<open>f \<in> U\<close>
      using \<open>f \<in> U\<close> by blast
    finally show \<open>x \<in> (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U\<close>
      by simp
  qed

  moreover have \<open>\<exists>Ua. open Ua \<and>
              (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` Ua\<close>
    if \<open>open U\<close> for U :: \<open>(('b, 'a) trace_class \<Rightarrow> complex) set\<close>
  proof (rule exI[of _ \<open>{f o Abs | f. f \<in> U}\<close>], intro conjI set_eqI iffI)
    show \<open>open {f \<circ> Abs |f. f \<in> U}\<close>
      sorry
  next
    fix x
    assume asm: \<open>x \<in> (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` U\<close>
    show \<open>x \<in> (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` {f \<circ> Abs |f. f \<in> U}\<close>
      apply (intro vimageI2 image_eqI)
      using asm 
      by (auto intro!: ext exI[of _ \<open>\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x)\<close>] simp: Abs_trace_class_inverse)
  next
    fix x
    assume asm: \<open>x \<in> (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` {f \<circ> Abs |f. f \<in> U}\<close>
    then obtain f where f_tc: \<open>(\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) = f \<circ> Abs\<close>
      and \<open>f \<in> U\<close>
      by auto
    have \<open>(\<lambda>t. trace (from_trace_class t o\<^sub>C\<^sub>L x))
            = (\<lambda>t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) o from_trace_class\<close>
      by auto
    also have \<open>\<dots> = (f o Abs) o from_trace_class\<close>
      using f_tc by auto
    also have \<open>\<dots> = f\<close>
      by (auto intro!: ext simp: Abs_def[abs_def] from_trace_class_inverse)
    also note \<open>f \<in> U\<close>
    finally show \<open>x \<in> (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` U\<close>
      by simp
  qed
   ultimately show ?thesis
     apply (auto intro!: simp: topology_eq weak_star_topology_def openin_pullback_topology)
     by -
qed *)

lemma weak_star_topology_topspace[simp]:
  "topspace weak_star_topology = UNIV"
  unfolding weak_star_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma weak_star_topology_basis:
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  assumes tc: \<open>\<And>i. i \<in> I \<Longrightarrow> trace_class (t i)\<close>
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  have 1: "openin (product_topology (\<lambda>_. euclidean) (Collect trace_class)) {g::('b\<Rightarrow>\<^sub>C\<^sub>L'a)\<Rightarrow>complex. \<forall>i\<in>I. g (t i) \<in> U i}"
    apply (subst asm_rl[of \<open>{g::('b\<Rightarrow>\<^sub>C\<^sub>L'a)\<Rightarrow>complex. \<forall>i\<in>I. g (t i) \<in> U i} = Pi\<^sub>E I\<close>])
    thm product_topology_basis
    apply (rule product_topology_basis)
  have 2: "{a. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L a) \<in> U i}
                = (\<lambda>a. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L a)) -` \<dots> \<inter> UNIV"
    using tc by auto
  show ?thesis
    unfolding weak_star_topology_def 2
    apply (subst openin_pullback_topology)
    using 1 by metis
qed

lemma wot_weaker_than_weak_star:
  "continuous_map weak_star_topology cweak_operator_topology (\<lambda>f. f)"
proof -
  let ?t = \<open>(\<lambda>(x::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0)\<close>
  let ?g = \<open>(\<lambda>a (x::'b, y::'a). x \<bullet>\<^sub>C (a *\<^sub>V y))\<close>
  have *: \<open>continuous_map euclidean euclidean (\<lambda>f (x::'b, y::'a). f (butterfly y x))\<close>
    apply simp
    apply (rule continuous_on_coordinatewise_then_product)
    by auto
  have *: \<open>continuous_map (pullback_topology UNIV ?t euclidean) euclidean ((\<lambda>f (x,y). f (butterfly y x)) \<circ> ?t)\<close>
    apply (rule continuous_map_pullback)
    using * by simp
  have *: \<open>continuous_map (pullback_topology UNIV ?t euclidean) euclidean
             (?g \<circ> (\<lambda>f. f))\<close>
    apply (subst asm_rl[of \<open>?g \<circ> (\<lambda>f. f) = (\<lambda>f (x,y). f (butterfly y x)) o ?t\<close>])
    using * by (auto intro!: ext simp: trace_butterfly_comp)
   show ?thesis
    unfolding cweak_operator_topology_def weak_star_topology_def
    apply (rule continuous_map_pullback')
    using * by auto
qed

(* TODO: Analogous lemmas for the other _weaker_ theorems *)
lemma wot_weaker_than_weak_star':
  \<open>openin cweak_operator_topology U \<Longrightarrow> openin weak_star_topology U\<close>
  using wot_weaker_than_weak_star[where 'a='a and 'b='b]
  by (auto simp: continuous_map_def weak_star_topology_topspace)

lemma weak_star_topology_continuous_duality:
  assumes \<open>trace_class t\<close>
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L x))"
proof -
  have "continuous_map weak_star_topology euclidean ((\<lambda>f. f t) o (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0))"
    unfolding weak_star_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  with assms
  show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_weak_star_topo_iff_coordinatewise:
  fixes f :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  shows "continuous_map T weak_star_topology f
    \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x)))"
proof (auto)
  fix t :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>trace_class t\<close>
  assume "continuous_map T weak_star_topology f"
  with continuous_map_compose[OF this weak_star_topology_continuous_duality, OF \<open>trace_class t\<close>]
  have "continuous_map T euclidean ((\<lambda>x. trace (t o\<^sub>C\<^sub>L x)) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))"
    unfolding comp_def by auto
next
  assume \<open>\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close>
  then have \<open>continuous_map T euclidean (\<lambda>x. if trace_class t then trace (t o\<^sub>C\<^sub>L f x) else 0)\<close> for t
    apply (cases \<open>trace_class t\<close>) by auto
  then have *: "continuous_map T euclidean ((\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) o f)"
    by (auto simp flip: euclidean_product_topology simp: o_def)
  show "continuous_map T weak_star_topology f"
    unfolding weak_star_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: *)
qed

lemma weak_star_topology_weaker_than_euclidean:
  "continuous_map euclidean weak_star_topology (\<lambda>f. f)"
  apply (subst continuous_on_weak_star_topo_iff_coordinatewise)
  by (auto intro!: linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_trace_duality)


typedef (overloaded) ('a,'b) cblinfun_weak_star = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> 
  morphisms from_weak_star to_weak_star ..
setup_lifting type_definition_cblinfun_weak_star

lift_definition id_weak_star :: \<open>('a::complex_normed_vector, 'a) cblinfun_weak_star\<close> is id_cblinfun .

instantiation cblinfun_weak_star :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_weak_star :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is uminus .
lift_definition zero_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star\<close> is 0 .
lift_definition minus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is minus .
lift_definition plus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is plus .
lift_definition scaleR_cblinfun_weak_star :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_space begin
lift_definition open_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star set \<Rightarrow> bool\<close> is \<open>openin weak_star_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_weak_star set)\<close>
    apply transfer
    by (metis weak_star_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_weak_star set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_weak_star set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star) (nhdsin weak_star_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: weak_star_topology_topspace)
  by transfer_prover


lemma limitin_weak_star_topology:
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>j. trace (t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L l)) F)\<close>
  by (simp add: weak_star_topology_def limitin_pullback_topology tendsto_coordinatewise)


lemma filterlim_weak_star_topology:
  \<open>filterlim f (nhdsin weak_star_topology l) = limitin weak_star_topology f l\<close>
  by (auto simp: weak_star_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

lemma openin_weak_star_topology: \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` V)\<close>
  by (simp add: weak_star_topology_def openin_pullback_topology)

lemma hausdorff_weak_star[simp]: \<open>hausdorff weak_star_topology\<close>
  by (metis cweak_operator_topology_topspace hausdorff_cweak_operator_topology hausdorff_def weak_star_topology_topspace wot_weaker_than_weak_star')
(* proof (unfold hausdorff_def, intro ballI impI)
  fix x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> assume \<open>x \<noteq> y\<close>
  then obtain a b where \<open>a \<bullet>\<^sub>C (x *\<^sub>V b) \<noteq> a \<bullet>\<^sub>C (y *\<^sub>V b)\<close>
    by (meson cblinfun_eqI cinner_extensionality)
  then have \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<noteq> trace (butterfly b a o\<^sub>C\<^sub>L y)\<close>
    by (simp add: trace_butterfly_comp)
  then obtain U' V' where U': \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<in> U'\<close> and V': \<open>trace (butterfly b a o\<^sub>C\<^sub>L y) \<in> V'\<close> 
    and \<open>open U'\<close> and \<open>open V'\<close> and \<open>U' \<inter> V' = {}\<close>
    by (meson separation_t2)
  define U'' V'' where \<open>U'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> U'}\<close> and \<open>V'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> V'}\<close>
  have \<open>open U''\<close>
    unfolding U''_def apply (rule product_topology_basis')
    using \<open>open U'\<close> by auto
  have \<open>open V''\<close>
    unfolding V''_def apply (rule product_topology_basis')
    using \<open>open V'\<close> by auto
  define U V where \<open>U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U''\<close> and
    \<open>V = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` V''\<close>
  have openU: \<open>openin weak_star_topology U\<close>
    using U_def \<open>open U''\<close> openin_weak_star_topology by blast
  have openV: \<open>openin weak_star_topology V\<close>
    using V_def \<open>open V''\<close> openin_weak_star_topology by blast
  have \<open>x \<in> U\<close>
    by (auto simp: U_def U''_def U')
  have \<open>y \<in> V\<close>
    by (auto simp: V_def V''_def V')
  have \<open>U \<inter> V = {}\<close>
    using \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def U''_def V''_def)
  show \<open>\<exists>U V. openin weak_star_topology U \<and> openin weak_star_topology V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
    apply (rule exI[of _ U], rule exI[of _ V])
    using \<open>x \<in> U\<close> \<open>y \<in> V\<close> openU openV \<open>U \<inter> V = {}\<close> by auto
qed *)


lemma Domainp_cr_cblinfun_weak_star[simp]: \<open>Domainp cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_weak_star.left_total left_totalE)

lemma Rangep_cr_cblinfun_weak_star[simp]: \<open>Rangep cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_weak_star_def)


lemma transfer_euclidean_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_weak_star) weak_star_topology euclidean\<close>
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (openin weak_star_topology) (openin euclidean)\<close>
    apply (auto simp: rel_topology_def cr_cblinfun_weak_star_def rel_set_def intro!: rel_funI)
     apply transfer
     apply auto
     apply (meson openin_subopen subsetI)
    apply transfer
    apply auto
    by (meson openin_subopen subsetI)
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin weak_star_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_weak_star set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Rangep_set)
qed


lemma hausdorff_OFCLASS_t2_space: \<open>OFCLASS('a::topological_space, t2_space_class)\<close> if \<open>hausdorff (euclidean :: 'a topology)\<close>
proof intro_classes
  fix a b :: 'a
  assume \<open>a \<noteq> b\<close>
  from that
  show \<open>\<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    unfolding hausdorff_def
    using \<open>a \<noteq> b\<close> by auto
qed

(* TODO move *)
definition \<open>opensets T = Collect (openin T)\<close>
  \<comment> \<open>This behaves more nicely with the @{method transfer}-method (and friends) than \<^const>\<open>openin\<close>.
      So rewriting a subgoal to use, e.g., \<^term>\<open>\<exists>U\<in>opensets T. xxx\<close> instead of \<^term>\<open>\<exists>U. openin T U \<longrightarrow> xxx\<close> can make @{method transfer} work better. \<close>

(* TODO move *)
lemma opensets_parametric[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_set (rel_set R)) opensets opensets\<close>
proof (intro rel_funI rel_setI)
  fix S T
  assume rel_topo: \<open>rel_topology R S T\<close>
  fix U
  assume \<open>U \<in> opensets S\<close>
  then show \<open>\<exists>V \<in> opensets T. rel_set R U V\<close>
    by (smt (verit, del_insts) Domainp.cases mem_Collect_eq opensets_def rel_fun_def rel_topo rel_topology_def)
next
  fix S T assume rel_topo: \<open>rel_topology R S T\<close>
  fix U assume \<open>U \<in> opensets T\<close>
  then show \<open>\<exists>V \<in> opensets S. rel_set R V U\<close>
    by (smt (verit) RangepE mem_Collect_eq opensets_def rel_fun_def rel_topo rel_topology_def)
qed

(* TODO move *)
lemma hausdorff_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> (\<longleftrightarrow>)) hausdorff hausdorff\<close>
proof -
  have hausdorff_def': \<open>hausdorff T \<longleftrightarrow> (\<forall>x\<in>topspace T. \<forall>y\<in>topspace T. x \<noteq> y \<longrightarrow> (\<exists>U \<in> opensets T. \<exists>V \<in> opensets T. x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>
    for T :: \<open>'z topology\<close>
    unfolding opensets_def hausdorff_def Bex_def by auto
  show ?thesis
    unfolding hausdorff_def'
    by transfer_prover
qed

instance cblinfun_weak_star :: (chilbert_space, chilbert_space) t2_space
  apply (rule hausdorff_OFCLASS_t2_space)
  apply transfer
  by (rule hausdorff_weak_star)
(* proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_weak_star\<close>
  assume \<open>a \<noteq> b\<close>
  then have \<open>Abs_cblinfun_wot (from_weak_star a) \<noteq> Abs_cblinfun_wot (from_weak_star b)\<close>
    by (simp add: Abs_cblinfun_wot_inject from_weak_star_inject)
  from hausdorff[OF this]

  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    apply transfer using wot_weaker_than_weak_star' by auto
qed *)

lemma weak_star_topology_plus_cont: \<open>LIM (x,y) nhdsin weak_star_topology a \<times>\<^sub>F nhdsin weak_star_topology b.
            x + y :> nhdsin weak_star_topology (a + b)\<close>
proof -
  have trace_plus: \<open>trace (t o\<^sub>C\<^sub>L (a + b)) = trace (t o\<^sub>C\<^sub>L a) + trace (t o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and a b
    by (auto simp: cblinfun_compose_add_right trace_plus that trace_class_comp_left)
  show ?thesis
    unfolding weak_star_topology_def
    apply (rule_tac pullback_topology_bi_cont[where f'=plus])
    by (auto simp: trace_plus case_prod_unfold tendsto_add_Pair)
qed

instance cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply transfer
    using weak_star_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have \<open>continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L - x))\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using weak_star_topology_continuous_duality[of \<open>-t\<close>]
    by (auto simp: cblinfun_compose_uminus_left cblinfun_compose_uminus_right intro!: that trace_class_uminus)
  then have *: \<open>continuous_map weak_star_topology weak_star_topology (uminus :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _)\<close>
    by (auto simp: continuous_on_weak_star_topo_iff_coordinatewise)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where s=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a::'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
proof -
  let ?t = \<open>\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0\<close>
  have *: \<open>open B \<Longrightarrow> open ((*\<^sub>V) b -` B)\<close> for B
    by (simp add: continuous_open_vimage)
  (* have **: \<open>((\<lambda>a. b *\<^sub>V a \<psi>) -` B \<inter> UNIV) = (Pi\<^sub>E UNIV (\<lambda>i. if i=\<psi> then (\<lambda>a. b *\<^sub>V a) -` B else UNIV))\<close>  *)
  have **: \<open>(\<lambda>f :: _ \<Rightarrow> complex. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0) -` B \<inter> UNIV
         = (Pi\<^sub>E UNIV (\<lambda>i. if i=t o\<^sub>C\<^sub>L b then B else UNIV))\<close> 
    if \<open>trace_class t\<close>
    for t and B
    apply (cases \<open>trace_class t\<close>)
    using that by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>f :: _ \<Rightarrow> complex. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0)\<close> for t
    apply (cases \<open>trace_class t\<close>)
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **, simp)
    apply (rule open_PiE)
    using * by auto
  have *: \<open>continuous_on UNIV (\<lambda>(f :: _ \<Rightarrow> complex) t. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0)\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    by (rule *)
  show ?thesis
    unfolding weak_star_topology_def
    apply (rule continuous_map_pullback')
     apply (subst asm_rl[of \<open>?t \<circ> (o\<^sub>C\<^sub>L) b = (\<lambda>f t. if trace_class t then f (t o\<^sub>C\<^sub>L b) else 0) \<circ> ?t\<close>])
      apply (auto simp: cblinfun_assoc_left(1) intro!: ext trace_class_comp_left)[1]
     apply (rule continuous_map_pullback)
    using * by auto
qed

lemma continuous_map_right_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>b::'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  define f and g where \<open>f x t = (if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0)\<close>
    and \<open>g f' t' = (if trace_class t' then f' (a o\<^sub>C\<^sub>L t') else 0)\<close> 
      for x :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'c\<close> and t :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and f' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> complex\<close> and t' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  have gf: \<open>((\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) \<circ> (\<lambda>b. b o\<^sub>C\<^sub>L a)) = g o f\<close>
    apply (auto intro!: ext simp add: o_def trace_class_comp_right f_def g_def)
    by (metis cblinfun_compose_assoc circularity_of_trace trace_class_comp_left)
  have cont: \<open>continuous_on UNIV (\<lambda>x. g x t)\<close> for t
    apply (cases \<open>trace_class t\<close>) by (auto simp: g_def)
  have \<open>continuous_map euclidean euclidean g\<close>
   by (auto intro!: continuous_on_coordinatewise_then_product cont)
  then have \<open>continuous_map (pullback_topology UNIV f euclidean) euclidean (g \<circ> f)\<close>
    by (rule continuous_map_pullback)
  then show ?thesis
    unfolding weak_star_topology_def gf[symmetric] f_def
    apply (rule continuous_map_pullback')
    by auto
qed

lemma continuous_map_scaleC_weak_star: \<open>continuous_map weak_star_topology weak_star_topology (scaleC c)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  by (rule continuous_map_left_comp_weak_star)

lemma continuous_scaleC_weak_star: \<open>continuous_on X (scaleC c :: (_,_) cblinfun_weak_star \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  by (rule continuous_map_scaleC_weak_star)

lemma weak_star_closure_is_csubspace[simp]:
  fixes A::"('a::chilbert_space, 'b::chilbert_space) cblinfun_weak_star set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof (rule complex_vector.subspaceI)
  show 0: \<open>0 \<in> closure A\<close>
    by (simp add: assms closure_def complex_vector.subspace_0)
  show \<open>x + y \<in> closure A\<close> if \<open>x \<in> closure A\<close> \<open>y \<in> closure A\<close> for x y
  proof -
    define FF where \<open>FF = ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
    have nt: \<open>FF \<noteq> bot\<close>
      by (simp add: prod_filter_eq_bot that(1) that(2) FF_def flip: closure_nhds_principal)
    have \<open>\<forall>\<^sub>F x in FF. fst x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter fst_conv inf_sup_ord(2) le_principal)
    moreover have \<open>\<forall>\<^sub>F x in FF. snd x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter snd_conv inf_sup_ord(2) le_principal)
    ultimately have FF_plus: \<open>\<forall>\<^sub>F x in FF. fst x + snd x \<in> A\<close>
      by (smt (verit, best) assms complex_vector.subspace_add eventually_elim2)

    have \<open>(fst \<longlongrightarrow> x) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_fst_prod_filter
      using le_inf_iff by blast
    moreover have \<open>(snd \<longlongrightarrow> y) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_snd_prod_filter
      using le_inf_iff by blast
    ultimately have \<open>(id \<longlongrightarrow> (x,y)) FF\<close>
      by (simp add: filterlim_def nhds_prod prod_filter_mono FF_def)

    moreover note tendsto_add_Pair[of x y]
    ultimately have \<open>(((\<lambda>x. fst x + snd x) o id) \<longlongrightarrow> (\<lambda>x. fst x + snd x) (x,y)) FF\<close>
      unfolding filterlim_def nhds_prod
      by (smt (verit, best) filterlim_compose filterlim_def filterlim_filtermap fst_conv snd_conv tendsto_compose_filtermap)

    then have \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> (x+y)) FF\<close>
      by simp
    then show \<open>x + y \<in> closure A\<close>
      using nt FF_plus by (rule limit_in_closure)
  qed
  show \<open>c *\<^sub>C x \<in> closure A\<close> if \<open>x \<in> closure A\<close> for x c
    using  that
    using image_closure_subset[where S=A and T=\<open>closure A\<close> and f=\<open>scaleC c\<close>, OF continuous_scaleC_weak_star]
    apply auto
    by (metis 0 assms closure_subset csubspace_scaleC_invariant imageI in_mono scaleC_eq_0_iff)
qed


lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (closedin weak_star_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] weak_star_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> rel_set cr_cblinfun_weak_star) (Abstract_Topology.closure_of weak_star_topology) closure\<close>
  apply (subst closure_of_hull[where X=weak_star_topology, unfolded weak_star_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma weak_star_closure_is_csubspace'[simp]:
  fixes A::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (weak_star_topology closure_of A)\<close>
  using weak_star_closure_is_csubspace[of \<open>to_weak_star ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_weak_star_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin weak_star_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>t. trace_class t \<Longrightarrow> has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L a i)) I (trace (t o\<^sub>C\<^sub>L b))\<close>
  shows \<open>b \<in> A\<close>
proof -
  have 1: \<open>range (sum a) \<subseteq> A\<close>
  proof -
    have \<open>sum a X \<in> A\<close> for X
      apply (induction X rule:infinite_finite_induct)
      by (auto simp add: subspace complex_vector.subspace_0 aA complex_vector.subspace_add)
    then show ?thesis
      by auto
  qed

  from has_sum
  have \<open>((\<lambda>F. \<Sum>i\<in>F. trace (t o\<^sub>C\<^sub>L a i)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L b)) (finite_subsets_at_top I)\<close> if \<open>trace_class t\<close> for t
    by (auto intro: that simp: has_sum_def)
  then have \<open>limitin weak_star_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_weak_star_topology cblinfun_compose_sum_right trace_sum trace_class_comp_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

lemma has_sum_in_weak_star:
  \<open>has_sum_in weak_star_topology f A l \<longleftrightarrow> 
     (\<forall>t. trace_class t \<longrightarrow> has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) A (trace (t o\<^sub>C\<^sub>L l)))\<close>
proof -
  have *: \<open>trace (t o\<^sub>C\<^sub>L sum f F) = sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) F\<close> if \<open>trace_class t\<close> 
    for t F
    by (simp_all add: cblinfun_compose_sum_right that trace_class_comp_left trace_sum)
  show ?thesis
    by (simp add: * has_sum_def has_sum_in_def limitin_weak_star_topology)
qed

lemma infsum_butterfly_ket: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (ket i) (ket i)) UNIV id_cblinfun\<close>
proof (rule has_sum_in_weak_star[THEN iffD2, rule_format])
  fix t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume [simp]: \<open>trace_class t\<close>
  from trace_has_sum[OF is_onb_ket \<open>trace_class t\<close>]
  have \<open>has_sum (\<lambda>i. ket i \<bullet>\<^sub>C (t *\<^sub>V ket i)) UNIV (trace t)\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def)
  then show \<open>has_sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L selfbutterket i)) UNIV (trace (t o\<^sub>C\<^sub>L id_cblinfun))\<close>
    by (simp add: trace_butterfly_comp')
qed

unbundle no_cblinfun_notation

end
