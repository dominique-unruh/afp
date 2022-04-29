section \<open>\<open>Misc_Tensor_Product\<close> -- Miscelleanous results missing from other theories\<close>

theory Misc_Tensor_Product
  imports "HOL-Analysis.Elementary_Topology" "HOL-Analysis.Abstract_Topology"
    "HOL-Analysis.Abstract_Limits" "HOL-Analysis.Function_Topology" "HOL-Cardinals.Cardinals"
    "HOL-Analysis.Infinite_Sum"
begin

(* TODO move, explain *)
lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis

lemma on_closure_leI:
  fixes f g :: \<open>'a::topological_space \<Rightarrow> 'b::linorder_topology\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x\<close>
  assumes xS: \<open>x \<in> closure S\<close>
  assumes cont: \<open>continuous_on UNIV f\<close> \<open>continuous_on UNIV g\<close> (* Is "isCont f x" "isCont g x" sufficient? *)
  shows \<open>f x \<le> g x\<close>
proof -
  define X where \<open>X = {x. f x \<le> g x}\<close>
  have \<open>closed X\<close>
    using cont by (simp add: X_def closed_Collect_le)
  moreover have \<open>S \<subseteq> X\<close>
    by (simp add: X_def eq subsetI)
  ultimately have \<open>closure S \<subseteq> X\<close>
    using closure_minimal by blast
  with xS have \<open>x \<in> X\<close>
    by auto
  then show ?thesis
    using X_def by blast
qed

lemma inv_prod_swap[simp]: \<open>inv prod.swap = prod.swap\<close>
  by (simp add: inv_unique_comp)

lemma limitin_pullback_topology: 
  \<open>limitin (pullback_topology A g T) f l F \<longleftrightarrow> l\<in>A \<and> (\<forall>\<^sub>F x in F. f x \<in> A) \<and> limitin T (g o f) (g l) F\<close>
  apply (simp add: topspace_pullback_topology limitin_def openin_pullback_topology imp_ex flip: ex_simps(1))
  apply rule
   apply simp
   apply safe
  using eventually_mono apply fastforce
   apply (simp add: eventually_conj_iff)
  by (simp add: eventually_conj_iff)

lemma tendsto_coordinatewise: \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
proof (intro iffI allI)
  assume asm: \<open>(f \<longlongrightarrow> l) F\<close>
  then show \<open>((\<lambda>i. f i x) \<longlongrightarrow> l x) F\<close> for x
    apply (rule continuous_on_tendsto_compose[where s=UNIV, rotated])
    by auto
next
  assume asm: \<open>(\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
  show \<open>(f \<longlongrightarrow> l) F\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
    from product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>l \<in> S\<close>]
    obtain U where lU: \<open>l \<in> Pi UNIV U\<close> and openU: \<open>\<And>x. open (U x)\<close> and finiteD: \<open>finite {x. U x \<noteq> UNIV}\<close> and US: \<open>Pi UNIV U \<subseteq> S\<close>
      by (auto simp add: PiE_UNIV_domain)

    define D where \<open>D = {x. U x \<noteq> UNIV}\<close>
    with finiteD have finiteD: \<open>finite D\<close>
      by simp
    have PiUNIV: \<open>t \<in> Pi UNIV U \<longleftrightarrow> (\<forall>x\<in>D. t x \<in> U x)\<close> for t
      using D_def by blast

    have f_Ui: \<open>\<forall>\<^sub>F i in F. f i x \<in> U x\<close> for x
      using asm[rule_format, of x] openU[of x]
      using lU topological_tendstoD by fastforce

    have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>D. f x i \<in> U i\<close>
      using finiteD
    proof induction
      case empty
      then show ?case
        by simp
    next
      case (insert x F)
      with f_Ui show ?case
        by (simp add: eventually_conj_iff)
    qed

    then show \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
      using US by (simp add: PiUNIV eventually_mono in_mono)
  qed
qed

lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover


definition rel_topology :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a topology \<Rightarrow> 'b topology \<Rightarrow> bool)\<close> where
  \<open>rel_topology R S T \<longleftrightarrow> (rel_fun (rel_set R) (=)) (openin S) (openin T)\<close>

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R ===> (=)) openin openin\<close>
  by (auto simp add: rel_fun_def rel_topology_def)

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total R\<close>
  shows \<open>(rel_topology R ===> rel_set R) topspace topspace\<close>
  unfolding topspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total S\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>bi_total R\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_topology S ===> (R ===> S) ===> (=)) continuous_map continuous_map\<close>
  unfolding continuous_map_def
  by transfer_prover


lemma limitin_closure_of:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) eventually_happens' in_closure_of limitin_def rangeI subsetD)

lemma limitin_closedin:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> S\<close>
  by (metis assms(1) assms(2) assms(3) assms(4) closure_of_eq limitin_closure_of)



lemma closure_nhds_principal: \<open>a \<in> closure A \<longleftrightarrow> inf (nhds a) (principal A) \<noteq> bot\<close>
proof (rule iffI)
  show \<open>inf (nhds a) (principal A) \<noteq> bot\<close> if \<open>a \<in> closure A\<close>
    apply (cases \<open>a \<in> A\<close>)
     apply (auto simp: filter_eq_iff eventually_inf eventually_principal eventually_nhds) apply blast
    apply (subgoal_tac \<open>a islimpt A\<close>)
     apply ( simp add: filter_eq_iff eventually_inf eventually_principal eventually_nhds islimpt_def)
     apply meson
    by (simp add: islimpt_in_closure that)
  show \<open>a \<in> closure A\<close> if \<open>inf (nhds a) (principal A) \<noteq> bot\<close>
    by (metis Diff_empty Diff_insert0 at_within_def closure_subset not_in_closure_trivial_limitI subsetD that)
qed


lemma limit_in_closure:
  assumes lim: \<open>(f \<longlongrightarrow> x) F\<close>
  assumes nt: \<open>F \<noteq> bot\<close>
  assumes inA: \<open>\<forall>\<^sub>F x in F. f x \<in> A\<close>
  shows \<open>x \<in> closure A\<close>
  apply (cases \<open>x \<in> A\<close>)
   apply (meson closure_subset in_mono)
  apply (auto simp: closure_def filterlim_def islimpt_def le_filter_def eventually_filtermap
      eventually_nhds image_def)
  by (smt (verit, ccfv_threshold) assms(1) assms(3) eventually_elim2 nt tendsto_def trivial_limit_eq)

lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin 
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)



lemma pullback_topology_bi_cont: 
  fixes g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c::topological_space)\<close>
    and f :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and f' :: \<open>'c \<Rightarrow> 'c \<Rightarrow> 'c\<close>
  assumes gf_f'g: \<open>\<And>a b i. g (f a b) i = f' (g a i) (g b i)\<close>
  assumes f'_cont: \<open>\<And>a' b'. (case_prod f' \<longlongrightarrow> f' a' b') (nhds a' \<times>\<^sub>F nhds b')\<close>
  defines \<open>T \<equiv> pullback_topology UNIV g euclidean\<close>
  shows \<open>LIM (x,y) nhdsin T a \<times>\<^sub>F nhdsin T b. f x y :> nhdsin T (f a b)\<close>
proof -
  have topspace[simp]: \<open>topspace T = UNIV\<close>
    unfolding T_def topspace_pullback_topology by simp
  have openin: \<open>openin T U \<longleftrightarrow> (\<exists>V. open V \<and> U = g -` V)\<close> for U
    by (simp add: assms openin_pullback_topology)

  have 1: \<open>nhdsin T a = filtercomap g (nhds (g a))\<close>
    for a :: 'a
    by (auto simp add: filter_eq_iff eventually_filtercomap eventually_nhds eventually_nhdsin openin)

  have \<open>((g \<circ> case_prod f) \<longlongrightarrow> g (f a b)) (nhdsin T a \<times>\<^sub>F nhdsin T b)\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and gfS: \<open>g (f a b) \<in> S\<close>
    obtain U where gf_PiE: \<open>g (f a b) \<in> Pi\<^sub>E UNIV U\<close> and openU: \<open>\<forall>i. openin euclidean (U i)\<close>
      and finiteD: \<open>finite {i. U i \<noteq> topspace euclidean}\<close> and US: \<open>Pi\<^sub>E UNIV U \<subseteq> S\<close>
      using product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] gfS]
      by auto

    define D where \<open>D = {i. U i \<noteq> UNIV}\<close>
    with finiteD have \<open>finite D\<close>
      by auto

    from openU have openU: \<open>open (U i)\<close> for i
      by auto

    have *: \<open>f' (g a i) (g b i) \<in> U i\<close> for i
      by (metis PiE_mem gf_PiE iso_tuple_UNIV_I gf_f'g)

    have \<open>\<forall>\<^sub>F x in nhds (g a i) \<times>\<^sub>F nhds (g b i). case_prod f' x \<in> U i\<close> for i
      using tendsto_def[THEN iffD1, rule_format, OF f'_cont openU *, of i] by -

    then obtain Pa Pb where \<open>eventually (Pa i) (nhds (g a i))\<close> and \<open>eventually (Pb i) (nhds (g b i))\<close>
      and PaPb_plus: \<open>(\<forall>x y. Pa i x \<longrightarrow> Pb i y \<longrightarrow> f' x y \<in> U i)\<close> for i
      unfolding eventually_prod_filter by (metis prod.simps(2))

    from \<open>\<And>i. eventually (Pa i) (nhds (g a i))\<close>
    obtain Ua where \<open>open (Ua i)\<close> and a_Ua: \<open>g a i \<in> Ua i\<close> and Ua_Pa: \<open>Ua i \<subseteq> Collect (Pa i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    from \<open>\<And>i. eventually (Pb i) (nhds (g b i))\<close>
    obtain Ub where \<open>open (Ub i)\<close> and b_Ub: \<open>g b i \<in> Ub i\<close> and Ub_Pb: \<open>Ub i \<subseteq> Collect (Pb i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    have UaUb_plus: \<open>x \<in> Ua i \<Longrightarrow> y \<in> Ub i \<Longrightarrow> f' x y \<in> U i\<close> for i x y
      by (metis PaPb_plus Ua_Pa Ub_Pb mem_Collect_eq subsetD)

    define Ua' where \<open>Ua' i = (if i\<in>D then Ua i else UNIV)\<close> for i
    define Ub' where \<open>Ub' i = (if i\<in>D then Ub i else UNIV)\<close> for i

    have Ua'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ua' i = UNIV\<close> for i
      by (simp add: D_def Ua'_def)
    have Ub'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ub' i = UNIV\<close> for i
      by (simp add: D_def Ub'_def)
    have [simp]: \<open>open (Ua' i)\<close> for i
      by (simp add: Ua'_def \<open>open (Ua _)\<close>)
    have [simp]: \<open>open (Ub' i)\<close> for i
      by (simp add: Ub'_def \<open>open (Ub _)\<close>)
    have a_Ua': \<open>g a i \<in> Ua' i\<close> for i
      by (simp add: Ua'_def a_Ua)
    have b_Ub': \<open>g b i \<in> Ub' i\<close> for i
      by (simp add: Ub'_def b_Ub)
    have UaUb'_plus: \<open>a' \<in> Ua' i \<Longrightarrow> b' \<in> Ub' i \<Longrightarrow> f' a' b' \<in> U i\<close> for i a' b'
      apply (cases \<open>i \<in> D\<close>)
      using UaUb_plus by (auto simp add: Ua'_def  Ub'_def D_def)

    define Ua'' where \<open>Ua'' = Pi UNIV Ua'\<close>
    define Ub'' where \<open>Ub'' = Pi UNIV Ub'\<close>

    have \<open>open Ua''\<close>
      using finiteD Ua'_UNIV
      apply (auto simp add: open_fun_def Ua''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ua'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have \<open>open Ub''\<close>
      using finiteD Ub'_UNIV
      apply (auto simp add: open_fun_def Ub''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ub'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have a_Ua'': \<open>g a \<in> Ua''\<close>
      by (simp add: Ua''_def a_Ua')
    have b_Ub'': \<open>g b \<in> Ub''\<close>
      by (simp add: Ub''_def b_Ub')
    have UaUb''_plus: \<open>a' \<in> Ua'' \<Longrightarrow> b' \<in> Ub'' \<Longrightarrow> f' (a' i) (b' i) \<in> U i\<close> for i a' b'
      using UaUb'_plus apply (auto simp add: Ua''_def  Ub''_def)
      by blast

    define Ua''' where \<open>Ua''' = g -` Ua''\<close>
    define Ub''' where \<open>Ub''' = g -` Ub''\<close>
    have \<open>openin T Ua'''\<close>
      using \<open>open Ua''\<close> by (auto simp: openin Ua'''_def)
    have \<open>openin T Ub'''\<close>
      using \<open>open Ub''\<close> by (auto simp: openin Ub'''_def)
    have a_Ua'': \<open>a \<in> Ua'''\<close>
      by (simp add: Ua'''_def a_Ua'')
    have b_Ub'': \<open>b \<in> Ub'''\<close>
      by (simp add: Ub'''_def b_Ub'')
    have UaUb'''_plus: \<open>a \<in> Ua''' \<Longrightarrow> b \<in> Ub''' \<Longrightarrow> f' (g a i) (g b i) \<in> U i\<close> for i a b
      by (simp add: Ua'''_def UaUb''_plus Ub'''_def)

    define Pa' where \<open>Pa' a \<longleftrightarrow> a \<in> Ua'''\<close> for a
    define Pb' where \<open>Pb' b \<longleftrightarrow> b \<in> Ub'''\<close> for b

    have Pa'_nhd: \<open>eventually Pa' (nhdsin T a)\<close>
      using \<open>openin T Ua'''\<close>
      by (auto simp add: Pa'_def eventually_nhdsin intro!: exI[of _ \<open>Ua'''\<close>] a_Ua'')
    have Pb'_nhd: \<open>eventually Pb' (nhdsin T b)\<close>
      using \<open>openin T Ub'''\<close>
      by (auto simp add: Pb'_def eventually_nhdsin intro!: exI[of _ \<open>Ub'''\<close>] b_Ub'')
    have Pa'Pb'_plus: \<open>(g \<circ> case_prod f) (a, b) \<in> S\<close> if \<open>Pa' a\<close> \<open>Pb' b\<close> for a b
      using that UaUb'''_plus US
      by (auto simp add: Pa'_def Pb'_def PiE_UNIV_domain Pi_iff gf_f'g)

    show \<open>\<forall>\<^sub>F x in nhdsin T a \<times>\<^sub>F nhdsin T b. (g \<circ> case_prod f) x \<in> S\<close>
      using Pa'_nhd Pb'_nhd Pa'Pb'_plus
      unfolding eventually_prod_filter
      apply (rule_tac exI[of _ Pa'])
      apply (rule_tac exI[of _ Pb'])
      by simp
  qed
  then show ?thesis
    unfolding 1 filterlim_filtercomap_iff by -
qed

definition \<open>has_sum_in T f A x \<longleftrightarrow> limitin T (sum f) x (finite_subsets_at_top A)\<close>

definition \<open>summable_on_in T f A \<longleftrightarrow> (\<exists>x. has_sum_in T f A x)\<close>

definition \<open>infsum_in T f A = (if summable_on_in T f A then (THE l. has_sum_in T f A l) else 0)\<close>

definition hausdorff where \<open>hausdorff T \<longleftrightarrow> (\<forall>x \<in> topspace T. \<forall>y \<in> topspace T. x \<noteq> y \<longrightarrow> (\<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>

lemma hausdorffI: 
  assumes \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
  shows \<open>hausdorff T\<close>
  using assms by (auto simp: hausdorff_def)

lemma limitin_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>F \<noteq> bot\<close>
  assumes lim: \<open>limitin T f l F\<close>
  assumes lim': \<open>limitin T f l' F\<close>
  shows \<open>l = l'\<close>
proof (rule ccontr)
  assume "l \<noteq> l'"
  have \<open>l \<in> topspace T\<close> \<open>l' \<in> topspace T\<close>
    by (meson lim lim' limitin_def)+
  obtain U V where "openin T U" "openin T V" "l \<in> U" "l' \<in> V" "U \<inter> V = {}"
    using \<open>hausdorff T\<close> \<open>l \<noteq> l'\<close> unfolding hausdorff_def
    by (meson \<open>l \<in> topspace T\<close> \<open>l' \<in> topspace T\<close>)
  have "eventually (\<lambda>x. f x \<in> U) F"
    using lim \<open>openin T U\<close> \<open>l \<in> U\<close>
    by (simp add: limitin_def)
  moreover
  have "eventually (\<lambda>x. f x \<in> V) F"
    using lim' \<open>openin T V\<close> \<open>l' \<in> V\<close>
    by (simp add: limitin_def)
  ultimately
  have "eventually (\<lambda>x. False) F"
  proof eventually_elim
    case (elim x)
    then have "f x \<in> U \<inter> V" by simp
    with \<open>U \<inter> V = {}\<close> show ?case by simp
  qed
  with \<open>\<not> trivial_limit F\<close> show "False"
    by (simp add: trivial_limit_def)
qed


lemma has_sum_in_unique:
  assumes \<open>hausdorff T\<close>
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>has_sum_in T f A l'\<close>
  shows \<open>l = l'\<close>
  using assms(1) _ assms(2,3)[unfolded has_sum_in_def] 
  apply (rule limitin_unique)
  by simp

lemma has_sum_in_infsum_in: 
  assumes \<open>hausdorff T\<close> and summable: \<open>summable_on_in T f A\<close>
  shows \<open>has_sum_in T f A (infsum_in T f A)\<close>
  apply (simp add: infsum_in_def summable)
  apply (rule theI'[of \<open>has_sum_in T f A\<close>])
  using has_sum_in_unique[OF \<open>hausdorff T\<close>, of f A] summable
  by (meson summable_on_in_def)


lemma nhdsin_mono:
  assumes [simp]: \<open>\<And>x. openin T' x \<Longrightarrow> openin T x\<close>
  assumes [simp]: \<open>topspace T = topspace T'\<close>
  shows \<open>nhdsin T a \<le> nhdsin T' a\<close>
  unfolding nhdsin_def 
  by (auto intro!: INF_superset_mono)


lemma card_prod_omega: \<open>X *c natLeq =o X\<close> if \<open>Cinfinite X\<close>
  by (simp add: Cinfinite_Cnotzero cprod_infinite1' natLeq_Card_order natLeq_cinfinite natLeq_ordLeq_cinfinite that)

lemma countable_leq_natLeq: \<open>|X| \<le>o natLeq\<close> if \<open>countable X\<close>
  using subset_range_from_nat_into[OF that]
  by (meson card_of_nat ordIso_iff_ordLeq ordLeq_transitive surj_imp_ordLeq)


lemma infsum_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) infsum infsum\<close>
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c\<close> and g :: \<open>'b \<Rightarrow> 'c\<close> and A B
  assume \<open>rel_set R A B\<close>
  with \<open>bi_unique R\<close>
  obtain m where \<open>B = m ` A\<close> and \<open>inj_on m A\<close> and Rm: \<open>\<forall>x\<in>A. R x (m x)\<close>
    apply (rule bi_unique_rel_set_lemma)
    by auto
  then have bij_m: \<open>bij_betw m A B\<close>
    by (simp add: inj_on_imp_bij_betw)

  assume \<open>(R ===> (=)) f g\<close>
  then have \<open>f x = g y\<close> if \<open>R x y\<close> for x y
    thm rel_funD
    using that by (rule rel_funD)
  with Rm have fg: \<open>f x = g (m x)\<close> if \<open>x\<in>A\<close> for x
    using that by blast

  show \<open>infsum f A = infsum g B\<close>
    apply (subst infsum_reindex_bij_betw[OF bij_m, symmetric])
    apply (rule infsum_cong)
    using fg by simp
qed

lemma summable_on_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) Infinite_Sum.summable_on Infinite_Sum.summable_on\<close>
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c\<close> and g :: \<open>'b \<Rightarrow> 'c\<close> and A B
  assume \<open>rel_set R A B\<close>
  with \<open>bi_unique R\<close>
  obtain m where \<open>B = m ` A\<close> and \<open>inj_on m A\<close> and Rm: \<open>\<forall>x\<in>A. R x (m x)\<close>
    apply (rule bi_unique_rel_set_lemma)
    by auto
  then have bij_m: \<open>bij_betw m A B\<close>
    by (simp add: inj_on_imp_bij_betw)

  assume \<open>(R ===> (=)) f g\<close>
  then have \<open>f x = g y\<close> if \<open>R x y\<close> for x y
    thm rel_funD
    using that by (rule rel_funD)
  with Rm have fg: \<open>f x = g (m x)\<close> if \<open>x\<in>A\<close> for x
    using that by blast

  show \<open>(f summable_on A) = (g summable_on B)\<close>
    apply (subst summable_on_reindex_bij_betw[OF bij_m, symmetric])
    apply (rule summable_on_cong)
    using fg by simp
qed


(* TODO move *)
lemma abs_gbinomial: \<open>abs (a gchoose n) = (-1)^(n - nat (ceiling a)) * (a gchoose n)\<close>
proof -
  have \<open>(\<Prod>i=0..<n. abs (a - of_nat i)) = (- 1) ^ (n - nat (ceiling a)) * (\<Prod>i=0..<n. a - of_nat i)\<close>
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
(*     then show ?case
      apply (simp add: Suc) *)
    consider (geq) \<open>of_int n \<ge> a\<close> | (lt) \<open>of_int n < a\<close>
      by fastforce
    then show ?case
    proof cases
      case geq
      from geq have \<open>abs (a - of_int n) = - (a - of_int n)\<close>
        by simp
      moreover from geq have \<open>(Suc n - nat (ceiling a)) = (n - nat (ceiling a)) + 1\<close>
        by (metis Suc_diff_le Suc_eq_plus1 ceiling_le nat_le_iff)
      ultimately show ?thesis
        apply (simp add: Suc)
        by (metis (no_types, lifting) \<open>\<bar>a - of_int (int n)\<bar> = - (a - of_int (int n))\<close> mult.assoc mult_minus_right of_int_of_nat_eq)
    next
      case lt
      from lt have \<open>abs (a - of_int n) = (a - of_int n)\<close>
        by simp
      moreover from lt have \<open>(Suc n - nat (ceiling a)) = (n - nat (ceiling a))\<close>
        by (smt (verit, ccfv_threshold) Suc_leI cancel_comm_monoid_add_class.diff_cancel diff_commute diff_diff_cancel diff_le_self less_ceiling_iff linorder_not_le order_less_le zless_nat_eq_int_zless)
      ultimately show ?thesis
        by (simp add: Suc)
    qed
  qed
  then show ?thesis
    by (simp add: gbinomial_prod_rev abs_prod)
qed

lemma gbinomial_sum_lower_abs: 
  fixes a :: \<open>'a::{floor_ceiling}\<close>
  defines \<open>a' \<equiv> nat (ceiling a)\<close>
  assumes \<open>of_nat m \<ge> a-1\<close>
  shows "(\<Sum>k\<le>m. abs (a gchoose k)) = 
                 (-1)^a' * ((-1) ^ m * (a - 1 gchoose m)) 
               - (-1)^a' * of_bool (a'>0) * ((-1) ^ (a'-1) * (a-1 gchoose (a'-1)))
               + (\<Sum>k<a'. abs (a gchoose k))"
proof -
  from assms
  have \<open>a' \<le> Suc m\<close>
    using ceiling_mono by force

  have \<open>(\<Sum>k\<le>m. abs (a gchoose k)) = (\<Sum>k=a'..m. abs (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst asm_rl[of \<open>{..m} = {a'..m} \<union> {..<a'}\<close>])
    using \<open>a' \<le> Suc m\<close> apply auto[1]
    apply (subst sum.union_disjoint)
    by auto
  also have \<open>\<dots> = (\<Sum>k=a'..m. (-1)^(k-a') * (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>])
    apply (rule sum.cong[OF refl])
    apply (subst abs_gbinomial)
    using a'_def by blast
  also have \<open>\<dots> = (\<Sum>k=a'..m. (-1)^k * (-1)^a' * (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>])
    apply (rule sum.cong[OF refl])
    by (simp add: power_diff_conv_inverse)
  also have \<open>\<dots> = (-1)^a' * (\<Sum>k=a'..m. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    by (auto intro: sum.cong simp: sum_distrib_left)
  also have \<open>\<dots> = (-1)^a' * (\<Sum>k\<le>m. (a gchoose k) * (-1)^k) - (-1)^a' * (\<Sum>k<a'. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst asm_rl[of \<open>{..m} = {..<a'} \<union> {a'..m}\<close>])
    using \<open>a' \<le> Suc m\<close> apply auto[1]
    apply (subst sum.union_disjoint)
    by (auto simp: distrib_left)
  also have \<open>\<dots> = (-1)^a' * ((- 1) ^ m * (a - 1 gchoose m)) - (-1)^a' * (\<Sum>k<a'. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst gbinomial_sum_lower_neg)
    by simp
  also have \<open>\<dots> = (-1)^a' * ((-1) ^ m * (a - 1 gchoose m)) - (-1)^a' 
               * of_bool (a'>0) * ((-1) ^ (a'-1) * (a-1 gchoose (a'-1)))
               + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (cases \<open>a' = 0\<close>)
    apply simp
    apply (subst asm_rl[of \<open>{..<a'} = {..a'-1}\<close>])
    apply auto
    apply (subst gbinomial_sum_lower_neg)
    by simp
  finally show ?thesis
    by -
qed

lemma abs_gbinomial_leq1:
  fixes a :: \<open>'a :: {linordered_field}\<close>
  assumes \<open>-1 \<le> a\<close> and \<open>a \<le> 0\<close>
  shows \<open>abs (a gchoose b) \<le> 1\<close>
proof -
  have \<open>abs (a gchoose b) = abs ((\<Prod>i = 0..<b. a - of_nat i) / fact b)\<close>
    by (simp add: gbinomial_prod_rev)
  also have \<open>\<dots> = abs ((\<Prod>i=0..<b. a - of_nat i)) / fact b\<close>
    apply (subst abs_divide)
    by simp
  also have \<open>\<dots> = (\<Prod>i=0..<b. abs (a - of_nat i)) / fact b\<close>
    apply (subst abs_prod) by simp
  also have \<open>\<dots> \<le> (\<Prod>i=0..<b. of_nat (Suc i)) / fact b\<close>
    apply (rule divide_right_mono[rotated])
     apply simp
    apply (rule prod_mono)
    using assms apply (auto simp: abs_if)
    using order_trans by fastforce
  also have \<open>\<dots> = fact b / fact b\<close>
    apply (subst (2) fact_prod_Suc)
    by auto
  also have \<open>\<dots> = 1\<close>
    by simp
  finally show ?thesis
    by -
qed


(* TODO move *)
lemma has_sum_singleton[simp]: \<open>has_sum f {x} y \<longleftrightarrow> f x = y\<close> for y :: \<open>'a :: {comm_monoid_add, t2_space}\<close>
  using has_sum_finite[of \<open>{x}\<close>]
  apply auto
  by (metis infsumI)


(* TODO move *)
lemma tendsto_compose_at_within:
  assumes f: "(f \<longlongrightarrow> y) F" and g: "(g \<longlongrightarrow> z) (at y within S)" 
    and fg: "eventually (\<lambda>w. f w = y \<longrightarrow> g y = z) F"
    and fS: \<open>\<forall>\<^sub>F w in F. f w \<in> S\<close>
  shows "((g \<circ> f) \<longlongrightarrow> z) F"
proof (cases \<open>g y = z\<close>)
  case False
  then have 1: "(\<forall>\<^sub>F a in F. f a \<noteq> y)"
    using fg by force
  have 2: "(g \<longlongrightarrow> z) (filtermap f F) \<or> \<not> (\<forall>\<^sub>F a in F. f a \<noteq> y)"
    by (smt (verit, best) eventually_elim2 f fS filterlim_at filterlim_def g tendsto_mono)
  show ?thesis
    using "1" "2" tendsto_compose_filtermap by blast
next
  case True
  have *: ?thesis if \<open>(g \<longlongrightarrow> z) (filtermap f F)\<close>
    using that by (simp add: tendsto_compose_filtermap)
  from g
  have \<open>(g \<longlongrightarrow> g y) (inf (nhds y) (principal (S-{y})))\<close>
    by (simp add: True at_within_def)
  then have g': \<open>(g \<longlongrightarrow> g y) (inf (nhds y) (principal S))\<close>
    using True g tendsto_at_iff_tendsto_nhds_within by blast
  from f have \<open>filterlim f (nhds y) F\<close>
    by -
  then have f': \<open>filterlim f (inf (nhds y) (principal S)) F\<close>
    using fS
    by (simp add: filterlim_inf filterlim_principal)
  from f' g' show ?thesis
    by (simp add: * True filterlim_compose filterlim_filtermap)
qed


(* TODO move *)
(* strengthening of original *)
lemma has_sum_comm_additive_general: 
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes inS: \<open>\<And>F. finite F \<Longrightarrow> sum g F \<in> T\<close>
  assumes cont: \<open>(f \<longlongrightarrow> f x) (at x within T)\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close> and \<^term>\<open>T=UNIV\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close> 
proof -
  have \<open>(sum g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    using infsum has_sum_def by blast
  then have \<open>((f o sum g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_compose_at_within[where S=T])
    using assms by auto
  then have \<open>(sum (f o g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    using f_sum by fastforce
  then show \<open>has_sum (f o g) S (f x)\<close>
    using has_sum_def by blast 
qed

(* TODO move *)
(* strengthening of original *)
lemma summable_on_comm_additive_general:
  fixes g :: \<open>'a \<Rightarrow> 'b :: {comm_monoid_add,topological_space}\<close> and f :: \<open>'b \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes inS: \<open>\<And>F. finite F \<Longrightarrow> sum g F \<in> T\<close>
  assumes cont: \<open>\<And>x. has_sum g S x \<Longrightarrow> (f \<longlongrightarrow> f x) (at x within T)\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close> and \<^term>\<open>T=UNIV\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (meson assms summable_on_def has_sum_comm_additive_general has_sum_def infsum_tendsto)


end
