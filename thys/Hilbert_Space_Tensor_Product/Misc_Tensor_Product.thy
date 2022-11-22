section \<open>\<open>Misc_Tensor_Product\<close> -- Miscelleanous results missing from other theories\<close>

theory Misc_Tensor_Product
  imports "HOL-Analysis.Elementary_Topology" "HOL-Analysis.Abstract_Topology"
    "HOL-Analysis.Abstract_Limits" "HOL-Analysis.Function_Topology" "HOL-Cardinals.Cardinals"
    "HOL-Analysis.Infinite_Sum" "HOL-Analysis.Harmonic_Numbers" 
    Complex_Bounded_Operators.Extra_General
    Complex_Bounded_Operators.Extra_Vector_Spaces
    Misc_Tensor_Product_TTS
begin

(* TODO explain *)
lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis

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
  \<open>rel_topology R S T \<longleftrightarrow> (rel_fun (rel_set R) (=)) (openin S) (openin T)
 \<and> (\<forall>U. openin S U \<longrightarrow> Domainp (rel_set R) U) \<and> (\<forall>U. openin T U \<longrightarrow> Rangep (rel_set R) U)\<close>

lemma rel_topology_eq[relator_eq]: \<open>rel_topology (=) = (=)\<close>
  unfolding rel_topology_def
  apply (auto intro!: ext simp: rel_fun_eq rel_set_eq)
  by (metis openin_inject)

lemma Rangep_conversep[simp]: \<open>Rangep (R\<inverse>\<inverse>) = Domainp R\<close>
  by blast

lemma Domainp_conversep[simp]: \<open>Domainp (R\<inverse>\<inverse>) = Rangep R\<close>
  by blast

lemma rel_fun_conversep_eq[simp]: \<open>rel_fun (R\<inverse>\<inverse>) (=) = (rel_fun R (=))\<inverse>\<inverse>\<close>
  by (auto intro!: ext simp: rel_fun_def)

lemma rel_topology_conversep[simp]: \<open>rel_topology (R\<inverse>\<inverse>) = ((rel_topology R)\<inverse>\<inverse>)\<close>
  by (auto simp add: rel_topology_def[abs_def])

lemma openin_parametric[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R ===> (=)) openin openin\<close>
  by (auto simp add: rel_fun_def rel_topology_def)

lemma topspace_parametric [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R) topspace topspace\<close>
proof -
  have *: \<open>\<exists>y\<in>topspace T'. R x y\<close> if \<open>rel_topology R T T'\<close> \<open>x \<in> topspace T\<close> for x T T' and R :: \<open>'q \<Rightarrow> 'r \<Rightarrow> bool\<close>
  proof -
    from that obtain U where \<open>openin T U\<close> and \<open>x \<in> U\<close>
      unfolding topspace_def
      by auto
    from \<open>openin T U\<close>
    have \<open>Domainp (rel_set R) U\<close>
      using \<open>rel_topology R T T'\<close> rel_topology_def by blast
    then obtain V where [transfer_rule]: \<open>rel_set R U V\<close>
      by blast
    with \<open>x \<in> U\<close> obtain y where \<open>R x y\<close> and \<open>y \<in> V\<close>
      by (meson rel_set_def)
    from \<open>rel_set R U V\<close> \<open>rel_topology R T T'\<close> \<open>openin T U\<close>
    have \<open>openin T' V\<close>
      by (simp add: rel_topology_def rel_fun_def)
    with \<open>y \<in> V\<close> have \<open>y \<in> topspace T'\<close>
      using openin_subset by auto
    with \<open>R x y\<close> show \<open>\<exists>y\<in>topspace T'. R x y\<close>
      by auto
  qed

  show ?thesis
    using *[where ?R.1=R]
    using *[where ?R.1=\<open>R\<inverse>\<inverse>\<close>]
    by (auto intro!: rel_setI)
qed

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

definition \<open>infsum_in T f A = (let L = Collect (has_sum_in T f A) in if card L = 1 then the_elem L else 0)\<close>
(* The reason why we return 0 also in the case that there are several solutions is to make sure infsum_in is parametric.
(See lemma 'infsum_in_parametric' below. *)

lemma hausdorffI: 
  assumes \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
  shows \<open>hausdorff T\<close>
  using assms by (auto simp: hausdorff_def)

lemma hausdorff_euclidean[simp]: \<open>hausdorff (euclidean :: _::t2_space topology)\<close>
  apply (rule hausdorffI)
  by (metis (mono_tags, lifting) hausdorff open_openin)

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

lemma infsum_in_def':
  assumes \<open>hausdorff T\<close>
  shows \<open>infsum_in T f A = (if summable_on_in T f A then (THE s. has_sum_in T f A s) else 0)\<close>
proof (cases \<open>Collect (has_sum_in T f A) = {}\<close>)
  case True
  then show ?thesis 
    apply (auto simp: infsum_in_def summable_on_in_def Let_def)
    by (metis (no_types, lifting) One_nat_def True card.empty zero_neq_one)
next
  case False
  then have \<open>summable_on_in T f A\<close>
    by (metis (no_types, lifting) empty_Collect_eq summable_on_in_def)
  from False \<open>hausdorff T\<close>
  have \<open>card (Collect (has_sum_in T f A)) = 1\<close>
    by (metis (mono_tags, opaque_lifting) has_sum_in_unique is_singletonI' is_singleton_altdef mem_Collect_eq)
  then show ?thesis
    using \<open>summable_on_in T f A\<close>
    by (smt (verit, best) assms card_1_singletonE has_sum_in_unique infsum_in_def mem_Collect_eq singletonI the_elem_eq the_equality)
qed

lemma has_sum_in_infsum_in: 
  assumes \<open>hausdorff T\<close> and summable: \<open>summable_on_in T f A\<close>
  shows \<open>has_sum_in T f A (infsum_in T f A)\<close>
  apply (simp add: infsum_in_def'[OF \<open>hausdorff T\<close>] summable)
  apply (rule theI'[of \<open>has_sum_in T f A\<close>])
  using has_sum_in_unique[OF \<open>hausdorff T\<close>, of f A] summable
  by (meson summable_on_in_def)


lemma nhdsin_mono:
  assumes [simp]: \<open>\<And>x. openin T' x \<Longrightarrow> openin T x\<close>
  assumes [simp]: \<open>topspace T = topspace T'\<close>
  shows \<open>nhdsin T a \<le> nhdsin T' a\<close>
  unfolding nhdsin_def 
  by (auto intro!: INF_superset_mono)


lemma has_sum_in_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "has_sum_in T f A x \<longleftrightarrow> has_sum_in T g A x"
proof -
  have \<open>(\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> U) \<longleftrightarrow> (\<forall>\<^sub>F x in finite_subsets_at_top A. sum g x \<in> U)\<close> for U
    apply (rule eventually_subst)
    apply (subst eventually_finite_subsets_at_top)
    by (metis (mono_tags, lifting) assms empty_subsetI finite.emptyI subset_eq sum.cong)
  then show ?thesis
    by (simp add: has_sum_in_def limitin_def)
qed

lemma infsum_in_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::comm_monoid_add\<close>
  assumes \<open>\<And>x. has_sum_in T f A x \<longleftrightarrow> has_sum_in T g B x\<close>
  shows \<open>infsum_in T f A = infsum_in T g B\<close>
  by (simp add: infsum_in_def assms[abs_def] summable_on_in_def)

lemma infsum_in_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum_in T f A = infsum_in T g A"
  using assms infsum_in_eqI' has_sum_in_cong by blast

lemma limitin_cong: "limitin T f c F \<longleftrightarrow> limitin T g c F" if "eventually (\<lambda>x. f x = g x) F"
  by (smt (verit, best) eventually_elim2 limitin_transform_eventually that)


(* TODO: show has_sum_reindex as a corollary of this *)
lemma has_sum_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>has_sum_in T g (h ` A) x \<longleftrightarrow> has_sum_in T (g \<circ> h) A x\<close>
proof -
  have \<open>has_sum_in T g (h ` A) x \<longleftrightarrow> limitin T (sum g) x (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_sum_in_def)
  also have \<open>\<dots> \<longleftrightarrow> limitin T (\<lambda>F. sum g (h ` F)) x (finite_subsets_at_top A)\<close>
    apply (subst filtermap_image_finite_subsets_at_top[symmetric])
    by (simp_all add: assms eventually_filtermap limitin_def)
  also have \<open>\<dots> \<longleftrightarrow> limitin T (sum (g \<circ> h)) x (finite_subsets_at_top A)\<close>
    apply (rule limitin_cong)
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum.reindex)
    using assms subset_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum_in T (g \<circ> h) A x\<close>
    by (simp add: has_sum_in_def)
  finally show ?thesis .
qed

lemma summable_on_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>summable_on_in T g (h ` A) \<longleftrightarrow> summable_on_in T (g \<circ> h) A\<close>
  by (simp add: assms summable_on_in_def has_sum_in_reindex)

lemma infsum_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>infsum_in T g (h ` A) = infsum_in T (g \<circ> h) A\<close>
  by (metis Collect_cong assms has_sum_in_reindex infsum_in_def)

lemma has_sum_in_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "has_sum_in T (\<lambda>x. f (g x)) A s \<longleftrightarrow> has_sum_in T f B s"
proof -
  have \<open>has_sum_in T (\<lambda>x. f (g x)) A s \<longleftrightarrow> has_sum_in T f (g ` A) s\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on has_sum_in_cong has_sum_in_reindex o_def)
  also have \<open>\<dots> = has_sum_in T f B s\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed


lemma has_sum_euclidean_iff: \<open>has_sum_in euclidean f A s \<longleftrightarrow> has_sum f A s\<close>
  by (simp add: has_sum_def has_sum_in_def)

lemma summable_on_euclidean_eq: \<open>summable_on_in euclidean f A \<longleftrightarrow> f summable_on A\<close>
  by (auto simp add: infsum_def infsum_in_def has_sum_euclidean_iff[abs_def] has_sum_def
      t2_space_class.Lim_def summable_on_def summable_on_in_def)

lemma infsum_euclidean_eq: \<open>infsum_in euclidean f A = infsum f A\<close>
  by (auto simp add: infsum_def infsum_in_def' summable_on_euclidean_eq
      has_sum_euclidean_iff[abs_def] has_sum_def t2_space_class.Lim_def)

(* TODO: prove infsum_reindex_bij_betw from this *)
lemma infsum_in_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsum_in T (\<lambda>x. f (g x)) A = infsum_in T f B"
proof -
  have \<open>infsum_in T (\<lambda>x. f (g x)) A = infsum_in T f (g ` A)\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on infsum_in_cong infsum_in_reindex o_def)
  also have \<open>\<dots> = infsum_in T f B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed

lemma limitin_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> S ===> rel_filter R ===> (\<longleftrightarrow>)) limitin limitin\<close>
proof (intro rel_funI, rename_tac T T' f f' l l' F F')
  fix T T' f f' l l' F F'
  assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  assume [transfer_rule]: \<open>S l l'\<close>
  assume [transfer_rule]: \<open>rel_filter R F F'\<close>

  have topspace: \<open>l \<in> topspace T \<longleftrightarrow> l' \<in> topspace T'\<close>
    by transfer_prover

  have open1: \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    if \<open>openin T U\<close> and \<open>l \<in> U\<close> and lhs: \<open>(\<forall>V. openin T' V \<and> l' \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F'. f' x \<in> V))\<close>
    for U
  proof -
    from \<open>rel_topology S T T'\<close> \<open>openin T U\<close>
    obtain V where \<open>openin T' V\<close> and [transfer_rule]: \<open>rel_set S U V\<close>
      by (smt (verit, best) Domainp.cases rel_fun_def rel_topology_def)
    with \<open>S l l'\<close> have \<open>l' \<in> V\<close>
      by (metis (no_types, lifting) assms bi_uniqueDr rel_setD1 that(2))
    with lhs \<open>openin T' V\<close>
    have \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
      by auto
    then show \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
      apply transfer by simp
  qed

  have open2: \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
    if \<open>openin T' V\<close> and \<open>l' \<in> V\<close> and lhs: \<open>(\<forall>U. openin T U \<and> l \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> U))\<close>
    for V
  proof -
    from \<open>rel_topology S T T'\<close> \<open>openin T' V\<close>
    obtain U where \<open>openin T U\<close> and [transfer_rule]: \<open>rel_set S U V\<close>
      apply (auto simp: rel_topology_def)
      by (metis (mono_tags, lifting) RangepE rel_fun_def)
    with \<open>S l l'\<close> have \<open>l \<in> U\<close>
      by (metis (full_types) assms bi_unique_def rel_setD2 that(2))
    with lhs \<open>openin T U\<close>
    have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
      by auto
    then show \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
      apply transfer by simp
  qed

  from topspace open1 open2
  show \<open>limitin T f l F = limitin T' f' l' F'\<close>
    unfolding limitin_def by auto
qed

lemma finite_subsets_at_top_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_set R ===> rel_filter (rel_set R)) finite_subsets_at_top finite_subsets_at_top\<close>
proof (intro rel_funI)
  fix A B assume \<open>rel_set R A B\<close>
  from \<open>bi_unique R\<close> obtain f where Rf: \<open>R x (f x)\<close> if \<open>x \<in> A\<close> for x
    by (metis (no_types, opaque_lifting) \<open>rel_set R A B\<close> rel_setD1)
  have \<open>inj_on f A\<close>
    by (metis (no_types, lifting) Rf assms bi_unique_def inj_onI)
  have \<open>B = f ` A\<close>
    by (metis (mono_tags, lifting) Rf \<open>rel_set R A B\<close> assms bi_uniqueDr bi_unique_rel_set_lemma image_cong)

  have RfX: \<open>rel_set R X (f ` X)\<close> if \<open>X \<subseteq> A\<close> for X
    apply (rule rel_setI)
    apply (metis (no_types, lifting) Rf \<open>inj_on f A\<close> in_mono inj_on_image_mem_iff that)
    by (metis (no_types, lifting) Rf imageE subsetD that)

  have Piff: \<open>(\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))) \<longleftrightarrow>
              (\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y))\<close> for P
  proof (rule iffI)
    assume \<open>\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))\<close>
    then obtain X where \<open>finite X\<close> and \<open>X \<subseteq> A\<close> and XP: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P (f ` Y)\<close> for Y
      by auto
    define X' where \<open>X' = f ` X\<close>
    have \<open>finite X'\<close>
      by (metis X'_def \<open>finite X\<close> finite_imageI)
    have \<open>X' \<subseteq> B\<close>
      by (smt (verit, best) Rf X'_def \<open>X \<subseteq> A\<close> \<open>rel_set R A B\<close> assms bi_uniqueDr image_subset_iff rel_setD1 subsetD)
    have \<open>P Y'\<close> if \<open>finite Y'\<close> and \<open>X' \<subseteq> Y'\<close> and \<open>Y' \<subseteq> B\<close> for Y'
    proof -
      define Y where \<open>Y = (f -` Y') \<inter> A\<close>
      have \<open>finite Y\<close>
        by (metis Y_def \<open>inj_on f A\<close> finite_vimage_IntI that(1))
      moreover have \<open>X \<subseteq> Y\<close>
        by (metis (no_types, lifting) X'_def Y_def \<open>X \<subseteq> A\<close> image_subset_iff_subset_vimage le_inf_iff that(2))
      moreover have \<open>Y \<subseteq> A\<close>
        by (metis (no_types, lifting) Y_def inf_le2)
      ultimately have \<open>P (f ` Y)\<close>
        by (rule XP)
      then show \<open>P Y'\<close>
        by (metis (no_types, lifting) Int_greatest Y_def \<open>B = f ` A\<close> dual_order.refl image_subset_iff_subset_vimage inf_le1 subset_antisym subset_image_iff that(3))
    qed
    then show \<open>\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y)\<close>
      by (metis (no_types, opaque_lifting) \<open>X' \<subseteq> B\<close> \<open>finite X'\<close>)
  next
    assume \<open>\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y)\<close>
    then obtain X where \<open>finite X\<close> and \<open>X \<subseteq> B\<close> and XP: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> P Y\<close> for Y
      by auto
    define X' where \<open>X' = (f -` X) \<inter> A\<close>
    have \<open>finite X'\<close>
      by (simp add: X'_def \<open>finite X\<close> \<open>inj_on f A\<close> finite_vimage_IntI)
    have \<open>X' \<subseteq> A\<close>
      by (simp add: X'_def)
    have \<open>P (f ` Y')\<close> if \<open>finite Y'\<close> and \<open>X' \<subseteq> Y'\<close> and \<open>Y' \<subseteq> A\<close> for Y'
    proof -
      define Y where \<open>Y = f ` Y'\<close>
      have \<open>finite Y\<close>
        by (metis Y_def finite_imageI that(1))
      moreover have \<open>X \<subseteq> Y\<close>
        using X'_def Y_def \<open>B = f ` A\<close> \<open>X \<subseteq> B\<close> that(2) by blast
      moreover have \<open>Y \<subseteq> B\<close>
        by (metis Y_def \<open>B = f ` A\<close> image_mono that(3))
      ultimately have \<open>P Y\<close>
        by (rule XP)
      then show \<open>P (f ` Y')\<close>
        by (smt (z3) Y_def \<open>B = f ` A\<close> imageE imageI subset_antisym subset_iff that(3) vimage_eq)
    qed
    then show \<open>\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))\<close>
      by (metis \<open>X' \<subseteq> A\<close> \<open>finite X'\<close>)
  qed

  define Z where \<open>Z = filtermap (\<lambda>M. (M, f`M)) (finite_subsets_at_top A)\<close>
  have \<open>\<forall>\<^sub>F (x, y) in Z. rel_set R x y\<close>
    by (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)
  moreover have \<open>map_filter_on {(x, y). rel_set R x y} fst Z = finite_subsets_at_top A\<close>
    apply (rule filter_eq_iff[THEN iffD2])
    apply (subst eventually_map_filter_on)
     apply (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)[1]
    by (auto simp add: Z_def eventually_filtermap eventually_finite_subsets_at_top RfX)
  moreover have \<open>map_filter_on {(x, y). rel_set R x y} snd Z = finite_subsets_at_top B\<close>
    apply (rule filter_eq_iff[THEN iffD2])
    apply (subst eventually_map_filter_on)
     apply (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)[1]
    by (simp add: Z_def eventually_filtermap eventually_finite_subsets_at_top RfX Piff)
  ultimately show \<open>rel_filter (rel_set R) (finite_subsets_at_top A) (finite_subsets_at_top B)\<close>
    by (rule rel_filter.intros[where Z=Z])
qed

lemma sum_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> and S :: \<open>'c::comm_monoid_add \<Rightarrow> 'd::comm_monoid_add \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>((R ===> S) ===> rel_set R ===> S) sum sum\<close>
proof (intro rel_funI)
  fix A B f g assume \<open>rel_set R A B\<close> and \<open>(R ===> S) f g\<close>
  from \<open>bi_unique R\<close> obtain p where Rf: \<open>R x (p x)\<close> if \<open>x \<in> A\<close> for x
    by (metis (no_types, opaque_lifting) \<open>rel_set R A B\<close> rel_setD1)
  have \<open>inj_on p A\<close>
    by (metis (no_types, lifting) Rf \<open>bi_unique R\<close> bi_unique_def inj_onI)
  have \<open>B = p ` A\<close>
    by (metis (mono_tags, lifting) Rf \<open>rel_set R A B\<close> \<open>bi_unique R\<close> bi_uniqueDr bi_unique_rel_set_lemma image_cong)

  define A_copy where \<open>A_copy = A\<close>

  have \<open>S (f x + sum f F) (g (p x) + sum g (p ` F))\<close>
    if [transfer_rule]: \<open>S (sum f F) (sum g (p ` F))\<close> and [simp]: \<open>x \<in> A\<close> for x F
    by (metis (no_types, opaque_lifting) Rf \<open>(R ===> S) f g\<close> assms(2) rel_fun_def that(1) that(2))
  then have ind_step: \<open>S (sum f (insert x F)) (sum g (p ` insert x F))\<close> 
    if [simp]: \<open>S (sum f F) (sum g (p ` F))\<close> \<open>x \<in> A\<close> \<open>x \<notin> F\<close> \<open>finite F\<close> \<open>F \<subseteq> A\<close> for x F
    apply auto
    apply (subst sum.insert)
      apply (auto simp: that)
    by (metis (no_types, lifting) \<open>inj_on p A\<close> in_mono inj_onD that(2) that(3) that(5))

  have \<open>S (\<Sum>x\<in>A. f x) (\<Sum>x\<in>p ` A. g x)\<close>
    apply (subgoal_tac \<open>A \<subseteq> A_copy\<close>)
     apply (induction A rule:infinite_finite_induct)
    unfolding A_copy_def
       apply (metis (no_types, lifting) \<open>inj_on p A\<close> assms(3) finite_image_iff subset_inj_on sum.infinite)
    using \<open>S 0 0\<close> ind_step by (auto simp: sum.insert)
  also have \<open>\<dots> = (\<Sum>x\<in>B. g x)\<close>
    by (metis (full_types) \<open>B = p ` A\<close>)
  finally show \<open>S (\<Sum>x\<in>A. f x) (\<Sum>x\<in>B. g x)\<close>
    by -
qed


lemma has_sum_in_parametric[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> and S :: \<open>'c::comm_monoid_add \<Rightarrow> 'd::comm_monoid_add \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> S ===> (=)) has_sum_in has_sum_in\<close>
proof -
  note sum_parametric'[transfer_rule]
  show ?thesis
    unfolding has_sum_in_def
    by transfer_prover
qed

(* lemma has_sum_in_transfer[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((=) ===> (R ===> (=)) ===> (rel_set R) ===> (=)) has_sum_in has_sum_in\<close>
  by transfer_prover
 *)

lemma has_sum_in_topspace: \<open>has_sum_in T f A s \<Longrightarrow> s \<in> topspace T\<close>
  by (metis has_sum_in_def limitin_def)

lemma summable_on_in_parametric[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> (=)) summable_on_in summable_on_in\<close>
proof (intro rel_funI)
  fix T T' assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  fix f f' assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  fix A A' assume [transfer_rule]: \<open>rel_set R A A'\<close>

  define ExT ExT' where \<open>ExT P \<longleftrightarrow> (\<exists>x\<in>Collect (Domainp S). P x)\<close> and \<open>ExT' P' \<longleftrightarrow> (\<exists>x\<in>Collect (Rangep S). P' x)\<close> for P P'
  have [transfer_rule]: \<open>((S ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) ExT ExT'\<close>
    by (smt (z3) Domainp_iff ExT'_def ExT_def RangePI Rangep.cases mem_Collect_eq rel_fun_def)
  from \<open>rel_topology S T T'\<close> have top1: \<open>topspace T \<subseteq> Collect (Domainp S)\<close>
    unfolding rel_topology_def
    by (metis (no_types, lifting) Domainp_set mem_Collect_eq openin_topspace subsetI)
  from \<open>rel_topology S T T'\<close> have top2: \<open>topspace T' \<subseteq> Collect (Rangep S)\<close>
    unfolding rel_topology_def
    by (metis (no_types, lifting) RangePI Rangep.cases mem_Collect_eq openin_topspace rel_setD2 subsetI)

  have \<open>ExT (has_sum_in T f A) = ExT' (has_sum_in T' f' A')\<close>
    by transfer_prover
  with top1 top2 show \<open>summable_on_in T f A \<longleftrightarrow> summable_on_in T' f' A'\<close>
    by (metis ExT'_def ExT_def has_sum_in_topspace in_mono summable_on_in_def)
qed

lemma not_summable_infsum_in_0: \<open>\<not> summable_on_in T f A \<Longrightarrow> infsum_in T f A = 0\<close>
  by (smt (verit, del_insts) Collect_empty_eq card_eq_0_iff infsum_in_def summable_on_in_def zero_neq_one)

lemma infsum_in_parametric[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> S) infsum_in infsum_in\<close>
proof (intro rel_funI)
  fix T T' assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  fix f f' assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  fix A A' assume [transfer_rule]: \<open>rel_set R A A'\<close>
  have S_has_sum: \<open>(S ===> (=)) (has_sum_in T f A) (has_sum_in T' f' A')\<close>
    by transfer_prover

  have sum_iff: \<open>summable_on_in T f A \<longleftrightarrow> summable_on_in T' f' A'\<close>
    by transfer_prover

  define L L' where \<open>L = Collect (has_sum_in T f A)\<close> and \<open>L' = Collect (has_sum_in T' f' A')\<close>

  have LT: \<open>L \<subseteq> topspace T\<close>
    by (metis (mono_tags, lifting) Ball_Collect L_def has_sum_in_topspace subset_iff)
  have TS: \<open>topspace T \<subseteq> Collect (Domainp S)\<close>
    by (metis (no_types, lifting) Ball_Collect Domainp_set \<open>rel_topology S T T'\<close> openin_topspace rel_topology_def)
  have LT': \<open>L' \<subseteq> topspace T'\<close>
    by (metis Ball_Collect L'_def has_sum_in_topspace subset_eq)
  have T'S: \<open>topspace T' \<subseteq> Collect (Rangep S)\<close>
    by (metis (mono_tags, opaque_lifting) Ball_Collect RangePI \<open>rel_topology S T T'\<close> rel_fun_def rel_setD2 topspace_parametric)
  have Sss': \<open>S s s' \<Longrightarrow> has_sum_in T f A s \<longleftrightarrow> has_sum_in T' f' A' s'\<close> for s s'
    using S_has_sum
    by (metis (mono_tags, lifting) rel_funE)

  have \<open>rel_set S L L'\<close>
    by (smt (verit) Domainp.cases L'_def L_def Rangep.cases \<open>L \<subseteq> topspace T\<close> \<open>L' \<subseteq> topspace T'\<close> \<open>\<And>s' s. S s s' \<Longrightarrow> has_sum_in T f A s = has_sum_in T' f' A' s'\<close> \<open>topspace T \<subseteq> Collect (Domainp S)\<close> \<open>topspace T' \<subseteq> Collect (Rangep S)\<close> in_mono mem_Collect_eq rel_setI)

  have cardLL': \<open>card L = 1 \<longleftrightarrow> card L' = 1\<close>
    by (metis (no_types, lifting) \<open>rel_set S L L'\<close> assms(2) bi_unique_rel_set_lemma card_image)

  have \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close> if \<open>card L \<noteq> 1\<close>
    using that cardLL' by (simp add: infsum_in_def L'_def L_def Let_def that \<open>S 0 0\<close> flip: sum_iff)

  moreover have \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close> if [simp]: \<open>card L = 1\<close>
  proof -
    have [simp]: \<open>card L' = 1\<close>
      using that cardLL' by simp
    have \<open>S (the_elem L) (the_elem L')\<close>
      using \<open>rel_set S L L'\<close>
      by (metis (no_types, opaque_lifting) \<open>card L' = 1\<close> is_singleton_altdef is_singleton_the_elem rel_setD1 singleton_iff that)
    then show ?thesis
      by (simp add: infsum_in_def flip: L'_def L_def)
  qed

  ultimately show \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close>
    by auto
qed

(* lemma infsum_in_parametric_same_topo[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((=) ===> (R ===> (=)) ===> (rel_set R) ===> (=)) infsum_in infsum_in\<close>
  using infsum_in_parametric[where S=\<open>(=)\<close>]
  apply simp
  by - *)

lemma infsum_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) infsum infsum\<close>
  unfolding infsum_euclidean_eq[symmetric]
  by transfer_prover

lemma summable_on_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) Infinite_Sum.summable_on Infinite_Sum.summable_on\<close>
  unfolding summable_on_euclidean_eq[symmetric]
  by transfer_prover

lemma abs_gbinomial: \<open>abs (a gchoose n) = (-1)^(n - nat (ceiling a)) * (a gchoose n)\<close>
proof -
  have \<open>(\<Prod>i=0..<n. abs (a - of_nat i)) = (- 1) ^ (n - nat (ceiling a)) * (\<Prod>i=0..<n. a - of_nat i)\<close>
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
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
  assumes \<open>abs a \<le> 1\<close>
  shows \<open>abs (a gchoose b) \<le> 1\<close>
proof -
  have *: \<open>-1 \<le> a\<close> \<open>a \<le> 1\<close>
    using abs_le_D2 assms minus_le_iff abs_le_iff assms by auto
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
    using * apply (auto simp: abs_if)
    using order_trans by fastforce
  also have \<open>\<dots> = fact b / fact b\<close>
    apply (subst (2) fact_prod_Suc)
    by auto
  also have \<open>\<dots> = 1\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma gbinomial_summable_abs:
  fixes a :: real
  assumes \<open>a \<ge> 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>summable (\<lambda>n. abs (a gchoose n))\<close>
proof -
  define a' where \<open>a' = nat (ceiling a)\<close>
  have a': \<open>a' = 0 \<or> a' = 1\<close>
    by (metis One_nat_def a'_def assms(2) ceiling_le_one less_one nat_1 nat_mono order_le_less)
  have aux1: \<open>abs x \<le> x' \<Longrightarrow> abs y \<le> y' \<Longrightarrow> abs z \<le> z' \<Longrightarrow> x - y + z \<le> x' + y' + z'\<close> for x y z x' y' z' :: real
    by auto
  have \<open>(\<Sum>i\<le>n. \<bar>a gchoose i\<bar>) = (- 1) ^ a' * ((- 1) ^ n * (a - 1 gchoose n)) -
    (- 1) ^ a' * of_bool (0 < a') * ((- 1) ^ (a' - 1) * (a - 1 gchoose (a' - 1))) +
    (\<Sum>k<a'. \<bar>a gchoose k\<bar>)\<close> for n
    unfolding a'_def 
    apply (rule gbinomial_sum_lower_abs)
    using assms by fastforce
  also have \<open>\<dots>n \<le> 1 + 1 + 1\<close> for n
    apply (rule aux1)
    using a' by (auto simp add: abs_mult abs_gbinomial_leq1 assms)
  also have \<open>\<dots> = 3\<close>
    by simp
  finally show ?thesis
    by (meson abs_ge_zero bounded_imp_summable)
qed

(* lemma harmonic_series_diverges: \<open>\<not> summable (\<lambda>n. c / n)\<close> if \<open>c \<noteq> 0\<close>
  by - *)

lemma summable_tendsto_times_n:
  fixes f :: \<open>nat \<Rightarrow> real\<close>
  assumes pos: \<open>\<And>n. f n \<ge> 0\<close>
  assumes dec: \<open>decseq (\<lambda>n. (n+M) * f (n + M))\<close>
  assumes sum: \<open>summable f\<close>
  shows \<open>(\<lambda>n. n * f n) \<longlonglongrightarrow> 0\<close>
proof (rule ccontr)
  assume lim_not_0: \<open>\<not> (\<lambda>n. n * f n) \<longlonglongrightarrow> 0\<close>
  obtain B where \<open>(\<lambda>n. (n+M) * f (n+M)) \<longlonglongrightarrow> B\<close> and nfB': \<open>(n+M) * f (n+M) \<ge> B\<close> for n
    apply (rule decseq_convergent[where B=0, OF dec])
    using pos that by auto
  then have lim_B: \<open>(\<lambda>n. n * f n) \<longlonglongrightarrow> B\<close>
    by (rule_tac LIMSEQ_offset)
  have \<open>B \<ge> 0\<close>
    apply (subgoal_tac \<open>\<And>n. n * f n \<ge> 0\<close>)
    using Lim_bounded2 lim_B apply blast
    by (simp add: pos)
  moreover have \<open>B \<noteq> 0\<close>
    using lim_B lim_not_0 by blast
  ultimately have \<open>B > 0\<close>
    by linarith

  have \<open>f n \<ge> B / n\<close> if \<open>n \<ge> M\<close> for n
    using nfB'[of \<open>n-M\<close>] that 
    apply auto
    by (smt (verit, best) \<open>0 \<le> B\<close> \<open>B \<noteq> 0\<close> divide_right_mono mult_nonpos_nonneg nonzero_mult_div_cancel_left pos)

  with sum \<open>B > 0\<close> have \<open>summable (\<lambda>n. B / n)\<close>
    apply (rule_tac summable_comparison_test'[where N=M])
    by auto

  moreover have \<open>\<not> summable (\<lambda>n. B / n)\<close>
  proof (rule ccontr)
    define C where \<open>C = (\<Sum>n. 1 / real n)\<close>
    assume \<open>\<not> \<not> summable (\<lambda>n. B / real n)\<close>
    then have \<open>summable (\<lambda>n. inverse B * (B / real n))\<close>
      using summable_mult by blast
    then have \<open>summable (\<lambda>n. 1 / real n)\<close>
      using \<open>B \<noteq> 0\<close> by auto
    then have \<open>(\<Sum>n=1..m. 1 / real n) \<le> C\<close> for m
      unfolding C_def apply (rule sum_le_suminf)
      by auto
    then have \<open>harm m \<le> C\<close> for m
      by (simp add: harm_def inverse_eq_divide)
    then have \<open>harm (nat (ceiling (exp C))) \<le> C\<close>
      by -
    then have \<open>ln (real (nat (ceiling (exp C))) + 1) \<le> C\<close>
      by (smt (verit, best) ln_le_harm)
    then show False
      by (smt (z3) exp_ln ln_ge_iff of_nat_0_le_iff real_nat_ceiling_ge)
  qed

  ultimately show False
    by simp
qed
  


lemma gbinomial_tendsto_0:
  fixes a :: real
  assumes \<open>a > -1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close>
proof -
  have thesis1: \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close> if \<open>a \<ge> 0\<close> for a :: real
  proof -
    define m where \<open>m = nat (floor a)\<close>
    have m: \<open>a \<ge> real m\<close> \<open>a \<le> real m + 1\<close>
      by (simp_all add: m_def that)
    show ?thesis
    proof (insert m, induction m arbitrary: a)
      case 0
      then have *: \<open>a \<ge> 0\<close> \<open>a \<le> 1\<close>
        using assms by auto
      show ?case
        using gbinomial_summable_abs[OF *]
        using summable_LIMSEQ_zero tendsto_rabs_zero_iff by blast
    next
      case (Suc m)
      have 1: \<open>(\<lambda>n. (a-1 gchoose n)) \<longlonglongrightarrow> 0\<close>
        apply (rule Suc.IH)
        using Suc.prems by auto
      then have \<open>(\<lambda>n. (a-1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        using filterlim_sequentially_Suc by blast
      with 1 have \<open>(\<lambda>n. (a-1 gchoose n) + (a-1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        by (simp add: tendsto_add_zero)
      then have \<open>(\<lambda>n. (a gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        using gbinomial_Suc_Suc[of \<open>a-1\<close>] by simp
      then show ?case
        using filterlim_sequentially_Suc by blast
    qed
  qed

  have thesis2: \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close> if \<open>a > -1\<close> \<open>a \<le> 0\<close>
  proof -
    have decseq: \<open>decseq (\<lambda>n. abs (a gchoose n))\<close>
    proof (rule decseq_SucI)
      fix n
      have \<open>\<bar>a gchoose Suc n\<bar> = \<bar>a gchoose n\<bar> * (\<bar>a - real n\<bar> / (1 + n))\<close>
        unfolding gbinomial_prod_rev by (simp add: abs_mult) 
      also have \<open>\<dots> \<le> \<bar>a gchoose n\<bar>\<close>
        apply (rule mult_left_le)
        using assms that(2) by auto
      finally show \<open>\<bar>a gchoose Suc n\<bar> \<le> \<bar>a gchoose n\<bar>\<close>
        by -
    qed
    have abs_a1: \<open>abs (a+1) = a+1\<close>
      using assms by auto

    have \<open>0 \<le> \<bar>a + 1 gchoose n\<bar>\<close> for n
      by simp
    moreover have \<open>decseq (\<lambda>n. (n+1) * abs (a+1 gchoose (n+1)))\<close>
      using decseq apply (simp add: gbinomial_rec abs_mult)
      by (smt (verit, best) decseq_def mult.commute mult_left_mono)
    moreover have \<open>summable (\<lambda>n. abs (a+1 gchoose n))\<close>
      apply (rule gbinomial_summable_abs)
      using that by auto
    ultimately have \<open>(\<lambda>n. n * abs (a+1 gchoose n)) \<longlonglongrightarrow> 0\<close>
      by (rule summable_tendsto_times_n)
    then have \<open>(\<lambda>n. Suc n * abs (a+1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
      by (rule_tac LIMSEQ_ignore_initial_segment[where k=1 and a=0, simplified])
    then have \<open>(\<lambda>n. abs (Suc n * (a+1 gchoose Suc n))) \<longlonglongrightarrow> 0\<close>
      by (simp add: abs_mult)
    then have \<open>(\<lambda>n. (a+1) * abs (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      apply (subst (asm) gbinomial_absorption)
      by (simp add: abs_mult abs_a1)
    then have \<open>(\<lambda>n. abs (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      using that(1) by force
    then show \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      by (rule tendsto_rabs_zero_cancel)
  qed

  from thesis1 thesis2 assms show ?thesis
    using linorder_linear by blast
qed


(* lemma gbinomial_minus1[simp]: \<open>(-1 gchoose n) = (case n of 0 \<Rightarrow> 1 | _ \<Rightarrow> -1)\<close>
  apply (cases n)
   apply auto
  unfolding gbinomial_prod_rev
  apply auto
  by auto *)

lemma gbinomial_abs_sum:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. abs (a gchoose n)) sums 2\<close>
proof -
  define a' where \<open>a' = nat (ceiling a)\<close>
  have \<open>a' = 1\<close>
    using a'_def assms(1) assms(2) by linarith
  have lim: \<open>(\<lambda>n. (a - 1 gchoose n)) \<longlonglongrightarrow> 0\<close>
    by (simp add: assms(1) gbinomial_tendsto_0)
  have \<open>(\<Sum>k\<le>n. abs (a gchoose k)) = (- 1) ^ a' * ((- 1) ^ n * (a - 1 gchoose n)) -
    (- 1) ^ a' * of_bool (0 < a') * ((- 1) ^ (a'-1) * (a - 1 gchoose (a' - 1))) +
    (\<Sum>k<a'. \<bar>a gchoose k\<bar>)\<close> for n
    unfolding a'_def
    apply (rule gbinomial_sum_lower_abs)
    using assms(2) by linarith
  also have \<open>\<dots>n = 2 - (- 1) ^ n * (a - 1 gchoose n)\<close> for n
    using assms
    by (auto simp add: \<open>a' = 1\<close>)
  finally have \<open>(\<Sum>k\<le>n. abs (a gchoose k)) = 2 - (- 1) ^ n * (a - 1 gchoose n)\<close> for n
    by -
  moreover have \<open>(\<lambda>n. 2 - (- 1) ^ n * (a - 1 gchoose n)) \<longlonglongrightarrow> 2\<close>
  proof -
    from lim have \<open>(\<lambda>n. ((-1) ^ n * (a-1 gchoose n))) \<longlonglongrightarrow> 0\<close>
      apply (rule_tac tendsto_rabs_zero_cancel)
      by (simp add: abs_mult tendsto_rabs_zero_iff)
    then have \<open>(\<lambda>n. 2 - (- 1) ^ n * (a - 1 gchoose n)) \<longlonglongrightarrow> 2 - 0\<close>
      apply (rule tendsto_diff[rotated])
      by simp
    then show ?thesis
      by simp
  qed
  ultimately have \<open>(\<lambda>n. \<Sum>k\<le>n. abs (a gchoose k)) \<longlonglongrightarrow> 2\<close>
    by auto
  then show ?thesis
    using sums_def_le by blast
qed

lemma has_sumI_metric:
  fixes l :: \<open>'a :: {metric_space, comm_monoid_add}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) l < e)\<close>
  shows \<open>has_sum f A l\<close>
  unfolding has_sum_metric using assms by simp

lemma sums_has_sum:
  fixes s :: \<open>'a :: banach\<close>
  assumes sums: \<open>f sums s\<close>
  assumes abs_sum: \<open>summable (\<lambda>n. norm (f n))\<close>
  shows \<open>has_sum f UNIV s\<close>
proof (rule has_sumI_metric)
  fix e :: real assume \<open>0 < e\<close>
  define e' where \<open>e' = e/2\<close>
  then have \<open>e' > 0\<close>
    using \<open>0 < e\<close> half_gt_zero by blast
  from suminf_exist_split[where r=e', OF \<open>0<e'\<close> abs_sum]
  obtain N where \<open>norm (\<Sum>i. norm (f (i + N))) < e'\<close>
    by auto
  then have N: \<open>(\<Sum>i. norm (f (i + N))) < e'\<close>
    by auto
  then have N': \<open>norm (\<Sum>i. f (i + N)) < e'\<close>
    apply (rule dual_order.strict_trans2)
    by (auto intro!: summable_norm summable_iff_shift[THEN iffD2] abs_sum)

  define X where \<open>X = {..<N}\<close>
  then have \<open>finite X\<close>
    by auto
  moreover have \<open>dist (sum f Y) s < e\<close> if \<open>finite Y\<close> and \<open>X \<subseteq> Y\<close> for Y
  proof -
    have \<open>dist (sum f Y) s = norm (s - sum f {..<N} - sum f (Y-{..<N}))\<close>
      by (metis X_def diff_diff_eq2 dist_norm norm_minus_commute sum.subset_diff that(1) that(2))
    also have \<open>\<dots> \<le> norm (s - sum f {..<N}) + norm (sum f (Y-{..<N}))\<close>
      using norm_triangle_ineq4 by blast
    also have \<open>\<dots> = norm (\<Sum>i. f (i + N)) + norm (sum f (Y-{..<N}))\<close>
      apply (subst suminf_minus_initial_segment)
      using sums sums_summable apply blast
      using sums sums_unique by blast
    also have \<open>\<dots> < e' + norm (sum f (Y-{..<N}))\<close>
      using N' by simp
    also have \<open>\<dots> \<le> e' + norm (\<Sum>i\<in>Y-{..<N}. norm (f i))\<close>
      apply (rule add_left_mono)
      by (smt (verit, best) real_norm_def sum_norm_le)
    also have \<open>\<dots> \<le> e' + (\<Sum>i\<in>Y-{..<N}. norm (f i))\<close>
      apply (rule add_left_mono)
      by (simp add: sum_nonneg)
    also have \<open>\<dots> = e' + (\<Sum>i|i+N\<in>Y. norm (f (i + N)))\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. e' + x\<close>])
      apply (rule sum.reindex_cong[where l=\<open>\<lambda>i. i + N\<close>])
      apply auto
      by (smt (verit, best) add.commute image_iff le_iff_add linorder_not_le mem_Collect_eq)
    also have \<open>\<dots> \<le> e' + (\<Sum>i. norm (f (i + N)))\<close>
      by (auto intro!: add_left_mono sum_le_suminf summable_iff_shift[THEN iffD2] abs_sum finite_inverse_image \<open>finite Y\<close>)
    also have \<open>\<dots> \<le> e' + e'\<close>
      using N by simp
    also have \<open>\<dots> = e\<close>
      by (simp add: e'_def)
    finally show ?thesis
      by -
  qed
  ultimately show \<open>\<exists>X. finite X \<and> X \<subseteq> UNIV \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> UNIV \<longrightarrow> dist (sum f Y) s < e)\<close>
    by auto
qed

lemma sums_has_sum_pos:
  fixes s :: real
  assumes \<open>f sums s\<close>
  assumes \<open>\<And>n. f n \<ge> 0\<close>
  shows \<open>has_sum f UNIV s\<close>
  apply (rule sums_has_sum)
  apply (simp add: assms(1))
  using assms(1) assms(2) summable_def by auto

lemma gbinomial_abs_has_sum:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>has_sum (\<lambda>n. abs (a gchoose n)) UNIV 2\<close>
  apply (rule sums_has_sum_pos)
   apply (rule gbinomial_abs_sum)
  using assms by auto

lemma gbinomial_abs_has_sum_1:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>has_sum (\<lambda>n. abs (a gchoose n)) (UNIV-{0}) 1\<close>
proof -
  have \<open>has_sum (\<lambda>n. abs (a gchoose n)) (UNIV-{0}) (2-(\<Sum>n\<in>{0}. abs (a gchoose n)))\<close>
    apply (rule has_sum_Diff)
      apply (rule gbinomial_abs_has_sum)
    using assms apply auto[2]
     apply (rule has_sum_finite)
    by auto
  then show ?thesis
    by simp
qed

lemma summable_onI:
  assumes \<open>has_sum f A s\<close>
  shows \<open>f summable_on A\<close>
  using assms summable_on_def by blast

lemma gbinomial_abs_summable:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) abs_summable_on UNIV\<close>
  using assms by (auto intro!: summable_onI gbinomial_abs_has_sum)

lemma gbinomial_abs_summable_1:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) abs_summable_on UNIV-{0}\<close>
  using assms by (auto intro!: summable_onI gbinomial_abs_has_sum_1)

lemma has_sum_singleton[simp]: \<open>has_sum f {x} y \<longleftrightarrow> f x = y\<close> for y :: \<open>'a :: {comm_monoid_add, t2_space}\<close>
  using has_sum_finite[of \<open>{x}\<close>]
  apply auto
  by (metis infsumI)


lemma has_sum_sums: \<open>f sums s\<close> if \<open>has_sum f UNIV s\<close>
proof -
  have \<open>(\<lambda>n. sum f {..<n}) \<longlonglongrightarrow> s\<close>
  proof (simp add: tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>s \<in> S\<close>
    with \<open>has_sum f UNIV s\<close>
    have \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV. sum f F \<in> S\<close>
      using has_sum_def tendsto_def by blast
    then
    show \<open>\<forall>\<^sub>F x in sequentially. sum f {..<x} \<in> S\<close>
      using eventually_compose_filterlim filterlim_lessThan_at_top by blast
  qed
  then show ?thesis
    by (simp add: sums_def)
qed

lemma The_eqI1:
  assumes \<open>\<And>x y. F x \<Longrightarrow> F y \<Longrightarrow> x = y\<close>
  assumes \<open>\<exists>z. F z\<close>
  assumes \<open>\<And>x. F x \<Longrightarrow> P x = Q x\<close>
  shows \<open>P (The F) = Q (The F)\<close>
  by (metis assms(1) assms(2) assms(3) theI)

lemma summable_on_uminus[intro!]: 
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close> (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  shows \<open>(\<lambda>i. - f i) summable_on A\<close>
  apply (subst asm_rl[of \<open>(\<lambda>i. - f i) = (\<lambda>i. (-1) *\<^sub>R f i)\<close>])
   apply simp
  using assms by (rule summable_on_scaleR_right)

lemma gbinomial_1: \<open>(1 gchoose n) = of_bool (n\<le>1)\<close>
proof -
  consider (0) \<open>n=0\<close> | (1) \<open>n=1\<close> | (bigger) m where \<open>n=Suc (Suc m)\<close>
    by (metis One_nat_def not0_implies_Suc)
  then show ?thesis
  proof cases
    case 0
    then show ?thesis
      by simp
  next
    case 1
    then show ?thesis
      by simp
  next
    case bigger
    then show ?thesis
      using gbinomial_rec[where a=0 and k=\<open>Suc m\<close>]
      by simp
  qed
qed



lemma gbinomial_a_Suc_n:
  \<open>(a gchoose Suc n) = (a gchoose n) * (a-n) / Suc n\<close>
  by (simp add: gbinomial_prod_rev)

lemma has_sum_in_0[simp]: \<open>has_sum_in T (\<lambda>_. 0) A 0\<close> if [simp]: \<open>0 \<in> topspace T\<close>
  by (simp add: has_sum_in_def sum.neutral_const[abs_def])


lemma has_sum_diff:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes \<open>has_sum f A a\<close>
  assumes \<open>has_sum g A b\<close>
  shows \<open>has_sum (\<lambda>x. f x - g x) A (a - b)\<close>
  by (auto intro!: has_sum_add has_sum_uminus[THEN iffD2] assms simp add: simp flip: add_uminus_conv_diff)

lemma has_sum_of_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes \<open>has_sum f A a\<close>
  shows \<open>has_sum (\<lambda>x. of_real (f x)) A (of_real a :: 'b::{real_algebra_1,real_normed_vector})\<close>
  apply (rule has_sum_comm_additive[unfolded o_def, where f=of_real])
  by (auto intro!: additive.intro assms tendsto_of_real)

lemma summable_on_cdivide:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. f x / c) summable_on A"
  apply (subst division_ring_class.divide_inverse)
  using assms summable_on_cmult_left by blast

lemma norm_abs[simp]: \<open>norm (abs x) = norm x\<close> for x :: \<open>'a :: {idom_abs_sgn, real_normed_div_algebra}\<close>
proof -
  have \<open>norm x = norm (sgn x * abs x)\<close>
    by (simp add: sgn_mult_abs)
  also have \<open>\<dots> = norm \<bar>x\<bar>\<close>
    by (simp add: norm_mult norm_sgn)
  finally show ?thesis
    by simp
qed

(* Strengthening of  *) thm abs_summable_product (* with narrower typeclass *)
lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes x2_sum: "(\<lambda>i. (x i)\<^sup>2) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i)\<^sup>2) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on, simp, rule bdd_aboveI2, rename_tac F)
  fix F assume \<open>F \<in> {F. F \<subseteq> A \<and> finite F}\<close>
  then have "finite F" and "F \<subseteq> A"
    by auto

  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm ((x i)\<^sup>2) + norm ((y i)\<^sup>2))"
    by (simp add: power2_eq_square sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm ((x i)\<^sup>2)) + (\<Sum>i\<in>F. norm ((y i)\<^sup>2))"
    by (simp add: sum.distrib)
  also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((x i)\<^sup>2)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((y i)\<^sup>2))"
    using x2_sum y2_sum \<open>finite F\<close> \<open>F \<subseteq> A\<close> by (auto intro!: finite_sum_le_infsum add_mono)
  finally show \<open>(\<Sum>xa\<in>F. norm (x xa * y xa)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((x i)\<^sup>2)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((y i)\<^sup>2))\<close>
    by simp
qed

lemma Cauchy_Schwarz_ineq_infsum:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra}"
  assumes x2_sum: "(\<lambda>i. (x i)\<^sup>2) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i)\<^sup>2) abs_summable_on A"
  shows \<open>(\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
proof -
  (* have \<open>(norm (\<Sum>\<^sub>\<infinity>i\<in>A. x i * y i)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i))\<close>
    by (simp add: Misc_Tensor_Product.abs_summable_product assms(2) norm_infsum_bound x2_sum)
  also *) have \<open>(\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>i. x i * y i) abs_summable_on A\<close>
      using Misc_Tensor_Product.abs_summable_product x2_sum y2_sum by blast
    fix F assume \<open>finite F\<close> and \<open>F \<subseteq> A\<close>


    have sum1: \<open>(\<lambda>i. (norm (x i))\<^sup>2) summable_on A\<close>
      by (metis (mono_tags, lifting) norm_power summable_on_cong x2_sum)
    have sum2: \<open>(\<lambda>i. (norm (y i))\<^sup>2) summable_on A\<close>
      by (metis (no_types, lifting) norm_power summable_on_cong y2_sum)

    have \<open>(\<Sum>i\<in>F. norm (x i * y i))\<^sup>2 = (\<Sum>i\<in>F. norm (x i) * norm (y i))\<^sup>2\<close>
      by (simp add: norm_mult)
    also have \<open>\<dots> \<le> (\<Sum>i\<in>F. (norm (x i))\<^sup>2) * (\<Sum>i\<in>F. (norm (y i))\<^sup>2)\<close>
      using Cauchy_Schwarz_ineq_sum by fastforce
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * (\<Sum>i\<in>F. (norm (y i))\<^sup>2)\<close>
      using sum1 \<open>finite F\<close> \<open>F \<subseteq> A\<close> 
      by (auto intro!: mult_right_mono finite_sum_le_infsum sum_nonneg)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
      using sum2 \<open>finite F\<close> \<open>F \<subseteq> A\<close> 
      by (auto intro!: mult_left_mono finite_sum_le_infsum infsum_nonneg)
    also have \<open>\<dots> = (sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2))\<^sup>2\<close>
      by (smt (verit, best) calculation real_sqrt_mult real_sqrt_pow2 zero_le_power2)
  finally show \<open>(\<Sum>i\<in>F. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
    apply (rule power2_le_imp_le)
    by (auto intro!: mult_nonneg_nonneg infsum_nonneg)
  qed
  then show ?thesis
    by -
qed

lemma continuous_map_pullback_both:
  assumes cont: \<open>continuous_map T1 T2 g'\<close>
  assumes g'g: \<open>\<And>x. f1 x \<in> topspace T1 \<Longrightarrow> x \<in> A1 \<Longrightarrow> g' (f1 x) = f2 (g x)\<close>
  assumes top1: \<open>f1 -` topspace T1 \<inter> A1 \<subseteq> g -` A2\<close>
  shows \<open>continuous_map (pullback_topology A1 f1 T1) (pullback_topology A2 f2 T2) g\<close>
proof -
  from cont
  have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (g' \<circ> f1)\<close>
    by (rule continuous_map_pullback)
  then have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (f2 \<circ> g)\<close>
    apply (rule continuous_map_eq)
    by (simp add: g'g topspace_pullback_topology)
  then show ?thesis
    apply (rule continuous_map_pullback')
    by (simp add: top1 topspace_pullback_topology)
qed

lemma onorm_case_prod_plus_leq: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::real_normed_vector) \<le> sqrt 2\<close>
  apply (rule onorm_bound)
  using norm_plus_leq_norm_prod by auto

lemma bounded_linear_case_prod_plus[simp]: \<open>bounded_linear (case_prod plus)\<close>
  apply (rule bounded_linear_intro[where K=\<open>sqrt 2\<close>])
  by (auto simp add: scaleR_right_distrib norm_plus_leq_norm_prod mult.commute)

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

definition \<open>opensets_in T = Collect (openin T)\<close>
  \<comment> \<open>This behaves more nicely with the @{method transfer}-method (and friends) than \<^const>\<open>openin\<close>.
      So when rewriting a subgoal, using, e.g., \<^term>\<open>\<exists>U\<in>opensets T. xxx\<close> instead of \<^term>\<open>\<exists>U. openin T U \<longrightarrow> xxx\<close> can make @{method transfer} work better. \<close>

lemma opensets_in_parametric[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_set (rel_set R)) opensets_in opensets_in\<close>
proof (intro rel_funI rel_setI)
  fix S T
  assume rel_topo: \<open>rel_topology R S T\<close>
  fix U
  assume \<open>U \<in> opensets_in S\<close>
  then show \<open>\<exists>V \<in> opensets_in T. rel_set R U V\<close>
    by (smt (verit, del_insts) Domainp.cases mem_Collect_eq opensets_in_def rel_fun_def rel_topo rel_topology_def)
next
  fix S T assume rel_topo: \<open>rel_topology R S T\<close>
  fix U assume \<open>U \<in> opensets_in T\<close>
  then show \<open>\<exists>V \<in> opensets_in S. rel_set R V U\<close>
    by (smt (verit) RangepE mem_Collect_eq opensets_in_def rel_fun_def rel_topo rel_topology_def)
qed

lemma hausdorff_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> (\<longleftrightarrow>)) hausdorff hausdorff\<close>
proof -
  have hausdorff_def': \<open>hausdorff T \<longleftrightarrow> (\<forall>x\<in>topspace T. \<forall>y\<in>topspace T. x \<noteq> y \<longrightarrow> (\<exists>U \<in> opensets_in T. \<exists>V \<in> opensets_in T. x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>
    for T :: \<open>'z topology\<close>
    unfolding opensets_in_def hausdorff_def Bex_def by auto
  show ?thesis
    unfolding hausdorff_def'
    by transfer_prover
qed

lemma sum_cmod_pos: 
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>(\<Sum>x\<in>A. cmod (f x)) = cmod (\<Sum>x\<in>A. f x)\<close>
  by (metis (mono_tags, lifting) Re_sum assms cmod_Re sum.cong sum_nonneg)

lemma min_power_distrib_left: \<open>(min x y) ^ n = min (x ^ n) (y ^ n)\<close> if \<open>x \<ge> 0\<close> and \<open>y \<ge> 0\<close> for x y :: \<open>_ :: linordered_semidom\<close>
  by (metis linorder_le_cases min.absorb_iff2 min.order_iff power_mono that(1) that(2))

lemma abs_summable_times: 
  fixes f :: \<open>'a \<Rightarrow> 'c::{real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes sum_f: \<open>f abs_summable_on A\<close>
  assumes sum_g: \<open>g abs_summable_on B\<close>
  shows \<open>(\<lambda>(i,j). f i * g j) abs_summable_on A \<times> B\<close>
proof -
  have a1: \<open>(\<lambda>j. norm (f i) * norm (g j)) abs_summable_on B\<close> if \<open>i \<in> A\<close> for i
    using sum_g by (simp add: summable_on_cmult_right)
  then have a2: \<open>(\<lambda>j. f i * g j) abs_summable_on B\<close> if \<open>i \<in> A\<close> for i
    apply (rule abs_summable_on_comparison_test)
     apply (fact that)
    by (simp add: norm_mult_ineq)
  from sum_f
  have \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B. norm (f x) * norm (g y)) abs_summable_on A\<close>
    by (auto simp add: infsum_cmult_right' infsum_nonneg intro!: summable_on_cmult_left)
  then have b1: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B. norm (f x * g y)) abs_summable_on A\<close>
    apply (rule abs_summable_on_comparison_test)
    using a1 a2 by (simp_all add: norm_mult_ineq infsum_mono infsum_nonneg)
  from a2 b1 show ?thesis
    apply (rule_tac abs_summable_on_Sigma_iff[THEN iffD2])
    by auto
qed


lemma closure_of_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close> and T :: \<open>'a topology\<close> and U :: \<open>'b topology\<close>
  assumes hausdorff: \<open>hausdorff U\<close>
  assumes f_eq_g: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes x: \<open>x \<in> T closure_of S\<close>
  assumes f: \<open>continuous_map T U f\<close> and g: \<open>continuous_map T U g\<close>
  shows \<open>f x = g x\<close>
proof -
  have \<open>topspace T \<noteq> {}\<close>
    by (metis assms(3) equals0D in_closure_of)
  have \<open>topspace U \<noteq> {}\<close>
    using \<open>topspace T \<noteq> {}\<close> assms(5) continuous_map_image_subset_topspace by blast

  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (topspace T)"
    then interpret T: local_typedef \<open>topspace T\<close> \<open>TYPE('t)\<close>
      by unfold_locales
    assume "\<exists>(Rep :: 'u \<Rightarrow> 'b) Abs. type_definition Rep Abs (topspace U)"
    then interpret U: local_typedef \<open>topspace U\<close> \<open>TYPE('u)\<close>
      by unfold_locales

    note on_closure_eqI
    note this[unfolded ud_with]
    note this[unoverload_type 'b, unoverload_type 'a]
    note this[unfolded ud_with]
    note this[where 'a='t and 'b='u]
    note this[untransferred]
    note this[where f=f and g=g and S=\<open>S \<inter> topspace T\<close> and x=x and ?open="openin T" and opena=\<open>openin U\<close>]
    note this[simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have 2: \<open>f ` topspace T \<subseteq> topspace U\<close>
  by (meson assms(4) continuous_map_image_subset_topspace)
  have 3: \<open>g ` topspace T \<subseteq> topspace U\<close>
    by (simp add: continuous_map_image_subset_topspace g)
  have 4: \<open>x \<in> topspace T\<close>
    by (meson assms(3) in_closure_of)
  have 5: \<open>topological_space_ow (topspace T) (openin T)\<close>
    by simp
  have 6: \<open>t2_space_ow (topspace U) (openin U)\<close>
    by (simp add: hausdorff)
  from x have \<open>x \<in> T closure_of (S \<inter> topspace T)\<close>
    by (metis closure_of_restrict inf_commute)
  then have 7: \<open>x \<in> closure_ow (topspace T) (openin T) (S \<inter> topspace T)\<close>
    by (simp add: closure_ow_from_topology)
  have 8: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f\<close>
     by (meson "2" continuous_on_ow_from_topology f)
  have 9: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) g\<close>
    by (simp add: "3" continuous_on_ow_from_topology g)

  show ?thesis
    apply (rule * )
    using 2 3 4 5 6 f_eq_g 7 8 9 by auto
qed

end
