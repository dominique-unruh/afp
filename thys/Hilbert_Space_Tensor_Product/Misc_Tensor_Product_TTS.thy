theory Misc_Tensor_Product_TTS
  imports
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    Types_To_Sets_Extension.SML_Topological_Space
    Types_To_Sets_Extension.SML_Groups
    Types_To_Sets_Extension.VS_Vector_Spaces
begin

unbundle lattice_syntax

subsection \<open>Retrieving axioms\<close>

attribute_setup axiom = \<open>Scan.lift Parse.name_position >> (fn name_pos => Thm.rule_attribute [] 
    (fn context => fn _ =>
       let val thy = Context.theory_of context
           val (full_name, _) = Name_Space.check context (Theory.axiom_table thy) name_pos
       in Thm.axiom thy full_name end))\<close> 
  \<open>Retrieve an axiom by name. E.g., write @{thm [source] [[axiom HOL.refl]]}.\<close>

subsection \<open>Auxiliary lemmas\<close>

locale local_typedef = fixes S ::"'b set" and s::"'s itself"
  assumes Ex_type_definition_S: "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S"
begin
definition "Rep = fst (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"
definition "Abs = snd (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"
lemma type_definition_S: "type_definition Rep Abs S"
  unfolding Abs_def Rep_def split_beta'
  by (rule someI_ex) (use Ex_type_definition_S in auto)
lemma rep_in_S[simp]: "Rep x \<in> S"
  and rep_inverse[simp]: "Abs (Rep x) = x"
  and Abs_inverse[simp]: "y \<in> S \<Longrightarrow> Rep (Abs y) = y"
  using type_definition_S
  unfolding type_definition_def by auto
definition cr_S where "cr_S \<equiv> \<lambda>s b. s = Rep b"
lemmas Domainp_cr_S = type_definition_Domainp[OF type_definition_S cr_S_def, transfer_domain_rule]
lemmas right_total_cr_S = typedef_right_total[OF type_definition_S cr_S_def, transfer_rule]
  and bi_unique_cr_S = typedef_bi_unique[OF type_definition_S cr_S_def, transfer_rule]
  and left_unique_cr_S = typedef_left_unique[OF type_definition_S cr_S_def, transfer_rule]
  and right_unique_cr_S = typedef_right_unique[OF type_definition_S cr_S_def, transfer_rule]
lemma cr_S_Rep[intro, simp]: "cr_S (Rep a) a" by (simp add: cr_S_def)
lemma cr_S_Abs[intro, simp]: "a\<in>S \<Longrightarrow> cr_S a (Abs a)" by (simp add: cr_S_def)
lemma UNIV_transfer[transfer_rule]: \<open>rel_set cr_S S UNIV\<close>
  using Domainp_cr_S right_total_cr_S right_total_UNIV_transfer by fastforce
end

lemma complete_space_as_set[simp]: \<open>complete (space_as_set V)\<close> for V :: \<open>_::cbanach ccsubspace\<close>
  by (simp add: complete_eq_closed)

definition \<open>transfer_ball_range A P \<longleftrightarrow> (\<forall>f. range f \<subseteq> A \<longrightarrow> P f)\<close>

lemma Domainp_conversep: \<open>Domainp (conversep R) = Rangep R\<close>
  by (auto simp add: Domainp_iff[abs_def])

lemma conversep_rel_fun:
  includes lifting_syntax
  shows \<open>(T ===> U)\<inverse>\<inverse> = (T\<inverse>\<inverse>) ===> (U\<inverse>\<inverse>)\<close>
  by (auto simp: rel_fun_def)

lemma transfer_ball_range_parametric'[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>right_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof (intro rel_funI impI, rename_tac A B P Q)
  fix A B P Q
  assume [transfer_rule]: \<open>rel_set U A B\<close>
  assume TUPQ[transfer_rule]: \<open>((T ===> U) ===> (\<longrightarrow>)) P Q\<close>
  assume \<open>transfer_ball_range A P\<close>
  then have Pf: \<open>P f\<close> if \<open>range f \<subseteq> A\<close> for f
    unfolding transfer_ball_range_def using that by auto
  have \<open>Q g\<close> if \<open>range g \<subseteq> B\<close> for g
  proof -
    from that \<open>rel_set U A B\<close>
    have \<open>Rangep (T ===> U) g\<close>
      apply (auto simp add: conversep_rel_fun Domainp_pred_fun_eq simp flip: Domainp_conversep)
      apply (simp add: Domainp_conversep)
      by (metis Rangep.simps range_subsetD rel_setD2)
    then obtain f where TUfg[transfer_rule]: \<open>(T ===> U) f g\<close>
      by blast
    from that have \<open>range f \<subseteq> A\<close>
      by transfer
    then have \<open>P f\<close>
      by (simp add: Pf)
    then show \<open>Q g\<close>
      by (metis TUfg TUPQ rel_funD)
  qed
  then show \<open>transfer_ball_range B Q\<close>
  by (simp add: transfer_ball_range_def)
qed

lemma transfer_ball_range_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof -
  have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    using assms(1) assms(2) assms(3) bi_unique_alt_def transfer_ball_range_parametric' by blast
  then have 1: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by auto

  have \<open>(rel_set (U\<inverse>\<inverse>) ===> ((T\<inverse>\<inverse> ===> U\<inverse>\<inverse>) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule transfer_ball_range_parametric')
    using assms(1) bi_unique_alt_def bi_unique_conversep apply blast
    by auto
  then have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule_tac conversepD[where r=\<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>)\<close>])
    by (simp add: conversep_rel_fun del: conversep_iff)
  then have 2: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by (auto simp: rev_implies_def)

  from 1 2 show ?thesis
    apply (auto intro!: rel_funI simp: conversep_iff[abs_def])
     apply (smt (z3) rel_funE)
    by (smt (verit) rel_funE rev_implies_def)
qed

(* TODO: Duplicated with Misc_Tensor_Product *)
lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin 
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)

definition \<open>transfer_Times A B = A \<times> B\<close>

lemma transfer_Times_parametricity[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set T ===> rel_set U ===> rel_set (rel_prod T U)) transfer_Times transfer_Times\<close>
  by (auto intro!: rel_funI simp add: transfer_Times_def rel_set_def)

definition \<open>transfer_bounded_filter_Inf B M = Inf M \<sqinter> principal B\<close>

lemma Inf_transfer_bounded_filter_Inf: \<open>Inf M = transfer_bounded_filter_Inf UNIV M\<close>
  by (metis inf_top.right_neutral top_eq_principal_UNIV transfer_bounded_filter_Inf_def)

lemma Inf_bounded_transfer_bounded_filter_Inf:
  assumes \<open>\<And>F. F \<in> M \<Longrightarrow> F \<le> principal B\<close>
  assumes \<open>M \<noteq> {}\<close>
  shows \<open>Inf M = transfer_bounded_filter_Inf B M\<close>
  by (simp add: Inf_less_eq assms(1) assms(2) inf_absorb1 transfer_bounded_filter_Inf_def)

lemma filtermap_cong: 
  assumes \<open>\<forall>\<^sub>F x in F. f x = g x\<close>
  shows \<open>filtermap f F = filtermap g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_filtermap)
  by (smt (verit, del_insts) assms eventually_elim2)


lemma filtermap_INF_eq: 
  assumes inj_f: \<open>inj_on f X\<close>
  assumes B_nonempty: \<open>B \<noteq> {}\<close>
  assumes F_bounded: \<open>\<And>b. b\<in>B \<Longrightarrow> F b \<le> principal X\<close>
  shows \<open>filtermap f (\<Sqinter> (F ` B)) = (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
proof (rule antisym)
  show \<open>filtermap f (\<Sqinter> (F ` B)) \<le> (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
    by (rule filtermap_INF)
  define f1 where \<open>f1 = inv_into X f\<close>
  have f1f: \<open>x \<in> X \<Longrightarrow> f1 (f x) = x\<close> for x
    by (simp add: inj_f f1_def)
  have ff1: \<open>x \<in> f ` X \<Longrightarrow> x = f (f1 x)\<close> for x
    by (simp add: f1_def f_inv_into_f)

  have \<open>filtermap f (F b) \<le> principal (f ` X)\<close> if \<open>b \<in> B\<close> for b
    by (metis F_bounded filtermap_mono filtermap_principal that)
  then have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> (\<Sqinter>b\<in>B. principal (f ` X))\<close>
    by (simp add: INF_greatest INF_lower2) 
  also have \<open>\<dots> = principal (f ` X)\<close>
    by (simp add: B_nonempty)
  finally have \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x \<in> f ` X\<close>
    using B_nonempty le_principal by auto
  then have *: \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x = f (f1 x)\<close>
    apply (rule eventually_mono)
    by (simp add: ff1)

  have \<open>\<forall>\<^sub>F x in F b. x \<in> X\<close> if \<open>b \<in> B\<close> for b
    using F_bounded le_principal that by blast
  then have **: \<open>\<forall>\<^sub>F x in F b. f1 (f x) = x\<close> if \<open>b \<in> B\<close> for b
    apply (rule eventually_mono)
    using that by (simp_all add: f1f)

  have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) = filtermap f (filtermap f1 (\<Sqinter>b\<in>B. filtermap f (F b)))\<close>
    apply (simp add: filtermap_filtermap)
    using * by (rule filtermap_cong[where f=id, simplified])
  also have \<open>\<dots> \<le> filtermap f (\<Sqinter>b\<in>B. filtermap f1 (filtermap f (F b)))\<close>
    apply (rule filtermap_mono)
    by (rule filtermap_INF)
  also have \<open>\<dots> = filtermap f (\<Sqinter>b\<in>B. F b)\<close>
    apply (rule arg_cong[where f=\<open>filtermap _\<close>])
    apply (rule INF_cong, rule refl)
    unfolding filtermap_filtermap
    using ** by (rule filtermap_cong[where g=id, simplified])
  finally show \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> filtermap f (\<Sqinter> (F ` B))\<close>
    by -
qed

lemma filtermap_inf_eq:
  assumes \<open>inj_on f X\<close>
  assumes \<open>F1 \<le> principal X\<close>
  assumes \<open>F2 \<le> principal X\<close>
  shows \<open>filtermap f (F1 \<sqinter> F2) = filtermap f F1 \<sqinter> filtermap f F2\<close>
proof -
  have \<open>filtermap f (F1 \<sqinter> F2) = filtermap f (INF F\<in>{F1,F2}. F)\<close>
    by simp
  also have \<open>\<dots> = (INF F\<in>{F1,F2}. filtermap f F)\<close>
    apply (rule filtermap_INF_eq[where X=X])
    using assms by auto
  also have \<open>\<dots> = filtermap f F1 \<sqinter> filtermap f F2\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma map_filter_on_cong:
  assumes [simp]: \<open>\<forall>\<^sub>F x in F. x \<in> D\<close>
  assumes \<open>\<And>x. x \<in> D \<Longrightarrow> f x = g x\<close>
  shows \<open>map_filter_on D f F = map_filter_on D g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_map_filter_on)
  apply (rule eventually_subst)
  apply (rule always_eventually)
  using assms(2) by auto 


lemma Domainp_rel_filter:
  assumes \<open>Domainp r = S\<close>
  shows \<open>Domainp (rel_filter r) F \<longleftrightarrow> (F \<le> principal (Collect S))\<close>
proof (intro iffI, elim Domainp.cases, hypsubst)
  fix G 
  assume \<open>rel_filter r F G\<close>
  then obtain Z where rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    and ZF: "map_filter_on {(x, y). r x y} fst Z = F" 
    and "map_filter_on {(x, y). r x y} snd Z = G"
    using rel_filter.simps by blast
  show \<open>F \<le> principal (Collect S)\<close>
    using rZ apply (auto simp flip: ZF assms intro!: filter_leI 
        simp: eventually_principal eventually_map_filter_on)
    by (smt (verit, best) DomainPI case_prod_beta eventually_elim2)
next
  assume asm: \<open>F \<le> principal (Collect S)\<close>
  define Z where \<open>Z = inf (filtercomap fst F) (principal {(x, y). r x y})\<close>
  have rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: Z_def eventually_inf_principal)
  moreover 
  have \<open>(\<forall>\<^sub>F x in Z. P (fst x) \<and> (case x of (x, xa) \<Rightarrow> r x xa)) = eventually P F\<close> for P
    using asm apply (auto simp add: le_principal Z_def eventually_inf_principal eventually_filtercomap)
    by (smt (verit, del_insts) DomainpE assms eventually_elim2)
  then have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    by (simp add: filter_eq_iff eventually_map_filter_on rZ)
  ultimately show \<open>Domainp (rel_filter r) F\<close>
    by (auto simp: Domainp_iff intro!: exI rel_filter.intros)
qed

lemma transfer_bounded_filter_Inf_parametric[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>(rel_set r ===> rel_set (rel_filter r) ===> rel_filter r)
     transfer_bounded_filter_Inf transfer_bounded_filter_Inf\<close>
proof (intro rel_funI, unfold transfer_bounded_filter_Inf_def)
  fix BF BG assume BFBG[transfer_rule]: \<open>rel_set r BF BG\<close>
  fix Fs Gs assume FsGs[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  define D R where \<open>D = Collect (Domainp r)\<close> and \<open>R = Collect (Rangep r)\<close>
  
  have \<open>rel_set r D R\<close>
    by (smt (verit) D_def DomainPI DomainpE R_def RangePI Rangep.simps ctr_simps_mem_Collect_eq rel_setI)
  with \<open>bi_unique r\<close>
  obtain f where \<open>R = f ` D\<close> and [simp]: \<open>inj_on f D\<close> and rf0: \<open>x\<in>D \<Longrightarrow> r x (f x)\<close> for x
    using bi_unique_rel_set_lemma
    by metis
  have rf: \<open>r x y \<longleftrightarrow> x \<in> D \<and> f x = y\<close> for x y
    apply (auto simp: rf0)
    using D_def apply auto[1]
    using D_def assms bi_uniqueDr rf0 by fastforce

  from BFBG
  have \<open>BF \<subseteq> D\<close>
    by (metis D_def Domainp.simps Domainp_set ctr_simps_mem_Collect_eq subsetI)

  have G: \<open>G = filtermap f F\<close> if \<open>rel_filter r F G\<close> for F G
    using that proof cases
    case (1 Z)
    then have Z[simp]: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
      by -
    then have \<open>filtermap f F = filtermap f (map_filter_on {(x, y). r x y} fst Z)\<close>
      using 1 by simp
    also have \<open>\<dots> = map_filter_on {(x, y). r x y} (f \<circ> fst) Z\<close>
      unfolding map_filter_on_UNIV[symmetric]
      apply (subst map_filter_on_comp)
      using Z by simp_all
    also have \<open>\<dots> = G\<close>
      apply (simp add: o_def rf)
      apply (subst map_filter_on_cong[where g=snd])
      using Z apply (rule eventually_mono)
      using 1 by (auto simp: rf)
    finally show ?thesis
      by simp
  qed

  have rf_filter: \<open>rel_filter r F G \<longleftrightarrow> F \<le> principal D \<and> filtermap f F = G\<close> for F G
    apply (intro iffI conjI)
      apply (metis D_def DomainPI Domainp_rel_filter)
    using G apply simp
    by (metis D_def Domainp_iff Domainp_rel_filter G)

  have FD: \<open>F \<le> principal D\<close> if \<open>F \<in> Fs\<close> for F
    by (meson FsGs rel_setD1 rf_filter that)

  from BFBG
  have [simp]: \<open>BG = f ` BF\<close>
    by (auto simp: rel_set_def rf)

  from FsGs
  have [simp]: \<open>Gs = filtermap f ` Fs\<close>
    using G apply (auto simp: rel_set_def rf)
    by fastforce

  show \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (\<Sqinter> Gs \<sqinter> principal BG)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by transfer
    have \<open>rel_filter r (principal BF) (principal BG)\<close>
      by transfer_prover
    with True \<open>Gs = {}\<close> show ?thesis
      by simp
  next
    case False
    note False[simp]
    then have [simp]: \<open>Gs \<noteq> {}\<close>
      by transfer
    have \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (filtermap f (\<Sqinter> Fs \<sqinter> principal BF))\<close>
      apply (rule rf_filter[THEN iffD2])
      by (simp add: \<open>BF \<subseteq> D\<close> le_infI2)
    then show ?thesis
      using FD \<open>BF \<subseteq> D\<close>
      by (simp add: Inf_less_eq 
          flip: filtermap_inf_eq[where X=D] filtermap_INF_eq[where X=D] flip: filtermap_principal)
  qed
qed

lemma csubspace_nonempty: \<open>csubspace X \<Longrightarrow> X \<noteq> {}\<close>
  using complex_vector.subspace_0 by auto


definition \<open>transfer_vimage_into f U s = (f -` U) \<inter> s\<close>

lemma transfer_vimage_into_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>((A ===> B) ===> rel_set B ===> rel_set A ===> rel_set A) transfer_vimage_into transfer_vimage_into\<close>
  unfolding transfer_vimage_into_def
  apply (auto intro!: rel_funI simp: rel_set_def)
  by (metis Int_iff apply_rsp' assms bi_unique_def vimage_eq)+

(* Simplify with these theorems to (try to) change all \<open>\<forall>x. ...\<close> into \<open>\<forall>x\<in>S. ...\<close>
  to enable automated creation of parametricity rules without `bi_total` assumptions. *)
lemma make_parametricity_proof_friendly:
  shows \<open>(\<forall>x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q x))\<close>
    and \<open>(\<forall>x. x \<in> S \<longrightarrow> Q x) \<longleftrightarrow> (\<forall>x\<in>S. Q x)\<close>
    and \<open>(\<forall>x\<subseteq>S. R x) \<longleftrightarrow> (\<forall>x\<in>Pow S. R x)\<close>
    and \<open>{x\<in>S. Q x} = Set.filter Q S\<close>
    and \<open>{x. x \<subseteq> S \<and> R x} = Set.filter R (Pow S)\<close>
    and \<open>\<And>P. (\<forall>f. range f \<subseteq> A \<longrightarrow> P f) = transfer_ball_range A P\<close>
    and \<open>\<And>A B. A \<times> B = transfer_Times A B\<close>
    and \<open>\<And>B P. (\<exists>A\<subseteq>B. P A) \<longleftrightarrow> (\<exists>A\<in>Pow B. P A)\<close>
    and \<open>\<And>f U s. (f -` U) \<inter> s = transfer_vimage_into f U s\<close>
    and \<open>\<And>M B. \<Sqinter>M \<sqinter> principal B = transfer_bounded_filter_Inf B M\<close>
  by (auto simp: transfer_ball_range_def transfer_Times_def transfer_vimage_into_def
      transfer_bounded_filter_Inf_def)

subsection \<open>ETTS compatibility\<close>

lemma [simp]: \<open>VS_Groups.semigroup_add_ow = SML_Semigroups.semigroup_add_ow\<close>
  by (auto intro!: ext simp: SML_Semigroups.semigroup_add_ow_def VS_Groups.semigroup_add_ow_def
      plus_ow_def semigroup_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.ab_semigroup_add_ow = SML_Semigroups.ab_semigroup_add_ow\<close>
  by (auto intro!: ext simp: SML_Semigroups.ab_semigroup_add_ow_def VS_Groups.ab_semigroup_add_ow_def
      VS_Groups.ab_semigroup_add_ow_axioms_def SML_Semigroups.ab_semigroup_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.comm_monoid_add_ow = SML_Monoids.comm_monoid_add_ow\<close>
  by (auto intro!: ext simp: SML_Monoids.comm_monoid_add_ow_def VS_Groups.comm_monoid_add_ow_def
      VS_Groups.comm_monoid_add_ow_axioms_def SML_Semigroups.ab_semigroup_add_ow_axioms_def
      zero_ow_def neutral_ow_def SML_Monoids.comm_monoid_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.ab_group_add_ow = SML_Groups.ab_group_add_ow\<close>
  apply (auto intro!: ext simp: SML_Groups.ab_group_add_ow_def VS_Groups.ab_group_add_ow_def
      VS_Groups.ab_group_add_ow_axioms_def minus_ow_def uminus_ow_def SML_Groups.ab_group_add_ow_axioms_def)
  by (metis SML_Monoids.comm_monoid_add_ow.axioms(1) SML_Semigroups.ab_semigroup_add_ow.axioms(1) plus_ow.plus_closed semigroup_add_ow.axioms(1))

ctr parametricity in VS_Groups.ab_group_add_ow_def[simplified VS_Groups.ab_group_add_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in vector_space_ow_def[simplified vector_space_ow_axioms_def make_parametricity_proof_friendly]
ctr parametricity in minus_ow_def[unfolded make_parametricity_proof_friendly]

subsection \<open>\<^class>\<open>topological_space\<close>\<close>

ctr parametricity in topological_space_ow_def[unfolded make_parametricity_proof_friendly]

lemma class_topological_space_ud[ud_with]: \<open>class.topological_space = topological_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.topological_space_def topological_space_ow_def)

lemma topological_space_ow_from_topology[simp]: \<open>topological_space_ow (topspace T) (openin T)\<close>
  by (auto intro!: topological_space_ow.intro)

subsection \<open>\<^class>\<open>t2_space\<close>\<close>

definition hausdorff where \<open>hausdorff T \<longleftrightarrow> (\<forall>x \<in> topspace T. \<forall>y \<in> topspace T. x \<noteq> y \<longrightarrow> (\<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>

locale t2_space_ow = topological_space_ow +
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. x \<noteq> y \<longrightarrow> (\<exists>S\<subseteq>U. \<exists>T\<subseteq>U. \<tau> S \<and> \<tau> T \<and> x \<in> S \<and> y \<in> T \<and> S \<inter> T = {})\<close>

ctr parametricity in t2_space_ow_def[unfolded t2_space_ow_axioms_def make_parametricity_proof_friendly]

lemma class_t2_space_ud[ud_with]: \<open>class.t2_space = t2_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.t2_space_def class.t2_space_axioms_def t2_space_ow_def
      t2_space_ow_axioms_def ud_with)

lemma t2_space_ow_from_topology[simp, iff]: \<open>t2_space_ow (topspace T) (openin T)\<close> if \<open>hausdorff T\<close>
  using that
  apply (auto intro!: t2_space_ow.intro simp: t2_space_ow_axioms_def hausdorff_def)
  by (metis openin_subset)

subsubsection \<open>\<^const>\<open>continuous_on\<close>\<close>

definition continuous_on_ow where \<open>continuous_on_ow A B opnA opnB s f 
  \<longleftrightarrow> (\<forall>U\<subseteq>B. opnB U \<longrightarrow> (\<exists>V\<subseteq>A. opnA V \<and> (V \<inter> s) = (f -` U) \<inter> s))\<close>
  for f :: \<open>'a \<Rightarrow> 'b\<close>

lemma continuous_on_ud[ud_with]: \<open>continuous_on s f \<longleftrightarrow> continuous_on_ow UNIV UNIV open open s f\<close>
  for f :: \<open>'a::topological_space \<Rightarrow> 'b::topological_space\<close>
  unfolding continuous_on_ow_def continuous_on_open_invariant by auto

lemma continuous_on_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>(rel_set A ===> rel_set B ===> (rel_set A ===> (\<longleftrightarrow>)) ===> (rel_set B ===> (\<longleftrightarrow>)) ===> rel_set A ===> (A ===> B) ===> (\<longleftrightarrow>)) continuous_on_ow continuous_on_ow\<close>
  unfolding continuous_on_ow_def make_parametricity_proof_friendly
  by transfer_prover


subsection \<open>\<^class>\<open>scaleR\<close>\<close>

locale scaleR_ow = 
  fixes U and scaleR :: \<open>real \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes scaleR_closed: \<open>\<forall>a \<in> U. scaleR r a \<in> U\<close>

lemma scaleR_ow_typeclass[simp]: \<open>scaleR_ow UNIV scaleR\<close> for scaleR
  by (simp add: scaleR_ow_def)

ctr parametricity in scaleR_ow_def

subsection \<open>\<^class>\<open>scaleC\<close>\<close>

locale scaleC_ow = scaleR_ow +
  fixes scaleC
  assumes scaleC_closed: \<open>\<forall>a\<in>U. scaleC c a \<in> U\<close>
  assumes \<open>\<forall>a\<in>U. scaleR r a = scaleC (complex_of_real r) a\<close>

(* `ctr parametricity scaleC_ow_def` doesn't find this rule *)
ctr relativization
synthesis ctr_blank
assumes [transfer_rule]: \<open>bi_unique A\<close>
trp (?'a A)
in scaleC_ow_def[unfolded scaleC_ow_axioms_def]

lemma class_scaleC_ud[ud_with]: \<open>class.scaleC = scaleC_ow UNIV\<close>
  by (auto intro!: ext simp: class.scaleC_def scaleC_ow_def scaleR_ow_def scaleC_ow_axioms_def)

(* XXXX *)

subsection \<open>\<^class>\<open>complex_vector\<close>\<close>

locale complex_vector_ow = vector_space_ow U plus zero minus uminus scaleC + scaleC_ow U scaleR scaleC
  for U scaleR scaleC plus zero minus uminus

ctr parametricity in complex_vector_ow_def

lemma class_complex_vector_ud[ud_with]: \<open>class.complex_vector = complex_vector_ow UNIV\<close>
  by (auto intro!: ext simp: class.complex_vector_def vector_space_ow_def vector_space_ow_axioms_def
      class.complex_vector_axioms_def class.scaleC_def complex_vector_ow_def
      SML_Groups.ab_group_add_ow class_scaleC_ud)

lemma module_on_typeclass[simp]: \<open>module_on V (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  by (auto simp add: module_on_def scaleC_add_right scaleC_add_left
      complex_vector.subspace_add complex_vector.subspace_0 complex_vector.subspace_scale)

lemma vector_space_on_typeclass[simp]: \<open>vector_space_on V (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  by (simp add: vector_space_on_def)

lemma vector_space_ow_typeclass[simp]: 
  \<open>vector_space_ow V (+) 0 (-) uminus (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  for V :: \<open>_::complex_vector set\<close>
  by (simp add: implicit_vector_space_ow)

lemma complex_vector_ow_typeclass[simp]:
  \<open>complex_vector_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus\<close> if [simp]: \<open>csubspace V\<close>
  by (auto intro!: scaleC_ow_def simp add: complex_vector_ow_def scaleC_ow_def 
      scaleC_ow_axioms_def scaleR_ow_def scaleR_scaleC complex_vector.subspace_scale)


subsection \<open>\<^class>\<open>open_uniformity\<close>\<close>

locale open_uniformity_ow = "open" "open" + uniformity uniformity
  for A "open" uniformity +
  assumes open_uniformity:
    "\<And>U. U \<subseteq> A \<Longrightarrow> open U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

ctr parametricity in open_uniformity_ow_def[simplified make_parametricity_proof_friendly]

lemma class_open_uniformity_ud[ud_with]: \<open>class.open_uniformity = open_uniformity_ow UNIV\<close>
  by (auto intro!: ext simp: class.open_uniformity_def open_uniformity_ow_def)

lemma open_uniformity_on_typeclass[simp]: 
  fixes V :: \<open>_::open_uniformity set\<close>
  assumes \<open>closed V\<close>
  shows \<open>open_uniformity_ow V (openin (top_of_set V)) (uniformity_on V)\<close>
proof (rule open_uniformity_ow.intro, intro allI impI iffI ballI)
  fix U assume \<open>U \<subseteq> V\<close>
  assume \<open>openin (top_of_set V) U\<close>
  then obtain T where \<open>U = T \<inter> V\<close> and \<open>open T\<close>
    by (metis Int_ac(3) openin_open)
  with open_uniformity 
  have *: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> T\<close> if \<open>x \<in> T\<close> for x
    using that by blast
  have \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_inf_principal[THEN iffD2])
    using *[of x] apply (rule eventually_rev_mp)
    using \<open>U = T \<inter> V\<close> that by (auto intro!: always_eventually)
  then show \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    using that by blast
next
  fix U assume \<open>U \<subseteq> V\<close>
  assume asm: \<open>\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close>
  from asm[rule_format]
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' \<in> V \<and> y \<in> V \<and> x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    unfolding eventually_inf_principal
    apply (rule eventually_rev_mp)
    using that by (auto intro!: always_eventually)
  then have xU: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_rev_mp)
    using that \<open>U \<subseteq> V\<close> by (auto intro!: always_eventually)
  have \<open>open (-V)\<close>
    using assms by auto
  with open_uniformity
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> -V\<close> if \<open>x \<in> -V\<close> for x
    using that by blast
  then have xV: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> -V\<close> for x
    apply (rule eventually_rev_mp)
     apply (rule that)
    apply (rule always_eventually)
    by auto
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U \<union> -V\<close> for x
    using xV[of x] xU[of x] that
    by auto
  then have \<open>open (U \<union> -V)\<close>
    using open_uniformity by blast
  then show \<open>openin (top_of_set V) U\<close>
    using \<open>U \<subseteq> V\<close>
    by (auto intro!: exI simp: openin_open)
qed

subsection \<open>\<^class>\<open>uniformity_dist\<close>\<close>

locale uniformity_dist_ow = dist dist + uniformity uniformity for U dist uniformity +
  assumes uniformity_dist: "uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>U\<times>U. dist x y < e})"

lemma class_uniformity_dist_ud[ud_with]: \<open>class.uniformity_dist = uniformity_dist_ow UNIV\<close>
  by (auto intro!: ext simp: class.uniformity_dist_def uniformity_dist_ow_def)

lemma uniformity_dist_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> (=)) ===> rel_filter (rel_prod A A) ===> (=))
     uniformity_dist_ow uniformity_dist_ow\<close>
proof -
  have *: "uniformity_dist_ow U dist uniformity \<longleftrightarrow> 
          uniformity = transfer_bounded_filter_Inf (transfer_Times U U)
              ((\<lambda>e. principal (Set.filter (\<lambda>(x,y). dist x y < e) (transfer_Times U U))) ` {0<..})"
  for  U dist uniformity
    unfolding uniformity_dist_ow_def make_parametricity_proof_friendly case_prod_unfold
      prod.collapse
    apply (subst Inf_bounded_transfer_bounded_filter_Inf[where B=\<open>U\<times>U\<close>])
    by (auto simp: transfer_Times_def)
  show ?thesis
    unfolding *[abs_def]
    by transfer_prover
qed

lemma uniformity_dist_on_typeclass[simp]: \<open>uniformity_dist_ow V dist (uniformity_on V)\<close> for V :: \<open>_::uniformity_dist set\<close>
  apply (auto simp add: uniformity_dist_ow_def uniformity_dist simp flip: INF_inf_const2)
  apply (subst asm_rl[of \<open>\<And>x. Restr {(xa, y). dist xa y < x} V = {(xa, y). xa \<in> V \<and> y \<in> V \<and> dist xa y < x}\<close>, rule_format])
  by auto

subsection \<open>\<^class>\<open>sgn\<close>\<close>

locale sgn_ow =
  fixes U and sgn :: \<open>'a \<Rightarrow> 'a\<close>
  assumes sgn_closed: \<open>\<forall>a\<in>U. sgn a \<in> U\<close>

ctr parametricity in sgn_ow_def

subsection \<open>\<^class>\<open>sgn_div_norm\<close>\<close>

locale sgn_div_norm_ow = scaleR_ow U scaleR + norm norm + sgn_ow U sgn for U sgn norm scaleR +
  assumes "\<forall>x\<in>U. sgn x = scaleR (inverse (norm x)) x"

lemma class_sgn_div_norm_ud[ud_with]: \<open>class.sgn_div_norm = sgn_div_norm_ow UNIV\<close>
  by (auto intro!: ext simp: class.sgn_div_norm_def sgn_div_norm_ow_def sgn_div_norm_ow_axioms_def ud_with sgn_ow_def)

ctr parametricity in sgn_div_norm_ow_def[unfolded sgn_div_norm_ow_axioms_def]

lemma sgn_div_norm_on_typeclass[simp]: 
  fixes V :: \<open>_::sgn_div_norm set\<close>
  assumes \<open>\<And>v r. v\<in>V \<Longrightarrow> scaleR r v \<in> V\<close>
  shows \<open>sgn_div_norm_ow V sgn norm (*\<^sub>R)\<close> 
  using assms 
  by (auto simp add: sgn_ow_def sgn_div_norm_ow_axioms_def scaleR_ow_def sgn_div_norm_ow_def sgn_div_norm)

subsection \<open>\<^class>\<open>dist_norm\<close>\<close>

locale dist_norm_ow = dist dist + norm norm + minus_ow U minus for U minus dist norm +
  assumes dist_norm: "\<forall>x\<in>U. \<forall>y\<in>U. dist x y = norm (minus x y)"

lemma dist_norm_ud[ud_with]: \<open>class.dist_norm = dist_norm_ow UNIV\<close>
  by (auto intro!: ext simp: class.dist_norm_def dist_norm_ow_def dist_norm_ow_axioms_def
      minus_ow_def ud_with)

ctr parametricity in dist_norm_ow_def[unfolded dist_norm_ow_axioms_def]

lemma dist_norm_ow_typeclass[simp]: 
  fixes A :: \<open>_::dist_norm set\<close>
  assumes \<open>\<And>a b. \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a - b \<in> A\<close>
  shows \<open>dist_norm_ow A (-) dist norm\<close> 
  by (auto simp add: assms dist_norm_ow_def minus_ow_def dist_norm_ow_axioms_def dist_norm)

subsection \<open>\<^class>\<open>complex_inner\<close>\<close>

locale complex_inner_ow = complex_vector_ow U scaleR scaleC plus zero minus uminus
  + dist_norm_ow U minus dist norm + sgn_div_norm_ow U sgn norm scaleR
  + uniformity_dist_ow U dist uniformity
  + open_uniformity_ow U "open" uniformity
  for U scaleR scaleC plus zero minus uminus dist norm sgn uniformity "open" +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes "\<forall>x\<in>U. \<forall>y\<in>U. cinner x y = cnj (cinner y x)"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. cinner (plus x y) z = cinner x z + cinner y z"
    and "\<forall>x\<in>U. \<forall>y\<in>U. cinner (scaleC r x) y = cnj r * cinner x y"
    and "\<forall>x\<in>U. 0 \<le> cinner x x"
    and "\<forall>x\<in>U. cinner x x = 0 \<longleftrightarrow> x = zero"
    and "\<forall>x\<in>U. norm x = sqrt (cmod (cinner x x))"

lemma class_complex_inner_ud[ud_with]: \<open>class.complex_inner = complex_inner_ow UNIV\<close>
  apply (intro ext)
  by (simp add: class.complex_inner_def class.complex_inner_axioms_def complex_inner_ow_def complex_inner_ow_axioms_def ud_with)

(* Does not manage *)
(* ctr parametricity in complex_inner_ow_def[unfolded complex_inner_ow_axioms_def] *)

lemma complex_inner_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T 
          ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
          ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
          ===> (T ===> T ===> (=)) ===> (=)) complex_inner_ow complex_inner_ow\<close>
  unfolding complex_inner_ow_def complex_inner_ow_axioms_def
  by transfer_prover

lemma complex_inner_ow_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes [simp]: \<open>closed V\<close> \<open>csubspace V\<close>
  shows \<open>complex_inner_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  apply (auto intro!: complex_vector_ow_typeclass dist_norm_ow_typeclass sgn_div_norm_on_typeclass
      simp: complex_inner_ow_def cinner_simps complex_vector.subspace_diff complex_inner_ow_axioms_def
      scaleR_scaleC complex_vector.subspace_scale 
      simp flip: norm_eq_sqrt_cinner)
  by -

subsection \<open>\<^const>\<open>is_ortho_set\<close>\<close>

definition is_ortho_set_ow where \<open>is_ortho_set_ow zero cinner S \<longleftrightarrow> 
  ((\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> cinner x y = 0) \<and> zero \<notin> S)\<close>
  for zero cinner

ctr parametricity in is_ortho_set_ow_def

lemma is_ortho_set_ud[ud_with]: \<open>is_ortho_set = is_ortho_set_ow 0 cinner\<close>
  by (auto simp: is_ortho_set_ow_def is_ortho_set_def)

subsection \<open>\<^class>\<open>metric_space\<close>\<close>

locale metric_space_ow = uniformity_dist_ow U dist uniformity + open_uniformity_ow U "open" uniformity
  for U dist uniformity "open" +
  assumes "\<forall>x \<in> U. \<forall>y \<in> U. dist x y = 0 \<longleftrightarrow> x = y"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. dist x y \<le> dist x z + dist y z"

ctr parametricity in metric_space_ow_def[unfolded metric_space_ow_axioms_def]

lemma class_metric_space_ud[ud_with]: \<open>class.metric_space = metric_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.metric_space_def class.metric_space_axioms_def metric_space_ow_def metric_space_ow_axioms_def ud_with)

lemma metric_space_ow_typeclass[simp]:
  fixes V :: \<open>_::metric_space set\<close>
  assumes \<open>closed V\<close>
  shows \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
  by (auto simp: assms metric_space_ow_def metric_space_ow_axioms_def class.metric_space_axioms_def dist_triangle2)

subsection \<open>\<^const>\<open>nhds\<close>\<close>

definition nhds_ow where \<open>nhds_ow U open a = (INF S\<in>{S. S \<subseteq> U \<and> open S \<and> a \<in> S}. principal S) \<sqinter> principal U\<close>
  for U "open"

ctr parametricity in nhds_ow_def[folded transfer_bounded_filter_Inf_def, unfolded make_parametricity_proof_friendly]

lemma topological_space_nhds_ud[ud_with]: \<open>topological_space.nhds = nhds_ow UNIV\<close>
  by (auto intro!: ext simp add: nhds_ow_def [[axiom topological_space.nhds_def_raw]])

lemma nhds_ud[ud_with]: \<open>nhds = nhds_ow UNIV open\<close>
  by (auto intro!: ext simp add: nhds_ow_def nhds_def)

lemma nhds_ow_topology[simp]: \<open>nhds_ow (topspace T) (openin T) x = nhdsin T x\<close> if \<open>x \<in> topspace T\<close>
  using that apply (auto intro!: ext simp add: nhds_ow_def nhdsin_def[abs_def])
   apply (subst INF_inf_const2[symmetric])
  using openin_subset by (auto intro!: INF_cong)

subsection \<open>\<^const>\<open>filterlim\<close>\<close>

(* TODO: duplicated with Misc_Tensor_Product *)
lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover

subsection \<open>\<^const>\<open>convergent\<close>\<close>

definition convergent_ow where
  \<open>convergent_ow U open X \<longleftrightarrow> (\<exists>L\<in>U. filterlim X (nhds_ow U open L) sequentially)\<close>
for U "open"

(* ctr parametricity in convergent_ow_def *)

lemma convergent_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> ((=) ===> T) ===> (\<longleftrightarrow>))
           convergent_ow convergent_ow\<close>
  unfolding convergent_ow_def
  by transfer_prover

lemma convergent_ud[ud_with]: \<open>convergent = convergent_ow UNIV open\<close>
  by (auto simp: convergent_ow_def[abs_def] convergent_def[abs_def] ud_with)

lemma topological_space_convergent_ud[ud_with]: \<open>topological_space.convergent = convergent_ow UNIV\<close>
  by (auto intro!: ext simp: [[axiom topological_space.convergent_def_raw]]
      convergent_ow_def ud_with)

lemma convergent_ow_topology[simp]:
  \<open>convergent_ow (topspace T) (openin T) f \<longleftrightarrow> (\<exists>l. limitin T f l sequentially)\<close>
  by (auto simp: convergent_ow_def simp flip: filterlim_nhdsin_iff_limitin)

lemma convergent_ow_typeclass[simp]:
  \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. limitin (top_of_set V) f l sequentially)\<close>
  by (simp flip: convergent_ow_topology)

subsection \<open>\<^const>\<open>uniform_space.cauchy_filter\<close>\<close>

(* ctr parametricity in [[axiom uniform_space.cauchy_filter_def_raw, where ?'a='a]] *)

lemma cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> rel_filter T ===> (=)) 
    uniform_space.cauchy_filter
    uniform_space.cauchy_filter"
  unfolding [[axiom uniform_space.cauchy_filter_def_raw]]
  by transfer_prover

subsection \<open>\<^const>\<open>uniform_space.Cauchy\<close>\<close>

(* ctr parametricity in [[axiom uniform_space.Cauchy_uniform_raw, where ?'a='a]] *)

lemma uniform_space_Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> ((=) ===> T) ===> (=)) 
    uniform_space.Cauchy
    uniform_space.Cauchy"
  unfolding [[axiom uniform_space.Cauchy_uniform_raw]]
  using filtermap_parametric[transfer_rule] apply fail?
  by transfer_prover

subsection \<open>\<^class>\<open>complete_space\<close>\<close>

locale complete_space_ow = metric_space_ow U dist uniformity "open"
  for U dist uniformity "open" +
  assumes \<open>range X \<subseteq> U \<longrightarrow> uniform_space.Cauchy uniformity X \<longrightarrow> convergent_ow U open X\<close>

lemma class_complete_space_ud[ud_with]: \<open>class.complete_space = complete_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.complete_space_def class.complete_space_axioms_def complete_space_ow_def complete_space_ow_axioms_def ud_with)

(* Not good enough *)
(* ctr parametricity in complete_space_ow_def[unfolded make_parametricity_proof_friendly transfer_ball_range_def[symmetric]] *)

lemma complete_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    complete_space_ow complete_space_ow"
  unfolding complete_space_ow_def complete_space_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma complete_space_ow_typeclass[simp]:
  fixes V :: \<open>_::uniform_space set\<close>
  assumes \<open>complete V\<close>
  shows \<open>complete_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
proof (rule complete_space_ow.intro)
  show \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
    apply (rule metric_space_ow_typeclass)
    by (simp add: assms complete_imp_closed)
  have \<open>\<exists>l. limitin (top_of_set V) X l sequentially\<close>
    if XV: \<open>\<And>n. X n \<in> V\<close> and cauchy: \<open>uniform_space.Cauchy (uniformity_on V) X\<close> for X
  proof -
    from cauchy
    have \<open>uniform_space.cauchy_filter (uniformity_on V) (filtermap X sequentially)\<close>
      by (simp add: [[axiom uniform_space.Cauchy_uniform_raw]])
    then have \<open>cauchy_filter (filtermap X sequentially)\<close>
      by (auto simp: cauchy_filter_def [[axiom uniform_space.cauchy_filter_def_raw]])
    then have \<open>Cauchy X\<close>
      by (simp add: Cauchy_uniform)
    with \<open>complete V\<close> XV obtain l where l: \<open>X \<longlonglongrightarrow> l\<close> \<open>l \<in> V\<close>
      apply atomize_elim
      by (meson completeE)
    with XV l show ?thesis
      by (auto intro!: exI[of _ l] simp: convergent_def limitin_subtopology)
  qed
  then show \<open>complete_space_ow_axioms V (uniformity_on V) (openin (top_of_set V))\<close>
    apply (auto simp: complete_space_ow_axioms_def complete_imp_closed assms)
    by blast
qed

subsection \<open>\<^class>\<open>chilbert_space\<close>\<close>

locale chilbert_space_ow = complex_inner_ow + complete_space_ow

ctr parametricity in chilbert_space_ow_def

lemma chilbert_space_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>complete V\<close> \<open>csubspace V\<close>
  shows \<open>chilbert_space_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn
     (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  by (auto intro!: chilbert_space_ow.intro complex_inner_ow_typeclass
      simp: assms complete_imp_closed)

lemma class_chilbert_space_ud[ud_with]:
  \<open>class.chilbert_space = chilbert_space_ow UNIV\<close>
  by (auto intro!: ext simp add: class.chilbert_space_def chilbert_space_ow_def ud_with)

subsection \<open>\<^const>\<open>hull\<close>\<close>

definition \<open>hull_ow A S s = ((\<lambda>x. S x \<and> x \<subseteq> A) hull s) \<inter> A\<close>

lemma hull_ow_nondegenerate: \<open>hull_ow A S s = ((\<lambda>x. S x \<and> x \<subseteq> A) hull s)\<close> if \<open>x \<subseteq> A\<close> and \<open>s \<subseteq> x\<close> and \<open>S x\<close>
proof -
  have \<open>((\<lambda>x. S x \<and> x \<subseteq> A) hull s) \<subseteq> x\<close>
    apply (rule hull_minimal)
    using that by auto
  also note \<open>x \<subseteq> A\<close>
  finally show ?thesis
    unfolding hull_ow_def by auto
qed

definition \<open>transfer_bounded_Inf B M = Inf M \<sqinter> B\<close>

lemma transfer_bounded_Inf_parametric[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> rel_set (rel_set T) ===> rel_set T) transfer_bounded_Inf transfer_bounded_Inf\<close>
  apply (auto intro!: rel_funI simp: transfer_bounded_Inf_def rel_set_def Bex_def)
  apply (metis (full_types) assms bi_uniqueDr)
  by (metis (full_types) assms bi_uniqueDl)

lemma hull_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (rel_set T ===> (=)) ===> rel_set T ===> rel_set T) 
    hull_ow hull_ow"
proof -
  have *: \<open>hull_ow A S s = transfer_bounded_Inf A (Set.filter (\<lambda>x. S x \<and> s \<subseteq> x) (Pow A))\<close> for A S s
    by (auto simp add: hull_ow_def hull_def transfer_bounded_Inf_def)
  show ?thesis
    unfolding *
    by transfer_prover      
qed

lemma hull_ow_ud[ud_with]: \<open>(hull) = hull_ow UNIV\<close>
  unfolding hull_def hull_ow_def by auto

subsection \<open>\<^const>\<open>csubspace\<close>\<close>

definition
  \<open>subspace_ow plus zero scale S = (zero \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. plus x y \<in> S) \<and> (\<forall>c. \<forall>x\<in>S. scale c x \<in> S))\<close>
  for plus zero scale S

lemma subspace_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>((T ===> T ===> T) ===> T ===> ((=) ===> T ===> T) ===> rel_set T ===> (=))
           subspace_ow subspace_ow\<close>
  unfolding subspace_ow_def
  by transfer_prover

lemma module_subspace_ud[ud_with]: \<open>module.subspace = subspace_ow plus 0\<close>
  by (auto intro!: ext simp: [[axiom module.subspace_def_raw]] subspace_ow_def)

lemma csubspace_ud[ud_with]: \<open>csubspace = subspace_ow (+) 0 (*\<^sub>C)\<close>
  by (simp add: csubspace_raw_def module_subspace_ud)

subsection \<open>\<^const>\<open>cspan\<close>\<close>

definition 
  \<open>span_ow U plus zero scale b = hull_ow U (subspace_ow plus zero scale) b\<close>
  for U plus zero scale b

lemma span_ow_on_typeclass: 
  assumes \<open>csubspace U\<close>
  assumes \<open>B \<subseteq> U\<close>
  shows \<open>span_ow U plus 0 scaleC B = cspan B\<close>
proof -
  have \<open>span_ow U plus 0 scaleC B = (\<lambda>x. csubspace x \<and> x \<subseteq> U) hull B\<close>
    using assms 
    by (auto simp add: span_ow_def hull_ow_nondegenerate[where x=U] csubspace_raw_def 
        simp flip: csubspace_ud)
  also have \<open>(\<lambda>x. csubspace x \<and> x \<subseteq> U) hull B = cspan B\<close>
    apply (rule hull_unique)
    using assms(2) complex_vector.span_superset apply force
    by (simp_all add: assms complex_vector.span_minimal)
  finally show ?thesis
    by -
qed

lemma (in module) span_ud[ud_with]: \<open>span = span_ow UNIV plus 0 scale\<close>
  by (auto intro!: ext simp: span_def span_ow_def
      module_subspace_ud hull_ow_ud)

lemmas cspan_ud[ud_with] = complex_vector.span_ud

lemma span_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (T ===> T ===> T) ===> T ===> ((=) ===> T ===> T) ===> rel_set T ===> rel_set T)
           span_ow span_ow\<close>
  unfolding span_ow_def
  by transfer_prover

subsubsection \<open>\<^const>\<open>islimpt\<close>\<close>

lemma islimpt_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> T ===> rel_set T ===> (\<longleftrightarrow>)) islimpt_ow islimpt_ow\<close>
  unfolding islimpt_ow_def
  by transfer_prover

definition \<open>islimptin T x S \<longleftrightarrow> x \<in> topspace T \<and> (\<forall>V. x \<in> V \<longrightarrow> openin T V \<longrightarrow> (\<exists>y\<in>S. y \<in> V \<and> y \<noteq> x))\<close>

lemma islimpt_ow_from_topology: \<open>islimpt_ow (topspace T) (openin T) x S \<longleftrightarrow> islimptin T x S \<or> x \<notin> topspace T\<close>
  apply (cases \<open>x \<in> topspace T\<close>)
   apply (simp_all add: islimpt_ow_def islimptin_def Pow_def)
  by blast+

subsubsection \<open>\<^const>\<open>closure\<close>\<close>

lemma closure_ow_with_typeclass[simp]: 
  \<open>closure_ow X (openin (top_of_set X)) S = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
proof -
  have \<open>closure_ow X (openin (top_of_set X)) S = (top_of_set X) closure_of S \<union> S\<close>
    apply (simp add: closure_ow_def islimpt_ow_def closure_of_def)
    apply safe
     apply (meson PowI openin_imp_subset)
    by auto
  also have \<open>\<dots> = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
    by (simp add: closure_of_subtopology)
  finally show ?thesis
    by -
qed

lemma closure_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> rel_set T ===> rel_set T) closure_ow closure_ow\<close>
  unfolding closure_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma closure_ow_from_topology: \<open>closure_ow (topspace T) (openin T) S = T closure_of S\<close> if \<open>S \<subseteq> topspace T\<close>
  using that apply (auto simp: closure_ow_def islimpt_ow_from_topology in_closure_of)
  apply (meson in_closure_of islimptin_def)
  by (metis islimptin_def)

declare SML_Topological_Space.closure.with[ud_with del]
lemma closure_ud[ud_with]: \<open>closure = closure_ow UNIV open\<close>
  unfolding closure_def closure_ow_def islimpt_def islimpt_ow_def by auto

subsection \<open>\<^const>\<open>continuous\<close>\<close>

lemma continuous_on_ow_from_topology: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f \<longleftrightarrow> continuous_map T U f\<close>
  if \<open>f ` topspace T \<subseteq> topspace U\<close>
  apply (simp add: continuous_on_ow_def continuous_map_def)
  apply safe
  apply (meson image_subset_iff that)
  apply (smt (verit) Collect_mono_iff Int_def ctr_simps_mem_Collect_eq inf_absorb1 openin_subopen openin_subset vimage_eq)
  by blast

subsection \<open>\<^const>\<open>is_onb\<close>\<close>

definition
  \<open>is_onb_ow U scaleC plus zero norm open cinner E \<longleftrightarrow> is_ortho_set_ow zero cinner E \<and> (\<forall>b\<in>E. norm b = 1) \<and> 
    closure_ow U open (span_ow U plus zero scaleC E) = U\<close>
  for U scaleC plus zero norm "open" cinner

ctr parametricity in is_onb_ow_def

lemma is_onb_ud[ud_with]:
  \<open>is_onb = is_onb_ow UNIV scaleC plus 0 norm open cinner\<close>
  unfolding is_onb_def is_onb_ow_def
  apply (subst asm_rl[of \<open>\<And>E. ccspan E = \<top> \<longleftrightarrow> closure (cspan E) = UNIV\<close>, rule_format])
   apply (transfer, rule)
  unfolding ud_with
  apply transfer by auto


end
