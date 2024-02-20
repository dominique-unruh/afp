(*  Author:     Ata Keskin, TU München 
*)

theory Example_Coin_Toss
  imports Martingale "HOL-Probability.Stream_Space" "HOL-Probability.Probability_Mass_Function"
begin

section \<open>Example: Coin Toss\<close>

text \<open>Consider a coin-tossing game, where the coin lands on heads with probability \<open>p \<in> [0, 1]\<close>. Assume that the gambler wins a fixed amount \<open>c > 0\<close> on a heads outcome 
      and loses the same amount \<open>c\<close> on a tails outcome. Let \<open>(X\<^sub>n)\<^sub>n\<^sub>\<in>\<^sub>\<nat>\<close> be a stochastic process, where \<open>X\<^sub>n\<close> denotes the gambler’s fortune after the \<open>n\<close>-th coin toss. 
      Then, we have the following three cases.\<close>

text \<open>1. If \<open>p = 1/2\<close>, it means the coin is fair and has an equal chance of landing heads or tails. 
      In this case, the gambler, on average, neither wins nor loses money over time. The expected value of the gambler’s fortune stays the same over time. 
      Therefore, \<open>(X\<^sub>n)\<^sub>n\<^sub>\<in>\<^sub>\<nat>\<close> is a martingale.\<close>
text \<open>2. If \<open>p \<ge> 1/2\<close> , it means the coin is biased in favor of heads. In this case, the gambler is more likely to win money on each bet. 
      Over time, the gambler’s fortune tends to increase on average. 
      Therefore, \<open>(X\<^sub>n)\<^sub>n\<^sub>\<in>\<^sub>\<nat>\<close> is a submartingale.\<close>

text \<open>3. If \<open>p \<le> 1/2\<close> , it means the coin is biased in favor of tails. In this scenario, the gambler is more likely to lose money on each bet. 
      Over time, the gambler’s fortune decreases on average. 
      Therefore, \<open>(X\<^sub>n)\<^sub>n\<^sub>\<in>\<^sub>\<nat>\<close> is a supermartingale.\<close>

text \<open>To formalize this example, we first consider a probability space consisting of infinite sequences of coin tosses.\<close>

definition bernoulli_stream :: "real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"
                                  
lemma space_bernoulli_stream[simp]: "space (bernoulli_stream p) = UNIV" by (simp add: bernoulli_stream_def space_stream_space)

text \<open>We define the fortune of the player at time \<^term>\<open>n\<close> to be the number of heads minus number of tails.\<close>

definition fortune :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "fortune n = (\<lambda>s. \<Sum>b \<leftarrow> stake (Suc n) s. if b then 1 else -1)"

definition toss :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "toss n = (\<lambda>s. if snth s n then 1 else -1)"

lemma toss_indicator_def: "toss n = indicator {s. s !! n} - indicator {s. \<not> s !! n}"
  unfolding toss_def indicator_def by force

lemma range_toss: "range (toss n) = {-1, 1}"
proof -
  have "sconst True !! n" by simp
  moreover have "\<not>sconst False !! n" by simp
  ultimately have "\<exists>x. x !! n" "\<exists>x. \<not>x !! n" by blast+
  thus ?thesis unfolding toss_def image_def by auto
qed

lemma vimage_toss: "toss n -` A = (if 1 \<in> A then {s. s !! n} else {}) \<union> (if -1 \<in> A then {s. \<not>s !! n} else {})"
  unfolding vimage_def toss_def by auto

lemma fortune_Suc: "fortune (Suc n) s = fortune n s + toss (Suc n) s"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def)+

lemma fortune_toss_sum: "fortune n s = (\<Sum>i \<in> {..n}. toss i s)"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def, simp add: fortune_Suc)

lemma fortune_bound: "norm (fortune n s) \<le> Suc n" by (induction n) (force simp add: fortune_toss_sum toss_def)+

text \<open>Our definition of \<^term>\<open>bernoulli_stream\<close> constitutes a probability space.\<close>

interpretation prob_space "bernoulli_stream p" unfolding bernoulli_stream_def by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

abbreviation "toss_filtration p \<equiv> nat_natural_filtration (bernoulli_stream p) toss"

text \<open>The stochastic process \<^term>\<open>toss\<close> is adapted to the filtration it generates.\<close> 

interpretation toss: nat_adapted_process "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) toss" toss 
  by (intro nat_adapted_process.intro stochastic_process.adapted_process_natural_filtration)
     (unfold_locales, auto simp add: toss_def bernoulli_stream_def)

text \<open>Similarly, the stochastic process \<^term>\<open>fortune\<close> is adapted to the filtration generated by the tosses.\<close>

interpretation fortune: nat_finite_adapted_process_linorder "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) toss" fortune 
proof -
  show "nat_finite_adapted_process_linorder (bernoulli_stream p) (toss_filtration p) fortune"
  unfolding fortune_toss_sum   
  by (intro nat_finite_adapted_process_linorder.intro 
            finite_adapted_process_linorder.intro 
            finite_adapted_process_order.intro 
            finite_adapted_process.intro
            toss.partial_sum_adapted[folded atMost_atLeast0]) intro_locales
qed

lemma integrable_toss: "integrable (bernoulli_stream p) (toss n)" 
  using toss.random_variable
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "1 :: real"]]) (auto simp add: toss_def)

lemma integrable_fortune: "integrable (bernoulli_stream p) (fortune n)" using fortune_bound 
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "Suc n"] fortune.random_variable]) auto

text \<open>We provide the following lemma to explicitly calculate the probability of events in this probability space.\<close>

lemma measure_bernoulli_stream_snth_pred:
  assumes "0 \<le> p" and "p \<le> 1" and "finite J" 
  shows "prob p {w \<in> space (bernoulli_stream p). \<forall>j\<in>J. P j = w !! j} = p ^ card (J \<inter> Collect P) * (1 - p) ^ (card (J - Collect P))"
proof -
  let ?PiE = "(\<Pi>\<^sub>E i\<in>J. if P i then {True} else {False})"
  have "product_prob_space (\<lambda>_. measure_pmf (bernoulli_pmf p))" by unfold_locales

  hence *: "to_stream -` {s. \<forall>i\<in>J. P i = s !! i} = {s. \<forall>i\<in>J. P i = s i}" using assms by (simp add: to_stream_def)
  also have "... = prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE"
  proof -
    {
      fix s assume "(\<forall>i\<in>J. P i = s i)"
      hence "(\<forall>i\<in>J. P i = s i) = (s \<in> prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)" 
        by (subst prod_emb_iff[of s]) (smt (verit, best) not_def assms(3) id_def PiE_eq_singleton UNIV_I extensional_UNIV insert_iff singletonD space_measure_pmf)
    }
    moreover
    {
      fix s assume "\<not>(\<forall>i\<in>J. P i = s i)"
      then obtain i where "i \<in> J" "P i \<noteq> s i" by blast
      hence "(\<forall>i\<in>J. P i = s i) = (s \<in> prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)"
        by (simp add: restrict_def prod_emb_iff[of s]) (smt (verit, ccfv_SIG) PiE_mem assms(3) id_def insert_iff singleton_iff)
    }
    ultimately show ?thesis by auto
  qed
  finally have inteq: "(to_stream -` {s. \<forall>i\<in>J. P i = s !! i}) = prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE" .
  let ?M = "(Pi\<^sub>M UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)))"
  have "emeasure (bernoulli_stream p) {s \<in> space (bernoulli_stream p). \<forall>i\<in>J. P i = s !! i} = emeasure ?M (to_stream -` {s. \<forall>i\<in>J. P i  = s !! i})"
    using assms emeasure_distr[of "to_stream" ?M "(vimage_algebra (streams (space (measure_pmf (bernoulli_pmf p)))) (!!) ?M)" "{s. \<forall>i\<in>J. P i = s !! i}", symmetric] measurable_to_stream[of "(measure_pmf (bernoulli_pmf p))"]
    by (simp only: bernoulli_stream_def stream_space_def *, simp add: space_PiM ) (smt (verit, best) emeasure_notin_sets in_vimage_algebra inf_top.right_neutral sets_distr vimage_Collect)
  also have "... = emeasure ?M (prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)" using inteq by (simp add: space_PiM)
  also have "... = (\<Prod>i\<in>J. emeasure (measure_pmf (bernoulli_pmf p)) (if P i then {True} else {False}))" 
    by (subst emeasure_PiM_emb) (auto simp add: prob_space_measure_pmf assms(3))
  also have "... = (\<Prod>i\<in>J \<inter> Collect P. ennreal p) * (\<Prod>i\<in>J - Collect P. ennreal (1 - p))"
    unfolding emeasure_pmf_single[of "bernoulli_pmf p" True, unfolded pmf_bernoulli_True[OF assms(1,2)], symmetric]
              emeasure_pmf_single[of "bernoulli_pmf p" False, unfolded pmf_bernoulli_False[OF assms(1,2)], symmetric]
    by (simp add: prod.Int_Diff[OF assms(3), of _ "Collect P"])
  also have "... = p ^ card (J \<inter> Collect P) * (1 - p) ^ card (J - Collect P)" using assms by (simp add: prod_ennreal ennreal_mult' ennreal_power)
  finally show ?thesis using assms by (intro measure_eq_emeasure_eq_ennreal) auto
qed

lemma 
  assumes "0 \<le> p" and "p \<le> 1"
  shows measure_bernoulli_stream_snth: "prob p {w \<in> space (bernoulli_stream p). w !! i} = p"
    and measure_bernoulli_stream_neg_snth: "prob p {w \<in> space (bernoulli_stream p). \<not>w !! i} = 1 - p"
  using measure_bernoulli_stream_snth_pred[OF assms, of "{i}" "\<lambda>x. True"]
        measure_bernoulli_stream_snth_pred[OF assms, of "{i}" "\<lambda>x. False"] by auto

text \<open>Now we can express the expected value of a single coin toss.\<close>

lemma integral_toss:
  assumes "0 \<le> p" "p \<le> 1"
  shows "expectation p (toss n) = 2 * p - 1"
proof -
  have [simp]:"{s. s !! n} \<in> events p" using measurable_snth[THEN measurable_sets, of "{True}" "measure_pmf (bernoulli_pmf p)" n, folded bernoulli_stream_def]
    by (simp add: vimage_def)
  have "expectation p (toss n) = Bochner_Integration.simple_bochner_integral (bernoulli_stream p) (toss n)"
    using toss.random_variable[of n, THEN measurable_sets]
    by (intro simple_bochner_integrable_eq_integral[symmetric] simple_bochner_integrable.intros) (auto simp add: toss_def simple_function_def image_def)
  also have "... = p - prob p {s. \<not> s !! n}" unfolding simple_bochner_integral_def using measure_bernoulli_stream_snth[OF assms]
    by (simp add: range_toss, simp add: toss_def)
  also have "... = p - (1 - prob p {s. s !! n})" by (subst prob_compl[symmetric], auto simp add: Collect_neg_eq Compl_eq_Diff_UNIV)
  finally show ?thesis using measure_bernoulli_stream_snth[OF assms] by simp
qed

text \<open>Now, we show that the tosses are independent from one another.\<close>

lemma indep_vars_toss:
  assumes "0 \<le> p" "p \<le> 1"
  shows "indep_vars p (\<lambda>_. borel) toss {0..}"
proof (subst indep_vars_def, intro conjI indep_sets_sigma)
  {
    fix A J assume asm: "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> {toss j -` A \<inter> space (bernoulli_stream p) |A. A \<in> borel}"
    hence "\<forall>j\<in>J. \<exists>B \<in> borel. A j = toss j -` B \<inter> space (bernoulli_stream p)" by auto
    then obtain B where B_is: "A j = toss j -` B j \<inter> space (bernoulli_stream p)" "B j \<in> borel" if "j \<in> J" for j by metis

    have "prob p (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob p (A j))"
    proof cases
      text \<open>We consider the case where there is a zero probability event.\<close>
      assume "\<exists>j \<in> J. 1 \<notin> B j \<and> -1 \<notin> B j"
      then obtain j where j_is: "j \<in> J" "1 \<notin> B j" "-1 \<notin> B j" by blast
      hence A_j_empty: "A j = {}" using B_is by (force simp add: toss_def vimage_def)
      hence "\<Inter> (A ` J) = {}" using j_is by blast
      moreover have "prob p (A j) = 0" using A_j_empty by simp
      ultimately show ?thesis using j_is asm(2) by auto
    next
      text \<open>We now assume all events have positive probability.\<close>
      assume "\<not>(\<exists>j \<in> J. 1 \<notin> B j \<and> -1 \<notin> B j)"
      hence *: "1 \<in> B j \<or> -1 \<in> B j" if "j \<in> J" for j using that by blast


      define J' where [simp]: "J' = {j \<in> J. (1 \<in> B j) \<longleftrightarrow> (-1 \<notin> B j)}"
      hence "toss j w \<in> B j \<longleftrightarrow> (1 \<in> B j) = w !! j" if "j \<in> J'" for w j using that unfolding toss_def by simp
      hence "(\<Inter> (A ` J')) = {w \<in> space (bernoulli_stream p). \<forall>j\<in>J'. (1 \<in> B j) = w !! j}" using B_is by force
      hence prob_J': "prob p (\<Inter> (A ` J')) = p ^ card (J' \<inter> {j. 1 \<in> B j}) * (1 - p) ^ card (J' - {j. 1 \<in> B j})" 
        using measure_bernoulli_stream_snth_pred[OF assms finite_subset[OF _ asm(2)], of J' "\<lambda>j. 1 \<in> B j"] by auto
      
      text \<open>The index set \<^term>\<open>J'\<close> consists of the indices of all non-trivial events.\<close>
      
      have A_j_True: "A j = {w \<in> space (bernoulli_stream p). w !! j}" if "j \<in> J' \<inter> {j. 1 \<in> B j}" for j
        using that by (auto simp add: toss_def B_is(1) split: if_splits) 

      have A_j_False: "A j = {w \<in> space (bernoulli_stream p). \<not>w !! j}" if "j \<in> J' - {j. 1 \<in> B j}" for j 
        using that B_is by (auto simp add: toss_def) 
      
      have A_j_top: "A j = space (bernoulli_stream p)" if "j \<in> J - J'" for j using that * by (auto simp add: B_is toss_def)
      hence "\<Inter> (A ` J) = \<Inter> (A ` J')" by auto
      hence "prob p (\<Inter> (A ` J)) = prob p (\<Inter> (A ` J'))" by presburger
      also have "... = (\<Prod>j\<in>J' \<inter> {j. 1 \<in> B j}. prob p (A j)) * (\<Prod>j\<in>J' - {j. 1 \<in> B j}. prob p (A j))" 
        by (simp only: prob_J' A_j_True A_j_False measure_bernoulli_stream_snth[OF assms] measure_bernoulli_stream_neg_snth[OF assms] cong: prod.cong) simp
      also have "... = (\<Prod>j\<in>J'. prob p (A j))" using asm(2) by (intro prod.Int_Diff[symmetric]) auto
      also have "... = (\<Prod>j\<in>J'. prob p (A j)) * (\<Prod>j\<in>J - J'. prob p (A j))" using A_j_top prob_space by simp
      also have "... = (\<Prod>j\<in>J. prob p (A j))" using asm(2) by (metis (no_types, lifting) J'_def mem_Collect_eq mult.commute prod.subset_diff subsetI)
      finally show ?thesis .
    qed
  }
  thus "indep_sets p (\<lambda>i. {toss i -` A \<inter> space (bernoulli_stream p) |A. A \<in> sets borel}) {0..}" using measurable_sets[OF toss.random_variable]
  by (intro indep_setsI subsetI) fastforce
qed (simp, intro Int_stableI, simp, metis sets.Int vimage_Int)

text \<open>The fortune of a player is a martingale (resp. sub- or supermartingale) with respect to the filtration generated by the coin tosses.\<close>

theorem fortune_martingale:
  assumes "p = 1/2"
  shows "nat_martingale (bernoulli_stream p) (toss_filtration p) fortune"
  using cond_exp_indep[OF fortune.subalg indep_set_natural_filtration integrable_toss, OF zero_order(1) lessI indep_vars_toss, of p] 
        integral_toss assms
    by (intro fortune.martingale_of_cond_exp_diff_Suc_eq_zero integrable_fortune) (force simp add: fortune_toss_sum)

theorem fortune_submartingale:
  assumes "1/2 \<le> p" "p \<le> 1"
  shows "nat_submartingale (bernoulli_stream p) (toss_filtration p) fortune"
proof (intro fortune.submartingale_of_cond_exp_diff_Suc_nonneg integrable_fortune)
  fix n
  show "AE \<xi> in bernoulli_stream p. 0 \<le> cond_exp (bernoulli_stream p) (toss_filtration p n) (\<lambda>\<xi>. fortune (Suc n) \<xi> - fortune n \<xi>) \<xi>"
    using cond_exp_indep[OF fortune.subalg indep_set_natural_filtration integrable_toss, OF zero_order(1) lessI indep_vars_toss, of p n] 
          integral_toss[of p "Suc n"] assms
    by (force simp add: fortune_toss_sum)
qed

theorem fortune_supermartingale:
  assumes "0 \<le> p" "p \<le> 1/2" 
  shows "nat_supermartingale (bernoulli_stream p) (toss_filtration p) fortune"
proof (intro fortune.supermartingale_of_cond_exp_diff_Suc_le_zero integrable_fortune)
  fix n
  show "AE \<xi> in bernoulli_stream p. 0 \<ge> cond_exp (bernoulli_stream p) (toss_filtration p n) (\<lambda>\<xi>. fortune (Suc n) \<xi> - fortune n \<xi>) \<xi>"
    using cond_exp_indep[OF fortune.subalg indep_set_natural_filtration integrable_toss, OF zero_order(1) lessI indep_vars_toss, of p n] 
          integral_toss[of p "Suc n"] assms
    by (force simp add: fortune_toss_sum)
qed

end