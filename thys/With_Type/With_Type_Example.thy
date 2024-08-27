theory With_Type_Example
  imports With_Type (* With_Type_Inst_HOL *)
begin

(* TODO: Introduce diagnostic command that provides the boilerplate for a given class.
Should: provide WITH_TYPE_(CLASS/REL)_ including arguments (ops!)
The registration command
 *)

subsection \<open>Finite\<close>

unbundle lifting_syntax

definition \<open>WITH_TYPE_CLASS_finite S (_::unit) \<longleftrightarrow> finite S\<close>
  for S :: \<open>'rep set\<close> and plus :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close>
definition \<open>WITH_TYPE_REL_finite r = (rel_unit_itself :: _ \<Rightarrow> 'abs itself \<Rightarrow> _)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

lemma with_type_wellformed_finite[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_finite S WITH_TYPE_REL_finite\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_REL_finite_def)

lemma with_type_transfer_finite:
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_finite r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_finite (Collect (Domainp r))) class.finite\<close>
  unfolding WITH_TYPE_REL_finite_def
proof (rule rel_funI)
  fix x :: unit and y :: \<open>'abs itself\<close>
  assume \<open>rel_unit_itself x y\<close>
  then have [simp]: \<open>y = TYPE('abs)\<close>
    by simp
  note right_total_UNIV_transfer[transfer_rule]
  show \<open>WITH_TYPE_CLASS_finite (Collect (Domainp r)) x \<longleftrightarrow> class.finite y\<close>
    apply (simp add: WITH_TYPE_CLASS_finite_def class.finite_def)
    apply transfer
    by simp
qed

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>finite\<close>,
  param_names = [],
  (* class_ops = \<^cterm>\<open>(+) :: 'a::semigroup_add \<Rightarrow> _ \<Rightarrow> _\<close>, *)
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_finite\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_finite\<close>,
  with_type_wellformed = @{thm with_type_wellformed_finite},
  transfer = SOME @{thm with_type_transfer_finite},
  rep_rel_itself = SOME @{lemma \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (WITH_TYPE_REL_finite r) p TYPE('abs2)\<close>
      by (simp add: WITH_TYPE_REL_finite_def rel_unit_itself.simps Transfer.Rel_def)}
}
\<close>

subsubsection \<open>Example\<close>



lemma example_finite:
  \<open>\<forall>\<^sub>\<tau> 'abs::finite = undefined::int set. undefined (3::nat)\<close>
  sorry

thm example_finite[cancel_with_type]
ML \<open>
With_Type.with_type_cancel \<^context> @{thm example_finite}
\<close>

subsection \<open>Semigroup-add\<close>


definition \<open>WITH_TYPE_CLASS_semigroup_add S plus \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. plus (plus a b) c = plus a (plus b c))\<close>
  for S :: \<open>'rep set\<close> and plus :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close>
definition \<open>WITH_TYPE_REL_semigroup_add r = (r ===> r ===> r)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

lemma with_type_wellformed_semigroup_add[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_semigroup_add S WITH_TYPE_REL_semigroup_add\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_CLASS_semigroup_add_def WITH_TYPE_REL_semigroup_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_alt_def)

lemma with_type_transfer_semigroup_add:
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_semigroup_add r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
proof -
  define f where \<open>f y = (SOME x. r x y)\<close> for y
  have rf: \<open>r x y \<longleftrightarrow> x = f y\<close> for x y
    unfolding f_def
    apply (rule someI2_ex)
    using assms
    by (auto intro!: simp: right_total_def bi_unique_def)
  have inj: \<open>inj f\<close>
    using \<open>bi_unique r\<close>
    by (auto intro!: injI simp: bi_unique_def rf)
  show ?thesis
    unfolding WITH_TYPE_REL_semigroup_add_def rel_fun_def
    unfolding WITH_TYPE_CLASS_semigroup_add_def
    unfolding Domainp_iff rf
    apply (auto intro!: simp: class.semigroup_add_def)
    by (metis inj injD)
qed

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>semigroup_add\<close>,
  param_names = ["plus"],
  (* class_ops = \<^cterm>\<open>(+) :: 'a::semigroup_add \<Rightarrow> _ \<Rightarrow> _\<close>, *)
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_semigroup_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_semigroup_add\<close>,
  with_type_wellformed = @{thm with_type_wellformed_semigroup_add},
  transfer = SOME @{thm with_type_transfer_semigroup_add},
  rep_rel_itself = NONE
}
\<close>

subsubsection \<open>Example\<close>

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>

lemma carrier_nonempty[iff]: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup[with_type_intros]: \<open>WITH_TYPE_CLASS_semigroup_add carrier carrier_plus\<close>
  by (auto simp: WITH_TYPE_CLASS_semigroup_add_def
        carrier_def carrier_plus_def)

lemma example_semigroup:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. 
    (ops_abs x y = ops_abs y x \<and> ops_abs x (ops_abs x x) = ops_abs (ops_abs x x) x)\<close>
proof with_type_intro
  show \<open>carrier \<noteq> {}\<close> by simp
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>bij_betw Rep UNIV carrier\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> carrier
    using type_definition_bij_betw_iff by blast
  print_theorems
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume \<open>WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) carrier_plus pls\<close>
  then have transfer_carrier[transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
    by (simp add: r_def WITH_TYPE_REL_semigroup_add_def)
  have [transfer_rule]: \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
  proof (intro rel_funI)
    fix x y
    assume xy[transfer_rule]: \<open>(r ===> r ===> r) x y\<close>
    show \<open>WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r)) x \<longleftrightarrow> class.semigroup_add y\<close>
      unfolding class.semigroup_add_def
      apply transfer
      apply (auto intro!: simp: WITH_TYPE_CLASS_semigroup_add_def)
       apply fast
      by (metis DomainPI rel_funD xy)
  qed
  have dom_r: \<open>Collect (Domainp r) = carrier\<close>
    apply (auto intro!: simp: Rep r_def Domainp_iff)
    by (meson Rep_cases)
  interpret semigroup_add pls
    apply transfer
    using carrier_semigroup dom_r by auto

  have 1: \<open>pls x y = pls y x\<close>
    apply transfer
    apply (simp add: carrier_plus_def)
    by presburger

  have 2: \<open>pls x (pls x x) = pls (pls x x) x\<close>
    by (simp add: add_assoc)

  from 1 2
  show \<open>pls x y = pls y x \<and> pls x (pls x x) = pls (pls x x) x\<close>
    by simp
qed


lemma tmp1: \<open>p x y = p y x \<Longrightarrow> 3=3\<close>
  by simp

lemma example_semigroup_tmp:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. 3=(3)\<close>
  using example_semigroup[of x y]
proof with_type_mp
  case with_type_mp
  then have \<open>ops_abs x (ops_abs x x) = ops_abs (ops_abs x x) x\<close>
    by simp
  then show \<open>3=3\<close>
    by (rule tmp1)
qed

declare [[show_types, show_sorts]]
thm example_semigroup_tmp[cancel_with_type]


subsection \<open>Ab-group-add\<close>

notation rel_prod (infixr \<open>***\<close> 80)

definition \<open>WITH_TYPE_CLASS_ab_group_add S = (\<lambda>(plus,zero,minus,uminus). zero \<in> S
 \<and> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. minus a b \<in> S) \<and> (\<forall>a\<in>S. uminus a \<in> S)
 \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. plus (plus a b) c= plus a (plus b c)) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b = plus b a)
 \<and> (\<forall>a\<in>S. plus zero a = a) \<and> (\<forall>a\<in>S. plus (uminus a) a = zero) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. minus a b = plus a (uminus b)))\<close>
  for S :: \<open>'rep set\<close>
definition \<open>WITH_TYPE_REL_ab_group_add r = (r ===> r ===> r) *** r *** (r ===> r ===> r) *** (r ===> r)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

lemma with_type_wellformed_ab_group_add[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_ab_group_add S WITH_TYPE_REL_ab_group_add\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_CLASS_ab_group_add_def WITH_TYPE_REL_ab_group_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_alt_def prod.Domainp_rel DomainPI)

lemma with_type_transfer_ab_group_add:
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_ab_group_add r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_ab_group_add (Collect (Domainp r))) (\<lambda>(p,z,m,u). class.ab_group_add p z m u)\<close>
proof -
  define f where \<open>f y = (SOME x. r x y)\<close> for y
  have rf: \<open>r x y \<longleftrightarrow> x = f y\<close> for x y
    unfolding f_def
    apply (rule someI2_ex)
    using assms
    by (auto intro!: simp: right_total_def bi_unique_def)
  have inj: \<open>inj f\<close>
    using \<open>bi_unique r\<close>
    by (auto intro!: injI simp: bi_unique_def rf)
  show ?thesis
    unfolding WITH_TYPE_REL_ab_group_add_def rel_fun_def
    unfolding WITH_TYPE_CLASS_ab_group_add_def
    unfolding Domainp_iff rf
    using inj
    apply (simp add: class.ab_group_add_def class.comm_monoid_add_def
        class.ab_semigroup_add_def class.semigroup_add_def class.ab_semigroup_add_axioms_def
        class.comm_monoid_add_axioms_def class.ab_group_add_axioms_def inj_def)
    apply safe
    by metis+
qed


setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>ab_group_add\<close>,
  param_names = ["plus", "zero", "minus", "uminus"],
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_ab_group_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_ab_group_add\<close>,
  with_type_wellformed = @{thm with_type_wellformed_ab_group_add},
  transfer = SOME @{thm with_type_transfer_ab_group_add},
  rep_rel_itself = NONE
}
\<close>

subsubsection \<open>Example\<close>

definition carrier_ab_group_add where \<open>carrier_ab_group_add = (carrier_plus, 0::int, (\<lambda> i j. (i - j) mod 3), (\<lambda>i. (- i) mod 3))\<close>

lemma carrier_ab_group_add[with_type_intros]: \<open>WITH_TYPE_CLASS_ab_group_add carrier carrier_ab_group_add\<close>
  by (auto simp: WITH_TYPE_CLASS_ab_group_add_def carrier_plus_def
        carrier_def carrier_ab_group_add_def)

declare [[show_sorts=false]]
lemma example_ab_group:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::ab_group_add = carrier with carrier_ab_group_add. 
    (plus_abs x y = plus_abs y x \<and> plus_abs x (plus_abs x x) = plus_abs (plus_abs x x) x)\<close>
proof with_type_intro
  show \<open>carrier \<noteq> {}\<close> by simp
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and abs_ops
  assume wt: \<open>WITH_TYPE_REL_ab_group_add (\<lambda>x y. x = Rep y) carrier_ab_group_add abs_ops\<close>
  define plus zero minus uminus where \<open>plus = fst abs_ops\<close>
    and \<open>zero = fst (snd abs_ops)\<close>
    and \<open>minus = fst (snd (snd abs_ops))\<close>
    and \<open>uminus = snd (snd (snd abs_ops)) \<close>

  assume \<open>bij_betw Rep UNIV carrier\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> carrier
    by (simp add: type_definition_bij_betw_iff)

  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  from wt have transfer_carrier[transfer_rule]: \<open>((r ===> r ===> r) *** r *** (r ===> r ===> r) *** (r ===> r)) carrier_ab_group_add abs_ops\<close>
    by (simp add: r_def WITH_TYPE_REL_ab_group_add_def)
  have dom_r: \<open>Collect (Domainp r) = carrier\<close>
    apply (auto intro!: simp: Rep r_def Domainp_iff)
    by (meson Rep_cases)
  
  from with_type_transfer_ab_group_add[OF \<open>bi_unique r\<close> \<open>right_total r\<close>]
  have [transfer_rule]: \<open>((r ===> r ===> r) ===> r ===> (r ===> r ===> r) ===> (r ===> r) ===> (\<longleftrightarrow>))
                         (\<lambda>p z m u. WITH_TYPE_CLASS_ab_group_add carrier (p,z,m,u)) class.ab_group_add\<close>
    unfolding dom_r WITH_TYPE_REL_ab_group_add_def
    by (auto intro!: simp: rel_fun_def)

  interpret ab_group_add plus zero minus uminus
    unfolding zero_def plus_def minus_def uminus_def
    apply transfer
    using carrier_ab_group_add dom_r
    by (auto intro!: simp: Let_def case_prod_beta)

  have 1: \<open>plus x y = plus y x\<close>
    unfolding plus_def
    apply transfer
    apply (simp add: carrier_ab_group_add_def carrier_plus_def)
    by presburger

  have 2: \<open>plus x (plus x x) = plus (plus x x) x\<close>
    by (simp add: add_assoc)

  from 1 2
  have final: \<open>plus x y = plus y x \<and> plus x (plus x x) = plus (plus x x) x\<close>
    by simp

  show \<open>plus x y = plus y x \<and> plus x (plus x x) = plus (plus x x) x\<close>
    using final
    by (simp add: plus_def case_prod_beta)

qed

end

