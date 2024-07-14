theory With_Type_Example
  imports With_Type (* With_Type_Inst_HOL *)
begin

(* TODO: Introduce diagnostic command that provides the boilerplate for a given class.
Should: provide WITH_TYPE_(CLASS/REL)_ including arguments (ops!)
The registration command
 *)

unbundle lifting_syntax

declare [[show_sorts]]

lemma tmp: \<open>x + y = y + x\<close> for y :: \<open>'a :: semigroup_add\<close>
  sorry

lemmas tmp2 = tmp[internalize_sort \<open>'a :: semigroup_add\<close>]

definition \<open>WITH_TYPE_CLASS_semigroup_add S plus \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. plus (plus a b) c = plus a (plus b c))\<close>
  for S :: \<open>'rep set\<close> and plus :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close>
definition \<open>WITH_TYPE_REL_semigroup_add r = (r ===> r ===> r)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

(* definition \<open>WITH_TYPE_REL_ab_group_add S = (\<lambda>(plus,zero,minus,uminus). True)\<close> *)

lemma with_type_compat_rel_semigroup_add[with_type_intros]:
  \<open>with_type_compat_rel WITH_TYPE_CLASS_semigroup_add S WITH_TYPE_REL_semigroup_add\<close>
  by (simp add: with_type_compat_rel_def WITH_TYPE_CLASS_semigroup_add_def WITH_TYPE_REL_semigroup_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_alt_def)

(* lemma with_type_relatable_semigroup_add[with_type_intros]:
  \<open>with_type_relatable WITH_TYPE_CLASS_semigroup_add (WITH_TYPE_REL_semigroup_add :: ('rep \<Rightarrow> 'abs::semigroup_add \<Rightarrow> _) \<Rightarrow> _) (+)\<close>
  unfolding with_type_relatable_def
proof (intro allI impI)
  fix S :: \<open>'rep set\<close> and rep_ops
  assume CLASS: \<open>WITH_TYPE_CLASS_semigroup_add S rep_ops\<close>
  assume \<open>\<exists>(Rep' :: 'abs \<Rightarrow> 'rep) Abs'. type_definition Rep' Abs' S\<close>
  then obtain Rep' :: \<open>'abs \<Rightarrow> 'rep\<close> and Abs' where \<open>type_definition Rep' Abs' S\<close>
    by auto
  define Rep :: \<open>'abs \<Rightarrow> 'rep\<close> and Abs :: \<open>'rep \<Rightarrow> 'abs\<close>
    where \<open>Rep = undefined\<close> and \<open>Abs = undefined\<close>
  have td: \<open>type_definition Rep Abs S\<close>
    by x
  have rel: \<open>WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) rep_ops (+)\<close>
    unfolding WITH_TYPE_REL_semigroup_add_def
    using CLASS apply (simp add: rel_fun_def WITH_TYPE_CLASS_semigroup_add_def)
try0
sledgehammer [dont_slice]
by -

    by x
  from td rel
  show \<open>\<exists>(Rep :: 'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs S \<and> WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) rep_ops (+)\<close>
    by auto
qed *)

(* bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (rep_rel r ===> (\<longleftrightarrow>)) (rep_class (Collect (Domainp r))) class.class *)
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

(* lemma with_type_transfer_semigroup_add':
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_semigroup_add r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
 *)


setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>semigroup_add\<close>,
  (* class_ops = \<^cterm>\<open>(+) :: 'a::semigroup_add \<Rightarrow> _ \<Rightarrow> _\<close>, *)
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_semigroup_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_semigroup_add\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_semigroup_add},
  transfer = SOME @{thm with_type_transfer_semigroup_add} (* TODO *)
}
\<close>

notation rel_prod (infixr \<open>***\<close> 80)

definition \<open>WITH_TYPE_CLASS_ab_group_add S = (\<lambda>(plus,zero,minus,uminus). zero \<in> S)\<close>
  for S :: \<open>'rep set\<close>
definition \<open>WITH_TYPE_REL_ab_group_add r = (r ===> r ===> (\<longleftrightarrow>)) *** r *** (r ===> r ===> (\<longleftrightarrow>)) *** (r ===> (\<longleftrightarrow>))\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

(* definition \<open>WITH_TYPE_REL_ab_group_add S = (\<lambda>(plus,zero,minus,uminus). True)\<close> *)

lemma with_type_compat_rel_ab_group_add[with_type_intros]:
  \<open>with_type_compat_rel WITH_TYPE_CLASS_ab_group_add S WITH_TYPE_REL_ab_group_add\<close>
  apply (simp add: with_type_compat_rel_def WITH_TYPE_CLASS_ab_group_add_def WITH_TYPE_REL_ab_group_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_def prod.Domainp_rel DomainPI)
  by -


setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>ab_group_add\<close>,
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_ab_group_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_ab_group_add\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_ab_group_add},
  transfer = NONE (* TODO *)
}
\<close>




subsection \<open>Example\<close>

experiment
begin

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>
ML \<open>
(* TODO: provide toplevel diagnostic command for this *)
get_params_of_class \<^theory> \<^class>\<open>semigroup_add\<close> |> #3
\<close>
definition carrier_ab_group_add where \<open>carrier_ab_group_add = (carrier_plus, 0::int, (\<lambda> i j. (i - j) mod 3), (\<lambda>i. (- i) mod 3))\<close>

lemma carrier_nonempty[iff]: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup[with_type_intros]: \<open>WITH_TYPE_CLASS_semigroup_add carrier carrier_plus\<close>
  by (auto simp: WITH_TYPE_CLASS_semigroup_add_def
        carrier_def carrier_plus_def)

lemma carrier_ab_group_add: \<open>WITH_TYPE_CLASS_ab_group_add carrier carrier_ab_group_add\<close>
  by (auto simp: WITH_TYPE_CLASS_ab_group_add_def
        carrier_def carrier_ab_group_add_def)

lemma example_semigroup:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. 
    let plus = (\<lambda>x y. abs (carrier_plus (rep x) (rep y))) in (x::'abs) + x + x + x = x\<close>
proof with_type_intro
  show \<open>carrier \<noteq> {}\<close> by simp
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>type_definition Rep Abs carrier\<close>
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    using \<open>type_definition Rep Abs carrier\<close> bi_unique_def r_def type_definition.Rep_inject by fastforce
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume \<open>WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) carrier_plus pls\<close>
  then have [transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
    by (simp add: r_def WITH_TYPE_REL_semigroup_add_def)
  have \<open>pls x y = pls y x\<close> for x y
    apply transfer
    apply (simp add: carrier_plus_def)
    by presburger
  note [[show_types]]
  show \<open>x + x + x + x = x\<close>
    apply transfer
(* TODO need a transfer theorem for semigroup_add *)
    by xxx
qed

lemma example_semigroup_tmp:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. 3=3\<close>
  apply (auto intro!: with_typeI simp add: )
  using carrier_semigroup apply auto[1] 
  apply (simp add: with_type_compat_rel_semigroup_add) 
by -

declare [[show_types, show_sorts]]
thm example_semigroup_tmp[cancel_with_type]


lemma example_ab_group_add:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::ab_group_add = carrier with carrier_ab_group_add. undefined (3::nat)\<close>
  sorry
(* TODO *)

lemma example_type:
  \<open>\<forall>\<^sub>\<tau> 'abs::type = undefined::int set. undefined (3::nat)\<close>
  sorry

lemma example_finite:
  \<open>\<forall>\<^sub>\<tau> 'abs::finite = undefined::int set. undefined (3::nat)\<close>
  sorry

declare [[show_consts, show_sorts]]

ML \<open>
With_Type.with_type_cancel \<^context> @{thm example_finite}
\<close>

ML \<open>
\<close>


thm example_type[cancel_with_type]
thm example_finite[cancel_with_type]
thm example_semigroup[cancel_with_type]
thm example_ab_group_add[cancel_with_type]

(* lemma \<open>a=1\<close> if \<open>a=1\<close> and \<open>b=1\<close> for a b :: \<open>'a::one\<close>
proof -
  note [[show_consts,show_hyps]]
  have \<open>\<forall>\<^sub>\<tau> 'd::type={1::nat}. a=b\<close>
    sorry
  note this[cancel_with_type]
  have cheat: \<open>PROP a\<close> for a
    sorry

  have xxx: \<open>xxx == xxx\<close> for xxx :: \<open>'c::{finite, semigroup_add, metric_space}\<close>
    sorry
  note [[show_consts,show_hyps]]
  thm xxx
  ML_val \<open>
Assumption.all_prems_of \<^context>
\<close>
  ML_val \<open>
unoverload_type_local \<^context> [("'c",2)] @{thm xxx} 
\<close> *)


end (* experiment *)




end