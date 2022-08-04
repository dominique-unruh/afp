theory With_Type_Example
  imports With_Type_Inst_HOL
begin


subsection \<open>Example\<close>

experiment
begin

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>
ML \<open>
(* TODO: provide toplevel diagnostic command for this *)
get_params_of_class \<^theory> \<^class>\<open>ab_group_add\<close> |> #3
\<close>
definition carrier_ab_group_add where \<open>carrier_ab_group_add = (carrier_plus, 0::int, (\<lambda> i j. (i - j) mod 3), (\<lambda>i. (- i) mod 3))\<close>

lemma carrier_nonempty: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup: \<open>with_type_semigroup_add_class_pred carrier carrier_plus\<close>
  by (auto simp: with_type_semigroup_add_class_pred_def
      with_type_semigroup_add_class_dom_def with_type_semigroup_add_class_pred'_def carrier_def carrier_plus_def)

lemma carrier_ab_group_add: \<open>with_type_ab_group_add_class_pred carrier carrier_ab_group_add\<close>
(* TODO *)
  sorry

lemma example_semigroup:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. undefined (3::nat)\<close>
  apply (rule with_typeI)
  apply (simp_all add: with_type_semigroup_add_class_def)
     apply (rule carrier_nonempty)
    apply (rule carrier_semigroup)
   apply (metis fst_conv snd_conv with_type_semigroup_add_class_def with_type_semigroup_add_class_rel_compat)
proof -
  include lifting_syntax
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>type_definition Rep Abs carrier\<close>
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    using \<open>type_definition Rep Abs carrier\<close> bi_unique_def r_def type_definition.Rep_inject by fastforce
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume \<open>with_type_semigroup_add_class_rel (\<lambda>x y. x = Rep y) carrier_plus pls\<close>
  then have [transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
    by (simp add: r_def with_type_semigroup_add_class_rel_def)
  have \<open>pls x y = pls y x\<close> for x y
    apply transfer
    sorry
  show \<open>undefined 3\<close>
    sorry
qed

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