theory With_Type_Inst_HOL
  imports With_Type
begin

subsection \<open>Finite\<close>

definition with_type_class_finite :: \<open>('a set \<Rightarrow> unit \<Rightarrow> bool) \<times> (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (unit \<Rightarrow> unit \<Rightarrow> bool))\<close>
  where \<open>with_type_class_finite = (\<lambda>F _. finite F, \<lambda>_. (=))\<close>

lemma finite_transfer'[unfolded case_prod_unfold]:
  includes lifting_syntax
  fixes r :: \<open>'rep\<Rightarrow>'abs\<Rightarrow>bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(snd with_type_class_finite r ===> (\<longleftrightarrow>)) (fst with_type_class_finite (Collect (Domainp r))) (\<lambda>_::unit. class.finite TYPE('abs))\<close>
  unfolding class.finite_def with_type_class_finite_def fst_conv
  by transfer_prover

lemma with_type_compat_rel_finite': \<open>with_type_compat_rel (fst with_type_class_finite) S (snd with_type_class_finite)\<close>
  by (auto simp: with_type_class_finite_def with_type_compat_rel_def)

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>finite\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_finite\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_finite'},
  rep_class_data_thm = NONE,
  transfer = SOME @{thm finite_transfer'}
}
\<close>

subsection \<open>Semigroup, additive\<close>

subsection \<open>XXX\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>semigroup_add\<close>\<close>

(* local_setup \<open>define_stuff \<^here> \<^class>\<open>ab_semigroup_add\<close>\<close> *)

subsection \<open>Example\<close>

experiment
begin

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>

lemma carrier_nonempty: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup: \<open>with_type_semigroup_add_class_pred carrier carrier_plus\<close>
  by (auto simp: with_type_semigroup_add_class_pred_def
      with_type_semigroup_add_class_dom_def with_type_semigroup_add_class_pred'_def carrier_def carrier_plus_def)

lemma example_semigroup2:
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

lemma example_type:
  includes lifting_syntax
  shows \<open>with_type with_type_class_type undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs). undefined (3::nat))\<close>
  sorry

lemma example_finite:
  includes lifting_syntax
  shows \<open>with_type with_type_class_finite undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::finite). undefined (3::nat))\<close>
  sorry

ML \<open>
With_Type.with_type_cancel \<^context> @{thm example_semigroup2}
\<close>

end (* experiment *)

end (* theory *)
