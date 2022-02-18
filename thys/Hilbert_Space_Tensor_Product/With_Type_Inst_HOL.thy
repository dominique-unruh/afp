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

definition semigroup_on :: \<open>'rep set \<Rightarrow> ('rep\<Rightarrow>'rep\<Rightarrow>'rep) \<Rightarrow> bool\<close> where
  \<open>semigroup_on S p \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. p x y \<in> S) \<and> 
      (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. p (p x y) z = p x (p y z))\<close>

definition with_type_class_semigroup_add where
  \<open>with_type_class_semigroup_add = (semigroup_on, \<lambda>r. rel_fun r (rel_fun r r))\<close>

lemma semigroup_on_transfer: 
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (semigroup_on (Collect (Domainp r))) class.semigroup_add\<close>
  unfolding semigroup_on_def class.semigroup_add_def
  apply (rule with_type_split_aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto

lemma with_type_compat_rel_semigroup_on: 
  includes lifting_syntax
  shows \<open>with_type_compat_rel semigroup_on S (\<lambda>r. r ===> r ===> r)\<close>
  by (simp add: Domainp_rel_fun_iff bi_unique_left_unique semigroup_on_def with_type_compat_rel_def)

lemma semigroup_on_transfer': 
  includes lifting_syntax
  shows \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd with_type_class_semigroup_add r ===> (\<longleftrightarrow>)) (fst with_type_class_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
  by (auto simp add: with_type_class_semigroup_add_def intro!: semigroup_on_transfer)

lemma with_type_compat_rel_semigroup_on': \<open>with_type_compat_rel (fst with_type_class_semigroup_add) S (snd with_type_class_semigroup_add)\<close>
  by (simp add: with_type_compat_rel_semigroup_on with_type_class_semigroup_add_def)

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>semigroup_add\<close>,
    rep_class_data = \<^const_name>\<open>with_type_class_semigroup_add\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>

subsection \<open>Example\<close>

experiment
begin

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>

lemma carrier_nonempty: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup: \<open>semigroup_on carrier carrier_plus\<close>
  by (auto simp: semigroup_on_def carrier_def carrier_plus_def)

lemma example_semigroup2:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. undefined (3::nat)\<close>
  apply (rule with_typeI)
  apply (simp_all add: with_type_class_semigroup_add_def)
     apply (rule carrier_nonempty)
    apply (rule carrier_semigroup)
   apply (rule with_type_compat_rel_semigroup_on)
proof -
  include lifting_syntax
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>type_definition Rep Abs carrier\<close>
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    using \<open>type_definition Rep Abs carrier\<close> bi_unique_def r_def type_definition.Rep_inject by fastforce
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume [transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
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
