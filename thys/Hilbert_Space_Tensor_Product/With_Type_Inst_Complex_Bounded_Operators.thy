theory With_Type_Inst_Complex_Bounded_Operators
  imports With_Type_Inst_HOL Complex_Bounded_Operators.Complex_Bounded_Linear_Function
begin

ML \<open>Class.rules \<^theory> \<^class>\<open>complex_vector\<close> |> fst\<close>

ML \<open>val (relationT, relationR, relationD, relationThm) = get_relation_thm \<^context> \<^class>\<open>complex_vector\<close>\<close>

ML \<open>fun local_def binding t = Local_Theory.define ((binding, Mixfix.NoSyn), ((Binding.suffix_name "_def" binding, []), t)) #> snd\<close>

local_setup \<open>local_def \<^binding>\<open>with_type_class_complex_vector_rel\<close> (Type.legacy_freeze relationR)\<close>

local_setup \<open>local_def \<^binding>\<open>with_type_class_complex_vector_dom\<close> (Type.legacy_freeze relationD)\<close>

thm with_type_class_complex_vector_rel_def
thm with_type_class_complex_vector_dom_def
term with_type_class_complex_vector_dom

definition \<open>with_type_class_complex_vector_pred S p \<longleftrightarrow> with_type_class_complex_vector_dom S p \<and> undefined ''rest'' p\<close>

definition with_type_class_complex_vector where
  \<open>with_type_class_complex_vector = (with_type_class_complex_vector_pred,
                                     with_type_class_complex_vector_rel)\<close>

schematic_goal with_type_class_complex_vector_transfer: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open> 
    (snd with_type_class_complex_vector r ===> (\<longleftrightarrow>)) ?X 
    (\<lambda>(scaleR, scaleC, plus, zero, minus, uminus). class.complex_vector scaleR scaleC plus zero minus uminus)\<close>
  unfolding with_type_class_complex_vector_def with_type_class_complex_vector_pred_def fst_conv snd_conv
    class.complex_vector_def class.complex_vector_axioms_def
  apply transfer_prover_start
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
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  thm class.comm_monoid_add_def
  apply (rule with_type_split_aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto x
  apply (auto simp add: intro!: semigroup_on_transfer) x
  by -

lemma with_type_compat_rel_conj1I:
  assumes \<open>with_type_compat_rel A S R\<close>
  shows \<open>with_type_compat_rel (\<lambda>S p. A S p \<and> B S p) S R\<close>
  using assms by (auto simp: with_type_compat_rel_def)

lemma with_type_compat_relI_weak_leq:
  assumes \<open>\<And>r. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> C (Collect (Domainp r)) \<le> Domainp (R r)\<close>
  shows \<open>with_type_compat_rel C S R\<close>
  unfolding with_type_compat_rel_def
  using assms by auto


lemma pred_fun_top[simp]: \<open>pred_fun A \<top> = \<top>\<close>
  by auto

lemma pred_prod_top[simp]: \<open>pred_prod \<top> \<top> = \<top>\<close>
  by auto

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>complex_vector\<close>,
    rep_class_data = \<^const_name>\<open>with_type_class_complex_vector\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>


subsection \<open>Complex Hilbert space\<close>



definition with_type_class_chilbert_space where
  \<open>with_type_class_chilbert_space = (undefined, \<lambda>r. rel_fun r (rel_fun r r))\<close>

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>chilbert\<close>,
    rep_class_data = \<^const_name>\<open>with_type_class_semigroup_add\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>



end
