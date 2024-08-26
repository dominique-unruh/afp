theory Experiment
  imports With_Type
begin

unbundle lifting_syntax
definition \<open>WITH_TYPE_CLASS_semigroup_add S p \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. p a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. p a (p b c) = p (p a b) c)\<close>
definition \<open>WITH_TYPE_REL_semigroup_add r = (r ===> r ===> r)\<close>

lemma WITH_TYPE_semigroup_add: \<open>with_type_compat_rel WITH_TYPE_CLASS_semigroup_add S WITH_TYPE_REL_semigroup_add\<close>
  by (auto intro!: simp: with_type_compat_rel_def WITH_TYPE_CLASS_semigroup_add_def
      WITH_TYPE_REL_semigroup_add_def Domainp_pred_fun_eq bi_unique_alt_def)

setup \<open>
With_Type.add_with_type_info_global {
class = \<^class>\<open>semigroup_add\<close>,
rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_semigroup_add\<close>,
rep_rel = \<^const_name>\<open>WITH_TYPE_REL_semigroup_add\<close>,
with_type_compat_rel = @{thm WITH_TYPE_semigroup_add},
transfer = NONE
}
\<close>

lemma \<open>\<forall>\<^sub>\<tau> 't::semigroup_add = XXX with ZZZ. YYY\<close>


definition \<open>with_type2 = (\<lambda>(C,R) (S,rep_ops) abs_ops P. S\<noteq>{} \<and> C S rep_ops \<and> with_type_compat_rel C S R
    \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs))\<close>



lemma \<open>a + (b + c) = (a + b) + c\<close>
  for a b c :: \<open>'a::semigroup_add\<close>
  by (simp add: add.assoc)


definition \<open>mygroup = {0::int}\<close>
definition \<open>myplus x y = (x::int)\<close>

definition \<open>WITH_TYPE_CLASS_semigroup_add S p \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. p a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. p a (p b c) = p (p a b) c)\<close>
definition \<open>WITH_TYPE_REL_semigroup_add r = (r ===> r ===> r)\<close>

lemma mysemigroup: \<open>WITH_TYPE_CLASS_semigroup_add mygroup myplus\<close>
  by (auto intro!: simp: WITH_TYPE_CLASS_semigroup_add_def myplus_def)

lemma myrel: \<open>with_type_compat_rel WITH_TYPE_CLASS_semigroup_add mygroup WITH_TYPE_REL_semigroup_add\<close>
  by (auto intro!: simp: with_type_compat_rel_def WITH_TYPE_CLASS_semigroup_add_def
      WITH_TYPE_REL_semigroup_add_def mygroup_def
      Domainp_pred_fun_eq bi_unique_alt_def)

lemma rt:
  assumes \<open>bi_unique r\<close> 
  assumes \<open>right_total r\<close>
  shows \<open>right_total (WITH_TYPE_REL_semigroup_add r)\<close>
  using assms 
  by (auto intro!: right_total_fun simp: WITH_TYPE_REL_semigroup_add_def bi_unique_alt_def)

lemma myneq0: \<open>mygroup \<noteq> {}\<close>
  by (simp add: mygroup_def)

lemma 1: \<open>a + a = a\<close>
  if td: \<open>type_definition Rep Abs mygroup\<close>
    and rel: \<open>WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) myplus (+)\<close>
  for a :: \<open>'t :: semigroup_add\<close> and Rep :: \<open>'t \<Rightarrow> _\<close>
proof -
  interpret type_definition Rep Abs mygroup
    by (rule td)
  define r where \<open>r x y \<longleftrightarrow> x = Rep y\<close> for x y
  have [iff, transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [iff, transfer_rule]: \<open>right_total r\<close> 
    by (auto intro!: right_totalI simp: r_def)
  from rel
  have trans_plus[transfer_rule]: \<open>(r ===> r ===> r) myplus plus\<close>
    by (simp add: WITH_TYPE_REL_semigroup_add_def flip: r_def) 
  show ?thesis
    apply transfer
    by (simp add: myplus_def)
qed

axiomatization fake_prop :: bool
lemma fake_thm: \<open>(\<forall>a::'t::semigroup_add. a+a=a) \<Longrightarrow> fake_prop\<close>
  sorry

lemma wt_thm_1: \<open>with_type2 (WITH_TYPE_CLASS_semigroup_add, WITH_TYPE_REL_semigroup_add :: (_ \<Rightarrow> 't \<Rightarrow> _) \<Rightarrow> _ \<Rightarrow> _)
 (mygroup, myplus) (plus :: 't\<Rightarrow>_\<Rightarrow>_) (\<lambda>rep abs. \<forall>a::'t::semigroup_add. a+a=a)\<close>
  by (auto intro!: simp: with_type2_def 1 mysemigroup myneq0 myrel)

lemma wt_thm_2: \<open>with_type2 (WITH_TYPE_CLASS_semigroup_add, WITH_TYPE_REL_semigroup_add :: (_ \<Rightarrow> 't::semigroup_add \<Rightarrow> _) \<Rightarrow> _ \<Rightarrow> _)
 (mygroup, myplus) (plus :: 't\<Rightarrow>_\<Rightarrow>_) (\<lambda>rep abs. fake_prop)\<close>
  using wt_thm_1
  by (auto intro!: simp: with_type2_def fake_thm)

lemma fake_prop if td: \<open>type_definition Rep Abs mygroup\<close>
  for Rep :: \<open>'t::semigroup_add \<Rightarrow> _\<close> and Abs
proof -
  interpret type_definition Rep Abs mygroup
    by (rule td)
  define r where \<open>r x y \<longleftrightarrow> x = Rep y\<close> for x y
  define R where \<open>R = WITH_TYPE_REL_semigroup_add r\<close>
  have [iff, transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [iff, transfer_rule]: \<open>right_total r\<close> 
    by (auto intro!: right_totalI simp: r_def)
  from wt_thm_2
  have \<open>mygroup \<noteq> {}\<close> 
    by (auto simp add: with_type2_def)
  from wt_thm_2    
  have sem: \<open>WITH_TYPE_CLASS_semigroup_add mygroup myplus\<close> 
    by (auto simp add: with_type2_def)
  from wt_thm_2
  have rel: \<open>with_type_compat_rel WITH_TYPE_CLASS_semigroup_add mygroup (WITH_TYPE_REL_semigroup_add :: (_ \<Rightarrow> 't \<Rightarrow> _) \<Rightarrow> _ \<Rightarrow> _)\<close>
    by (auto simp add: with_type2_def)
  have dom_r: \<open>mygroup = Collect (Domainp r)\<close>
    apply (auto intro!: Rep elim!: Rep_cases simp: r_def Domainp_iff )
    by -
  have dom: \<open>Domainp R myplus\<close>
    unfolding R_def
    apply (rule rel[unfolded with_type_compat_rel_def, rule_format, where r=r])
    by (auto intro!: dom_r sem simp: )

  from rt (* Should come from with-type *)
  have \<open>right_total R\<close>
    using R_def by blast
  then obtain plus' where \<open>R plus' plus\<close>
    apply atomize_elim
    by (auto intro!: simp: right_total_def)


(* Imagine:

S = size-eight-type
myplus = XOR on 3-bit-strings
plus = + mod 8

 *)

  have 2: \<open>\<exists>Rep'. inj Rep' \<and> WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep' y) myplus plus\<close>
    by xxx
  sorry

  from wt_thm_2
  have \<open>type_definition Rep Abs mygroup \<Longrightarrow> (WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) myplus plus) \<Longrightarrow>
            fake_prop\<close> for Rep :: \<open>'t::semigroup_add \<Rightarrow> _\<close> and Abs
    apply (auto intro!: simp: with_type2_def)
    by -

  have 

  with td have   \<open>R myplus plus \<Longrightarrow>           fake_prop\<close>
    by (simp add: R_def r_def[abs_def])

qed

end
