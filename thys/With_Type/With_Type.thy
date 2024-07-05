theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets" Misc_With_Type Instantiate_Term_Antiquotation
begin

definition with_type_compat_rel where
  \<open>with_type_compat_rel C S R \<longleftrightarrow> 
      (\<forall>r rp. bi_unique r \<longrightarrow> right_total r \<longrightarrow> S = Collect (Domainp r) \<longrightarrow> C S rp \<longrightarrow> Domainp (R r) rp)\<close>

text \<open>
\<^term>\<open>S\<close> -- the carrier set of the representation of the type

\<^term>\<open>rep_ops\<close> -- operations of the representation type (i.e., operations like addition or similar)

\<^term>\<open>C\<close> -- the properties that \<^term>\<open>R\<close> and \<^term>\<open>rep_ops\<close> are guaranteed to satisfy
(basically, the type-class definition)

\<^term>\<open>R\<close> -- transfers a relation \<^term>\<open>r\<close> between representation and abstract type to a relation
between representation operations and abstract operations (\<^term>\<open>r\<close> is always bi-unique and right-total)

\<^term>\<open>P\<close> -- the predicate that we claim holds.
It can work on the type \<^typ>\<open>'abs\<close> (which is type-classed) but it also gets \<^term>\<open>Rep\<close> and \<^term>\<open>Abs\<close>
so that it can transfer things back and forth.

If \<^term>\<open>P\<close> does not contain \<^typ>\<open>'abs\<close>, we can erase the \<^term>\<open>with_type\<close> using the \<open>Types_To_Sets\<close> mechanism.
See lemma \<open>erasure_example\<close> below.


The intuitive meaning of \<^term>\<open>with_type (C,R) (S,rep_ops) P\<close> is that \<^term>\<open>P\<close> holds for
any type \<^typ>\<open>'t\<close> that that can be represented by a concrete representation (S,rep_ops)
and that has a type class matching the specification (C,R).
\<close>
definition \<open>with_type = (\<lambda>(C,R) (S,rep_ops) P. S\<noteq>{} \<and> C S rep_ops \<and> with_type_compat_rel C S R
    \<and> (\<forall>Rep Abs abs_ops. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs))\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> ('rep \<Rightarrow> 'abs) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep_ops\<close>

definition with_type_type_class where \<open>with_type_type_class = ((\<lambda>_ (_::unit). True), (\<lambda>_. (=)))\<close>

lemma with_type_compat_rel_type: \<open>with_type_compat_rel (fst with_type_type_class) S (snd with_type_type_class)\<close>
  by (simp add: with_type_type_class_def with_type_compat_rel_def Domainp_iff)

(* Demonstration *)
lemma \<open>with_type with_type_type_class (S,()) P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>
  by (auto simp: with_type_def with_type_type_class_def with_type_compat_rel_def)

lemma with_typeI:
  fixes Sp :: \<open>'a set \<times> 'c\<close> and CR
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C S p\<close>
  assumes \<open>with_type_compat_rel C S R\<close>
  assumes \<open>\<And>Rep Abs abs_ops. type_definition Rep Abs S \<Longrightarrow> R (\<lambda>x y. x = Rep y) p abs_ops \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type CR Sp P\<close>
  using assms
  by (auto simp add: with_type_def case_prod_beta)

lemma with_type_mp: 
  assumes \<open>with_type CR (S,p) P\<close>
  shows \<open>(\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> fst CR S p \<Longrightarrow> P Rep Abs \<Longrightarrow> Q Rep Abs) \<Longrightarrow> with_type CR (S,p) Q\<close>
  using assms by (auto simp add: with_type_def case_prod_beta)

lemma with_type_nonempty: \<open>with_type CR Sp P \<Longrightarrow> fst Sp \<noteq> {}\<close>
  by (simp add: with_type_def case_prod_beta)

lemma with_type_prepare_cancel:
  fixes Sp :: \<open>'rep set \<times> _\<close>
  assumes wt: \<open>with_type CR Sp (\<lambda>_ (_::'rep\<Rightarrow>'abs). P)\<close>
  assumes ex: \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs (fst Sp))\<close>
  shows P
proof -
  define S p C R where \<open>S = fst Sp\<close> and \<open>p = snd Sp\<close> and \<open>C = fst CR\<close> and \<open>R = snd CR\<close>
  with ex obtain Rep :: \<open>'abs\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [simp]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    using r_def td typedef_bi_unique apply blast
    by (simp add: r_def right_totalI)
  have Sr: \<open>S = Collect (Domainp r)\<close>
    using type_definition.Rep[OF td] 
    apply (auto simp: r_def intro!: DomainPI)
    apply (subst type_definition.Abs_inverse[OF td])
    by auto
  from wt have nice: \<open>with_type_compat_rel C S R\<close> and \<open>C S p\<close>
    by (simp_all add: with_type_def p_def R_def S_def C_def case_prod_beta)
  from nice[unfolded with_type_compat_rel_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = Rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from td abs_ops wt
  show P
    by (auto simp: with_type_def case_prod_beta S_def p_def R_def)
qed

(* lemma Domainp_rel_fun_iff: (* TODO: use Domainp_pred_fun_eq instead *)
  includes lifting_syntax
  assumes \<open>left_unique R\<close>
  shows \<open>Domainp (R ===> S) p \<longleftrightarrow> (\<forall>x. Domainp R x \<longrightarrow> Domainp S (p x))\<close>
  using Domainp_pred_fun_eq[OF assms, of S]
  by auto *)

lemma with_type_split_aux:
  includes lifting_syntax
  assumes \<open>(R ===> (\<longleftrightarrow>)) A B\<close>
  assumes \<open>\<And>x. Domainp R x \<Longrightarrow> C x\<close>
  shows \<open>(R ===> (\<longleftrightarrow>)) (\<lambda>x. C x \<and> A x) B\<close>
  by (smt (verit) DomainPI assms(1) assms(2) rel_fun_def)

lemma bi_unique_left_unique: \<open>bi_unique R \<Longrightarrow> left_unique R\<close>
  by (simp add: bi_unique_alt_def)
lemma bi_unique_right_unique: \<open>bi_unique R \<Longrightarrow> right_unique R\<close>
  by (simp add: bi_unique_alt_def)

lemma with_type_class_axioms:
  includes lifting_syntax
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and CR :: \<open>_ \<times> (('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool))\<close>
    and Sp
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>with_type_compat_rel C S R2\<close>
  assumes wt: \<open>with_type CR Sp P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs_ops2. axioms x\<close>
proof -
  from ex obtain Rep :: \<open>'abs2\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r x y = (x = Rep y)\<close> for x y
  have bi_unique_r: \<open>bi_unique r\<close>
    using bi_unique_def td type_definition.Rep_inject r_def by fastforce
  have right_total_r: \<open>right_total r\<close>
    by (simp add: right_totalI r_def)
  have right_total_R[transfer_rule]: \<open>right_total (r ===> r ===> r)\<close>
    by (meson bi_unique_r right_total_r bi_unique_alt_def right_total_fun)
  note trans = trans[OF bi_unique_r, OF right_total_r, transfer_rule]

  from td
  have rS: \<open>Collect (Domainp r) = S\<close>
    apply (auto simp: r_def Domainp_iff type_definition.Rep)
    by (meson type_definition.Rep_cases)

  from wt have sg: \<open>C S p\<close>
    by (simp_all add: with_type_def C_def S_def p_def case_prod_beta)

  with nice have \<open>Domainp (R2 r) p\<close>
    by (simp add: bi_unique_r with_type_compat_rel_def rS right_total_r)
  
  with sg
  have \<open>\<exists>x :: 'abs_ops2. axioms x\<close>
    apply (transfer' fixing: R2 S p)
    using apply_rsp' local.trans rS by fastforce
  
  then obtain abs_plus :: 'abs_ops2 
    where abs_plus: \<open>axioms abs_plus\<close>
    apply atomize_elim by auto

  then show ?thesis
    by auto
qed

ML_file "with_type.ML"

attribute_setup cancel_with_type = 
  \<open>Thm.rule_attribute [] (With_Type.with_type_cancel o Context.proof_of) |> Scan.succeed\<close>
  \<open>Transforms (\<forall>\<^sub>\<tau> 't=\<dots>. P) into P\<close>

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>type\<close>,
  rep_class_data = \<^const_name>\<open>with_type_type_class\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_type},
  rep_class_data_thm = NONE,
  transfer = NONE
}
\<close>

syntax "_with_type" :: "type \<Rightarrow> 'a => 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_. _" [0,0,10] 10)
syntax "_with_type_with" :: "type \<Rightarrow> 'a => args \<Rightarrow> 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_ with _. _" [0,0,10] 10)
parse_translation \<open>[
  (\<^syntax_const>\<open>_with_type\<close>, With_Type.with_type_parse_translation),
  (\<^syntax_const>\<open>_with_type_with\<close>, With_Type.with_type_parse_translation)
]\<close>

term \<open>\<forall>\<^sub>\<tau>'t::type = N. (rep_t = rep_t)\<close>
(* term \<open>\<forall>\<^sub>\<tau>'t::type = N with pls. (rep_t = rep_t)\<close> *)





end
