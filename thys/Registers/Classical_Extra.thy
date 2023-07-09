section \<open>Derived facts about classical references\<close>

theory Classical_Extra
  imports Laws_Classical Misc
begin

hide_const (open) Disjoint_Sets.disjoint
hide_fact (open) Disjoint_Sets.disjoint_def

lemma reference_from_getter_setter_of_getter_setter[simp]: \<open>reference_from_getter_setter (getter F) (setter F) = F\<close> if \<open>reference F\<close>
  by (metis getter_of_reference_from_getter_setter reference_def setter_of_reference_from_getter_setter that)

lemma valid_getter_setter_getter_setter[simp]: \<open>valid_getter_setter (getter F) (setter F)\<close> if \<open>reference F\<close>
  by (metis getter_of_reference_from_getter_setter reference_def setter_of_reference_from_getter_setter that)

lemma reference_reference_from_getter_setter[simp]: \<open>reference (reference_from_getter_setter g s)\<close> if \<open>valid_getter_setter g s\<close>
  using reference_def that by blast

definition \<open>total_fun f = (\<forall>x. f x \<noteq> None)\<close>

lemma reference_total:
  assumes \<open>reference F\<close>
  assumes \<open>total_fun a\<close>
  shows \<open>total_fun (F a)\<close>
  using assms 
  by (auto simp: reference_def total_fun_def reference_from_getter_setter_def option.case_eq_if)

lemma reference_apply:
  assumes \<open>reference F\<close>
  shows \<open>Some o reference_apply F a = F (Some o a)\<close>
proof -
  have \<open>total_fun (F (Some o a))\<close>
    using assms apply (rule reference_total)
    by (auto simp: total_fun_def)
  then show ?thesis
    by (auto simp: reference_apply_def dom_def total_fun_def)
qed

lemma reference_empty:
  assumes \<open>prereference F\<close>
  shows \<open>F Map.empty = Map.empty\<close>
  using assms unfolding prereference_def by auto

lemma disjoint_setter:
  fixes F :: \<open>('a,'c) prereference\<close> and G :: \<open>('b,'c) prereference\<close>
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close>
  shows \<open>Laws_Classical.disjoint F G \<longleftrightarrow> (\<forall>a b. setter F a o setter G b = setter G b o setter F a)\<close>
proof (intro allI iffI)
  fix a b
  assume \<open>disjoint F G\<close>
  then show \<open>setter F a o setter G b = setter G b o setter F a\<close>
    apply (rule_tac disjoint_setter)
    unfolding disjoint_def by auto
next
  assume commute[rule_format, THEN fun_cong, unfolded o_def]: \<open>\<forall>a b. setter F a \<circ> setter G b = setter G b \<circ> setter F a\<close>
  have \<open>valid_getter_setter (getter F) (setter F)\<close>
    by auto
  then have \<open>F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a\<close> for a b
    apply (subst (2) reference_from_getter_setter_of_getter_setter[symmetric, of F], simp)
    apply (subst (1) reference_from_getter_setter_of_getter_setter[symmetric, of F], simp)
    apply (subst (2) reference_from_getter_setter_of_getter_setter[symmetric, of G], simp)
    apply (subst (1) reference_from_getter_setter_of_getter_setter[symmetric, of G], simp)
    unfolding reference_from_getter_setter_def valid_getter_setter_def
    apply (auto intro!: ext simp: option.case_eq_if map_comp_def)
      (* Sledgehammer: *)
          apply ((metis commute option.distinct option.simps)+)[4]
      apply (smt (verit, ccfv_threshold) assms(2) commute valid_getter_setter_def valid_getter_setter_getter_setter)
     apply (smt (verit, ccfv_threshold) assms(2) commute valid_getter_setter_def valid_getter_setter_getter_setter)
    by (smt (verit, del_insts) assms(2) commute option.inject valid_getter_setter_def valid_getter_setter_getter_setter)
  then show \<open>disjoint F G\<close>
    unfolding disjoint_def by auto
qed

lemma reference_from_getter_setter_disjointI[intro]:
  assumes [simp]: \<open>valid_getter_setter g s\<close> \<open>valid_getter_setter g' s'\<close>
  assumes \<open>\<And>x y m. s x (s' y m) = s' y (s x m)\<close>
  shows \<open>disjoint (reference_from_getter_setter g s) (reference_from_getter_setter g' s')\<close>
  apply (subst disjoint_setter)
  using assms by auto

lemma separating_update1:
  \<open>separating TYPE(_) {update1 x y | x y. True}\<close>
  by (smt (verit) mem_Collect_eq separating_def update1_extensionality)

definition "permutation_reference (p::'b\<Rightarrow>'a) = reference_from_getter_setter p (\<lambda>a _. inv p a)"

lemma permutation_reference_reference[simp]: 
  fixes p :: "'b \<Rightarrow> 'a"
  assumes [simp]: "bij p"
  shows "reference (permutation_reference p)"
  apply (auto intro!: reference_reference_from_getter_setter simp: permutation_reference_def valid_getter_setter_def bij_inv_eq_iff)
  by (meson assms bij_inv_eq_iff)

lemma getter_permutation_reference: \<open>bij p \<Longrightarrow> getter (permutation_reference p) = p\<close>
  by (smt (verit, ccfv_threshold) bij_inv_eq_iff getter_of_reference_from_getter_setter permutation_reference_def valid_getter_setter_def)

lemma setter_permutation_reference: \<open>bij p \<Longrightarrow> setter (permutation_reference p) a m = inv p a\<close>
  by (metis bij_inv_eq_iff getter_permutation_reference permutation_reference_reference valid_getter_setter_def valid_getter_setter_getter_setter)

definition empty_var :: \<open>'a::{CARD_1} update \<Rightarrow> 'b update\<close> where
  "empty_var = reference_from_getter_setter (\<lambda>_. undefined) (\<lambda>_ m. m)"

lemma valid_empty_var[simp]: \<open>valid_getter_setter (\<lambda>_. (undefined::_::CARD_1)) (\<lambda>_ m. m)\<close>
  by (simp add: valid_getter_setter_def)

lemma reference_empty_var[simp]: \<open>reference empty_var\<close>
  using empty_var_def reference_def valid_empty_var by blast

lemma getter_empty_var[simp]: \<open>getter empty_var m = undefined\<close>
  by (rule everything_the_same)

lemma setter_empty_var[simp]: \<open>setter empty_var a m = m\<close>
  by (simp add: empty_var_def setter_of_reference_from_getter_setter)

lemma empty_var_disjoint[simp]: \<open>disjoint empty_var X\<close> if [simp]: \<open>reference X\<close>
  apply (subst disjoint_setter) by auto

lemma empty_var_disjoint'[simp]: \<open>reference X \<Longrightarrow> disjoint X empty_var\<close>
  using disjoint_sym empty_var_disjoint by blast

paragraph \<open>Example\<close>

record memory = 
  x :: "int*int"
  y :: nat

definition "X = reference_from_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)"
definition "Y = reference_from_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)"

lemma validX[simp]: \<open>valid_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma referenceX[simp]: \<open>reference X\<close>
  using X_def reference_def validX by blast

lemma validY[simp]: \<open>valid_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma referenceY[simp]: \<open>reference Y\<close>
  using Y_def reference_def validY by blast

lemma disjointXY[simp]: \<open>disjoint X Y\<close>
  unfolding X_def Y_def by auto

(* Avoiding namespace pollution *)
hide_const (open) x y x_update y_update X Y

end
