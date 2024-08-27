theory Misc_With_Type
  imports Main
begin

(* TODO cleanup *)

lemma distinct_prems_rl_protected: \<open>PROP Pure.prop (PROP A \<Longrightarrow> PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP Pure.prop (PROP A \<Longrightarrow> PROP B)\<close>
  unfolding Pure.prop_def by (rule distinct_prems_rl)

definition \<open>rel_square r = r OO r\<inverse>\<inverse>\<close>

lemma rel_square_eq[simp]: \<open>rel_square (=) = (=)\<close>
  by (simp add: eq_OO rel_square_def)

lemma Domainp_rel_square: \<open>Domainp (rel_square r) = Domainp r\<close>
  by (auto intro!: ext simp: Domainp_iff rel_square_def)

lemma equiv_rel_square: 
  assumes \<open>right_total r\<close> and \<open>right_unique r\<close>
  shows \<open>equiv (Collect (Domainp r)) (Collect (case_prod (rel_square r)))\<close>
proof (rule equivI)
  show \<open>refl_on (Collect (Domainp r)) {(x, y). rel_square r x y}\<close>
    by (smt (verit) Domainp_iff OO_def case_prodI conversep_iff mem_Collect_eq refl_on_def' rel_square_def split_cong)
  show \<open>sym {(x, y). rel_square r x y}\<close>
    by (metis CollectD CollectI converse_relcompp conversep_conversep conversep_iff curryE curryI curry_case_prod rel_square_def symI)
  show \<open>trans {(x, y). rel_square r x y}\<close>
    by (smt (verit, best) CollectD CollectI OO_def assms(2) case_prodD conversep_iff curryE curry_case_prod rel_square_def right_unique_def transI)
qed

lemma type_definition_bij_betw_iff: \<open>type_definition rep (inv rep) S \<longleftrightarrow> bij_betw rep UNIV S\<close>
  by (smt (verit, best) UNIV_I bij_betw_def bij_betw_iff_bijections inj_on_def inv_f_eq type_definition.Rep_inject type_definition.Rep_range type_definition.intro)

inductive rel_unit_itself :: \<open>unit \<Rightarrow> 'a itself \<Rightarrow> bool\<close> where
\<comment> \<open>A canonical relation between \<^typ>\<open>unit\<close> and \<^typ>\<open>'a itself\<close>.
  Note that while the latter may not be a singleton type, in many situations we treat it as 
  one by only using the element \<^term>\<open>TYPE('a)\<close>.\<close>
  \<open>rel_unit_itself () TYPE('a)\<close>

lemma Domain_rel_unit_itself[simp]: \<open>Domainp rel_unit_itself x\<close>
  by (simp add: Domainp_iff rel_unit_itself.simps)
lemma [simp]: \<open>rel_unit_itself () y \<longleftrightarrow> (y = TYPE('a))\<close>
  by (simp add: rel_unit_itself.simps)


end