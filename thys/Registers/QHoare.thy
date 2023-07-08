section \<open>Very simple Quantum Hoare logic\<close>

theory QHoare
  imports Quantum_Extra
begin

locale qhoare =
  fixes memory_type :: "'mem itself"
begin

type_synonym 'm statement = \<open>'m ell2 \<Rightarrow> 'm ell2 list\<close>

definition \<open>seq P Q \<psi> = [\<gamma>. \<phi> \<leftarrow> P \<psi>, \<gamma> \<leftarrow> Q \<phi>]\<close> for P Q :: \<open>'mem statement\<close>
definition skip :: \<open>'m statement\<close> where \<open>skip \<psi> = [\<psi>]\<close>
definition \<open>program S = foldr seq S skip\<close> for S :: \<open>'mem statement list\<close>
  \<comment> \<open>Convenience abbreviation: List of statements as repeated seq\<close>
definition \<open>apply U R \<psi> = [R U *\<^sub>V \<psi>]\<close> for R :: \<open>'a update \<Rightarrow> 'mem update\<close>
definition \<open>ifthenelse R x P Q \<psi> = P (R (proj (ket x)) \<psi>) @
                                   Q (R (proj (ket (binary_other x))) \<psi>)\<close>
  for R :: \<open>'a::binary update \<Rightarrow> 'mem update\<close> and P Q :: \<open>'mem statement\<close>

definition hoare :: \<open>'mem ell2 ccsubspace \<Rightarrow> 'mem statement \<Rightarrow> 'mem ell2 ccsubspace \<Rightarrow> bool\<close> where
  \<open>hoare C p D \<longleftrightarrow> (\<forall>\<psi> \<in> space_as_set C. set (p \<psi>) \<subseteq> space_as_set D)\<close> for C p D

definition EQ :: \<open>('a update \<Rightarrow> 'mem update) \<Rightarrow> 'a ell2 \<Rightarrow> 'mem ell2 ccsubspace\<close> (infix "=\<^sub>q" 75) where
  \<open>EQ R \<psi> = R (proj \<psi>) *\<^sub>S \<top>\<close>

lemma seq_skip[simp]: \<open>seq P skip = P\<close> and \<open>seq skip P = P\<close>
  by (auto simp: seq_def skip_def)

lemma seq_assoc: \<open>seq (seq P Q) R = seq P (seq Q R)\<close>
proof (rule ext)
  fix \<psi>
  define P\<psi> where \<open>P\<psi> = P \<psi>\<close>
  show \<open>seq (seq P Q) R \<psi> = seq P (seq Q R) \<psi>\<close>
    apply (simp add: seq_def flip: P\<psi>_def)
    apply (induction P\<psi>)
    by auto
qed

lemma program_seq: \<open>program (p1@p2) = seq (program p1) (program p2)\<close>
  apply (induction p1)
   apply (simp add: program_def seq_def skip_def)
  by (simp add: program_def seq_assoc)

lemma hoare_seq[trans]: \<open>hoare C p1 D \<Longrightarrow> hoare D p2 E \<Longrightarrow> hoare C (seq p1 p2) E\<close>
  by (auto simp: hoare_def seq_def)

lemma hoare_weaken_left[trans]: \<open>A \<le> B \<Longrightarrow> hoare B p C \<Longrightarrow> hoare A p C\<close>
  unfolding hoare_def
  by (meson in_mono less_eq_ccsubspace.rep_eq) 

lemma hoare_weaken_right[trans]: \<open>hoare A p B \<Longrightarrow> B \<le> C \<Longrightarrow> hoare A p C\<close>
  by (auto simp add: hoare_def less_eq_ccsubspace.rep_eq)

lemma hoare_skip: \<open>C \<le> D \<Longrightarrow> hoare C skip D\<close>
  by (auto simp: skip_def hoare_def less_eq_ccsubspace.rep_eq)

lemma hoare_apply: 
  assumes \<open>R U *\<^sub>S pre \<le> post\<close>
  shows \<open>hoare pre (apply U R) post\<close>
  using assms apply (auto simp: hoare_def apply_def seq_def)
  by (metis (no_types, lifting) cblinfun_image.rep_eq closure_subset imageI less_eq_ccsubspace.rep_eq subsetD)

lemma hoare_ifthenelse:
  fixes R :: \<open>'a::binary update \<Rightarrow> 'mem update\<close>
  assumes \<open>hoare (R (selfbutterket x) *\<^sub>S pre) P post\<close>
  assumes \<open>hoare (R (selfbutterket (binary_other x)) *\<^sub>S pre) Q post\<close>
  shows \<open>hoare pre (ifthenelse R x P Q) post\<close>
  using assms
  by (auto simp: hoare_def ifthenelse_def cblinfun_apply_in_image' simp flip: butterfly_eq_proj)

end

end
