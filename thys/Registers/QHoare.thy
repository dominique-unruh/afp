section \<open>Very simple Quantum Hoare logic\<close>

theory QHoare
  imports Quantum_Extra
begin

locale qhoare =
  fixes memory_type :: "'mem itself"
begin

type_synonym 'm statement = \<open>'m update list\<close>
type_synonym 'm program = \<open>'m statement list\<close>

definition \<open>seq P Q = [q o\<^sub>C\<^sub>L p. p \<leftarrow> P, q \<leftarrow> Q]\<close> for P Q :: \<open>'mem statement\<close>
definition \<open>program S = foldr seq S [id_cblinfun]\<close> for S :: \<open>'mem program\<close>
definition \<open>apply U R = [R U]\<close> for R :: \<open>'a update \<Rightarrow> 'mem update\<close>
definition \<open>ifthenelse R M P Q = seq [R (Proj (ccspan (ket ` M)))] (program P) @
                                 seq [R (Proj (ccspan (ket ` (-M))))] (program Q)\<close>
  for R :: \<open>'a update \<Rightarrow> 'mem update\<close> and P Q :: \<open>'mem program\<close>

definition hoare :: \<open>'mem ell2 ccsubspace \<Rightarrow> 'mem program \<Rightarrow> 'mem ell2 ccsubspace \<Rightarrow> bool\<close> where
  \<open>hoare C p D \<longleftrightarrow> (\<forall>\<psi> \<in> space_as_set C. \<forall>A \<in> set (program p). A *\<^sub>V \<psi> \<in> space_as_set D)\<close> for C p D

definition EQ :: \<open>('a update \<Rightarrow> 'mem update) \<Rightarrow> 'a ell2 \<Rightarrow> 'mem ell2 ccsubspace\<close> (infix "=\<^sub>q" 75) where
  \<open>EQ R \<psi> = R (proj \<psi>) *\<^sub>S \<top>\<close>

lemma seq_assoc: \<open>seq (seq P Q) R = seq P (seq Q R)\<close>
  apply (induction P)
  by (simp_all add: map_concat o_def seq_def cblinfun_compose_assoc)

lemma program_seq: \<open>program (p1@p2) = seq (program p1) (program p2)\<close>
  apply (induction p1)
   apply (simp add: program_def seq_def)
  by (simp add: program_def seq_assoc)

lemma hoare_seq[trans]: \<open>hoare C p1 D \<Longrightarrow> hoare D p2 E \<Longrightarrow> hoare C (p1@p2) E\<close>
  by (auto simp: program_seq hoare_def seq_def)

lemma hoare_weaken_left[trans]: \<open>A \<le> B \<Longrightarrow> hoare B p C \<Longrightarrow> hoare A p C\<close>
  unfolding hoare_def
  by (meson in_mono less_eq_ccsubspace.rep_eq) 

lemma hoare_weaken_right[trans]: \<open>hoare A p B \<Longrightarrow> B \<le> C \<Longrightarrow> hoare A p C\<close>
  unfolding hoare_def 
  by (meson in_mono less_eq_ccsubspace.rep_eq) 

lemma hoare_skip: \<open>C \<le> D \<Longrightarrow> hoare C [] D\<close>
  by (auto simp: program_def hoare_def in_mono less_eq_ccsubspace.rep_eq)

lemma hoare_apply: 
  assumes \<open>R U *\<^sub>S pre \<le> post\<close>
  shows \<open>hoare pre [apply U R] post\<close>
  using assms apply (auto simp: hoare_def program_def apply_def seq_def)
  by (metis (no_types, lifting) cblinfun_image.rep_eq closure_subset imageI less_eq_ccsubspace.rep_eq subsetD)

lemma hoare_ifthenelse:
  fixes R :: \<open>'a update \<Rightarrow> 'mem update\<close>
  assumes \<open>hoare (R (Proj (ccspan (ket ` M))) *\<^sub>S pre) P post\<close>
  assumes \<open>hoare (R (Proj (ccspan (ket ` (-M)))) *\<^sub>S pre) Q post\<close>
  shows \<open>hoare pre [ifthenelse R M P Q] post\<close>
  using assms
  by (auto simp: program_def[of \<open>[_]\<close>] hoare_def ifthenelse_def butterfly_def seq_def cblinfun_apply_in_image')

end

end
