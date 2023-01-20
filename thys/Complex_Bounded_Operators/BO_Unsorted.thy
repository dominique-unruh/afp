text \<open>Files in this directory are intended to be added to other theory files when the next AFP 
      release is near. The reason why they are currently held in a separate file is that this will
      lessen the severity of merge conflicts due to changes made to the Complex_Bounded_Operators
      session in the development branch of the AFP by the AFP maintainers.\<close>

theory BO_Unsorted
  imports Complex_L2
begin

lemma bounded_clinear_Rep_ell2[simp, bounded_clinear]: \<open>bounded_clinear (\<lambda>\<psi>. Rep_ell2 \<psi> x)\<close>
  apply (subst asm_rl[of \<open>(\<lambda>\<psi>. Rep_ell2 \<psi> x) = (\<lambda>\<psi>. ket x \<bullet>\<^sub>C \<psi>)\<close>])
   apply (auto simp: cinner_ket_left) 
  by (simp add: bounded_clinear_cinner_right)

lemma norm_is_Proj_nonzero: \<open>norm P = 1\<close> if \<open>is_Proj P\<close> and \<open>P \<noteq> 0\<close> for P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof (rule antisym)
  show \<open>norm P \<le> 1\<close>
    by (simp add: norm_is_Proj that(1))
  from \<open>P \<noteq> 0\<close>
  have \<open>range P \<noteq> 0\<close>
    by (metis cblinfun_eq_0_on_UNIV_span complex_vector.span_UNIV rangeI set_zero singletonD)
  then obtain \<psi> where \<open>\<psi> \<in> range P\<close> and \<open>\<psi> \<noteq> 0\<close>
    by force
  then have \<open>P \<psi> = \<psi>\<close>
    using is_Proj.rep_eq is_projection_on_fixes_image is_projection_on_image that(1) by blast
  then show \<open>norm P \<ge> 1\<close>
    apply (rule_tac cblinfun_norm_geqI[of _ _ \<psi>])
    using \<open>\<psi> \<noteq> 0\<close> by simp
qed


end
