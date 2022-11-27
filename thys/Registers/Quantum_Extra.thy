section \<open>Derived facts about quantum registers\<close>

theory Quantum_Extra
  imports
    Laws_Quantum
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle lattice_syntax
unbundle register_notation
unbundle cblinfun_notation

lemma zero_not_register[simp]: \<open>~ register (\<lambda>_. 0)\<close>
  unfolding register_def by simp

lemma register_pair_is_register_converse:
  \<open>register (F;G) \<Longrightarrow> register F\<close> \<open>register (F;G) \<Longrightarrow> register G\<close>
  using [[simproc del: Laws_Quantum.compatibility_warn]]
   apply (cases \<open>register F\<close>)
    apply (auto simp: register_pair_def)[2]
  apply (cases \<open>register G\<close>)
  by (auto simp: register_pair_def)[2]

lemma register_id'[simp]: \<open>register (\<lambda>x. x)\<close>
  using register_id by (simp add: id_def)

lemma compatible_proj_intersect:
  (* I think this also holds without is_Proj premises, but my proof ideas use the Penrose-Moore 
     pseudoinverse or simultaneous diagonalization and we do not have an existence theorem for either. *)
  assumes "compatible R S" and "is_Proj a" and "is_Proj b"
  shows "(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) = ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)"
proof (rule antisym)
  have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (S b *\<^sub>S \<top>)"
    apply (subst swap_registers[OF assms(1)])
    by (simp add: cblinfun_compose_image cblinfun_image_mono)
  moreover have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>)"
    by (simp add: cblinfun_compose_image cblinfun_image_mono)
  ultimately show \<open>((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>)\<close>
    by auto

  have "is_Proj (R a)"
    using assms(1) assms(2) compatible_register1 register_projector by blast
  have "is_Proj (S b)"
    using assms(1) assms(3) compatible_register2 register_projector by blast
  show \<open>(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) \<le> (R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>\<close>
  proof (unfold less_eq_ccsubspace.rep_eq, rule)
    fix \<psi>
    assume asm: \<open>\<psi> \<in> space_as_set ((R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>))\<close>
    then have \<open>\<psi> \<in> space_as_set (R a *\<^sub>S \<top>)\<close>
      by auto
    then have R: \<open>R a *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>is_Proj (R a)\<close> cblinfun_fixes_range is_Proj_algebraic by blast
    from asm have \<open>\<psi> \<in> space_as_set (S b *\<^sub>S \<top>)\<close>
      by auto
    then have S: \<open>S b *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>is_Proj (S b)\<close> cblinfun_fixes_range is_Proj_algebraic by blast
    from R S have \<open>\<psi> = (R a o\<^sub>C\<^sub>L S b) *\<^sub>V \<psi>\<close>
      by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      apply simp by (metis R S calculation cblinfun_apply_in_image)
    finally show \<open>\<psi> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      by -
  qed
qed

lemma compatible_proj_mult:
  assumes "compatible R S" and "is_Proj a" and "is_Proj b"
  shows "is_Proj (R a o\<^sub>C\<^sub>L S b)"
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using assms unfolding is_Proj_algebraic compatible_def
  apply auto
   apply (metis (no_types, lifting) cblinfun_compose_assoc register_mult)
  by (simp add: assms(2) assms(3) is_proj_selfadj register_projector)

lemma sandwich_tensor: 
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  assumes [simp]: \<open>unitary a\<close> \<open>unitary b\<close>
  shows "(*\<^sub>V) (sandwich (a \<otimes>\<^sub>o b)) = sandwich a \<otimes>\<^sub>r sandwich b"
  apply (rule tensor_extensionality)
  by (auto simp: unitary_sandwich_register sandwich_apply register_tensor_is_register
      comp_tensor_op tensor_op_adjoint unitary_tensor_op intro!: register_preregister unitary_sandwich_register)

lemma sandwich_grow_left:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes "unitary a"
  shows "sandwich a \<otimes>\<^sub>r id = sandwich (a \<otimes>\<^sub>o id_cblinfun)"
  by (simp add: unitary_sandwich_register sandwich_tensor assms id_def)

lemma register_sandwich: \<open>register F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) register_def sandwich_apply)

lemma assoc_ell2_sandwich: \<open>assoc = sandwich assoc_ell2\<close>
  apply (rule tensor_extensionality3')
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_apply assoc_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor
      flip: tensor_ell2_ket)

lemma assoc_ell2'_sandwich: \<open>assoc' = sandwich (assoc_ell2*)\<close>
  apply (rule tensor_extensionality3)
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_apply assoc'_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor 
           flip: tensor_ell2_ket)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_apply unitary_sandwich_register)[2]
  apply (rule tensor_ell2_extensionality)
  by (simp add: sandwich_apply cblinfun_apply_cblinfun_compose tensor_op_ell2)

(* TODO move *)
lemma unitary_tensor_op: \<open>unitary a \<Longrightarrow> unitary b \<Longrightarrow> unitary (a \<otimes>\<^sub>o b)\<close>
  unfolding unitary_def by (simp add: tensor_op_adjoint comp_tensor_op)

lemma id_tensor_sandwich: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2"
  assumes "unitary a"
  shows "id \<otimes>\<^sub>r sandwich a = sandwich (id_cblinfun \<otimes>\<^sub>o a)"
  apply (rule tensor_extensionality) 
  using assms
  by (auto simp: register_tensor_is_register comp_tensor_op sandwich_apply tensor_op_adjoint unitary_sandwich_register
      intro!: register_preregister unitary_sandwich_register unitary_tensor_op)

lemma compatible_selfbutter_join:
  assumes [register]: "compatible R S"
  shows "R (selfbutter \<psi>) o\<^sub>C\<^sub>L S (selfbutter \<phi>) = (R; S) (selfbutter (\<psi> \<otimes>\<^sub>s \<phi>))"
  apply (subst register_pair_apply[symmetric, where F=R and G=S])
  using assms by auto

lemma register_mult':
  assumes \<open>register F\<close>
  shows \<open>F a *\<^sub>V F b *\<^sub>V c = F (a o\<^sub>C\<^sub>L b) *\<^sub>V c\<close>
  by (simp add: assms lift_cblinfun_comp(4) register_mult)

lemma register_scaleC:
  assumes \<open>register F\<close> shows \<open>F (c *\<^sub>C a) = c *\<^sub>C F a\<close>
  using assms [[simproc del: Laws_Quantum.compatibility_warn]] 
  unfolding register_def
  by (simp add: bounded_clinear.clinear clinear.scaleC)

lemma register_adjoint: "F (a*) = (F a)*" if \<open>register F\<close>
  using register_def that by blast

(* TODO move *)
lemma finite_rank_cfinite_dim[simp]: \<open>finite_rank (a :: 'a :: {cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b :: complex_normed_vector)\<close>
proof -
  obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
    using is_onb_some_chilbert_basis by blast
  from \<open>is_onb B\<close> have [simp]: \<open>finite B\<close>
    by (auto intro!: cindependent_cfinite_dim_finite is_ortho_set_cindependent simp add: is_onb_def)
  have [simp]: \<open>cspan B = UNIV\<close>
  proof -
    from \<open>is_onb B\<close> have \<open>ccspan B = \<top>\<close>
      using is_onb_def by blast
    then have \<open>closure (cspan B) = UNIV\<close>
      by (metis ccspan.rep_eq space_as_set_top)
    then show ?thesis
      by simp
  qed
  have a_sum: \<open>a = (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b)\<close>
  proof (rule cblinfun_eq_on_UNIV_span[OF \<open>cspan B = UNIV\<close>])
    fix s assume [simp]: \<open>s \<in> B\<close>
    with \<open>is_onb B\<close> have \<open>norm s = 1\<close>
      by (simp add: is_onb_def)
    have 1: \<open>j \<noteq> s \<Longrightarrow> j \<in> B \<Longrightarrow> (a o\<^sub>C\<^sub>L selfbutter j) *\<^sub>V s = 0\<close> for j
      apply auto
      by (metis \<open>is_onb B\<close> \<open>s \<in> B\<close> cblinfun.scaleC_right is_onb_def is_ortho_set_def scaleC_eq_0_iff)
    have 2: \<open>a *\<^sub>V s = (if s \<in> B then (a o\<^sub>C\<^sub>L selfbutter s) *\<^sub>V s else 0)\<close>
      using \<open>norm s = 1\<close> \<open>s \<in> B\<close> by (simp add: cnorm_eq_1)
    show \<open>a *\<^sub>V s = (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b) *\<^sub>V s\<close>
      apply (subst cblinfun.sum_left)
      apply (subst sum_single[where i=s])
      using 1 2 by auto
  qed
  have \<open>rank1 (a o\<^sub>C\<^sub>L selfbutter b)\<close> for b
    by (simp add: cblinfun_comp_butterfly)
  then have \<open>finite_rank (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b)\<close>
    by (metis (no_types, lifting) Compact_Operators.rank1_def finite_rank_butterfly finite_rank_sum)
  with a_sum show ?thesis
    by simp
qed

(* TODO move *)
lemma id_onb_sum_cfinite_dim: \<open>id_cblinfun = (\<Sum>x\<in>B. selfbutter x)\<close> if \<open>is_onb B\<close> for B :: \<open>'a :: {cfinite_dim, chilbert_space} set\<close>
proof (rule cblinfun_eq_gen_eqI)
  from \<open>is_onb B\<close> show \<open>ccspan B = \<top>\<close>
    by (simp add: is_onb_def)
  from \<open>is_onb B\<close> have \<open>cindependent B\<close>
    by (simp add: is_onb_def is_ortho_set_cindependent)
  then have [simp]: \<open>finite B\<close>
    using cindependent_cfinite_dim_finite by blast
  from \<open>is_onb B\<close>
  have 1: \<open>j \<noteq> b \<Longrightarrow> j \<in> B \<Longrightarrow> is_orthogonal j b\<close> if \<open>b \<in> B\<close> for j b
    using that by (auto simp add: is_onb_def is_ortho_set_def)
  from \<open>is_onb B\<close>
  have 2: \<open>b \<bullet>\<^sub>C b = 1\<close> if \<open>b \<in> B\<close> for b
    using that by (simp add: is_onb_def cnorm_eq_1)
  fix b assume \<open>b \<in> B\<close>
  then show \<open>id_cblinfun *\<^sub>V b = (\<Sum>x\<in>B. selfbutter x) *\<^sub>V b\<close>
    using 1 2 by (simp add: cblinfun.sum_left sum_single[where i=b])
qed

(* TODO move *)
lemma wot_is_norm_topology_findim[simp]:
  \<open>(cweak_operator_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have \<open>continuous_map euclidean cweak_operator_topology id\<close>
    by (simp add: id_def cweak_operator_topology_weaker_than_euclidean)
  moreover have \<open>continuous_map cweak_operator_topology euclidean (id :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> _)\<close>
  proof (rule continuous_map_iff_preserves_convergence)
    fix l and F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) filter\<close>
    assume lim_wot: \<open>limitin cweak_operator_topology id l F\<close>
    obtain A :: \<open>'a set\<close> where \<open>is_onb A\<close>
      using is_onb_some_chilbert_basis by blast
    then have idA: \<open>id_cblinfun = (\<Sum>x\<in>A. selfbutter x)\<close>
      using id_onb_sum_cfinite_dim by blast
    obtain B :: \<open>'b set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    then have idB: \<open>id_cblinfun = (\<Sum>x\<in>B. selfbutter x)\<close>
      using id_onb_sum_cfinite_dim by blast
    from lim_wot have \<open>((\<lambda>x. b \<bullet>\<^sub>C (x *\<^sub>V a)) \<longlongrightarrow> b \<bullet>\<^sub>C (l *\<^sub>V a)) F\<close> for a b
      by (simp add: limitin_cweak_operator_topology)
    then have \<open>((\<lambda>x. (b \<bullet>\<^sub>C (x *\<^sub>V a)) *\<^sub>C butterfly b a) \<longlongrightarrow> (b \<bullet>\<^sub>C (l *\<^sub>V a)) *\<^sub>C butterfly b a) F\<close> for a b
      by (simp add: tendsto_scaleC)
    then have \<open>((\<lambda>x. selfbutter b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (selfbutter b o\<^sub>C\<^sub>L l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a b
      by (simp add: cblinfun_comp_butterfly)
    then have \<open>((\<lambda>x. \<Sum>b\<in>B. selfbutter b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (\<Sum>b\<in>B. selfbutter b o\<^sub>C\<^sub>L l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a
      by (rule tendsto_sum)
    then have \<open>((\<lambda>x. x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a
      by (simp add: flip: cblinfun_compose_sum_left idB)
    then have \<open>((\<lambda>x. \<Sum>a\<in>A. x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (\<Sum>a\<in>A. l o\<^sub>C\<^sub>L selfbutter a)) F\<close>
      by (rule tendsto_sum)
    then have \<open>(id \<longlongrightarrow> l) F\<close>
      by (simp add: flip: cblinfun_compose_sum_right idA id_def)
    then show \<open>limitin euclidean id (id l) F\<close>
      by simp
  qed
  ultimately show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed

(* TODO move *)
lemma weak_star_topology_is_norm_topology_fin_dim[simp]: 
  \<open>(weak_star_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have 1: \<open>continuous_map euclidean weak_star_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp add: id_def weak_star_topology_weaker_than_euclidean)
  have \<open>continuous_map weak_star_topology cweak_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: id_def wot_weaker_than_weak_star)
  then have 2: \<open>continuous_map weak_star_topology euclidean (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: wot_is_norm_topology_findim)
  from 1 2
  show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed


(* TODO move *)
lemma sot_is_norm_topology_fin_dim[simp]: 
  \<open>(cstrong_operator_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have 1: \<open>continuous_map euclidean cstrong_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp add: id_def cstrong_operator_topology_weaker_than_euclidean)
  have \<open>continuous_map cstrong_operator_topology cweak_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (metis eq_id_iff wot_weaker_than_sot)
  then have 2: \<open>continuous_map cstrong_operator_topology euclidean (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: wot_is_norm_topology_findim)
  from 1 2
  show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed


lemma register_finite_dim: \<open>register F \<longleftrightarrow> clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
  for F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
    (* I conjecture that this holds even when only 'a is finite. *)
proof
  assume \<open>register F\<close>
  then show \<open>clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
    unfolding register_def
    by (auto simp add: bounded_clinear_def)
next
  assume asm: \<open>clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
  then have \<open>clinear F\<close>
    by simp
  then have \<open>bounded_clinear F\<close>
    by simp
  then have \<open>continuous_map euclidean euclidean F\<close>
    by (auto intro!: continuous_at_imp_continuous_on clinear_continuous_at)
  then have wstar: \<open>continuous_map weak_star_topology weak_star_topology F\<close>
    by simp
  from asm \<open>bounded_clinear F\<close> wstar
  show \<open>register F\<close>
    unfolding register_def by simp
qed

end

