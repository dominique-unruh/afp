section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports
    Complex_Bounded_Operators.Complex_L2
    Misc_Tensor_Product  
    "HOL-Library.Function_Algebras" 
    "HOL-ex.Sketch_and_Explore" 
    Misc_Tensor_Product_TTS
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"

(* TODO move *)
lemma butterfly_sum_left: \<open>butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. butterfly (\<psi> i) \<phi>)\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_left)

(* TODO move *)
lemma butterfly_sum_right: \<open>butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. butterfly \<psi> (\<phi> i))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_right)


lemma trunc_ell2_singleton: \<open>trunc_ell2 {x} \<psi> = Rep_ell2 \<psi> x *\<^sub>C ket x\<close>
  apply transfer by auto

lemma trunc_ell2_insert: \<open>trunc_ell2 (insert x M) \<psi> = trunc_ell2 M \<psi> + Rep_ell2 \<psi> x *\<^sub>C ket x\<close> if \<open>x \<notin> M\<close>
  using trunc_ell2_union_disjoint[where M=M and N=\<open>{x}\<close> and \<psi>=\<psi>]
  using that by (auto simp: trunc_ell2_singleton)

lemma trunc_ell2_finite_sum: \<open>trunc_ell2 M \<psi> = (\<Sum>i\<in>M. Rep_ell2 \<psi> i *\<^sub>C ket i)\<close> if \<open>finite M\<close>
  using that apply induction by (auto simp: trunc_ell2_insert)

lemma bounded_clinear_cblinfun_compose_left: \<open>bounded_clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose)
lemma bounded_clinear_cblinfun_compose_right: \<open>bounded_clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose)
lemma clinear_cblinfun_compose_left: \<open>clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose bounded_clinear.clinear)
lemma clinear_cblinfun_compose_right: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_clinear.clinear bounded_clinear_cblinfun_compose_right)

(* TODO: rename \<rightarrow> norm_isometry_compose' *)
lemma norm_isometry_o': \<open>norm (A o\<^sub>C\<^sub>L U) = norm A\<close> if \<open>isometry (U*)\<close>
  by (smt (verit, ccfv_threshold) adj_0 cblinfun_assoc_right(1) cblinfun_compose_id_right cblinfun_compose_zero_right double_adj isometryD isometry_partial_isometry mult_cancel_left2 norm_adj norm_cblinfun_compose norm_partial_isometry norm_zero that)

lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and norm: \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
proof -
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (space_as_set V)"
    then interpret T: local_typedef \<open>space_as_set V\<close> \<open>TYPE('t)\<close>
      by unfold_locales

    note orthonormal_basis_exists
    note this[unfolded ud_with]
    note this[unoverload_type 'a]
    note this[unfolded ud_with]
    note this[where 'a='t]
    note this[untransferred]
    note this[where plus=plus and scaleC=scaleC and scaleR=scaleR and zero=0 and minus=minus
        and uminus=uminus and sgn=sgn and S=S and norm=norm and cinner=cinner and dist=dist
        and ?open=\<open>openin (top_of_set (space_as_set V))\<close>
        and uniformity=\<open>uniformity_on (space_as_set V)\<close>]
    note this[simplified Domainp_rel_filter prod.Domainp_rel T.Domainp_cr_S]
  }    
  note * = this[cancel_type_definition]
  have 1: \<open>uniformity_on (space_as_set V)
    \<le> principal (Collect (pred_prod (\<lambda>x. x \<in> space_as_set V) (\<lambda>x. x \<in> space_as_set V)))\<close>
    by (auto simp: uniformity_dist intro!: le_infI2)
  have \<open>\<exists>B\<in>{A. \<forall>x\<in>A. x \<in> space_as_set V}.
     S \<subseteq> B \<and> is_onb_ow (space_as_set V) (*\<^sub>C) (+) 0 norm (openin (top_of_set (space_as_set V))) (\<bullet>\<^sub>C) B\<close>
    apply (rule * )
    using \<open>S \<subseteq> space_as_set V\<close> \<open>is_ortho_set S\<close>
    by (auto simp flip: ud_with
        intro!: complex_vector.subspace_scale real_vector.subspace_scale csubspace_is_subspace
        csubspace_nonempty complex_vector.subspace_add complex_vector.subspace_diff
        complex_vector.subspace_neg sgn_in_spaceI 1 norm)

  then obtain B where \<open>B \<subseteq> space_as_set V\<close> and \<open>S \<subseteq> B\<close>
    and is_onb: \<open>is_onb_ow (space_as_set V) (*\<^sub>C) (+) 0 norm (openin (top_of_set (space_as_set V))) (\<bullet>\<^sub>C) B\<close>
    by auto

  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>cspan B \<inter> space_as_set V = cspan B\<close>
    by (smt (verit) basic_trans_rules(8) ccspan.rep_eq ccspan_leqI ccspan_superset complex_vector.span_span inf_absorb1 less_eq_ccsubspace.rep_eq)
  then have [simp]: \<open>space_as_set V \<inter> cspan B = cspan B\<close>
    by blast
  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>space_as_set V \<inter> closure (cspan B) = closure (cspan B)\<close>
    by (metis Int_absorb1 ccspan.rep_eq ccspan_leqI less_eq_ccsubspace.rep_eq)
  have [simp]: \<open>closure X \<union> X = closure X\<close> for X :: \<open>'z::topological_space set\<close>
    using closure_subset by blast

  from is_onb have \<open>is_ortho_set B\<close>
    by (auto simp: is_onb_ow_def ud_with)

  moreover from is_onb have \<open>norm x = 1\<close> if \<open>x \<in> B\<close> for x
    by (auto simp: is_onb_ow_def that)

  moreover from is_onb have \<open>closure (cspan B) = space_as_set V\<close>
    by (simp add: is_onb_ow_def \<open>B \<subseteq> space_as_set V\<close>
        closure_ow_with_typeclass span_ow_on_typeclass flip: ud_with)
  then have \<open>ccspan B = V\<close>
    by (simp add: ccspan.abs_eq space_as_set_inverse)

  ultimately show ?thesis
    using \<open>S \<subseteq> B\<close> by auto
qed

unbundle no_cblinfun_notation

end
