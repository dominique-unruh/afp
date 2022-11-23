section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports
    Complex_Bounded_Operators.Complex_L2
    Misc_Tensor_Product  
    "HOL-Library.Function_Algebras" 
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

unbundle no_cblinfun_notation

end
