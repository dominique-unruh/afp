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

definition selfadjoint :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>selfadjoint a \<longleftrightarrow> a* = a\<close>

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma sandwich_unitary_commutant: 
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>sandwich U ` commutant X = commutant (sandwich U ` X)\<close>
proof (rule Set.set_eqI)
  fix x
  let ?comm = \<open>\<lambda>a b. a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close>
  have \<open>x \<in> sandwich U ` commutant X \<longleftrightarrow> sandwich (U*) x \<in> commutant X\<close>
    apply (subst inj_image_mem_iff[symmetric, where f=\<open>sandwich (U*)\<close>])
    by (auto intro!: inj_sandwich_isometry simp: image_image
        simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm (sandwich (U*) x) y)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm x (sandwich U y))\<close>
    apply (rule ball_cong, simp)
    apply (simp add: sandwich_apply)
    by (smt (verit) assms cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD1 unitaryD2)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>sandwich U ` X. ?comm x y)\<close>
  by fast
  also have \<open>\<dots> \<longleftrightarrow> x \<in> commutant (sandwich U ` X)\<close>
    by (simp add: commutant_def)
  finally show \<open>(x \<in> (*\<^sub>V) (sandwich U) ` commutant X) \<longleftrightarrow> (x \<in> commutant ((*\<^sub>V) (sandwich U) ` X))\<close>
    by -
qed


unbundle no_cblinfun_notation

end
