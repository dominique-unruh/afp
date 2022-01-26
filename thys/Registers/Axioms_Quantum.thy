section \<open>Quantum instantiation of registers\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Quantum.thy)

    # Type classes
    domain \<rightarrow> type

    # Types
    some_domain \<rightarrow> unit

    # Constants
    comp_update \<rightarrow> cblinfun_compose
    id_update \<rightarrow> id_cblinfun
    tensor_update \<rightarrow> tensor_op
    
    # Lemmas
    id_update_left \<rightarrow> cblinfun_compose_id_left
    id_update_right \<rightarrow> cblinfun_compose_id_right
    comp_update_assoc \<rightarrow> cblinfun_compose_assoc
    tensor_update_mult \<rightarrow> comp_tensor_op

    # Chapter name
    Generic laws about registers \<rightarrow> Generic laws about registers, instantiated quantumly
    Generic laws about complements \<rightarrow> Generic laws about complements, instantiated quantumly
*)

theory Axioms_Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
          Complex_Bounded_Operators.Complex_L2
          (* Finite_Tensor_Product *)
          Tensor_Product.Hilbert_Space_Tensor_Product
begin


unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)

type_synonym 'a update = \<open>('a ell2, 'a ell2) cblinfun\<close>

(* TODO define *)
(* TODO: is it meaningful for non-square operators? *)
axiomatization weak_star_topology :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) topology\<close>

definition preregister :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close> where
  \<open>preregister F \<longleftrightarrow> bounded_clinear F \<and> continuous_map weak_star_topology weak_star_topology F\<close>

lemma preregister_mult_right: \<open>preregister (\<lambda>a. a o\<^sub>C\<^sub>L z)\<close>
  apply (auto simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose
      preregister_def)
  sorry
lemma preregister_mult_left: \<open>preregister (\<lambda>a. z o\<^sub>C\<^sub>L a)\<close>
  apply (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose
      preregister_def)
  sorry

lemma comp_preregister: "preregister F \<Longrightarrow> preregister G \<Longrightarrow> preregister (G \<circ> F)"
  by (auto simp add: preregister_def continuous_map_compose comp_bounded_clinear)

lemma id_preregister: \<open>preregister id\<close>
  unfolding preregister_def by auto

lemma tensor_extensionality:
  \<open>preregister F \<Longrightarrow> preregister G \<Longrightarrow> (\<And>a b. F (tensor_op a b) = G (tensor_op a b)) \<Longrightarrow> F = G\<close>
  sorry

definition register :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close> where
  "register F \<longleftrightarrow> 
     bounded_clinear F
   \<and> continuous_map weak_star_topology weak_star_topology F
   \<and> F id_cblinfun = id_cblinfun 
   \<and> (\<forall>a b. F(a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b)
   \<and> (\<forall>a. F (a*) = (F a)*)"

lemma register_of_id: \<open>register F \<Longrightarrow> F id_cblinfun = id_cblinfun\<close>
  by (simp add: register_def)

lemma register_id: \<open>register id\<close>
  by (simp add: register_def complex_vector.module_hom_id)

lemma register_preregister: "register F \<Longrightarrow> preregister F"
  unfolding register_def preregister_def apply auto
  sorry

lemma register_comp: "register F \<Longrightarrow> register G \<Longrightarrow> register (G \<circ> F)"
  using bounded_clinear_compose continuous_map_compose apply (auto simp: o_def register_def)
  by blast

lemma register_mult: "register F \<Longrightarrow> cblinfun_compose (F a) (F b) = F (cblinfun_compose a b)"
  unfolding register_def
  by auto

lemma register_tensor_left: \<open>register (\<lambda>a. tensor_op a id_cblinfun)\<close>
  apply (auto simp add: comp_tensor_op register_def tensor_op_cbilinear tensor_op_adjoint)
  sorry

lemma register_tensor_right: \<open>register (\<lambda>a. tensor_op id_cblinfun a)\<close>
  apply (auto simp add: comp_tensor_op register_def tensor_op_cbilinear tensor_op_adjoint)
  sorry

definition register_pair ::
  \<open>('a update \<Rightarrow> 'c update) \<Rightarrow> ('b update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>register_pair F G = (if register F \<and> register G \<and> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a) then 
                        SOME R. (\<forall>a b. register R \<and> R (a\<otimes>\<^sub>ob) = F a o\<^sub>C\<^sub>L G b) else (\<lambda>_. 0))\<close>

lemma cbilinear_F_comp_G[simp]: \<open>clinear F \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. F a o\<^sub>C\<^sub>L G b)\<close>
  unfolding cbilinear_def
  by (auto simp add: clinear_iff bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right)

lemma register_pair_apply: 
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  shows \<open>(register_pair F G) (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close>
(*   unfolding register_pair_def
  apply (simp flip: assms(3))
  by (metis assms(1) assms(2) cbilinear_F_comp_G register_preregister tensor_lift_correct)x *)
  sorry

lemma register_pair_is_register:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  shows \<open>register (register_pair F G)\<close> 
  sorry
(* proof (unfold register_def, intro conjI allI)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    using assms register_def by blast+
  have [simp]: \<open>F id_cblinfun = id_cblinfun\<close> \<open>G id_cblinfun = id_cblinfun\<close>
    using assms(1,2) register_def by blast+
  show [simp]: \<open>clinear (register_pair F G)\<close>
    unfolding register_pair_def 
    using assms apply auto
    apply (rule tensor_lift_clinear)
    by (simp flip: assms(3))
  show \<open>register_pair F G id_cblinfun = id_cblinfun\<close>
    apply (simp flip: tensor_id)
    apply (subst register_pair_apply)
    using assms by simp_all
  have [simp]: \<open>clinear (\<lambda>y. register_pair F G (x o\<^sub>C\<^sub>L y))\<close> for x :: \<open>('a\<times>'b) update\<close>
    apply (rule clinear_compose[unfolded o_def, where g=\<open>register_pair F G\<close>])
    by (simp_all add: preregister_mult_left bounded_cbilinear.add_right clinearI)
  have [simp]: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L register_pair F G y)\<close> for x :: \<open>'c update\<close>
    apply (rule clinear_compose[unfolded o_def, where f=\<open>register_pair F G\<close>])
    by (simp_all add: preregister_mult_left bounded_cbilinear.add_right clinearI)
  have [simp]: \<open>clinear (\<lambda>x. register_pair F G (x o\<^sub>C\<^sub>L y))\<close> for y :: \<open>('a\<times>'b) update\<close>
    apply (rule clinear_compose[unfolded o_def, where g=\<open>register_pair F G\<close>])
    by (simp_all add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose clinearI)
  have [simp]: \<open>clinear (\<lambda>x. register_pair F G x o\<^sub>C\<^sub>L y)\<close> for y :: \<open>'c update\<close>
    apply (rule clinear_compose[unfolded o_def, where f=\<open>register_pair F G\<close>])
    by (simp_all add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose clinearI)
  have [simp]: \<open>F (x o\<^sub>C\<^sub>L y) = F x o\<^sub>C\<^sub>L F y\<close> for x y
    by (simp add: register_mult)
  have [simp]: \<open>G (x o\<^sub>C\<^sub>L y) = G x o\<^sub>C\<^sub>L G y\<close> for x y
    by (simp add: register_mult)
  have [simp]: \<open>clinear (\<lambda>a. (register_pair F G (a* ))* )\<close>
    apply (rule antilinear_o_antilinear[unfolded o_def, where f=\<open>adj\<close>])
     apply simp
    apply (rule antilinear_o_clinear[unfolded o_def, where g=\<open>adj\<close>])
    by (simp_all)
  have [simp]: \<open>F (a* ) = (F a)*\<close> for a
    using assms(1) register_def by blast
  have [simp]: \<open>G (b* ) = (G b)*\<close> for b
    using assms(2) register_def by blast

  fix a b
  show \<open>register_pair F G (a o\<^sub>C\<^sub>L b) = register_pair F G a o\<^sub>C\<^sub>L register_pair F G b\<close>
    apply (rule tensor_extensionality[THEN fun_cong, where x=b], simp_all)
    apply (rule tensor_extensionality[THEN fun_cong, where x=a], simp_all)
    apply (simp_all add: comp_tensor_op register_pair_apply assms(3))
    using assms(3)
    by (metis cblinfun_compose_assoc)
  have \<open>(register_pair F G (a* ))* = register_pair F G a\<close>
    apply (rule tensor_extensionality[THEN fun_cong, where x=a])
    by (simp_all add: tensor_op_adjoint register_pair_apply assms(3))
  then show \<open>register_pair F G (a* ) = register_pair F G a*\<close>
    by (metis double_adj)
qed *)

end
