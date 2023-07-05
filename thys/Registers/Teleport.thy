section \<open>Quantum teleportation\<close>

theory Teleport
  imports 
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Word"
    QHoare
    Tensor_Product_Matrices
    Complex_Bounded_Operators.Cblinfun_Code
begin

hide_const (open) Finite_Cartesian_Product.vec
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.row
hide_const (open) Finite_Cartesian_Product.column
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle no_vec_syntax
unbundle no_inner_syntax

text \<open>We first declare a locale that declares the registers we use,
      only assuming that they are mutually compatible.
      This makes it very easy to reuse the result in different concrete settings
      by instantiating the registers.\<close>
locale teleport_locale = qhoare "TYPE('mem)" +
  fixes X :: "bit update \<Rightarrow> 'mem update"
    and \<Phi> :: "(bit*bit) update \<Rightarrow> 'mem update"
    and A :: "'atype update \<Rightarrow> 'mem update"
    and B :: "'btype update \<Rightarrow> 'mem update"
  assumes compat[register]: "mutually compatible (X,\<Phi>,A,B)"
begin

text \<open>Several abbreviations for readability.\<close>

abbreviation "\<Phi>1 \<equiv> \<Phi> \<circ> Fst"
abbreviation "\<Phi>2 \<equiv> \<Phi> \<circ> Snd"
abbreviation "X\<Phi>2 \<equiv> (X;\<Phi>2)"
abbreviation "X\<Phi>1 \<equiv> (X;\<Phi>1)"
abbreviation "X\<Phi> \<equiv> (X;\<Phi>)"
abbreviation "XAB \<equiv> ((X;A); B)"
abbreviation "AB \<equiv> (A;B)"
abbreviation "\<Phi>2AB \<equiv> ((\<Phi> o Snd; A); B)"

text \<open>The teleportation program.\<close>

definition "teleport = [
    apply CNOT X\<Phi>1,
    apply hadamard X,
    ifthenelse \<Phi>1 {1} [apply pauliX \<Phi>2] [],
    ifthenelse X {1} [apply pauliZ \<Phi>2] []
  ]"

text \<open>In the following, we declare various rewriting rules for the registers at hand.
  These are simple rules to be able to rewrite subterms written in terms of a specific register
  (e.g., \<^term>\<open>\<Phi>1 x\<close>) in terms of a bigger register (e.g., \<^term>\<open>\<Phi> (x \<otimes>\<^sub>o id_cblinfun)\<close> when needed.\<close>

lemma \<Phi>_X\<Phi>: \<open>\<Phi> a = X\<Phi> (id_cblinfun \<otimes>\<^sub>o a)\<close>
  by (auto simp: register_pair_apply)
lemma X\<Phi>1_X\<Phi>: \<open>X\<Phi>1 a = X\<Phi> (assoc (a \<otimes>\<^sub>o id_cblinfun))\<close>
  apply (subst pair_o_assoc[unfolded o_def, of X \<Phi>1 \<Phi>2, simplified, THEN fun_cong])
  by (auto simp: register_pair_apply)
lemma X\<Phi>2_X\<Phi>: \<open>X\<Phi>2 a = X\<Phi> ((id \<otimes>\<^sub>r swap) (assoc (a \<otimes>\<^sub>o id_cblinfun)))\<close>
  apply (subst pair_o_tensor[unfolded o_def, THEN fun_cong], simp, simp, simp)
  apply (subst (2) register_Fst_register_Snd[symmetric, of \<Phi>], simp)
  using [[simproc del: compatibility_warn]]
  apply (subst pair_o_swap[unfolded o_def], simp)
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong], simp, simp, simp)
  by (auto simp: register_pair_apply)
lemma \<Phi>2_X\<Phi>: \<open>\<Phi>2 a = X\<Phi> (id_cblinfun \<otimes>\<^sub>o (id_cblinfun \<otimes>\<^sub>o a))\<close>
  by (auto simp: Snd_def register_pair_apply)
lemma X_X\<Phi>: \<open>X a = X\<Phi> (a \<otimes>\<^sub>o id_cblinfun)\<close>
  by (auto simp: register_pair_apply)
lemmas to_X\<Phi> = \<Phi>_X\<Phi> X\<Phi>1_X\<Phi> X\<Phi>2_X\<Phi> \<Phi>2_X\<Phi> X_X\<Phi>

lemma XAB_to_X\<Phi>2_AB: \<open>XAB a = (X\<Phi>2;AB) ((swap \<otimes>\<^sub>r id) (assoc' (id_cblinfun \<otimes>\<^sub>o assoc a)))\<close>
  by (simp add: pair_o_tensor[unfolded o_def, THEN fun_cong] register_pair_apply
      pair_o_swap[unfolded o_def, THEN fun_cong]
      pair_o_assoc'[unfolded o_def, THEN fun_cong]
      pair_o_assoc[unfolded o_def, THEN fun_cong])

lemma X\<Phi>2_to_X\<Phi>2_AB: \<open>X\<Phi>2 a = (X\<Phi>2;AB) (a \<otimes>\<^sub>o id_cblinfun)\<close>
  by (simp add: register_pair_apply)

schematic_goal \<Phi>2AB_to_X\<Phi>2_AB: "\<Phi>2AB a = (X\<Phi>2;AB) ?b"
  apply (subst pair_o_assoc'[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  apply (subst register_pair_apply[where a=id_cblinfun])
   apply simp_all[2]
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  by simp

lemmas to_X\<Phi>2_AB = XAB_to_X\<Phi>2_AB  X\<Phi>2_to_X\<Phi>2_AB  \<Phi>2AB_to_X\<Phi>2_AB

lemma X_to_X\<Phi>2: \<open>X x = X\<Phi>2 (x \<otimes>\<^sub>o id_cblinfun)\<close>
  by (simp add: register_pair_apply)
lemma \<Phi>2_to_X\<Phi>2: \<open>\<Phi>2 x = X\<Phi>2 (id_cblinfun \<otimes>\<^sub>o x)\<close>
  by (simp add: register_pair_apply)
lemmas to_X\<Phi>2 = X_to_X\<Phi>2  \<Phi>2_to_X\<Phi>2

text \<open>The main theorem: correctness of the teleportation.\<close>

lemma teleport: \<open>hoare (XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) teleport (\<Phi>2AB =\<^sub>q \<psi>)\<close>
proof -
  define XZ :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit update\<close> where "XZ a b = (if a=1 then (if b=1 then pauliZ o\<^sub>C\<^sub>L pauliX else pauliX) else (if b=1 then pauliZ else id_cblinfun))" for a b

  define pre where "pre = XAB =\<^sub>q \<psi>"

  define O1 where "O1 = \<Phi> (selfbutter \<beta>00)"
  have \<open>(XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) = O1 *\<^sub>S pre\<close>
    unfolding pre_def O1_def EQ_def
    apply (subst compatible_proj_intersect[where R=XAB and S=\<Phi>])
    by (simp_all add: butterfly_eq_proj swap_registers[where R=XAB and S=\<Phi>] cblinfun_assoc_left(2))

  also
  define O2 where "O2 = X\<Phi>1 CNOT o\<^sub>C\<^sub>L O1"
  have \<open>hoare (O1 *\<^sub>S pre) [apply CNOT X\<Phi>1] (O2 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O2_def cblinfun_assoc_left(2))

  also
  define O3' where \<open>O3' a' b' a b = (1/2) *\<^sub>C \<Phi>2 (XZ a b*) o\<^sub>C\<^sub>L X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a' \<otimes>\<^sub>s ket b') \<beta>00)\<close> for a b a' b'
  have \<open>hoare (O2 *\<^sub>S pre) [apply hadamard X] (\<Squnion>(a,b)\<in>UNIV. O3' a b a b *\<^sub>S pre)\<close>
  proof -
    have \<open>X hadamard o\<^sub>C\<^sub>L O2 = (\<Sum>(a,b)\<in>UNIV. O3' a b a b)\<close>
      unfolding O2_def O1_def O3'_def
      apply (simp split del: if_split only: to_X\<Phi> register_mult[of X\<Phi>])
      apply (simp split del: if_split
          add: register_mult[of X\<Phi>] clinear_register UNIV_bit XZ_def assoc_ell2_sandwich insert_Times_insert' 
          flip: complex_vector.linear_scale complex_vector.linear_add[of X\<Phi>] UNIV_Times_UNIV
          del: comp_apply insert_Times_insert)
      apply (rule arg_cong[of _ _ X\<Phi>])
      apply (rule cblinfun_eq_mat_of_cblinfunI)
      apply (simp add: assoc_ell2_sandwich mat_of_cblinfun_tensor_op XZ_def mat_of_cblinfun_plus
          butterfly_def mat_of_cblinfun_compose mat_of_cblinfun_vector_to_cblinfun
          mat_of_cblinfun_adj vec_of_basis_enum_ket mat_of_cblinfun_id
          swap_sandwich[abs_def] mat_of_cblinfun_scaleR mat_of_cblinfun_scaleC
          id_tensor_sandwich vec_of_basis_enum_tensor_state mat_of_cblinfun_cblinfun_apply
          mat_of_cblinfun_sandwich)
      by normalization (* Slow (time used for code compilation?) *)
    then have *: \<open>X hadamard *\<^sub>S O2 *\<^sub>S pre \<le> (\<Squnion>(a,b)\<in>UNIV. O3' a b a b *\<^sub>S pre)\<close>
      by (simp add: cblinfun_sum_image_distr case_prod_beta flip: cblinfun_compose_image)
    then show ?thesis
      apply (rule_tac hoare_apply) by simp
  qed

  also
  have \<open>hoare (\<Squnion>(a,b)\<in>UNIV. O3' a b a b *\<^sub>S pre)
              [ifthenelse \<Phi>1 {1} [apply pauliX \<Phi>2] []]
              (\<Squnion>(a,b)\<in>UNIV. O3' a b 0 b *\<^sub>S pre)\<close>
  proof (rule hoare_ifthenelse, 
         simp_all only: image_insert image_empty singleton_bit_complement add_bit_eq_xor xor_self_eq)
    have *: \<open>\<Phi>1 (proj (ket a')) o\<^sub>C\<^sub>L O3' a b a b = of_bool (a=a') *\<^sub>C O3' a b a b\<close> for a a' b
      apply (simp_all add: O3'_def cblinfun_compose_assoc
          lift_cblinfun_comp[OF swap_registers, of \<Phi>1 \<Phi>2]
          lift_cblinfun_comp[OF swap_registers, of \<Phi>1 X\<Phi>2] del: o_apply)
      apply (simp_all add: register_mult[of \<Phi>] o_def flip: cblinfun_compose_assoc)
      by (simp_all add: Fst_def cblinfun_comp_butterfly tensor_op_ell2 
          cinner_ket complex_vector.linear_0 clinear_register
          flip: butterfly_eq_proj)
    have **: \<open>\<Phi>2 pauliX o\<^sub>C\<^sub>L O3' a b 1 b = O3' a b 0 b\<close> for a b
      apply (simp add: O3'_def lift_cblinfun_comp[OF register_mult, of \<Phi>2]
          cblinfun_compose_assoc XZ_def
          del: o_apply)
      by (simp flip: cblinfun_compose_assoc)
    show \<open>hoare (\<Phi>1 (proj (ket 1)) *\<^sub>S (\<Squnion>(a, b). O3' a b a b *\<^sub>S pre))
                [apply pauliX \<Phi>2]
                (\<Squnion>(a, b). O3' a b 0 b *\<^sub>S pre)\<close>
      using * **
      apply (auto intro!: hoare_apply SUP_mono 
          simp add: cblinfun_image_SUP cblinfun_compose_assoc
          simp flip: cblinfun_compose_image)
      by blast
    show \<open>hoare (\<Phi>1 (proj (ket 0)) *\<^sub>S (\<Squnion>(a, b). O3' a b a b *\<^sub>S pre)) []
     (\<Squnion>(a, b). O3' a b 0 b *\<^sub>S pre)\<close>
      using * 
      apply (auto intro!:  hoare_skip SUP_mono 
          simp add: cblinfun_image_SUP 
          simp flip: cblinfun_compose_image)
      by blast
  qed

  also
  have \<open>hoare (\<Squnion>(a,b)\<in>UNIV. O3' a b 0 b *\<^sub>S pre)
              [ifthenelse X {1} [apply pauliZ \<Phi>2] []]
              (\<Squnion>(a,b)\<in>UNIV. O3' a b 0 0 *\<^sub>S pre)\<close>
  proof (rule hoare_ifthenelse, 
         simp_all only: image_insert image_empty singleton_bit_complement add_bit_eq_xor xor_self_eq)
    have *: \<open>X (proj (ket b')) o\<^sub>C\<^sub>L O3' a b 0 b = of_bool (b=b') *\<^sub>C O3' a b 0 b\<close> for a b b'
    proof -
      have 1: \<open>X x o\<^sub>C\<^sub>L X\<Phi>2 Uswap = X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi>2 x\<close> for x
        by (simp add: to_X\<Phi>2 register_mult Uswap_compose del: o_apply)
      show ?thesis
        apply (simp_all add: O3'_def cblinfun_compose_assoc
            lift_cblinfun_comp[OF swap_registers, of  X \<Phi>] lift_cblinfun_comp[OF 1]
            register_mult[of \<Phi>])
        by (simp_all add: Snd_def cblinfun_comp_butterfly tensor_op_ell2 
            cinner_ket complex_vector.linear_0 clinear_register
            flip: butterfly_eq_proj)
    qed
    have **: \<open>\<Phi>2 pauliZ o\<^sub>C\<^sub>L O3' a b 0 1 = O3' a b 0 0\<close> for a b
      by (simp add: O3'_def lift_cblinfun_comp[OF register_mult, of \<Phi>2]
          cblinfun_compose_assoc XZ_def
          del: o_apply)
    show \<open>hoare (X (proj (ket 1)) *\<^sub>S (\<Squnion>(a, b). O3' a b 0 b *\<^sub>S pre))
                [apply pauliZ \<Phi>2]
                (\<Squnion>(a, b). O3' a b 0 0 *\<^sub>S pre)\<close>
      using * ** 
      apply (auto intro!: hoare_apply SUP_mono 
          simp add: cblinfun_image_SUP cblinfun_compose_assoc
          simp flip: cblinfun_compose_image)
      by blast
    show \<open>hoare (X (proj (ket 0)) *\<^sub>S (\<Squnion>(a, b). O3' a b 0 b *\<^sub>S pre))
                []
                (\<Squnion>(a, b). O3' a b 0 0 *\<^sub>S pre)\<close>
      using * 
      apply (auto intro!:  hoare_skip SUP_mono 
          simp add: cblinfun_image_SUP 
          simp flip: cblinfun_compose_image)
      by blast
  qed

  also have \<open>(\<Squnion>(a,b)\<in>UNIV. O3' a b 0 0 *\<^sub>S pre) \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
  proof (rule SUP_least, simp only: case_prod_unfold)
    fix a b
    have \<open>O3' a b 0 0 *\<^sub>S pre = (X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)) *\<^sub>S (XAB =\<^sub>q \<psi>)\<close>
      by (simp add: O3'_def XZ_def pre_def)
    also have \<open>\<dots> \<le> X\<Phi>2 Uswap *\<^sub>S (XAB =\<^sub>q \<psi>)\<close>
      by (auto intro!: cblinfun_image_mono
          simp add: cblinfun_compose_image EQ_def lift_cblinfun_comp[OF swap_registers, of \<Phi> XAB])
    also have \<open>\<dots> = (X\<Phi>2;AB) (Uswap \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (X\<Phi>2;AB)
                      ((swap \<otimes>\<^sub>r id) (assoc' (id_cblinfun \<otimes>\<^sub>o assoc (proj \<psi>)))) *\<^sub>S \<top>\<close>
      by (simp add: to_X\<Phi>2_AB EQ_def)
    also have \<open>\<dots> = \<Phi>2AB (proj \<psi>) *\<^sub>S X\<Phi>2 Uswap *\<^sub>S \<top>\<close>
      apply (simp add: swap_sandwich sandwich_grow_left to_X\<Phi>2_AB   
          cblinfun_compose_image[symmetric] register_mult)
      by (simp add: sandwich_apply cblinfun_compose_assoc[symmetric] comp_tensor_op tensor_op_adjoint)
    also have \<open>\<dots> \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
      by (simp add: EQ_def cblinfun_image_mono)
    finally show \<open>O3' a b 0 0 *\<^sub>S pre \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
      by -
  qed

  finally
  show ?thesis
    by (simp add: teleport_def o_def)
qed

end

text \<open>For illustration, we reinstantiate the above theorem with some
  very concrete memory layout below.\<close>

text \<open>Declaring the concrete layout inside a locale.\<close>
locale concrete_teleport_vars begin

type_synonym a_state = "64 word"
type_synonym b_state = "1000000 word"
type_synonym mem = "a_state * bit * bit * b_state * bit"
type_synonym 'a var = \<open>'a update \<Rightarrow> mem update\<close>

text \<open>The registers. Note that while in \<^locale>\<open>teleport_locale\<close>, \<^term>\<open>\<Phi>\<close> was a single register,
      now it consists of separate registers \<^term>\<open>\<Phi>1\<close>, \<^term>\<open>\<Phi>2\<close> that are not even located next to each other
      in memory.\<close>
definition A :: "a_state var" where \<open>A a = a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition X :: \<open>bit var\<close> where \<open>X a = id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition \<Phi>1 :: \<open>bit var\<close> where \<open>\<Phi>1 a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition B :: \<open>b_state var\<close> where \<open>B a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun\<close>
definition \<Phi>2 :: \<open>bit var\<close> where \<open>\<Phi>2 a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a\<close>

end

text \<open>We can now interpret the \<^locale>\<open>teleport_locale\<close> for our concrete registers.
All we need to do it specify which of our concrete registers correspond to
which in the generic setting, and prove that all registers are compatible.\<close>

interpretation teleport_concrete:
  concrete_teleport_vars +
  teleport_locale concrete_teleport_vars.X
                  \<open>(concrete_teleport_vars.\<Phi>1; concrete_teleport_vars.\<Phi>2)\<close>
                  concrete_teleport_vars.A
                  concrete_teleport_vars.B
  apply standard
  by (auto simp: concrete_teleport_vars.X_def[abs_def]
                 concrete_teleport_vars.\<Phi>1_def[abs_def]
                 concrete_teleport_vars.\<Phi>2_def[abs_def]
                 concrete_teleport_vars.A_def[abs_def]
                 concrete_teleport_vars.B_def[abs_def]
           intro!: compatible3' compatible3)

text \<open>The resulting theorems in the concrete setting:\<close>

thm teleport
thm teleport_def

end
