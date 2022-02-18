theory HS2Ell2
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product
begin

unbundle cblinfun_notation


definition some_chilbert_basis :: \<open>'a::chilbert_space set\<close> where
  \<open>some_chilbert_basis = (SOME B::'a set. is_onb B)\<close>

lemma is_onb_some_chilbert_basis[simp]: \<open>is_onb (some_chilbert_basis :: 'a::chilbert_space set)\<close>
  using orthonormal_basis_exists[OF is_ortho_set_empty]
  by (auto simp add: some_chilbert_basis_def intro: someI2)

lemma is_ortho_set_some_chilbert_basis[simp]: \<open>is_ortho_set some_chilbert_basis\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma is_normal_some_chilbert_basis: \<open>\<And>x. x \<in> some_chilbert_basis \<Longrightarrow> norm x = 1\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma ccspan_some_chilbert_basis[simp]: \<open>ccspan some_chilbert_basis = \<top>\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast
lemma span_some_chilbert_basis[simp]: \<open>closure (cspan some_chilbert_basis) = UNIV\<close>
  by (metis ccspan.rep_eq ccspan_some_chilbert_basis top_ccsubspace.rep_eq)

lemma some_chilbert_basis_nonempty: \<open>(some_chilbert_basis :: 'a::{chilbert_space, not_singleton} set) \<noteq> {}\<close>
proof (rule ccontr, simp)
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  assume [simp]: \<open>B = {}\<close>
  have \<open>UNIV = closure (cspan B)\<close>
    using B_def span_some_chilbert_basis by blast
  also have \<open>\<dots> = {0}\<close>
    by simp
  also have \<open>\<dots> \<noteq> UNIV\<close>
    using Extra_General.UNIV_not_singleton by blast
  finally show False
    by simp
qed

typedef (overloaded) 'a::\<open>{chilbert_space, not_singleton}\<close> chilbert2ell2 = \<open>some_chilbert_basis :: 'a set\<close>
  using some_chilbert_basis_nonempty by auto

definition ell2_to_hilbert where \<open>ell2_to_hilbert = cblinfun_extension (range ket) (Rep_chilbert2ell2 o inv ket)\<close>

lemma ell2_to_hilbert_ket: \<open>ell2_to_hilbert *\<^sub>V ket x = Rep_chilbert2ell2 x\<close>
proof -
  have \<open>cblinfun_extension_exists (range ket) (Rep_chilbert2ell2 o inv ket)\<close>
    apply (rule cblinfun_extension_exists_ortho[where B=1])
       apply auto
    apply (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  then show ?thesis
    apply (simp add: ell2_to_hilbert_def)
    apply (subst cblinfun_extension_apply)
    by simp_all
qed

lemma norm_ell2_to_hilbert: \<open>norm ell2_to_hilbert = 1\<close>
proof (rule order.antisym)
  show \<open>norm ell2_to_hilbert \<le> 1\<close>
    unfolding ell2_to_hilbert_def
    apply (rule cblinfun_extension_exists_ortho_norm[where B=1])
       apply auto
    apply (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  show \<open>norm ell2_to_hilbert \<ge> 1\<close>
    apply (rule cblinfun_norm_geqI[where x=\<open>ket undefined\<close>])
    apply (auto simp: ell2_to_hilbert_ket)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
qed

lemma unitary_ell2_to_hilbert: \<open>unitary ell2_to_hilbert\<close>
proof (rule surj_isometry_is_unitary)
  show \<open>isometry (ell2_to_hilbert :: 'a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  proof (rule orthogonal_on_basis_is_isometry)
    show \<open>ccspan (range ket) = \<top>\<close>
      by auto
    fix x y :: \<open>'a chilbert2ell2 ell2\<close>
    assume \<open>x \<in> range ket\<close> \<open>y \<in> range ket\<close>
    then obtain x' y' where [simp]: \<open>x = ket x'\<close> \<open>y = ket y'\<close>
      by auto
    show \<open>(ell2_to_hilbert *\<^sub>V x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V y) = x \<bullet>\<^sub>C y\<close>
    proof (cases \<open>x'=y'\<close>)
      case True
      then show ?thesis
        apply (auto simp: ell2_to_hilbert_ket)
        using Rep_chilbert2ell2 cnorm_eq_1 is_normal_some_chilbert_basis by blast
    next
      case False
      then show ?thesis
        apply (auto simp: ell2_to_hilbert_ket cinner_ket)
        by (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    qed
  qed
  have \<open>cblinfun_apply ell2_to_hilbert ` range ket \<supseteq> some_chilbert_basis\<close>
    by (metis Rep_chilbert2ell2_cases UNIV_I ell2_to_hilbert_ket image_eqI subsetI)
  then have \<open>ell2_to_hilbert *\<^sub>S \<top> \<ge> ccspan some_chilbert_basis\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (smt (verit, del_insts) cblinfun_image_ccspan ccspan_mono ccspan_range_ket)
  also have \<open>\<dots> = \<top>\<close>
    by simp
  finally show \<open>ell2_to_hilbert *\<^sub>S \<top> = \<top>\<close>
    by (simp add: top.extremum_unique)
qed

lemma ell2_to_hilbert_adj_ket: \<open>ell2_to_hilbert* *\<^sub>V \<psi> = ket (Abs_chilbert2ell2 \<psi>)\<close> if \<open>\<psi> \<in> some_chilbert_basis\<close>
  using ell2_to_hilbert_ket unitary_ell2_to_hilbert
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply that type_definition.Abs_inverse type_definition_chilbert2ell2 unitaryD1)

unbundle no_cblinfun_notation

end
