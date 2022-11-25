section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum Quantum_Extra Tensor_Product.Weak_Star_Topology
    Tensor_Product.Partial_Trace
    With_Type.With_Type
    Tensor_Product.Misc_Tensor_Product_TTS
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")
hide_const (open) Order.top
declare [[eta_contract]]












(* (* TODO: can we use a generic rule similar to sum_parametric' instead? *)
lemma has_sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star ===> (\<longleftrightarrow>)) (has_sum_in weak_star_topology) has_sum\<close>
  unfolding has_sum_euclidean_iff[symmetric]
  by transfer_prover
 *)

(* lemma summable_on_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> (\<longleftrightarrow>)) (summable_on_in weak_star_topology) Infinite_Sum.summable_on\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
  unfolding summable_on_def summable_on_in_def
  by transfer_prover
 *)

(* lemma infsum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star) (infsum_in weak_star_topology) infsum\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd\<close> and g A B
  assume [transfer_rule]: \<open>(R ===> cr_cblinfun_weak_star) f g\<close>
  assume [transfer_rule]: \<open>rel_set R A B\<close>
  show \<open>cr_cblinfun_weak_star (infsum_in Weak_Star_Topology.weak_star_topology f A) (infsum g B)\<close>
  proof (cases \<open>g summable_on B\<close>)
    case True
    then have True': \<open>summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    define a b where \<open>a = infsum_in weak_star_topology f A\<close> and \<open>b = infsum g B\<close>
    from True' have 1: \<open>has_sum_in weak_star_topology f A a\<close>
      by (simp add: a_def has_sum_in_infsum_in)
    from True have \<open>has_sum g B b\<close>
      using b_def summable_iff_has_sum_infsum by blast
    then have 2: \<open>b' = b\<close> if \<open>has_sum g B b'\<close> for b'
      using infsumI that by blast
    from 1 2 show \<open>cr_cblinfun_weak_star a b\<close>
      unfolding cr_cblinfun_weak_star_def
      apply transfer
      by simp
  next
    case False
    then have False': \<open>\<not> summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    then show ?thesis
      by (simp add: False infsum_not_exists not_summable_infsum_in_0 zero_cblinfun_weak_star.transfer)
  qed
qed
 *)

(* lemma map_filter_on_id: \<open>map_filter_on S (\<lambda>x. x) F = F\<close> if \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
  using that
  by (auto intro!: filter_eq_iff[THEN iffD2] simp: eventually_map_filter_on eventually_frequently_simps)
 *)

(* lemma inverse_real_inverse: \<open>inverse_real_inst.inverse_real = inverse\<close>
  by (simp add: HOL.nitpick_unfold)
 *)

(* lemma top_filter_parametric':
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  shows \<open>rel_filter r (principal (Collect S)) \<top>\<close>
proof (rule rel_filter.intros)
  define Z where \<open>Z = principal {(x,y). r x y}\<close>
  show \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: eventually_principal Z_def)
  show \<open>map_filter_on {(x, y). r x y} fst Z = principal (Collect S)\<close>
    using \<open>Domainp r = S\<close> by (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
  show \<open>map_filter_on {(x, y). r x y} snd Z = \<top>\<close>
    apply (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
    by (metis assms(2) right_totalE)
qed
 *)

(* 
lemma Inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes \<open>Domainp r = S\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_set (rel_filter r) ===> rel_filter r)
     (\<lambda>M. inf (Inf M) (principal (Collect S)))
     Inf\<close>
proof (rule rel_funI)
  fix Fs Gs
  assume asm[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  show \<open>rel_filter r (inf (Inf Fs) (principal (Collect S))) (Inf Gs)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by (metis asm empty_iff equals0I rel_setD2)
    show ?thesis
      using assms by (simp add: True \<open>Gs = {}\<close> top_filter_parametric')
  next
    case False
    then have \<open>Gs \<noteq> {}\<close>
      by (metis asm ex_in_conv rel_setD1)
    have dom: \<open>Domainp (rel_filter r) F = (F \<le> principal (Collect S))\<close> for F
      by (simp add: Domainp_rel_filter assms(1))
    have 1: \<open>(rel_filter r)
       (Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F})
       (Inf Gs)\<close> (is \<open>(rel_filter r) ?I _\<close>)
      unfolding Inf_filter_def[abs_def]
      by transfer_prover
    have \<open>F \<le> principal (Collect S)\<close> if \<open>F \<in> Fs\<close> for F
      by (meson DomainPI asm dom rel_setD1 that)
    have \<open>?I = (inf (Inf Fs) (principal (Collect S)))\<close>
      unfolding dom Inf_filter_def
      apply auto
      apply (rule antisym)
      apply auto
        apply (simp add: Collect_mono_iff Sup_subset_mono)
      apply (metis (no_types, lifting) Sup_least mem_Collect_eq)
      by (smt (verit, del_insts) Collect_mono False Sup_subset_mono \<open>\<And>Fa. Fa \<in> Fs \<Longrightarrow> Fa \<le> principal (Collect S)\<close> bot.extremum_unique dual_order.refl inf.bounded_iff order_trans subsetI)
    show ?thesis
      using "1" \<open>Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F} = inf (Inf Fs) (principal (Collect S))\<close> by fastforce
  qed
qed
 *)


(* 
lemma inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_filter r ===> rel_filter r ===> rel_filter r)
     inf inf\<close>
proof (rule rel_funI, rule rel_funI, rename_tac F1 F2 G1 G2)
  fix F1 F2 G1 G2
  assume asmF[transfer_rule]: \<open>rel_filter r F1 F2\<close>
  assume asmG[transfer_rule]: \<open>rel_filter r G1 G2\<close>
  then have *: \<open>G1 \<le> principal (Collect (Domainp r))\<close>
    by (meson Domainp.intros Domainp_rel_filter)
  have \<open>rel_filter r (Inf {F1,G1} \<sqinter> principal (Collect (Domainp r))) (Inf {F2,G2})\<close>
    by transfer_prover
  with * show \<open>rel_filter r (inf F1 G1) (inf F2 G2)\<close>
    by (auto simp: inf_assoc inf.absorb_iff1)
qed
 *)


(* lemma convergent_ow_typeclass2[simp]:
  assumes \<open>open V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. f \<longlonglongrightarrow> l \<and> l \<in> V)\<close>
  by (simp add: limitin_canonical_iff_gen assms)
 *)

(* lemma convergent_on_typeclass3[simp]:
  assumes \<open>open V\<close> \<open>closed V\<close> \<open>range f \<subseteq> V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> convergent f\<close>
  apply (simp add: assms)
  by (meson assms(2) assms(3) closed_sequentially convergent_def range_subsetD)
 *)

(* lemma cmod_distrib_plus: \<open>a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> cmod (a + b) = cmod a + cmod b\<close>
  by (simp add: cmod_Re) *)

lemma register_decomposition_converse:
  assumes \<open>unitary U\<close>
  shows \<open>register (\<lambda>x. sandwich U (id_cblinfun \<otimes>\<^sub>o x))\<close>
  using _ unitary_sandwich_register apply (rule register_comp[unfolded o_def])
  using assms by auto

lemma register_inj: \<open>inj F\<close> if [simp]: \<open>register F\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F. inj F\<close>
    using register_decomposition[OF \<open>register F\<close>] 
  proof (rule with_type_mp)
    fix rep :: \<open>'c \<Rightarrow> 'd\<close> and abs and S
    assume \<open>type_definition rep abs S\<close>
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>unitary U\<close> and F: \<open>F a = Complex_Bounded_Linear_Function.sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
      apply atomize_elim by auto
    have \<open>inj (Complex_Bounded_Linear_Function.sandwich U)\<close>
      by (smt (verit, best) \<open>unitary U\<close> cblinfun_assoc_left inj_onI sandwich_apply cblinfun_compose_id_right cblinfun_compose_id_left unitary_def)
    moreover have \<open>inj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (rule inj_tensor_left, simp)
    ultimately show \<open>inj F\<close>
      unfolding F
      by (smt (z3) inj_def)
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show \<open>inj F\<close>
    by -
qed

lemma clinear_register: \<open>register F \<Longrightarrow> clinear F\<close>
  using bounded_clinear.clinear register_bounded_clinear by blast

lemma weak_star_cont_register: \<open>register F \<Longrightarrow> continuous_map weak_star_topology weak_star_topology F\<close>
  using register_def by blast

lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  from register_decomposition
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
        \<exists>U. unitary U \<and> F = sandwich U\<close>
  proof (rule with_type_mp)
    show [simp]: \<open>register F\<close>
      using assms iso_register_is_register by blast 

    assume register_decomposition:
      \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>

    let ?ida = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

    from register_decomposition
    obtain V :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
      and FV: \<open>F \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o ?ida)\<close> for \<theta>
      by (auto simp: sandwich_apply sandwich_def)

    have \<open>surj F\<close>
      by (meson assms iso_register_inv_comp2 surj_iff)
    have surj_tensor: \<open>surj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. a \<otimes>\<^sub>o ?ida)\<close>
      apply (rule surj_from_comp[where g=\<open>sandwich V\<close>])
      using \<open>surj F\<close> apply (auto simp: FV)
      by (meson \<open>unitary V\<close> register_inj unitary_sandwich_register)
    then obtain a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close> 
      where a: \<open>a \<otimes>\<^sub>o ?ida = selfbutterket undefined \<otimes>\<^sub>o selfbutterket undefined\<close>
      by (smt (verit, best) surjD)

    then have \<open>a \<noteq> 0\<close>
      apply (auto simp: tensor_ell2_ket)
      by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_nonzero orthogonal_ket)

    obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C selfbutterket undefined\<close>
      apply atomize_elim
      using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
    then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (selfbutterket undefined *\<^sub>V ket undefined)\<close>
      by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C selfbutterket undefined\<close> scaleC_cblinfun.rep_eq)
    then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
      by (metis butterfly_apply cinner_ket_same id_cblinfun_apply ket_nonzero scaleC_cancel_right scaleC_one)
    then have \<open>\<gamma> = 1\<close>
      by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero)

    define T U where \<open>T = CBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
    have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
      unfolding T_def
      apply (subst bounded_clinear_CBlinfun_apply)
      by (auto intro!: bounded_clinear_tensor_ell22)
    have \<open>sandwich T (butterket i j) = butterket i j \<otimes>\<^sub>o id_cblinfun\<close> for i j
      by (simp add: T sandwich_def cblinfun_comp_butterfly butterfly_comp_cblinfun \<gamma> \<open>\<gamma> = 1\<close>)
    then have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by auto

    have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: Misc.sandwich_def FV)
    also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: T \<gamma> \<open>\<gamma> = 1\<close>)
    also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
      by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
    finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by (auto simp: clinear_register weak_star_cont_register simp flip: sandwich_def)

    have \<open>isometry T\<close>
      apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
      by (auto simp: T)
    moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
    proof -
      have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
      proof -
        have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
          by (simp add: T tensor_ell2_scaleC1 tensor_ell2_scaleC2)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (selfbutterket undefined *\<^sub>V \<xi>)\<close>
          by simp
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (?ida *\<^sub>V \<xi>)\<close>
          by (simp add: \<gamma> \<open>\<gamma> = 1\<close>)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<xi>\<close>
          by simp
        finally show ?thesis
          by (metis range_eqI)
      qed

      have \<open>\<top> \<le> ccspan {ket x | x. True}\<close>
        by (simp add: full_SetCompr_eq)
      also have \<open>\<dots> \<le> ccspan {\<phi> \<otimes>\<^sub>s \<xi> | \<phi> \<xi>. True}\<close>
        apply (rule ccspan_mono)
        by (auto simp flip: tensor_ell2_ket)
      also from 1 have \<open>\<dots> \<le> ccspan (range ((*\<^sub>V) T))\<close>
        by (auto intro!: ccspan_mono)
      also have \<open>\<dots> = T *\<^sub>S \<top>\<close>
        by (metis (mono_tags, opaque_lifting) calculation cblinfun_image_ccspan cblinfun_image_mono eq_iff top_greatest)
      finally show \<open>T *\<^sub>S \<top> = \<top>\<close>
        using top.extremum_uniqueI by blast
    qed

    ultimately have \<open>unitary T\<close>
      by (rule surj_isometry_is_unitary)
    then have \<open>unitary U\<close>
      by (simp add: U_def \<open>unitary V\<close>)

    from F_rep \<open>unitary U\<close> show \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
      by (auto simp: sandwich_def[abs_def])
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show ?thesis
    by -
qed

lemma complement_exists:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         \<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof (use register_decomposition[OF \<open>register F\<close>] in \<open>rule with_type_mp\<close>)
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  assume register_decomposition: \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
  then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    by (auto simp: sandwich_def sandwich_apply)
  define G :: \<open>'c update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      apply (auto simp: register_pair_apply F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: unitary_sandwich_register)
    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have \<open>I o (F;G) = id\<close> and FGI: \<open>(F;G) o I = id\<close>
       apply (auto intro!:ext simp: I_def[abs_def] FG sandwich_def)
       apply (metis (no_types, opaque_lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
      by (metis (no_types, lifting) \<open>unitary U\<close> cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD2)
    then show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show \<open>\<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    apply (rule_tac exI[of _ G]) by auto
qed

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma register_norm: \<open>norm (F a) = norm a\<close> if \<open>register F\<close>
proof -
  from register_decomposition[OF that]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
         norm (F a) = norm a\<close>
  proof (rule with_type_mp) 
    fix Rep :: \<open>'c \<Rightarrow> 'b ell2\<close> and Abs
      assume \<open>type_definition Rep Abs (register_decomposition_basis F)\<close>
    assume \<open>(\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary U\<close>
      and FU: \<open>F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by (metis sandwich_def sandwich_apply)
    show \<open>norm (F a) = norm a\<close>
      using \<open>unitary U\<close> by (simp add: FU sandwich_def norm_isometry_compose norm_isometry_o' tensor_op_norm)
  qed
  note this[cancel_with_type]
  then show ?thesis
    by simp
qed

lemma commutant_exchange:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>iso_register F\<close>
  shows \<open>commutant (F ` X) = F ` commutant X\<close>
proof (rule Set.set_eqI)
  fix x :: \<open>'b update\<close>
  from assms
  obtain G where \<open>F o G = id\<close> and \<open>G o F = id\<close> and [simp]: \<open>register G\<close>
    using iso_register_def by blast
  from assms have [simp]: \<open>register F\<close>
    using iso_register_def by blast
  have \<open>x \<in> commutant (F ` X) \<longleftrightarrow> (\<forall>y \<in> F ` X. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> F ` X. G x o\<^sub>C\<^sub>L G y = G y o\<^sub>C\<^sub>L G x)\<close>
    by (metis (no_types, opaque_lifting) \<open>F \<circ> G = id\<close> \<open>G o F = id\<close> \<open>register G\<close> comp_def eq_id_iff register_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> X. G x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L G x)\<close>
    by (simp add: \<open>G \<circ> F = id\<close> pointfree_idE)
  also have \<open>\<dots> \<longleftrightarrow> G x \<in> commutant X\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by (metis (no_types, opaque_lifting) \<open>G \<circ> F = id\<close> \<open>F \<circ> G = id\<close> image_iff pointfree_idE)
  finally show \<open>x \<in> commutant (F ` X) \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by -
qed

lemma commutant_tensor1: \<open>commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)) = range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  fix \<gamma> :: 'a
  assume \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
  then have comm: \<open>(a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V \<psi> = x *\<^sub>V (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>\<close> for a \<psi>
    by (metis (mono_tags, lifting) commutant_def mem_Collect_eq rangeI cblinfun_apply_cblinfun_compose)

  define op where \<open>op = classical_operator (\<lambda>i. Some (\<gamma>,i::'b))\<close>
  have [simp]: \<open>classical_operator_exists (\<lambda>i. Some (\<gamma>,i))\<close>
    apply (rule classical_operator_exists_inj)
    using inj_map_def by blast
  define x' where \<open>x' = op* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L op\<close>
  have x': \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close> for j l
    by (simp add: x'_def op_def classical_operator_ket cinner_adj_right)

  have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l)) = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close> for i j k l
  proof -
    have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l))
        = cinner ((butterket i \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      unfolding comm by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close>
      by (simp add: comp_tensor_op tensor_op_ket tensor_op_scaleC_left cinner_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket j) (x' *\<^sub>V ket l)\<close>
      by (simp add: x')
    also have \<open>\<dots> = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close>
      apply (simp add: tensor_op_ket)
      by (simp flip: tensor_ell2_ket)
    finally show ?thesis by -
  qed
  then have \<open>x = (id_cblinfun \<otimes>\<^sub>o x')\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then show \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by auto
next
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  assume \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
  then obtain b where x: \<open>x = id_cblinfun \<otimes>\<^sub>o b\<close>
    by auto
  then show \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: x commutant_def comp_tensor_op)
qed

lemma complement_range:
  assumes [simp]: \<open>compatible F G\<close> and [simp]: \<open>iso_register (F;G)\<close>
  shows \<open>range G = commutant (range F)\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms compatible_def by metis+
  have [simp]: \<open>(F;G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
    using Laws_Quantum.register_pair_apply assms by blast
  have [simp]: \<open>range F = (F;G) ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  have [simp]: \<open>range G = (F;G) ` range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by force
  show \<open>range G = commutant (range F)\<close>
    by (simp add: commutant_exchange commutant_tensor1)
qed

lemma continuous_map_iff_preserves_convergence:
  assumes \<open>\<And>F a. a \<in> topspace T \<Longrightarrow> limitin T id a F \<Longrightarrow> limitin U f (f a) F\<close>
  shows \<open>continuous_map T U f\<close>
  apply (rule continuous_map_atin[THEN iffD2], intro ballI)
  using assms
  by (simp add: limitin_continuous_map)

(* lemma isCont_iff_preserves_convergence:
  assumes \<open>\<And>F. (id \<longlongrightarrow> a) F \<Longrightarrow> (f \<longlongrightarrow> f a) F\<close>
  shows \<open>isCont f a\<close>
  using assms
  by (simp add: isCont_def Lim_at_id) *)


lemma register_inv_weak_star_continuous:
  assumes \<open>register F\<close>
  shows \<open>continuous_map (subtopology weak_star_topology (range F)) weak_star_topology (inv F)\<close>
proof (rule continuous_map_iff_preserves_convergence, rename_tac K a)
  fix K a
  assume limit_id: \<open>limitin (subtopology weak_star_topology (range F)) id a K\<close>
  from register_decomposition
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
        limitin weak_star_topology (inv F) (inv F a) K\<close>
  proof (rule with_type_mp)
    from assms show \<open>register F\<close> by -
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where \<open>unitary U\<close> and FU: \<open>F \<theta> = Misc.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by (auto simp: sandwich_def sandwich_apply)
    define \<delta> :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where \<open>\<delta> = selfbutter (ket (undefined))\<close>
    then have [simp]: \<open>trace_class \<delta>\<close>
      by simp
    define u where \<open>u t = U o\<^sub>C\<^sub>L (from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L U*\<close> for t
    have [simp]: \<open>trace_class (u t)\<close> for t
      unfolding u_def
      apply (rule trace_class_comp_left)
      apply (rule trace_class_comp_right)
      by (simp add: trace_class_tensor)
    have uF: \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (u t o\<^sub>C\<^sub>L F a)\<close> for t a 
    proof -
      have \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (from_trace_class t o\<^sub>C\<^sub>L a) * trace (\<delta> o\<^sub>C\<^sub>L id_cblinfun)\<close>
        by (simp add: \<delta>_def trace_butterfly)
      also have \<open>\<dots> = trace ((from_trace_class t o\<^sub>C\<^sub>L a) \<otimes>\<^sub>o (\<delta> o\<^sub>C\<^sub>L id_cblinfun))\<close>
        by (simp add: trace_class_comp_left trace_tensor)
      also have \<open>\<dots> = trace ((from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> = trace (U* o\<^sub>C\<^sub>L u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        using \<open>unitary U\<close>
        by (simp add: u_def lift_cblinfun_comp[OF unitaryD1] cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*)\<close>
        apply (subst (2) circularity_of_trace)
        by (simp_all add: trace_class_comp_left cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L F a)\<close>
        by (simp add: Misc.sandwich_def FU cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    from limit_id
    have \<open>a \<in> range F\<close> and KrangeF: \<open>\<forall>\<^sub>F a in K. a \<in> range F\<close> and limit_id': \<open>limitin weak_star_topology id a K\<close>
      unfolding limitin_subtopology by auto
    from \<open>a \<in> range F\<close> have FiFa: \<open>F (inv F a) = a\<close>
      by (simp add: f_inv_into_f)
    from KrangeF
    have *: \<open>\<forall>\<^sub>F x in K. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F x)) = trace (from_trace_class t o\<^sub>C\<^sub>L x)\<close> for t
      apply (rule eventually_mono)
      by (simp add: f_inv_into_f)
    from limit_id' have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L a)) K\<close> for t
      unfolding limitin_weak_star_topology' by simp
    then have *: \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      unfolding FiFa using * by (rule tendsto_cong[THEN iffD2, rotated])
    have \<open>((\<lambda>a'. trace (u t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (u t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      using *[of \<open>Abs_trace_class (u t)\<close>]
      by (simp add: Abs_trace_class_inverse)
    then have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L inv F a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L inv F a)) K\<close> for t
      by (simp add: uF[symmetric])
    then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
      by (simp add: limitin_weak_star_topology')
  qed
  note this[cancel_with_type]
  then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
    by -
qed

lemma same_range_equivalent:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G :: \<open>'b update \<Rightarrow> 'c update\<close>
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes \<open>range F = range G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  have G_rangeF[simp]: \<open>G x \<in> range F\<close> for x
    by (simp add: assms)
  have F_rangeG[simp]: \<open>F x \<in> range G\<close> for x
    by (simp add: assms(3)[symmetric])
  have [simp]: \<open>inj F\<close> and [simp]: \<open>inj G\<close>
    by (simp_all add: register_inj)
  have [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
    by (simp_all add: register_bounded_clinear)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    by (simp_all add: bounded_clinear.clinear)
  define I J where \<open>I x = inv F (G x)\<close> and \<open>J y = inv G (F y)\<close> for x y
  have addI: \<open>I (x + y) = I x + I y\<close> for x y
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_add)
  have addJ: \<open>J (x + y) = J x + J y\<close> for x y
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_add)
  have scaleI: \<open>I (r *\<^sub>C x) = r *\<^sub>C I x\<close> for r x
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_scale)
  have scaleJ: \<open>J (r *\<^sub>C x) = r *\<^sub>C J x\<close> for r x
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_scale)
  have unitalI: \<open>I id_cblinfun = id_cblinfun\<close>
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F])
     apply auto
    by (metis register_of_id G_rangeF assms(2))
  have unitalJ: \<open>J id_cblinfun = id_cblinfun\<close>
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G])
     apply auto
    by (metis register_of_id F_rangeG assms(1))
  have multI: \<open>I (a o\<^sub>C\<^sub>L b) = I a o\<^sub>C\<^sub>L I b\<close> for a b
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_mult[symmetric, OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: register_mult)
  have multJ: \<open>J (a o\<^sub>C\<^sub>L b) = J a o\<^sub>C\<^sub>L J b\<close> for a b
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_mult[symmetric, OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: register_mult)
  have adjI: \<open>I (a*) = (I a)*\<close> for a
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_adjoint[OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    using assms(2) register_adjoint by blast
  have adjJ: \<open>J (a*) = (J a)*\<close> for a
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_adjoint[OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    using assms(1) register_adjoint by blast
  have normI: \<open>norm (I a) = norm a\<close> for a
    unfolding I_def
    by (metis G_rangeF assms(1) assms(2) f_inv_into_f register_norm)
  have normJ: \<open>norm (J a) = norm a\<close> for a
    unfolding J_def
    by (metis F_rangeG assms(1) assms(2) f_inv_into_f register_norm)
  have weak_star_I: \<open>continuous_map weak_star_topology weak_star_topology I\<close>
  proof -
    have \<open>continuous_map weak_star_topology weak_star_topology G\<close>
      by (simp add: weak_star_cont_register)
    then have \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range G)) G\<close>
      by (simp add: continuous_map_into_subtopology)
    moreover have \<open>continuous_map (subtopology weak_star_topology (range F)) weak_star_topology (inv F)\<close>
      using \<open>register F\<close> register_inv_weak_star_continuous by blast
    ultimately show \<open>continuous_map weak_star_topology weak_star_topology I\<close>
      unfolding \<open>range F = range G\<close> I_def
      by (rule continuous_map_compose[unfolded o_def])
  qed
  have weak_star_J: \<open>continuous_map weak_star_topology weak_star_topology J\<close>
  proof -
    have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
      by (simp add: weak_star_cont_register)
    then have \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range F)) F\<close>
      by (simp add: continuous_map_into_subtopology)
    moreover have \<open>continuous_map (subtopology weak_star_topology (range G)) weak_star_topology (inv G)\<close>
      using \<open>register G\<close> register_inv_weak_star_continuous by blast
    ultimately show \<open>continuous_map weak_star_topology weak_star_topology J\<close>
      unfolding \<open>range F = range G\<close> J_def
      by (rule continuous_map_compose[unfolded o_def])
  qed

  from addI scaleI unitalI multI adjI normI weak_star_I
  have \<open>register I\<close>
    unfolding register_def by (auto intro!: bounded_clinearI[where K=1])
  from addJ scaleJ unitalJ multJ adjJ normJ weak_star_J
  have \<open>register J\<close>
    unfolding register_def by (auto intro!: bounded_clinearI[where K=1])

  have \<open>I o J = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj F\<close>])
    by auto
  have \<open>J o I = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj G\<close>])
    by auto

  from \<open>I o J = id\<close> \<open>J o I = id\<close> \<open>register I\<close> \<open>register J\<close>
  have \<open>iso_register I\<close>
    using iso_register_def by blast

  have \<open>F o I = G\<close>
    unfolding I_def o_def
    by (subst Hilbert_Choice.f_inv_into_f[where f=F], auto)

  with \<open>iso_register I\<close> show ?thesis
    unfolding equivalent_registers_def by auto
qed

lemma complement_unique:
  assumes "compatible F G" and \<open>iso_register (F;G)\<close>
  assumes "compatible F H" and \<open>iso_register (F;H)\<close>
  shows \<open>equivalent_registers G H\<close>
  by (metis assms compatible_def complement_range same_range_equivalent)

end
