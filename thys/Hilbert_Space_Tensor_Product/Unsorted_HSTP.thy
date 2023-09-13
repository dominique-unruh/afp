theory Unsorted_HSTP
  imports Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    Tensor_Product.Hilbert_Space_Tensor_Product
    Jordan_Normal_Form.Matrix
    Complex_Bounded_Operators.Extra_Jordan_Normal_Form
    Complex_Bounded_Operators.Cblinfun_Matrix
begin

unbundle cblinfun_notation Finite_Cartesian_Product.no_vec_syntax jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Coset.kernel

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

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
        = cinner ((butterfly (ket i) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterfly (ket \<gamma>) (ket i) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterfly (ket \<gamma>) (ket i) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
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


lemma sandwich_tensor_op: \<open>sandwich (a \<otimes>\<^sub>o b) (c \<otimes>\<^sub>o d) = sandwich a c \<otimes>\<^sub>o sandwich b d\<close>
  by (simp add: sandwich_apply tensor_op_adjoint flip: cblinfun_compose_assoc comp_tensor_op)

lemma tensor_ell2_extensionality3:
  assumes "(\<And>s t u. a *\<^sub>V (s \<otimes>\<^sub>s t \<otimes>\<^sub>s u) = b *\<^sub>V (s \<otimes>\<^sub>s t \<otimes>\<^sub>s u))"
  shows "a = b"
  apply (rule equal_ket, case_tac x, hypsubst_thin)
  by (simp add: assms flip: tensor_ell2_ket)

lemma sandwich_assoc_ell2_tensor_op[simp]: \<open>sandwich assoc_ell2 ((a \<otimes>\<^sub>o b) \<otimes>\<^sub>o c) = a \<otimes>\<^sub>o (b \<otimes>\<^sub>o c)\<close>
  by (auto intro!: tensor_ell2_extensionality3 
      simp: sandwich_apply assoc_ell2'_tensor assoc_ell2_tensor tensor_op_ell2)

lemma unitary_tensor_op: \<open>unitary (a \<otimes>\<^sub>o b)\<close> if [simp]: \<open>unitary a\<close> \<open>unitary b\<close>
  by (auto intro!: unitaryI simp add: tensor_op_adjoint comp_tensor_op)

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
  have \<open>finite_rank (\<Sum>b\<in>B. a o\<^sub>C\<^sub>L selfbutter b)\<close>
    by (auto intro!: finite_rank_sum simp: cblinfun_comp_butterfly)
  with a_sum show ?thesis
    by simp
qed

lemma continuous_map_iff_preserves_convergence:
  assumes \<open>\<And>F a. a \<in> topspace T \<Longrightarrow> limitin T id a F \<Longrightarrow> limitin U f (f a) F\<close>
  shows \<open>continuous_map T U f\<close>
  apply (rule continuous_map_atin[THEN iffD2], intro ballI)
  using assms
  by (simp add: limitin_continuous_map)

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
      using butterflies_sum_id_finite by blast
    obtain B :: \<open>'b set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    then have idB: \<open>id_cblinfun = (\<Sum>x\<in>B. selfbutter x)\<close>
      using butterflies_sum_id_finite by blast
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


definition tensor_pack :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat"
  where "tensor_pack X Y = (\<lambda>(x, y). x * Y + y)"

definition tensor_unpack :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"
  where "tensor_unpack X Y xy = (xy div Y, xy mod Y)"

lemma tensor_unpack_inj:
  assumes "i < A * B" and "j < A * B"
  shows "tensor_unpack A B i = tensor_unpack A B j \<longleftrightarrow> i = j"
  by (metis div_mult_mod_eq prod.sel(1) prod.sel(2) tensor_unpack_def)

lemma tensor_unpack_bound1[simp]: "i < A * B \<Longrightarrow> fst (tensor_unpack A B i) < A"
  unfolding tensor_unpack_def
  apply auto
  using less_mult_imp_div_less by blast
lemma tensor_unpack_bound2[simp]: "i < A * B \<Longrightarrow> snd (tensor_unpack A B i) < B"
  unfolding tensor_unpack_def
  apply auto
  by (metis mod_less_divisor mult.commute mult_zero_left nat_neq_iff not_less0)

lemma tensor_unpack_fstfst: \<open>fst (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))
     = fst (tensor_unpack A (B * C) i)\<close>
  unfolding tensor_unpack_def apply auto
  by (metis div_mult2_eq mult.commute)
lemma tensor_unpack_sndsnd: \<open>snd (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack (A * B) C i)\<close>
  unfolding tensor_unpack_def apply auto
  by (meson dvd_triv_right mod_mod_cancel)
lemma tensor_unpack_fstsnd: \<open>fst (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))\<close>
  unfolding tensor_unpack_def apply auto
  by (cases \<open>C = 0\<close>) (simp_all add: mult.commute [of B C] mod_mult2_eq [of i C B])

definition "tensor_state_jnf \<psi> \<phi> = (let d1 = dim_vec \<psi> in let d2 = dim_vec \<phi> in
  vec (d1*d2) (\<lambda>i. let (i1,i2) = tensor_unpack d1 d2 i in (vec_index \<psi> i1) * (vec_index \<phi> i2)))"

lemma tensor_state_jnf_dim[simp]: \<open>dim_vec (tensor_state_jnf \<psi> \<phi>) = dim_vec \<psi> * dim_vec \<phi>\<close>
  unfolding tensor_state_jnf_def Let_def by simp

lemma enum_prod_nth_tensor_unpack:
  assumes \<open>i < CARD('a) * CARD('b)\<close>
  shows "(Enum.enum ! i :: 'a::enum\<times>'b::enum) = 
        (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in 
              (Enum.enum ! i1, Enum.enum ! i2))"
  using assms 
  by (simp add: enum_prod_def product_nth tensor_unpack_def)

lemma vec_of_basis_enum_tensor_state_index:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('a) * CARD('b)\<close>
  shows \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in
    vec_of_basis_enum \<psi> $ i1 * vec_of_basis_enum \<phi> $ i2)\<close>
proof -
  define i1 i2 where "i1 = fst (tensor_unpack CARD('a) CARD('b) i)"
    and "i2 = snd (tensor_unpack CARD('a) CARD('b) i)"
  have [simp]: "i1 < CARD('a)" "i2 < CARD('b)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 by presburger

  have \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = Rep_ell2 (\<psi> \<otimes>\<^sub>s \<phi>) (enum_class.enum ! i)\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = Rep_ell2 \<psi> (Enum.enum!i1) * Rep_ell2 \<phi> (Enum.enum!i2)\<close>
    apply (transfer fixing: i i1 i2)
    by (simp add: enum_prod_nth_tensor_unpack case_prod_beta i1_def i2_def)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> $ i1 * vec_of_basis_enum \<phi> $ i2\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  finally show ?thesis
    by (simp add: case_prod_beta i1_def i2_def)
qed

lemma vec_of_basis_enum_tensor_state:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  shows \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) = tensor_state_jnf (vec_of_basis_enum \<psi>) (vec_of_basis_enum \<phi>)\<close>
  apply (rule eq_vecI, simp_all)
  apply (subst vec_of_basis_enum_tensor_state_index, simp_all)
  by (simp add: tensor_state_jnf_def case_prod_beta Let_def)


lemma mat_of_cblinfun_tensor_op_index:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('b) * CARD('d)\<close>
  assumes [simp]: \<open>j < CARD('a) * CARD('c)\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) = 
            (let (i1,i2) = tensor_unpack CARD('b) CARD('d) i in
             let (j1,j2) = tensor_unpack CARD('a) CARD('c) j in
                  mat_of_cblinfun a $$ (i1,j1) * mat_of_cblinfun b $$ (i2,j2))\<close>
proof -
  define i1 i2 j1 j2
    where "i1 = fst (tensor_unpack CARD('b) CARD('d) i)"
      and "i2 = snd (tensor_unpack CARD('b) CARD('d) i)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('c) j)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('c) j)"
  have [simp]: "i1 < CARD('b)" "i2 < CARD('d)" "j1 < CARD('a)" "j2 < CARD('c)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 apply blast
    using assms(2) j1_def tensor_unpack_bound1 apply blast
    using assms(2) j2_def tensor_unpack_bound2 by presburger

  have \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) 
       = Rep_ell2 (tensor_op a b *\<^sub>V ket (Enum.enum!j)) (Enum.enum ! i)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
  also have \<open>\<dots> = Rep_ell2 ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s (b *\<^sub>V ket (Enum.enum!j2))) (Enum.enum!i)\<close>
    by (simp add: tensor_op_ell2 enum_prod_nth_tensor_unpack[where i=j] Let_def case_prod_beta j1_def[symmetric] j2_def[symmetric] flip: tensor_ell2_ket)
  also have \<open>\<dots> = vec_of_basis_enum ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s b *\<^sub>V ket (Enum.enum!j2)) $ i\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = vec_of_basis_enum (a *\<^sub>V ket (enum_class.enum ! j1)) $ i1 *
                  vec_of_basis_enum (b *\<^sub>V ket (enum_class.enum ! j2)) $ i2\<close>
    by (simp add: case_prod_beta vec_of_basis_enum_tensor_state_index i1_def[symmetric] i2_def[symmetric])
  also have \<open>\<dots> = Rep_ell2 (a *\<^sub>V ket (enum_class.enum ! j1)) (enum_class.enum ! i1) *
                  Rep_ell2 (b *\<^sub>V ket (enum_class.enum ! j2)) (enum_class.enum ! i2)\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i1, j1) * mat_of_cblinfun b $$ (i2, j2)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
  finally show ?thesis
    by (simp add: i1_def[symmetric] i2_def[symmetric] j1_def[symmetric] j2_def[symmetric] case_prod_beta)
qed


definition "tensor_op_jnf A B = 
  (let r1 = dim_row A in
   let c1 = dim_col A in
   let r2 = dim_row B in
   let c2 = dim_col B in
   mat (r1 * r2) (c1 * c2)
   (\<lambda>(i,j). let (i1,i2) = tensor_unpack r1 r2 i in
            let (j1,j2) = tensor_unpack c1 c2 j in
              (A $$ (i1,j1)) * (B $$ (i2,j2))))"

lemma tensor_op_jnf_dim[simp]: 
  \<open>dim_row (tensor_op_jnf a b) = dim_row a * dim_row b\<close>
  \<open>dim_col (tensor_op_jnf a b) = dim_col a * dim_col b\<close>
  unfolding tensor_op_jnf_def Let_def by simp_all


lemma mat_of_cblinfun_tensor_op:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) = tensor_op_jnf (mat_of_cblinfun a) (mat_of_cblinfun b)\<close>
  apply (rule eq_matI, simp_all add: canonical_basis_length)
  apply (subst mat_of_cblinfun_tensor_op_index, simp_all)
  by (simp add: tensor_op_jnf_def case_prod_beta Let_def canonical_basis_length)


lemma mat_of_cblinfun_assoc_ell2'[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2* :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof  (rule mat_eq_iff[THEN iffD2], intro conjI allI impI)

  show \<open>dim_row (mat_of_cblinfun ?assoc) =
    dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp add: canonical_basis_length)
  show \<open>dim_col (mat_of_cblinfun ?assoc) =
    dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp add: canonical_basis_length)

  fix i j
  let ?i = "Enum.enum ! i :: (('a\<times>'b)\<times>'c)" and ?j = "Enum.enum ! j :: ('a\<times>('b\<times>'c))"

  assume \<open>i < dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have iB[simp]: \<open>i < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have iB'[simp]: \<open>i < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith
  assume \<open>j < dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have jB[simp]: \<open>j < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have jB'[simp]: \<open>j < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith

  define i1 i23 i2 i3
    where "i1 = fst (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i23 = snd (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i2 = fst (tensor_unpack CARD('b) CARD('c) i23)"
      and "i3 = snd (tensor_unpack CARD('b) CARD('c) i23)"
  define j12 j1 j2 j3
    where "j12 = fst (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('b) j12)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('b) j12)"
      and "j3 = snd (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"

  have [simp]: "j12 < CARD('a)*CARD('b)" "i23 < CARD('b)*CARD('c)"
    using j12_def jB tensor_unpack_bound1 apply presburger
    using i23_def iB' tensor_unpack_bound2 by blast

  have j1': \<open>fst (tensor_unpack CARD('a) (CARD('b) * CARD('c)) j) = j1\<close>
    by (simp add: j1_def j12_def tensor_unpack_fstfst)

  let ?i1 = "Enum.enum ! i1 :: 'a" and ?i2 = "Enum.enum ! i2 :: 'b" and ?i3 = "Enum.enum ! i3 :: 'c"
  let ?j1 = "Enum.enum ! j1 :: 'a" and ?j2 = "Enum.enum ! j2 :: 'b" and ?j3 = "Enum.enum ! j3 :: 'c"

  have i: \<open>?i = ((?i1,?i2),?i3)\<close>
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
          tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd i1_def i2_def i23_def i3_def)
  have j: \<open>?j = (?j1,(?j2,?j3))\<close> 
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
        tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd j1_def j2_def j12_def j3_def)
  have ijeq: \<open>(?i1,?i2,?i3) = (?j1,?j2,?j3) \<longleftrightarrow> i = j\<close>
    unfolding i1_def i2_def i3_def j1_def j2_def j3_def apply simp
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst tensor_unpack_inj[symmetric, where i=i and j=j and A="CARD('a)" and B="CARD('b)*CARD('c)"], simp, simp)
    unfolding prod_eq_iff
    apply (subst tensor_unpack_inj[symmetric, where i=\<open>snd (tensor_unpack CARD('a) (CARD('b) * CARD('c)) i)\<close> and A="CARD('b)" and B="CARD('c)"], simp, simp)
    by (simp add: i1_def[symmetric] j1_def[symmetric] i2_def[symmetric] j2_def[symmetric] i3_def[symmetric] j3_def[symmetric]
        i23_def[symmetric] j12_def[symmetric] j1'
        prod_eq_iff tensor_unpack_fstsnd tensor_unpack_sndsnd)

  have \<open>mat_of_cblinfun ?assoc $$ (i, j) = Rep_ell2 (assoc_ell2* *\<^sub>V ket ?j) ?i\<close>
    by (subst mat_of_cblinfun_ell2_component, auto)
  also have \<open>\<dots> = Rep_ell2 ((ket ?j1 \<otimes>\<^sub>s ket ?j2) \<otimes>\<^sub>s ket ?j3) ?i\<close>
    by (simp add: j assoc_ell2'_tensor flip: tensor_ell2_ket)
  also have \<open>\<dots> = (if (?i1,?i2,?i3) = (?j1,?j2,?j3) then 1 else 0)\<close>
    by (auto simp add: ket.rep_eq i tensor_ell2_ket)
  also have \<open>\<dots> = (if i=j then 1 else 0)\<close>
    using ijeq by simp
  finally
  show \<open>mat_of_cblinfun ?assoc $$ (i, j) =
           1\<^sub>m (CARD('a) * CARD('b) * CARD('c)) $$ (i, j)\<close>
    by auto
qed

lemma assoc_ell2'_inv: "assoc_ell2 o\<^sub>C\<^sub>L assoc_ell2* = id_cblinfun"
  apply (rule equal_ket, case_tac x, hypsubst)
  by (simp flip: tensor_ell2_ket add: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor)

lemma assoc_ell2_inv: "assoc_ell2* o\<^sub>C\<^sub>L assoc_ell2 = id_cblinfun"
  apply (rule equal_ket, case_tac x, hypsubst)
  by (simp flip: tensor_ell2_ket add: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor)

lemma mat_of_cblinfun_assoc_ell2[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2 :: ((('a::enum\<times>'b::enum)\<times>'c::enum) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof -
  let ?assoc' = "assoc_ell2* :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
  have "one_mat (CARD('a)*CARD('b)*CARD('c)) = mat_of_cblinfun (?assoc o\<^sub>C\<^sub>L ?assoc')"
    by (simp add: mult.assoc mat_of_cblinfun_id)
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * mat_of_cblinfun ?assoc'\<close>
    using mat_of_cblinfun_compose by blast
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
    by simp
  also have \<open>\<dots> = mat_of_cblinfun ?assoc\<close>
    apply (rule right_mult_one_mat')
    by (simp add: canonical_basis_length)
  finally show ?thesis
    by simp
qed

lemma csubspace_commutant[simp]: \<open>csubspace (commutant X)\<close>
  by (auto simp add: complex_vector.subspace_def commutant_def cblinfun_compose_add_right cblinfun_compose_add_left)

lemma closed_commutant[simp]: \<open>closed (commutant X)\<close>
proof (subst closed_sequential_limits, intro allI impI, erule conjE)
  fix s :: \<open>nat \<Rightarrow> _\<close> and l 
  assume s_comm: \<open>\<forall>n. s n \<in> commutant X\<close>
  assume \<open>s \<longlonglongrightarrow> l\<close>
  have \<open>l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l = 0\<close> if \<open>x \<in> X\<close> for x
  proof -
    from \<open>s \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda>n. s n o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L s n) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      apply (rule isCont_tendsto_compose[rotated])
      by (intro continuous_intros)
    then have \<open>(\<lambda>_. 0) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      using s_comm that by (auto simp add: commutant_def)
    then show ?thesis
      by (simp add: LIMSEQ_const_iff that)
  qed
  then show \<open>l \<in> commutant X\<close>
    by (simp add: commutant_def)
qed

lemma closed_csubspace_commutant[simp]: \<open>closed_csubspace (commutant X)\<close>
  apply (rule closed_csubspace.intro) by simp_all

lemma commutant_mult: \<open>a o\<^sub>C\<^sub>L b \<in> commutant X\<close> if \<open>a \<in> commutant X\<close> and \<open>b \<in> commutant X\<close>
  using that 
  apply (auto simp: commutant_def cblinfun_compose_assoc)
  by (simp flip: cblinfun_compose_assoc)

lemma double_commutant_grows[simp]: \<open>X \<subseteq> commutant (commutant X)\<close>
  by (auto simp add: commutant_def)

lemma commutant_antimono: \<open>X \<subseteq> Y \<Longrightarrow> commutant X \<supseteq> commutant Y\<close>
  by (auto simp add: commutant_def)




lemma triple_commutant[simp]: \<open>commutant (commutant (commutant X)) = commutant X\<close>
  by (auto simp: commutant_def)

lemma commutant_adj: \<open>adj ` commutant X = commutant (adj ` X)\<close>
  apply (auto intro!: image_eqI double_adj[symmetric] simp: commutant_def simp flip: adj_cblinfun_compose)
  by (metis adj_cblinfun_compose double_adj)

lemma commutant_empty[simp]: \<open>commutant {} = UNIV\<close>
  by (simp add: commutant_def)


lemma commutant_weak_star_closed[simp]: \<open>closedin weak_star_topology (commutant X)\<close>
proof -
  have comm_inter: \<open>commutant X = (\<Inter>x\<in>X. commutant {x})\<close>
    by (auto simp: commutant_def)
  have comm_x: \<open>commutant {x} = (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0}\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    by (auto simp add: commutant_def vimage_def)
  have cont: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x)\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    apply (rule continuous_intros)
    by (simp_all add: continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star)
  have \<open>closedin weak_star_topology ((\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0})\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using closedin_vimage[where U=\<open>weak_star_topology\<close> and S=\<open>{0}\<close> and T=weak_star_topology]
    using cont by (auto simp add: closedin_singleton')
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    using closedin_topspace[of weak_star_topology]
    by (auto simp add: comm_inter comm_x)
qed

lemma cspan_in_double_commutant: \<open>cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: complex_vector.span_minimal)

lemma weak_star_closure_in_double_commutant: \<open>weak_star_topology closure_of X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal)

lemma weak_star_closure_cspan_in_double_commutant: \<open>weak_star_topology closure_of cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal cspan_in_double_commutant)


lemma commutant_memberI:
  assumes \<open>\<And>y. y \<in> X \<Longrightarrow> x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close>
  shows \<open>x \<in> commutant X\<close>
  using assms by (simp add: commutant_def)

lemma commutant_sot_closed: \<open>closedin cstrong_operator_topology (commutant A)\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Exercise IX.6.2\<close>
proof (cases \<open>A = {}\<close>)
  case True
  then show ?thesis
    apply simp
    by (metis closedin_topspace cstrong_operator_topology_topspace)
next
  case False
  have closed_a: \<open>closedin cstrong_operator_topology (commutant {a})\<close> for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    have comm_a: \<open>commutant {a} = (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a) -` {0}\<close>
      by (auto simp: commutant_def)
    have closed_0: \<open>closedin cstrong_operator_topology {0}\<close>
      apply (rule closedin_singleton')
      by simp_all
    have cont: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a)\<close>
      by (intro continuous_intros continuous_map_left_comp_sot continuous_map_right_comp_sot)
      (* TODO: Put continuous_map_left_comp_sot continuous_map_right_comp_sot into [continuous_intros]
              (suitably rewritten) *)
    show ?thesis
      using closedin_vimage[OF closed_0 cont]
      by (simp add: comm_a)
  qed
  have *: \<open>commutant A = (\<Inter>a\<in>A. commutant {a})\<close>
    by (auto simp add: commutant_def)
  show ?thesis
    by (auto intro!: closedin_Inter simp: * False closed_a)
qed

fun inflation_op' :: \<open>nat \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list \<Rightarrow> ('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2\<close> where
  \<open>inflation_op' n Nil = 0\<close>
| \<open>inflation_op' n (a#as) = (a \<otimes>\<^sub>o butterfly (ket n) (ket n)) + inflation_op' (n+1) as\<close>

abbreviation \<open>inflation_op \<equiv> inflation_op' 0\<close>

fun inflation_state' :: \<open>nat \<Rightarrow> 'a ell2 list \<Rightarrow> ('a\<times>nat) ell2\<close> where
  \<open>inflation_state' n Nil = 0\<close>
| \<open>inflation_state' n (a#as) = (a \<otimes>\<^sub>s ket n) + inflation_state' (n+1) as\<close>

abbreviation \<open>inflation_state \<equiv> inflation_state' 0\<close>

fun inflation_space' :: \<open>nat \<Rightarrow> 'a ell2 ccsubspace list \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_space' n Nil = 0\<close>
| \<open>inflation_space' n (S#Ss) = (S \<otimes>\<^sub>S ccspan {ket n}) + inflation_space' (n+1) Ss\<close>

abbreviation \<open>inflation_space \<equiv> inflation_space' 0\<close>

definition inflation_carrier :: \<open>nat \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_carrier n = inflation_space (replicate n \<top>)\<close>

definition inflation_op_carrier :: \<open>nat \<Rightarrow> (('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2) set\<close> where
  \<open>inflation_op_carrier n = { Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) | a. True }\<close>

lemma inflation_op_compose_outside: \<open>inflation_op' m ops o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o butterfly (ket n) (ket n)) = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_left comp_tensor_op cinner_ket)

lemma inflation_op_compose_outside_rev: \<open>(a \<otimes>\<^sub>o butterfly (ket n) (ket n)) o\<^sub>C\<^sub>L inflation_op' m ops = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_right comp_tensor_op cinner_ket)


lemma Proj_inflation_carrier: \<open>Proj (inflation_carrier n) = inflation_op (replicate n id_cblinfun)\<close>
proof -
  have \<open>Proj (inflation_space' m (replicate n \<top>)) = inflation_op' m (replicate n id_cblinfun)\<close> for m
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    have *: \<open>orthogonal_spaces ((\<top> :: 'b ell2 ccsubspace) \<otimes>\<^sub>S ccspan {ket m}) (inflation_space' (Suc m) (replicate n \<top>))\<close>
      by (auto simp add: orthogonal_projectors_orthogonal_spaces Suc tensor_ccsubspace_via_Proj 
          Proj_on_own_range is_Proj_tensor_op inflation_op_compose_outside_rev butterfly_is_Proj
          simp flip: butterfly_eq_proj)
    show ?case 
      apply (simp add: Suc * Proj_sup)
      by (metis (no_types, opaque_lifting) Proj_is_Proj Proj_on_own_range Proj_top 
          butterfly_eq_proj is_Proj_tensor_op norm_ket tensor_ccsubspace_via_Proj)
  qed
  then show ?thesis
    by (force simp add: inflation_carrier_def)
qed

lemma inflation_op_carrierI:
  assumes \<open>Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) = a\<close>
  shows \<open>a \<in> inflation_op_carrier n\<close>
  using assms by (auto intro!: exI[of _ a] simp add: inflation_op_carrier_def)

lemma inflation_op_compose: \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n ops2 = inflation_op' n (map2 cblinfun_compose ops1 ops2)\<close>
proof (induction ops2 arbitrary: ops1 n)
  case Nil
  then show ?case by simp
next
  case (Cons op ops2)
  note IH = this
  fix ops1 :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list\<close>
  show \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n (op # ops2) =
        inflation_op' n (map2 (o\<^sub>C\<^sub>L) ops1 (op # ops2))\<close>
  proof (cases ops1)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun_compose_add_right cblinfun_compose_add_left tensor_op_ell2
          inflation_op_compose_outside comp_tensor_op inflation_op_compose_outside_rev
          flip: IH)
  qed
qed

lemma inflation_op_in_carrier: \<open>inflation_op ops \<in> inflation_op_carrier n\<close> if \<open>length ops \<le> n\<close>
  apply (rule inflation_op_carrierI)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_carrier_def inflation_op_compose
      zip_replicate1 zip_replicate2 o_def)

lemma inflation_op'_apply_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma inflation_op'_compose_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = 0\<close>
  apply (rule cblinfun_eqI)
  by (simp add: inflation_op'_apply_tensor_outside)

lemma inflation_state'_apply_tensor_outside: \<open>n < m \<Longrightarrow> (a \<otimes>\<^sub>o butterfly \<psi> (ket n)) *\<^sub>V inflation_state' m vs = 0\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cblinfun.add_right tensor_op_ell2 cinner_ket)

lemma inflation_op_apply_inflation_state: \<open>inflation_op' n ops *\<^sub>V inflation_state' n vecs = inflation_state' n (map2 cblinfun_apply ops vecs)\<close>
proof (induction vecs arbitrary: ops n)
  case Nil
  then show ?case by simp
next
  case (Cons v vecs)
  note IH = this
  fix ops :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) list\<close>
  show \<open>inflation_op' n ops *\<^sub>V inflation_state' n (v # vecs) =
        inflation_state' n (map2 (*\<^sub>V) ops (v # vecs))\<close>
  proof (cases ops)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun.add_right cblinfun.add_left tensor_op_ell2
          inflation_op'_apply_tensor_outside inflation_state'_apply_tensor_outside
          flip: IH)
  qed
qed

lemma inflation_state_in_carrier: \<open>inflation_state vecs \<in> space_as_set (inflation_carrier n)\<close> if \<open>length vecs + m \<le> n\<close>
  apply (rule space_as_setI_via_Proj)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_apply_inflation_state zip_replicate1 o_def)

lemma inflation_op'_apply_tensor_outside': \<open>n \<ge> length as + m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma Proj_inflation_carrier_outside: \<open>Proj (inflation_carrier n) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close>
  by (simp add: Proj_inflation_carrier inflation_op'_apply_tensor_outside' that)

lemma inflation_state'_is_orthogonal_outside: \<open>n < m \<Longrightarrow> is_orthogonal (a \<otimes>\<^sub>s ket n) (inflation_state' m vs)\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cinner_add_right)

lemma inflation_op_adj: \<open>(inflation_op' n ops)* = inflation_op' n (map adj ops)\<close>
  apply (induction ops arbitrary: n)
  by (simp_all add: adj_plus tensor_op_adjoint)


lemma inflation_state0:
  assumes \<open>\<And>v. v \<in> set f \<Longrightarrow> v = 0\<close>
  shows \<open>inflation_state' n f = 0\<close>
  using assms apply (induction f arbitrary: n)
   apply simp
  using tensor_ell2_0_left by force

lemma inflation_state_plus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f + inflation_state' n g = inflation_state' n (map2 plus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_add1)

lemma inflation_state_minus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f - inflation_state' n g = inflation_state' n (map2 minus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_diff1)

lemma inflation_state_scaleC:
  shows \<open>c *\<^sub>C inflation_state' n f = inflation_state' n (map (scaleC c) f)\<close>
  apply (induction f arbitrary: n)
  by (auto simp: algebra_simps tensor_ell2_scaleC1)

lemma inflation_op_compose_tensor_ell2_right:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = tensor_ell2_right (ket i) o\<^sub>C\<^sub>L (f!(i-n))\<close>
proof (insert assms, induction f arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons a f)
  show ?case
  proof (cases \<open>i = n\<close>)
    case True
    have \<open>a \<otimes>\<^sub>o butterfly (ket n) (ket n) o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = tensor_ell2_right (ket n) o\<^sub>C\<^sub>L a\<close>
      apply (rule cblinfun_eqI)
      by (simp add: tensor_op_ell2 cinner_ket)
    with True show ?thesis
      by (simp add: cblinfun_compose_add_left inflation_op'_compose_tensor_outside)
  next
    case False
    with Cons.prems have 1: \<open>Suc n \<le> i\<close>
      by presburger
    have 2: \<open>a \<otimes>\<^sub>o butterfly (ket n) (ket n) o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = 0\<close>
      apply (rule cblinfun_eqI)
      using False by (simp add: tensor_op_ell2 cinner_ket)
    show ?thesis
      using Cons.prems 1
      by (simp add: cblinfun_compose_add_left Cons.IH[where n=\<open>Suc n\<close>] 2)
  qed
qed

lemma inflation_op_apply:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = (f!(i-n) *\<^sub>V \<psi>) \<otimes>\<^sub>s ket i\<close>
  by (simp add: inflation_op_compose_tensor_ell2_right assms
      flip: tensor_ell2_right_apply cblinfun_apply_cblinfun_compose)

lemma norm_inflation_state:
  \<open>norm (inflation_state' n f) = sqrt (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
proof -
  have \<open>(norm (inflation_state' n f))\<^sup>2 = (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
  proof (induction f arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons v f)
    have \<open>(norm (inflation_state' n (v # f)))\<^sup>2 = (norm (v \<otimes>\<^sub>s ket n + inflation_state' (Suc n) f))\<^sup>2\<close>
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (norm (inflation_state' (Suc n) f))\<^sup>2\<close>
      apply (rule pythagorean_theorem)
      apply (rule inflation_state'_is_orthogonal_outside)
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = (norm v)\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: norm_tensor_ell2)
    also have \<open>\<dots> = (\<Sum>v\<leftarrow>v#f. (norm v)\<^sup>2)\<close>
      by simp
    finally show ?case
      by -
  qed
  then show ?thesis
    by (simp add: real_sqrt_unique)
qed


lemma cstrong_operator_topology_in_closure_algebraicI:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.5.3\<close>
  assumes space: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes one: \<open>id_cblinfun \<in> A\<close>
  assumes main: \<open>\<And>n S. S \<le> inflation_carrier n \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S S \<le> S) \<Longrightarrow>
                 inflation_op (replicate n b) *\<^sub>S S \<le> S\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof (rule cstrong_operator_topology_in_closureI)
  fix F :: \<open>'a ell2 set\<close> and \<epsilon> :: real
  assume \<open>finite F\<close> and \<open>\<epsilon> > 0\<close>
  obtain f where \<open>set f = F\<close> and \<open>distinct f\<close>
    using \<open>finite F\<close> finite_distinct_list by blast
  define n M' M where \<open>n = length f\<close>
    and \<open>M' = ((\<lambda>a. inflation_state (map (cblinfun_apply a) f)) ` A)\<close>
    and \<open>M = ccspan M'\<close>
  have M_carrier: \<open>M \<le> inflation_carrier n\<close>
  proof -
    have \<open>M' \<subseteq> space_as_set (inflation_carrier n)\<close>
      by (auto intro!: inflation_state_in_carrier simp add: M'_def n_def)
    then show ?thesis
      by (simp add: M_def ccspan_leqI)
  qed

  have \<open>inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> if \<open>a \<in> A\<close> for a
  proof (unfold M_def, rule cblinfun_image_ccspan_leqI)
    fix v assume \<open>v \<in> M'\<close>
    then obtain a' where \<open>a' \<in> A\<close> and v_def: \<open>v = inflation_state (map (cblinfun_apply a') f)\<close>
      using M'_def by blast
    then have \<open>inflation_op (replicate n a) *\<^sub>V v = inflation_state (map ((*\<^sub>V) (a o\<^sub>C\<^sub>L a')) f)\<close>
      by (simp add: v_def n_def inflation_op_apply_inflation_state map2_map_map 
          flip: cblinfun_apply_cblinfun_compose map_replicate_const)
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def \<open>a' \<in> A\<close> \<open>a \<in> A\<close> mult
      by simp
    also have \<open>\<dots> \<subseteq> space_as_set (ccspan M')\<close>
      by (simp add: ccspan_superset)
    finally show \<open>inflation_op (replicate n a) *\<^sub>V v \<in> space_as_set (ccspan M')\<close>
      by -
  qed
  then have b_invariant: \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    using M_carrier by (simp add: main)
  have f_M: \<open>inflation_state f \<in> space_as_set M\<close>
  proof -
    have \<open>inflation_state f = inflation_state (map (cblinfun_apply id_cblinfun) f)\<close>
      by simp
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def one by blast
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      by (simp add: M_def ccspan_superset)
    finally show ?thesis
      by -
  qed
  have \<open>csubspace M'\<close>
  proof (rule complex_vector.subspaceI)
    fix c x y
    show \<open>0 \<in> M'\<close>
      apply (auto intro!: image_eqI[where x=0] simp add: M'_def)
       apply (subst inflation_state0)
      by (auto simp add: space complex_vector.subspace_0)
    show \<open>x \<in> M' \<Longrightarrow> y \<in> M' \<Longrightarrow> x + y \<in> M'\<close>
      by (auto intro!: image_eqI[where x=\<open>_ + _\<close>] 
          simp add: M'_def inflation_state_plus map2_map_map
          cblinfun.add_left[abs_def] space complex_vector.subspace_add)
    show \<open>c *\<^sub>C x \<in> M' \<close> if \<open>x \<in> M'\<close>
    proof -
      from that
      obtain a where \<open>a \<in> A\<close> and \<open>x = inflation_state (map ((*\<^sub>V) a) f)\<close>
        by (auto simp add: M'_def)
      then have \<open>c *\<^sub>C x = inflation_state (map ((*\<^sub>V) (c *\<^sub>C a)) f)\<close>
        by (simp add: inflation_state_scaleC o_def scaleC_cblinfun.rep_eq)
      moreover have \<open>c *\<^sub>C a \<in> A\<close>
         by (simp add: \<open>a \<in> A\<close> space complex_vector.subspace_scale)
      ultimately show ?thesis
        unfolding M'_def
        by (rule image_eqI)
    qed
  qed
  then have M_closure_M': \<open>space_as_set M = closure M'\<close>
    by (metis M_def ccspan.rep_eq complex_vector.span_eq_iff)
  have \<open>inflation_state (map (cblinfun_apply b) f) \<in> space_as_set M\<close>
  proof -
    have \<open>map2 (*\<^sub>V) (replicate n b) f = map ((*\<^sub>V) b) f\<close>
      using map2_map_map[where h=cblinfun_apply and g=id and f=\<open>\<lambda>_. b\<close> and xs=f]
      by (simp add: n_def flip: map_replicate_const)
    then have \<open>inflation_state (map (cblinfun_apply b) f) = inflation_op (replicate n b) *\<^sub>V inflation_state f\<close>
      by (simp add: inflation_op_apply_inflation_state)
    also have \<open>\<dots> \<in> space_as_set (inflation_op (replicate n b) *\<^sub>S M)\<close>
      by (simp add: f_M cblinfun_apply_in_image')
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      using b_invariant less_eq_ccsubspace.rep_eq by blast
    finally show ?thesis
      by -
  qed
    (* apply (auto intro!: ccspan_superset' simp add: M_def M'_def) *)
  then obtain m where \<open>m \<in> M'\<close> and m_close: \<open>norm (m - inflation_state (map (cblinfun_apply b) f)) \<le> \<epsilon>\<close>
    apply atomize_elim
    apply (simp add: M_closure_M' closure_approachable dist_norm)
    using \<open>\<epsilon> > 0\<close> by fastforce
  from \<open>m \<in> M'\<close>
  obtain a where \<open>a \<in> A\<close> and m_def: \<open>m = inflation_state (map (cblinfun_apply a) f)\<close>
    by (auto simp add: M'_def)
  have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) \<le> \<epsilon>\<^sup>2\<close>
  proof -
    have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) = (norm (inflation_state (map (cblinfun_apply (a - b)) f)))\<^sup>2\<close>
      apply (simp add: norm_inflation_state o_def)
      apply (subst real_sqrt_pow2)
       apply (rule sum_list_nonneg)
      by (auto simp: sum_list_nonneg)
    also have \<open>\<dots> = (norm (m - inflation_state (map (cblinfun_apply b) f)))\<^sup>2\<close>
      by (simp add: m_def inflation_state_minus map2_map_map cblinfun.diff_left[abs_def])
    also have \<open>\<dots> \<le> \<epsilon>\<^sup>2\<close>
      by (simp add: m_close power_mono)
    finally show ?thesis
      by -
  qed
  then have \<open>(norm ((a - b) *\<^sub>V v))\<^sup>2 \<le> \<epsilon>\<^sup>2\<close> if \<open>v \<in> F\<close> for v
    using that apply (simp flip: sum.distinct_set_conv_list add: \<open>distinct f\<close>)
    by (smt (verit) \<open>finite F\<close> \<open>set f = F\<close> sum_nonneg_leq_bound zero_le_power2)
  then show \<open>\<exists>a\<in>A. \<forall>f\<in>F. norm ((b - a) *\<^sub>V f) \<le> \<epsilon>\<close>
    using \<open>0 < \<epsilon>\<close> \<open>a \<in> A\<close>
    by (metis cblinfun.real.diff_left norm_minus_commute power2_le_imp_le power_eq_0_iff power_zero_numeral realpow_pos_nth_unique zero_compare_simps(12))
qed

lemma commutant_inflation:
  \<comment> \<open>One direction of \<^cite>\<open>conway2013course\<close>, Proposition IX.6.2.\<close>
  fixes n
  defines \<open>\<And>X. commutant' X \<equiv> commutant X \<inter> inflation_op_carrier n\<close>
  shows \<open>(\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A) 
         \<subseteq> commutant' (commutant' ((\<lambda>a. inflation_op (replicate n a)) ` A))\<close>
proof (unfold commutant'_def, rule subsetI, rule IntI)
  fix b
  assume \<open>b \<in> (\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A)\<close>
  then obtain b0 where b_def: \<open>b = inflation_op (replicate n b0)\<close> and b0_A'': \<open>b0 \<in> commutant (commutant A)\<close>
    by auto
  show \<open>b \<in> inflation_op_carrier n\<close>
    by (simp add: b_def inflation_op_in_carrier)
  show \<open>b \<in> commutant (commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n)\<close>
  proof (rule commutant_memberI)
    fix c
    assume \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n\<close>
    then have c_comm: \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A)\<close>
      and c_carr: \<open>c \<in> inflation_op_carrier n\<close>
      by auto
    define c' where \<open>c' i j = (tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close> for i j
    have \<open>c' i j o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L c' i j\<close> if \<open>a \<in> A\<close> and \<open>i < n\<close> and \<open>j < n\<close> for a i j
    proof -
      from c_comm have \<open>c o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L c\<close>
        using that by (auto simp: commutant_def)
      then have \<open>(tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L tensor_ell2_right (ket j))
               = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close>
        apply (simp add: inflation_op_adj)
        by (metis (no_types, lifting) lift_cblinfun_comp(2))
      then show ?thesis
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        by (simp add: that c'_def cblinfun_compose_assoc)
    qed
    then have \<open>c' i j \<in> commutant A\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_memberI)
    with b0_A'' have b0_c': \<open>b0 o\<^sub>C\<^sub>L c' i j = c' i j o\<^sub>C\<^sub>L b0\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_def)

    from c_carr obtain c'' where c'': \<open>c = Proj (inflation_carrier n) o\<^sub>C\<^sub>L c'' o\<^sub>C\<^sub>L Proj (inflation_carrier n)\<close>
      by (auto simp add: inflation_op_carrier_def)
    
    have c0: \<open>c *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close> for i \<psi>
      using that by (simp add: c'' Proj_inflation_carrier_outside)
    have cadj0: \<open>c* *\<^sub>V (\<psi> \<otimes>\<^sub>s ket j) = 0\<close> if \<open>j \<ge> n\<close> for j \<psi>
      using that by (simp add: c'' adj_Proj Proj_inflation_carrier_outside)

    have \<open>inflation_op (replicate n b0) o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L inflation_op (replicate n b0)\<close>
    proof (rule equal_ket, rule cinner_ket_eqI)
      fix ii jj
      obtain i' j' :: 'a and i j :: nat where ii_def: \<open>ii = (i',i)\<close> and jj_def: \<open>jj = (j',j)\<close>
        by force
      show \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) =
                 ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
      proof (cases \<open>i < n \<and> j < n\<close>)
        case True
        have \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) = ((b0* *\<^sub>V ket i') \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V ket j' \<otimes>\<^sub>s ket j)\<close>
          using True by (simp add: ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        also have \<open>\<dots> = (ket i' \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V (b0 *\<^sub>V ket j') \<otimes>\<^sub>s ket j)\<close>
          using b0_c' apply (simp add: c'_def flip: tensor_ell2_right_apply cinner_adj_right)
          by (metis (no_types, lifting) True simp_a_oCL_b')
        also have \<open>\<dots> = ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
          by (simp add: True ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        finally show ?thesis
          by -
      next
        case False
        then show ?thesis
          apply (auto simp add: ii_def jj_def inflation_op_adj c0 inflation_op'_apply_tensor_outside'
              simp flip: tensor_ell2_ket  cinner_adj_left[where G=\<open>inflation_op _\<close>])
          by (simp add: cadj0 flip: cinner_adj_left[where G=c])
      qed
    qed
    then show \<open>b o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L b\<close>
      by (simp add: b_def)
  qed
qed

lemma double_commutant_theorem_aux:
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of the form \<^typ>\<open>'a ell2\<close>\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>csubspace A\<close>
  assumes \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (intro Set.set_eqI iffI)
  show \<open>x \<in> commutant (commutant A)\<close> if \<open>x \<in> cstrong_operator_topology closure_of A\<close> for x
    using closure_of_minimal commutant_sot_closed double_commutant_grows that by blast
next
  show \<open>b \<in> cstrong_operator_topology closure_of A\<close> if b_A'': \<open>b \<in> commutant (commutant A)\<close> for b
  proof (rule cstrong_operator_topology_in_closure_algebraicI)
    show \<open>csubspace A\<close> and \<open>a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close> and \<open>id_cblinfun \<in> A\<close> for a a'
      using assms by auto
    fix n M
    assume asm: \<open>a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> for a
    assume M_carrier: \<open>M \<le> inflation_carrier n\<close>
    define commutant' where \<open>commutant' X = commutant X \<inter> inflation_op_carrier n\<close> for X :: \<open>(('a \<times> nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> nat) ell2) set\<close>
    define An where \<open>An = (\<lambda>a. inflation_op (replicate n a)) ` A\<close>
    have *: \<open>Proj M o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
      apply (rule Proj_compose_cancelI)
      using asm that by (simp add: cblinfun_compose_image)
    have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
    proof -
      have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        by (simp add: inflation_op_adj adj_Proj)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        apply (subst *[symmetric])
        by (simp_all add: that assms flip: cblinfun_compose_assoc)
      also have \<open>\<dots> = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        by (simp add: inflation_op_adj adj_Proj cblinfun_compose_assoc)
      also have \<open>\<dots> = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        apply (subst *[symmetric])
        by (simp_all add: that flip: cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    then have \<open>Proj M \<in> commutant' An\<close>
      using  M_carrier 
      apply (auto intro!: inflation_op_carrierI simp add: An_def commutant_def commutant'_def)
      by (metis Proj_compose_cancelI Proj_range adj_Proj adj_cblinfun_compose)
    from b_A'' have \<open>inflation_op (replicate n b) \<in> commutant' (commutant' An)\<close>
      using commutant_inflation[of n A, folded commutant'_def]
      by (auto simp add: An_def commutant'_def)
    with \<open>Proj M \<in> commutant' An\<close>
    have *: \<open>inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)\<close>
      by (simp add: commutant_def commutant'_def)
    show \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    proof -
      have \<open>inflation_op (replicate n b) *\<^sub>S M = (inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M) *\<^sub>S \<top>\<close>
        by (metis lift_cblinfun_comp(3) Proj_range)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)) *\<^sub>S \<top>\<close>
        by (simp add: * )
      also have \<open>\<dots> \<le> M\<close>
        by (metis lift_cblinfun_comp(3) Proj_image_leq)
      finally show ?thesis
        by -
    qed
  qed
qed

lemma sandwich_sot_cont[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. sandwich A (f x))\<close>
  apply (simp add: sandwich_apply)
  by (intro continuous_intros assms)

lemma double_commutant_theorem_aux2:
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of typeclass \<^class>\<open>not_singleton\<close>\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof -
  define A' :: \<open>('a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a chilbert2ell2 ell2) set\<close>
    where \<open>A' = sandwich (ell2_to_hilbert*) ` A\<close>
  have subspace: \<open>csubspace A'\<close>
    using subspace by (auto intro!: complex_vector.linear_subspace_image simp: A'_def)
  have mult: \<open>\<And>a a'. a \<in> A' \<Longrightarrow> a' \<in> A' \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A'\<close>
    using mult by (auto simp add: A'_def sandwich_arg_compose unitary_ell2_to_hilbert)
  have id: \<open>id_cblinfun \<in> A'\<close>
    using id by (auto intro!: image_eqI simp add: A'_def sandwich_isometry_id unitary_ell2_to_hilbert)
  have adj: \<open>\<And>a. a \<in> A' \<Longrightarrow> a* \<in> A'\<close>
    using adj by (auto intro!: image_eqI simp: A'_def simp flip: sandwich_apply_adj)
  have homeo: \<open>homeomorphic_map cstrong_operator_topology cstrong_operator_topology
     ((*\<^sub>V) (sandwich ell2_to_hilbert))\<close>
    by (auto intro!: continuous_intros homeomorphic_maps_imp_map[where g=\<open>sandwich (ell2_to_hilbert*)\<close>]
        simp: homeomorphic_maps_def unitary_ell2_to_hilbert
        simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)
  have \<open>commutant (commutant A') = cstrong_operator_topology closure_of A'\<close>
    using subspace mult id adj by (rule double_commutant_theorem_aux)
  then have \<open>sandwich ell2_to_hilbert ` commutant (commutant A') = sandwich ell2_to_hilbert ` (cstrong_operator_topology closure_of A')\<close>
    by simp
  then show ?thesis
    by (simp add: A'_def unitary_ell2_to_hilbert sandwich_unitary_commutant image_image homeo
        flip: cblinfun_apply_cblinfun_compose sandwich_compose
        homeomorphic_map_closure_of[where Y=cstrong_operator_topology])
qed

lemma double_commutant_theorem:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (cases \<open>UNIV = {0::'a}\<close>)
  case True
  then have \<open>(x :: 'a) = 0\<close> for x
    by auto
  then have UNIV_0: \<open>UNIV = {0 :: 'a\<Rightarrow>\<^sub>C\<^sub>L'a}\<close>
    by (auto intro!: cblinfun_eqI)
  have \<open>0 \<in> commutant (commutant A)\<close>
    using complex_vector.subspace_0 csubspace_commutant by blast
  then have 1: \<open>commutant (commutant A) = UNIV\<close>
    using UNIV_0
    by force
  have \<open>0 \<in> A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have \<open>0 \<in> cstrong_operator_topology closure_of A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have 2: \<open>cstrong_operator_topology closure_of A = UNIV\<close>
    using UNIV_0
    by force
  from 1 2 show ?thesis 
    by simp
next
  case False
  note aux2 = double_commutant_theorem_aux2[where 'a=\<open>'z::{chilbert_space,not_singleton}\<close>, rule_format, internalize_sort \<open>'z::{chilbert_space,not_singleton}\<close>]
  have hilbert: \<open>class.chilbert_space (*\<^sub>R) (*\<^sub>C) (+) (0::'a) (-) uminus dist norm sgn uniformity open (\<bullet>\<^sub>C)\<close>
    by (rule chilbert_space_class.chilbert_space_axioms)
  from False
  have not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    by (rule class_not_singletonI_monoid_add)
  show ?thesis 
    apply (rule aux2)
    using assms hilbert not_singleton by auto
qed

hide_fact double_commutant_theorem_aux double_commutant_theorem_aux2



definition one_algebra :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close> where
  \<open>one_algebra = range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>

lemma commutant_tensor1': \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
proof -
  have \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = commutant (sandwich swap_ell2 ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (metis (no_types, lifting) image_cong range_composition swap_tensor_op_sandwich)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (simp add: sandwich_unitary_commutant)
  also have \<open>\<dots> = sandwich swap_ell2 ` range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
    by (simp add: commutant_tensor1)
  also have \<open>\<dots> = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  finally show ?thesis
    by -
qed



lemma closed_map_sot_tensor_op_id_right: 
  \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close>
proof (unfold closed_map_def, intro allI impI)
  fix U :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assume closed_U: \<open>closedin cstrong_operator_topology U\<close>

  have aux1: \<open>range f \<subseteq> X \<longleftrightarrow> (\<forall>x. f x \<in> X)\<close> for f :: \<open>'x \<Rightarrow> 'y\<close> and X
    by blast

  have \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close> if range: \<open>range (\<lambda>x. f x) \<subseteq> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
    and limit: \<open>limitin cstrong_operator_topology f l F\<close> and \<open>F \<noteq> \<bottom>\<close> 
  for f and l :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> and F :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) filter\<close>
  proof -
    from range obtain f' where f'U: \<open>range f' \<subseteq> U\<close> and f_def: \<open>f y = f' y \<otimes>\<^sub>o id_cblinfun\<close> for y
      apply atomize_elim
      apply (subst aux1)
      apply (rule choice2)
      by auto
    have \<open>l \<in> commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a))\<close>
    proof (rule commutant_memberI)
      fix c :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> 
      assume \<open>c \<in> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
      then obtain c' where c_def: \<open>c = id_cblinfun \<otimes>\<^sub>o c'\<close>
        by blast
      from limit have 1: \<open>limitin cstrong_operator_topology ((\<lambda>z. z o\<^sub>C\<^sub>L c) o f) (l o\<^sub>C\<^sub>L c) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_right_comp_sot)
      from limit have 2: \<open>limitin cstrong_operator_topology ((\<lambda>z. c o\<^sub>C\<^sub>L z) o f) (c o\<^sub>C\<^sub>L l) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_left_comp_sot)
      have 3: \<open>f x o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L f x\<close> for x
        by (simp add: f_def c_def comp_tensor_op)
      from 1 2 show \<open>l o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L l\<close>
        unfolding 3 o_def
        by (meson hausdorff_sot limitin_unique that(3))
    qed
    then have \<open>l \<in> range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: commutant_tensor1')
    then obtain l' where l_def: \<open>l = l' \<otimes>\<^sub>o id_cblinfun\<close>
      by blast
    have \<open>limitin cstrong_operator_topology f' l' F\<close>
    proof (rule limitin_cstrong_operator_topology[THEN iffD2], rule allI)
      fix \<psi> fix b :: 'b
      have \<open>((\<lambda>x. f x *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) \<longlongrightarrow> l *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) F\<close>
        using limitin_cstrong_operator_topology that(2) by auto
      then have \<open>((\<lambda>x. (f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) \<longlongrightarrow> (l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) F\<close>
        by (simp add: f_def l_def tensor_op_ell2)
      then have \<open>((\<lambda>x. (tensor_ell2_right (ket b))* *\<^sub>V ((f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) 
                  \<longlongrightarrow> (tensor_ell2_right (ket b))* *\<^sub>V ((l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) F\<close>
        apply (rule cblinfun.tendsto[rotated])
        by simp
      then show \<open>((\<lambda>x. f' x *\<^sub>V \<psi>) \<longlongrightarrow> l' *\<^sub>V \<psi>) F\<close>
        by (simp add: tensor_ell2_right_adj_apply)
    qed
    with closed_U f'U \<open>F \<noteq> \<bottom>\<close> have \<open>l' \<in> U\<close>
      by (simp add: Misc_Tensor_Product.limitin_closedin)
    then show \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
      by (simp add: l_def)
  qed
  then show \<open>closedin cstrong_operator_topology ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) ` U)\<close>
    apply (rule_tac closedin_if_converge_inside)
    by simp_all
qed

definition von_neumann_algebra where \<open>von_neumann_algebra A \<longleftrightarrow> (\<forall>a\<in>A. a* \<in> A) \<and> commutant (commutant A) = A\<close>
definition von_neumann_factor where \<open>von_neumann_factor A \<longleftrightarrow> von_neumann_algebra A \<and> A \<inter> commutant A = one_algebra\<close>

lemma von_neumann_algebraI: \<open>(\<And>a. a\<in>A \<Longrightarrow> a* \<in> A) \<Longrightarrow> commutant (commutant A) \<subseteq> A \<Longrightarrow> von_neumann_algebra A\<close> for \<FF>
  apply (auto simp: von_neumann_algebra_def)
  using double_commutant_grows by blast

lemma von_neumann_factorI:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>A \<inter> commutant A \<subseteq> one_algebra\<close>
  shows \<open>von_neumann_factor A\<close>
proof -
  have 1: \<open>A \<supseteq> one_algebra\<close>
    apply (subst asm_rl[of \<open>A = commutant (commutant A)\<close>])
    using assms(1) von_neumann_algebra_def apply blast
    by (auto simp: commutant_def one_algebra_def)
  have 2: \<open>commutant A \<supseteq> one_algebra\<close>
    by (auto simp: commutant_def one_algebra_def)
  from 1 2 assms show ?thesis
    by (auto simp add: von_neumann_factor_def)
qed

lemma commutant_UNIV: \<open>commutant (UNIV :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set) = one_algebra\<close>
  (* Not sure if the assumption chilbert_space is needed *)
proof -
  have 1: \<open>c *\<^sub>C id_cblinfun \<in> commutant UNIV\<close> for c
    by (simp add: commutant_def)
  moreover have 2: \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close> if x_comm: \<open>x \<in> commutant UNIV\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    have \<open>\<exists>c. x *\<^sub>V \<psi> = c *\<^sub>C \<psi>\<close> for \<psi>
    proof -
      have \<open>norm (x *\<^sub>V \<psi>) = norm ((x o\<^sub>C\<^sub>L selfbutter (sgn \<psi>)) *\<^sub>V \<psi>)\<close>
        by (simp add: cnorm_eq_1)
      also have \<open>\<dots> = norm ((selfbutter (sgn \<psi>) o\<^sub>C\<^sub>L x) *\<^sub>V \<psi>)\<close>
        using x_comm by (simp add: commutant_def del: butterfly_apply)
      also have \<open>\<dots> = norm (proj \<psi> *\<^sub>V (x *\<^sub>V \<psi>))\<close>
        by (simp add: butterfly_sgn_eq_proj)
      finally have \<open>x *\<^sub>V \<psi> \<in> space_as_set (ccspan {\<psi>})\<close>
        by (metis norm_Proj_apply)
      then show ?thesis
        by (auto simp add: ccspan_finite complex_vector.span_singleton)
    qed
    then obtain f where f: \<open>x *\<^sub>V \<psi> = f \<psi> *\<^sub>C \<psi>\<close> for \<psi>
      apply atomize_elim apply (rule choice) by auto

    have \<open>f \<psi> = f \<phi>\<close> if \<open>\<psi> \<in> B\<close> and \<open>\<phi> \<in> B\<close> for \<psi> \<phi>
    proof (cases \<open>\<psi> = \<phi>\<close>)
      case True
      then show ?thesis by simp
    next
      case False
      with that \<open>is_onb B\<close>
      have [simp]: \<open>\<psi> \<bullet>\<^sub>C \<phi> = 0\<close>
        by (auto simp: is_onb_def is_ortho_set_def)
      then have [simp]: \<open>\<phi> \<bullet>\<^sub>C \<psi> = 0\<close>
        using is_orthogonal_sym by blast
      from that \<open>is_onb B\<close> have [simp]: \<open>\<psi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)
      from that \<open>is_onb B\<close> have [simp]: \<open>\<phi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)

      have \<open>f (\<psi>+\<phi>) *\<^sub>C \<psi> + f (\<psi>+\<phi>) *\<^sub>C \<phi> = f (\<psi>+\<phi>) *\<^sub>C (\<psi> + \<phi>)\<close>
        by (simp add: complex_vector.vector_space_assms(1))
      also have \<open>\<dots> = x *\<^sub>V (\<psi> + \<phi>)\<close>
        by (simp add: f)
      also have \<open>\<dots> = x *\<^sub>V \<psi> + x *\<^sub>V \<phi>\<close>
        by (simp add: cblinfun.add_right)
      also have \<open>\<dots> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by (simp add: f)
      finally have *: \<open>f (\<psi> + \<phi>) *\<^sub>C \<psi> + f (\<psi> + \<phi>) *\<^sub>C \<phi> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by -
      have \<open>f (\<psi> + \<phi>) = f \<psi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<psi>\<close>]]
        by (simp add: cinner_add_right)
      moreover have \<open>f (\<psi> + \<phi>) = f \<phi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<phi>\<close>]]
        by (simp add: cinner_add_right)
      ultimately show \<open>f \<psi> = f \<phi>\<close>
        by simp
    qed
    then obtain c where \<open>f \<psi> = c\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by meson
    then have \<open>x *\<^sub>V \<psi> = (c *\<^sub>C id_cblinfun) *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by (simp add: f that)
    then have \<open>x = c *\<^sub>C id_cblinfun\<close>
      apply (rule cblinfun_eq_gen_eqI[where G=B])
      using \<open>is_onb B\<close> by (auto simp: is_onb_def)
    then show \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>
      by (auto)
  qed

  from 1 2 show ?thesis
    by (auto simp: one_algebra_def)
qed


lemma von_neumann_algebra_UNIV: \<open>von_neumann_algebra UNIV\<close>
  by (auto simp: von_neumann_algebra_def commutant_def)

lemma von_neumann_factor_UNIV: \<open>von_neumann_factor UNIV\<close>
  by (simp add: von_neumann_factor_def commutant_UNIV von_neumann_algebra_UNIV)

lemma von_neumann_algebra_UNION:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> von_neumann_algebra (A x)\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (\<Union>x\<in>X. A x)))\<close>
proof (rule von_neumann_algebraI)
  show \<open>commutant (commutant (commutant (commutant (\<Union>x\<in>X. A x))))
    \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by (meson commutant_antimono double_commutant_grows)
next
  fix a
  assume \<open>a \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
  then have \<open>a* \<in> adj ` commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by simp
  also have \<open>\<dots> = commutant (commutant (\<Union>x\<in>X. adj ` A x))\<close>
    by (simp add: commutant_adj image_UN)
  also have \<open>\<dots> \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    using assms by (auto simp: von_neumann_algebra_def intro!: commutant_antimono)
  finally show \<open>a* \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by -
qed

lemma von_neumann_algebra_union:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>von_neumann_algebra B\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (A \<union> B)))\<close>
  using von_neumann_algebra_UNION[where X=\<open>{True,False}\<close> and A=\<open>\<lambda>x. if x then A else B\<close>]
  by (auto simp: assms Un_ac(3))


lemma closed_map_sot_unitary_sandwich:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>unitary U\<close> (* Probably holds under weaker assumptions. *)
  shows \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>x. sandwich U x)\<close>
  apply (rule closed_eq_continuous_inverse_map[where g=\<open>sandwich (U*)\<close>, THEN iffD2])
  using assms 
  by (auto intro!: continuous_intros
      simp flip: sandwich_compose cblinfun_apply_cblinfun_compose)

lemma von_neumann_algebra_commutant: \<open>von_neumann_algebra (commutant A)\<close> if \<open>von_neumann_algebra A\<close>
proof (rule von_neumann_algebraI)
  show \<open>a* \<in> commutant A\<close> if \<open>a \<in> commutant A\<close> for a
    by (smt (verit) Set.basic_monos(7) \<open>von_neumann_algebra A\<close> commutant_adj commutant_antimono double_adj image_iff image_subsetI that von_neumann_algebra_def)
  show \<open>commutant (commutant (commutant A)) \<subseteq> commutant A \<close>
    by simp
qed


lemma id_in_commutant[iff]: \<open>id_cblinfun \<in> commutant A\<close>
  by (simp add: commutant_memberI)

lemma von_neumann_algebra_def_sot:
  \<open>von_neumann_algebra \<FF> \<longleftrightarrow> 
      (\<forall>a\<in>\<FF>. a* \<in> \<FF>) \<and> csubspace \<FF> \<and> (\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>) \<and> id_cblinfun \<in> \<FF> \<and>
      closedin cstrong_operator_topology \<FF>\<close>
proof (unfold von_neumann_algebra_def, intro iffI conjI; elim conjE; assumption?)
  assume comm: \<open>commutant (commutant \<FF>) = \<FF>\<close>
  from comm show \<open>closedin cstrong_operator_topology \<FF>\<close>
    by (metis commutant_sot_closed)
  from comm show \<open>csubspace \<FF>\<close>
    by (metis csubspace_commutant)
  from comm show \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
    using commutant_mult by blast
  from comm show \<open>id_cblinfun \<in> \<FF>\<close>
    by blast
next
  assume adj: \<open>\<forall>a\<in>\<FF>. a* \<in> \<FF>\<close>
  assume subspace: \<open>csubspace \<FF>\<close>
  assume closed: \<open>closedin cstrong_operator_topology \<FF>\<close>
  assume mult: \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
  assume id: \<open>id_cblinfun \<in> \<FF>\<close>
  have \<open>commutant (commutant \<FF>) = cstrong_operator_topology closure_of \<FF>\<close>
    apply (rule double_commutant_theorem)
    thm double_commutant_theorem[of \<FF>]
    using subspace subspace mult id adj 
    by simp_all
  also from closed have \<open>\<dots> = \<FF>\<close>
    by (simp add: closure_of_eq)
  finally show \<open>commutant (commutant \<FF>) = \<FF>\<close>
    by -
qed


lemma double_commutant_hull: \<open>commutant (commutant X) = (\<lambda>X. commutant (commutant X) = X) hull X\<close>
  by (smt (verit) commutant_antimono double_commutant_grows hull_unique triple_commutant)

lemma commutant_adj_closed: \<open>(\<And>x. x \<in> X \<Longrightarrow> x* \<in> X) \<Longrightarrow> x \<in> commutant X \<Longrightarrow> x* \<in> commutant X\<close>
  by (metis (no_types, opaque_lifting) commutant_adj commutant_antimono double_adj imageI subset_iff)

lemma double_commutant_hull':
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x* \<in> X\<close>
  shows \<open>commutant (commutant X) = von_neumann_algebra hull X\<close>
proof (rule antisym)
  show \<open>commutant (commutant X) \<subseteq> von_neumann_algebra hull X\<close>
    apply (subst double_commutant_hull)
    apply (rule hull_antimono)
    by (simp add: von_neumann_algebra_def)
  show \<open>von_neumann_algebra hull X \<subseteq> commutant (commutant X)\<close>
    apply (rule hull_minimal)
    by (simp_all add: von_neumann_algebra_def assms commutant_adj_closed)
qed

lemma double_commutant_Un_left: \<open>commutant (commutant (commutant (commutant X) \<union> Y)) = commutant (commutant (X \<union> Y))\<close>
  apply (simp add: double_commutant_hull cong: arg_cong[where f=\<open>Hull.hull _\<close>])
  using hull_Un_left by fastforce

lemma double_commutant_Un_right: \<open>commutant (commutant (X \<union> commutant (commutant Y))) = commutant (commutant (X \<union> Y))\<close>
  by (metis Un_ac(3) double_commutant_Un_left)

lemma tensor_ell2_right_butterfly: \<open>tensor_ell2_right \<psi> o\<^sub>C\<^sub>L tensor_ell2_right \<phi>* = id_cblinfun \<otimes>\<^sub>o butterfly \<psi> \<phi>\<close>
  by (auto intro!: equal_ket cinner_ket_eqI simp: tensor_op_ell2 simp flip: tensor_ell2_ket)
lemma tensor_ell2_left_butterfly: \<open>tensor_ell2_left \<psi> o\<^sub>C\<^sub>L tensor_ell2_left \<phi>* = butterfly \<psi> \<phi> \<otimes>\<^sub>o id_cblinfun\<close>
  by (auto intro!: equal_ket cinner_ket_eqI simp: tensor_op_ell2 simp flip: tensor_ell2_ket)

lemma amplification_double_commutant_commute:
  \<open>commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))
    = (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) `  commutant (commutant X)\<close>
\<comment> \<open>\<^cite>\<open>takesaki\<close>, Corollary IV.1.5\<close>
proof -
  define \<pi> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> (('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close> where 
    \<open>\<pi> a = a \<otimes>\<^sub>o id_cblinfun\<close> for a
  define U :: \<open>'b \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> where \<open>U i = tensor_ell2_right (ket i)\<close> for i :: 'b
  write commutant (\<open>_''\<close> [120] 120)
      \<comment> \<open>Notation \<^term>\<open>X '\<close> for \<^term>\<open>commutant X\<close>\<close>
  write id_cblinfun (\<open>\<one>\<close>)
  have *: \<open>(\<pi> ` X)'' \<subseteq> range \<pi>\<close> for X
  proof (rule subsetI)
    fix x assume asm: \<open>x \<in> (\<pi> ` X)''\<close>
    fix t
    define y where \<open>y = U t* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L U t\<close>
    have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close> for k l m n
    proof -
      have comm: \<open>x o\<^sub>C\<^sub>L (U i o\<^sub>C\<^sub>L U j*) = (U i o\<^sub>C\<^sub>L U j*) o\<^sub>C\<^sub>L x\<close> for i j
      proof -
        have \<open>U i o\<^sub>C\<^sub>L U j* = id_cblinfun \<otimes>\<^sub>o butterfly (ket i) (ket j)\<close>
          by (simp add: U_def tensor_ell2_right_butterfly)
        also have \<open>\<dots> \<in> (\<pi> ` X)'\<close>
          by (simp add: \<pi>_def commutant_def comp_tensor_op)
        finally show ?thesis
          using asm
          by (simp add: commutant_def)
      qed
      have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V ket m)\<close>
        by (simp add: cinner_adj_right U_def tensor_ell2_ket)
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V U t* *\<^sub>V U t *\<^sub>V ket m)\<close>
        using U_def by fastforce
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V U n *\<^sub>V U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m)\<close>
        using simp_a_oCL_b'[OF comm]
        by simp
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m))\<close>
        using U_def by fastforce
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (y *\<^sub>V ket m))\<close>
        using y_def by force
      also have \<open>\<dots> = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close>
        by (simp add: \<pi>_def tensor_op_ell2 flip: tensor_ell2_ket)
      finally show ?thesis
        by -
    qed
    then have \<open>x = \<pi> y\<close>
      by (metis cinner_ket_eqI equal_ket surj_pair)
    then show \<open>x \<in> range \<pi>\<close>
      by simp
  qed
  have **: \<open>\<pi> ` (Y ') = (\<pi> ` Y)' \<inter> range \<pi>\<close> for Y
    using inj_tensor_left[of id_cblinfun]
    apply (auto simp add: commutant_def \<pi>_def comp_tensor_op
        intro!: image_eqI)
    using injD by fastforce
  have 1: \<open>(\<pi> ` X)'' \<subseteq> \<pi> ` (X '')\<close> for X
  proof -
    have \<open>(\<pi> ` X)'' \<subseteq> (\<pi> ` X)'' \<inter> range \<pi>\<close>
      by (simp add: "*")
    also have \<open>\<dots> \<subseteq> ((\<pi> ` X)' \<inter> range \<pi>)' \<inter> range \<pi>\<close>
      by (simp add: commutant_antimono inf.coboundedI1)
    also have \<open>\<dots> = \<pi> ` (X '')\<close>
      by (simp add: ** )
    finally show ?thesis
      by -
  qed

  have \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close> if \<open>x \<in> \<pi> ` (X '')\<close> and \<open>y \<in> (\<pi> ` X)'\<close> for x y
  proof (intro equal_ket cinner_ket_eqI)
    fix i j :: \<open>'a \<times> 'b\<close>
    from that obtain w where \<open>w \<in> X ''\<close> and x_def: \<open>x = w \<otimes>\<^sub>o \<one>\<close>
      by (auto simp: \<pi>_def)
    obtain i1 i2 where i_def: \<open>i = (i1, i2)\<close> by force
    obtain j1 j2 where j_def: \<open>j = (j1, j2)\<close> by force
    define y\<^sub>0 where \<open>y\<^sub>0 = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>

    have \<open>y\<^sub>0 \<in> X '\<close>
    proof (rule commutant_memberI)
      fix z assume \<open>z \<in> X\<close>
      then have \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close>
        by (auto simp: \<pi>_def)
      have \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L U j2\<close>
        by (auto intro!: equal_ket simp add: y\<^sub>0_def U_def tensor_op_ell2)
      also have \<open>\<dots> = U i2* o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>
        using \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close> and \<open>y \<in> (\<pi> ` X)'\<close>
        apply (auto simp add: commutant_def)
        by (simp add: cblinfun_compose_assoc)
      also have \<open>\<dots> = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by (auto intro!: equal_ket cinner_ket_eqI
            simp add: y\<^sub>0_def U_def tensor_op_ell2 tensor_op_adjoint simp flip: cinner_adj_left)
      finally show \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by -
    qed
    have \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V (U i2 o\<^sub>C\<^sub>L U i2*) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (w *\<^sub>V y\<^sub>0 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (y\<^sub>0 *\<^sub>V w *\<^sub>V ket j1)\<close>
      using \<open>y\<^sub>0 \<in> X '\<close> \<open>w \<in> X ''\<close>
      apply (subst (asm) (2) commutant_def)
      using lift_cblinfun_comp(4) by force
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (U j2 o\<^sub>C\<^sub>L U j2*) *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    finally show \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by -
  qed
  then have 2: \<open>(\<pi> ` X)'' \<supseteq> \<pi> ` (X '')\<close>
    by (auto intro!: commutant_memberI)
  from 1 2 show ?thesis
    by (auto simp flip: \<pi>_def)
qed

lemma amplification_double_commutant_commute':
  \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
proof -
  have \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = commutant (commutant (sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: sandwich_unitary_commutant)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  finally show ?thesis
    by -
qed

lemma commutant_one_algebra: \<open>commutant one_algebra = UNIV\<close>
  by (metis commutant_UNIV commutant_empty triple_commutant)

definition tensor_vn (infixr "\<otimes>\<^sub>v\<^sub>N" 70) where
  \<open>tensor_vn X Y = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>

lemma von_neumann_algebra_adj_image: \<open>von_neumann_algebra X \<Longrightarrow> adj ` X = X\<close>
  by (auto simp: von_neumann_algebra_def intro!: image_eqI[where x=\<open>_*\<close>])

lemma von_neumann_algebra_tensor_vn:
  assumes \<open>von_neumann_algebra X\<close>
  assumes \<open>von_neumann_algebra Y\<close>
  shows \<open>von_neumann_algebra (X \<otimes>\<^sub>v\<^sub>N Y)\<close>
proof (rule von_neumann_algebraI)
  have \<open>adj ` (X \<otimes>\<^sub>v\<^sub>N Y) = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` adj ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` adj ` Y))\<close>
    by (simp add: tensor_vn_def commutant_adj image_image image_Un tensor_op_adjoint)
  also have \<open>\<dots> = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>
    using assms by (simp add: von_neumann_algebra_adj_image)
  also have \<open>\<dots> = X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
  finally show \<open>a* \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> if \<open>a \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> for a
    using that by blast
  show \<open>commutant (commutant (X \<otimes>\<^sub>v\<^sub>N Y)) \<subseteq> X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
qed

lemma tensor_vn_one_one[simp]: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N one_algebra = one_algebra\<close>
  apply (simp add: tensor_vn_def one_algebra_def image_image
      tensor_op_scaleC_left tensor_op_scaleC_right)
  by (simp add: commutant_one_algebra commutant_UNIV flip: one_algebra_def)

lemma sandwich_swap_tensor_vn: \<open>sandwich swap_ell2 ` (X \<otimes>\<^sub>v\<^sub>N Y) = Y \<otimes>\<^sub>v\<^sub>N X\<close>
  by (simp add: tensor_vn_def sandwich_unitary_commutant image_Un image_image Un_commute)

lemma tensor_vn_one_left: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = commutant
     (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))\<close>
    apply (simp add: tensor_vn_def one_algebra_def image_image)
    by (metis (no_types, lifting) Un_commute Un_empty_right commutant_UNIV commutant_empty double_commutant_Un_right image_cong one_algebra_def tensor_id tensor_op_scaleC_left)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute')
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X\<close>
    using that von_neumann_algebra_def by blast
  finally show ?thesis
    by -
qed
lemma tensor_vn_one_right: \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = sandwich swap_ell2 ` (one_algebra \<otimes>\<^sub>v\<^sub>N X)\<close>
    by (simp add: sandwich_swap_tensor_vn)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close>
    by (simp add: tensor_vn_one_left that)
  also have \<open>\<dots> = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close>
    by (simp add: image_image)
  finally show ?thesis
    by -
qed

lemma double_commutant_in_vn_algI: \<open>commutant (commutant X) \<subseteq> Y\<close>
  if \<open>von_neumann_algebra Y\<close> and \<open>X \<subseteq> Y\<close>
  by (metis commutant_antimono that(1) that(2) von_neumann_algebra_def)

lemma cblinfun_cinner_tensor_eqI:
  assumes \<open>\<And>\<psi> \<phi>. (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (A *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>)) = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (B *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>))\<close>
  shows \<open>A = B\<close>
proof -
  define C where \<open>C = A - B\<close>
  from assms have assmC: \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (C *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>)) = 0\<close> for \<psi> \<phi>
    by (simp add: C_def cblinfun.diff_left cinner_simps(3))

  have \<open>(x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V (z \<otimes>\<^sub>s w)) = 0\<close> for x y z w
  proof -
    define d e f g h j k l m n p q
      where defs: \<open>d = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>
        \<open>e = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>f = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>g = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>h = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>j = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>k = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>l = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>m = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>n = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>p = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>
        \<open>q = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>

    have constraint: \<open>cnj \<alpha> * e + cnj \<beta> * f + cnj \<beta> * cnj \<alpha> * g + \<alpha> * h + \<alpha> * cnj \<beta> * j +
          \<alpha> * cnj \<beta> * cnj \<alpha> * k + \<beta> * m + \<beta> * cnj \<alpha> * n + \<beta> * cnj \<beta> * cnj \<alpha> * l +
          \<beta> * \<alpha> * d + \<beta> * \<alpha> * cnj \<alpha> * p + \<beta> * \<alpha> * cnj \<beta> * q = 0\<close>
      (is \<open>?lhs = _\<close>) for \<alpha> \<beta>
    proof -
      from assms 
      have \<open>0 = ((x + \<alpha> *\<^sub>C z) \<otimes>\<^sub>s (y + \<beta> *\<^sub>C w)) \<bullet>\<^sub>C (C *\<^sub>V ((x + \<alpha> *\<^sub>C z) \<otimes>\<^sub>s (y + \<beta> *\<^sub>C w)))\<close>
        by (simp add: assmC)
      also have \<open>\<dots> = ?lhs\<close>
        apply (simp add: tensor_ell2_add1 tensor_ell2_add2 cinner_add_right cinner_add_left
            cblinfun.add_right tensor_ell2_scaleC1 tensor_ell2_scaleC2 semiring_class.distrib_left
            cblinfun.scaleC_right
            flip: add.assoc mult.assoc)
        apply (simp add: assmC)
        by (simp flip: defs)
      finally show ?thesis
        by simp
    qed

    have aux1: \<open>a = 0 \<Longrightarrow> b = 0 \<Longrightarrow> a + b = 0\<close> for a b :: complex
      by auto
    have aux2: \<open>a = 0 \<Longrightarrow> b = 0 \<Longrightarrow> a - b = 0\<close> for a b :: complex
      by auto
    have aux3: \<open>- (x * k) - x * j = x * (- k - j)\<close> for x k :: complex
      by (simp add: right_diff_distrib')
    have aux4: \<open>2 * a = 0 \<longleftrightarrow> a = 0\<close> for a :: complex
      by auto
    have aux5: \<open>8 = 2 * 2 * (2::complex)\<close>
      by simp

    from constraint[of 1 0]
    have 1: \<open>e + h = 0\<close>
      by simp
    from constraint[of \<i> 0]
    have 2: \<open>h = e\<close>
      by simp
    from 1 2
    have [simp]: \<open>e = 0\<close> \<open>h = 0\<close>
      by auto
    from constraint[of 0 1]
    have 3: \<open>f + m = 0\<close>
      by simp
    from constraint[of 0 \<i>]
    have 4: \<open>m = f\<close>
      by simp
    from 3 4
    have [simp]: \<open>m = 0\<close> \<open>f = 0\<close>
      by auto
    from constraint[of 1 1]
    have 5: \<open>g + j + k + n + l + d + p + q = 0\<close>
      by simp
    from constraint[of 1 \<open>-1\<close>]
    have 6: \<open>- g - j - k - n + l - d - p + q = 0\<close>
      by simp
    from aux1[OF 5 6]
    have 7: \<open>l + q = 0\<close>
      apply simp
      by (metis distrib_left_numeral mult_eq_0_iff zero_neq_numeral)
    from aux2[OF 5 7]
    have 8: \<open>g + j + k + n + d + p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of 1 \<i>]
    have 9: \<open>- (\<i> * g) - \<i> * j - \<i> * k + \<i> * n + l + \<i> * d + \<i> * p + q = 0\<close>
      by simp
    from constraint[of 1 \<open>-\<i>\<close>]
    have 10: \<open>\<i> * g + \<i> * j + \<i> * k - \<i> * n + l - \<i> * d - \<i> * p + q = 0\<close>
      by simp
    from aux2[OF 9 10]
    have 11: \<open>n + d + p - k - j - g = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from aux2[OF 8 11]
    have 12: \<open>g + j + k = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from aux1[OF 8 11]
    have 13: \<open>n + d + p = 0\<close>
      apply simp
      using 12 8 by fastforce
    from constraint[of \<i> 1]
    have 14: \<open>\<i> * j - \<i> * g + k - \<i> * n - \<i> * l + \<i> * d + p + \<i> * q = 0\<close>
      by simp
    from constraint[of \<i> \<open>-1\<close>]
    have 15: \<open>\<i> * g - \<i> * j - k + \<i> * n - \<i> * l - \<i> * d - p + \<i> * q = 0\<close>
      by simp
    from aux1[OF 14 15]
    have [simp]: \<open>q = l\<close>
      by simp
    from 7
    have [simp]: \<open>q = 0\<close> \<open>l = 0\<close>
      by auto
    from 14
    have 16: \<open>\<i> * j - \<i> * g + k - \<i> * n + \<i> * d + p = 0\<close>
      by simp
    from constraint[of \<open>-\<i>\<close> 1]
    have 17: \<open>\<i> * g - \<i> * j + k + \<i> * n - \<i> * d + p = 0\<close>
      by simp
    from aux1[OF 16 17]
    have [simp]: \<open>k = - p\<close>
      apply simp
      by (metis add_eq_0_iff2 add_scale_eq_noteq is_num_normalize(8) mult_2 zero_neq_numeral)
    from aux2[OF 16 17]
    have 18: \<open>j + d - n - g = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from constraint[of \<open>-\<i>\<close> 1]
    have 19: \<open>\<i> * g - \<i> * j + \<i> * n - \<i> * d = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<open>-\<i>\<close> \<open>-1\<close>]
    have 20: \<open>\<i> * j - \<i> * g - \<i> * n + \<i> * d = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<i> \<i>]
    have 21: \<open>j - g + n - d + 2 * \<i> * p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<i> \<open>-\<i>\<close>]
    have 22: \<open>g - j - n + d - 2 * \<i> * p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of 2 1]
    have 23: \<open>g + j + n + d = 0\<close>
      apply simp
      by (metis "12" "13" \<open>k = - p\<close> add_eq_0_iff2 is_num_normalize(1))
    from aux2[OF 23 18]
    have [simp]: \<open>g = - n\<close>
      apply simp
      by (simp only: aux4 add_eq_0_iff2 flip: distrib_left)
    from 23
    have [simp]: \<open>j = - d\<close>
      by (simp add: add_eq_0_iff2)
    from constraint[of 2 \<i>]
    have 24: \<open>2 * p + d + n = 0\<close>
      apply simp
      apply (simp only: aux5 aux4 add_eq_0_iff2 flip: distrib_left)
      by (smt (z3) "13" add.commute add_cancel_right_left add_eq_0_iff2 complex_i_not_zero eq_num_simps(6) more_arith_simps(8) mult_2 mult_right_cancel no_zero_divisors num.distinct(1) numeral_Bit0 numeral_eq_iff)
    from aux2[OF 24 13]
    have [simp]: \<open>p = 0\<close>
      by simp
    then have [simp]: \<open>k = 0\<close>
      by auto
    from 12
    have \<open>g = - j\<close>
      by simp
    from 21
    have \<open>d = - g\<close>
      by auto

    show \<open>d = 0\<close>
      using refl[of d]
      apply (subst (asm) \<open>d = - g\<close>)
      apply (subst (asm) \<open>g = - j\<close>)
      apply (subst (asm) \<open>j = - d\<close>)
      by simp
  qed
  then show ?thesis
    by (auto intro!: equal_ket cinner_ket_eqI
        simp: C_def cblinfun.diff_left cinner_diff_right
        simp flip: tensor_ell2_ket)
qed

lemma von_neumann_algebra_compose:
  assumes \<open>von_neumann_algebra M\<close>
  assumes \<open>x \<in> M\<close> and \<open>y \<in> M\<close>
  shows \<open>x o\<^sub>C\<^sub>L y \<in> M\<close>
  using assms apply (auto simp: von_neumann_algebra_def commutant_def)
  by (metis (no_types, lifting) assms(1) commutant_mult von_neumann_algebra_def)

lemma von_neumann_algebra_id:
  assumes \<open>von_neumann_algebra M\<close>
  shows \<open>id_cblinfun \<in> M\<close>
  using assms by (auto simp: von_neumann_algebra_def)

definition cstar_algebra where \<open>cstar_algebra A \<longleftrightarrow> csubspace A \<and> (\<forall>x\<in>A. \<forall>y\<in>A. x o\<^sub>C\<^sub>L y \<in> A) \<and> (\<forall>x\<in>A. x* \<in> A) \<and> closed A\<close>

lemma sqrt_op_in_cstar_algebra:
  assumes \<open>cstar_algebra A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>a \<in> A\<close>
  shows \<open>sqrt_op a \<in> A\<close>
proof -
  have *: \<open>cblinfun_power a n \<in> A\<close> for n
    apply (induction n)
    using assms by (auto simp: cblinfun_power_Suc cstar_algebra_def)
  have \<open>sqrt_op a \<in> closure (cspan (range (cblinfun_power a)))\<close>
    by (rule sqrt_op_in_closure)
  also have \<open>\<dots> \<subseteq> closure (cspan A)\<close>
    apply (intro closure_mono complex_vector.span_mono)
    by (auto intro!: * )
  also have \<open>\<dots> = closure A\<close>
    using \<open>cstar_algebra A\<close>
    apply (simp add: cstar_algebra_def)
    by (metis closure_closed complex_vector.span_eq_iff)
  also have \<open>\<dots> = A\<close>
    using \<open>cstar_algebra A\<close>
    by (simp add: cstar_algebra_def)
  finally show \<open>sqrt_op a \<in> A\<close>
    by -
qed

lemma cstar_decompose_four_unitaries:
  \<comment> \<open>\<^cite>\<open>takesaki\<close>, Proposition I.4.9\<close>
  fixes M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close>
  assumes \<open>cstar_algebra M\<close>
  assumes [simp]: \<open>id_cblinfun \<in> M\<close>
  assumes \<open>x \<in> M\<close>
  shows \<open>\<exists>a1 a2 a3 a4 u1 u2 u3 u4. u1 \<in> M \<and> u2 \<in> M \<and> u3 \<in> M \<and> u4 \<in> M
              \<and> unitary u1 \<and> unitary u2 \<and> unitary u3 \<and> unitary u4
              \<and> x = a1 *\<^sub>C u1 + a2 *\<^sub>C u2 + a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
proof -
  have herm: \<open>\<exists>u1 u2 a1 a2. u1 \<in> M \<and> u2 \<in> M \<and> unitary u1 \<and> unitary u2 \<and> h = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close> 
    if \<open>h \<in> M\<close> and \<open>h* = h\<close> for h
  proof (cases \<open>h = 0\<close>)
    case True
    show ?thesis 
      apply (rule exI[of _ id_cblinfun]; rule exI[of _  id_cblinfun])
      apply (rule exI[of _ 0]; rule exI[of _ 0])
      by (simp add: True)
  next
    case False
    define h' where \<open>h' = sgn h\<close>
    from False have [simp]: \<open>h' \<in> M\<close> and [simp]: \<open>h'* = h'\<close> and \<open>norm h' = 1\<close>
        using \<open>cstar_algebra M\<close>
        by (auto simp: h'_def sgn_cblinfun_def complex_vector.subspace_scale norm_inverse that
            cstar_algebra_def)
    define u where \<open>u = h' + imaginary_unit *\<^sub>C sqrt_op (id_cblinfun - (h' o\<^sub>C\<^sub>L h'))\<close>
    have [simp]: \<open>u \<in> M\<close>
    proof -
      have \<open>id_cblinfun - h' o\<^sub>C\<^sub>L h' \<in> M\<close>
        using \<open>cstar_algebra M\<close>
        by (simp add: complex_vector.subspace_diff cstar_algebra_def)
      then have \<open>sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') \<in> M\<close>
        apply (rule sqrt_op_in_cstar_algebra[rotated -1])
        using \<open>cstar_algebra M\<close> by auto
      then show ?thesis
        using \<open>cstar_algebra M\<close>
        by (auto simp: u_def cstar_algebra_def intro!: complex_vector.subspace_add complex_vector.subspace_scale)
    qed
    then have [simp]: \<open>u* \<in> M\<close>
      using \<open>cstar_algebra M\<close>
      by (simp add: cstar_algebra_def)
    have *: \<open>h' o\<^sub>C\<^sub>L h' \<le> id_cblinfun\<close>
    proof (rule cblinfun_leI)
      fix x :: 'a assume \<open>norm x = 1\<close>
      have \<open>x \<bullet>\<^sub>C ((h' o\<^sub>C\<^sub>L h') *\<^sub>V x) = (norm (h' *\<^sub>V x))\<^sup>2\<close>
        by (metis \<open>h'* = h'\<close> cblinfun_apply_cblinfun_compose cdot_square_norm cinner_adj_right)
      also have \<open>\<dots> \<le> (norm h')\<^sup>2\<close>
        by (metis \<open>norm h' = 1\<close> \<open>norm x = 1\<close> cnorm_eq_square cnorm_le_square norm_cblinfun one_power2 power2_eq_square)
      also have \<open>\<dots> \<le> 1\<close>
        by (simp add: \<open>norm h' = 1\<close>)
      also have \<open>\<dots> = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V x)\<close>
        using \<open>norm x = 1\<close> cnorm_eq_1 by auto
      finally show \<open>x \<bullet>\<^sub>C ((h' o\<^sub>C\<^sub>L h') *\<^sub>V x) \<le> x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V x)\<close>
        by -
    qed
    have **: \<open>h' o\<^sub>C\<^sub>L sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') = sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') o\<^sub>C\<^sub>L h'\<close>
      apply (rule sqrt_op_commute[symmetric])
      by (auto simp: * cblinfun_compose_minus_right cblinfun_compose_minus_left cblinfun_compose_assoc)
    have [simp]: \<open>unitary u\<close>
      by (auto intro!: unitary_def[THEN iffD2] simp: * ** u_def cblinfun_compose_add_right
          cblinfun_compose_add_left adj_plus cblinfun_compose_minus_left cblinfun_compose_minus_right
          positive_hermitianI sqrt_op_pos scaleC_diff_right scaleC_add_right)
    have [simp]: \<open>u + u* = h' + h'\<close>
      by (simp add: * u_def adj_plus positive_hermitianI[symmetric] sqrt_op_pos)
    show ?thesis
      apply (rule exI[of _ u]; rule exI[of _ \<open>u*\<close>])
      apply (rule exI[of _ \<open>of_real (norm h) / 2\<close>]; rule exI[of _ \<open>of_real (norm h) / 2\<close>])
      by (auto simp flip: scaleC_add_right scaleC_2 simp: h'_def)
  qed
  obtain a1 a2 u1 u2 where \<open>u1 \<in> M\<close> and \<open>u2 \<in> M\<close> and \<open>unitary u1\<close> and \<open>unitary u2\<close> and decomp1: \<open>x + x* = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> complex_vector.subspace_add adj_plus cstar_algebra_def)
  obtain a3 a4 u3 u4 where \<open>u3 \<in> M\<close> and \<open>u4 \<in> M\<close> and \<open>unitary u3\<close> and \<open>unitary u4\<close> 
    and decomp2: \<open>\<i> *\<^sub>C (x - x*) = a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> adj_minus complex_vector.subspace_diff complex_vector.subspace_scale cstar_algebra_def flip: scaleC_minus_right)
  have \<open>x = (1/2) *\<^sub>C (x + x*) + (-\<i>/2) *\<^sub>C (\<i> *\<^sub>C (x - x*))\<close>
    by (simp add: scaleC_add_right scaleC_diff_right flip: scaleC_add_left)
  also have \<open>\<dots> = (a1 / 2) *\<^sub>C u1 + (a2 / 2) *\<^sub>C u2 + (- \<i> * a3 / 2) *\<^sub>C u3 + (- \<i> * a4 / 2) *\<^sub>C u4\<close>
    apply (simp only: decomp1 decomp2)
    by (simp add: scaleC_add_right scaleC_diff_right)
  finally show ?thesis
    using \<open>u1 \<in> M\<close> \<open>u2 \<in> M\<close> \<open>u3 \<in> M\<close> \<open>u4 \<in> M\<close>
      \<open>unitary u1\<close> \<open>unitary u2\<close> \<open>unitary u3\<close> \<open>unitary u4\<close>
    by blast
qed

lemma commutant_cspan: \<open>commutant (cspan A) = commutant A\<close>
  by (meson basic_trans_rules(24) commutant_antimono complex_vector.span_superset cspan_in_double_commutant dual_order.trans)

lemma double_commutant_theorem_span:
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of (cspan A)\<close>
proof -
  have \<open>commutant (commutant A) = commutant (commutant (cspan A))\<close>
    by (simp add: commutant_cspan)
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan A)\<close>
    apply (rule double_commutant_theorem)
    using assms
    apply (auto simp: cspan_compose_closed cspan_adj_closed)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

lemma double_commutant_grows': \<open>x \<in> X \<Longrightarrow> x \<in> commutant (commutant X)\<close>
  using double_commutant_grows by blast

lemma tensor_vn_UNIV[simp]: \<open>UNIV \<otimes>\<^sub>v\<^sub>N UNIV = (UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set)\<close>
proof -
  have \<open>(UNIV \<otimes>\<^sub>v\<^sub>N UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set) = 
        commutant (commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<union> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)))\<close> (is \<open>_ = ?rhs\<close>)
    by (simp add: tensor_vn_def commutant_cspan)
  also have \<open>\<dots> \<supseteq> commutant (commutant {a \<otimes>\<^sub>o b |a b. True})\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
  proof (rule double_commutant_in_vn_algI)
    show vn: \<open>von_neumann_algebra ?rhs\<close>
      by (metis calculation von_neumann_algebra_UNIV von_neumann_algebra_tensor_vn)
    show \<open>{a \<otimes>\<^sub>o b |(a :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _) (b :: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _). True} \<subseteq> ?rhs\<close>
    proof (rule subsetI)
      fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
      assume \<open>x \<in> {a \<otimes>\<^sub>o b |a b. True}\<close>
      then obtain a b where \<open>x = a \<otimes>\<^sub>o b\<close>
        by auto
      then have \<open>x = (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o b)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> \<in> ?rhs\<close>
      proof -
        have \<open>a \<otimes>\<^sub>o id_cblinfun \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        moreover have \<open>id_cblinfun \<otimes>\<^sub>o b \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        ultimately show ?thesis
          using commutant_mult by blast
      qed
      finally show \<open>x \<in> ?rhs\<close>
        by -
    qed
  qed
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b |a b. True})\<close>
    apply (rule double_commutant_theorem_span)
      apply (auto simp: comp_tensor_op tensor_op_adjoint)
    using tensor_id[symmetric] by blast+
  also have \<open>\<dots> = UNIV\<close>
    using tensor_op_dense by blast
  finally show ?thesis
    by auto
qed

lemma norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
proof -
  have \<open>B \<ge> 0\<close>
    using assms by force
  have sqrtA: \<open>(sqrt_op A)* o\<^sub>C\<^sub>L sqrt_op A = A\<close>
    by (simp add: \<open>A \<ge> 0\<close> positive_hermitianI)
  have sqrtB: \<open>(sqrt_op B)* o\<^sub>C\<^sub>L sqrt_op B = B\<close>
    by (simp add: \<open>B \<ge> 0\<close> positive_hermitianI)
  have \<open>norm (sqrt_op A \<psi>) \<le> norm (sqrt_op B \<psi>)\<close> for \<psi>
    apply (auto intro!: cnorm_le[THEN iffD2]
        simp: sqrtA sqrtB
        simp flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    using assms less_eq_cblinfun_def by auto
  then have \<open>norm (sqrt_op A) \<le> norm (sqrt_op B)\<close>
    by (meson dual_order.trans norm_cblinfun norm_cblinfun_bound norm_ge_zero)
  moreover have \<open>norm A = (norm (sqrt_op A))\<^sup>2\<close>
    by (metis norm_AadjA sqrtA)
  moreover have \<open>norm B = (norm (sqrt_op B))\<^sup>2\<close>
    by (metis norm_AadjA sqrtB)
  ultimately show \<open>norm A \<le> norm B\<close>
    by force
qed

lemma sandwich_mono: \<open>sandwich A B \<le> sandwich A C\<close> if \<open>B \<le> C\<close>
  by (metis cblinfun.real.diff_right diff_ge_0_iff_ge sandwich_pos that)

lemma abs_op_id_on_pos: \<open>a \<ge> 0 \<Longrightarrow> abs_op a = a\<close>
  using abs_opI by force

lemma trace_norm_bounded:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_class A\<close>
proof -
  have \<open>(\<lambda>x. x \<bullet>\<^sub>C (B *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    by (metis assms(2) is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)
  then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_on_comparison_test)
    using \<open>A \<ge> 0\<close> \<open>A \<le> B\<close>
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos less_eq_cblinfun_def)
  then show ?thesis
    by (auto intro!: trace_classI[OF is_onb_some_chilbert_basis] simp: abs_op_id_on_pos \<open>A \<ge> 0\<close>)
qed

lemma trace_norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_norm A \<le> trace_norm B\<close>
proof -
  from assms have \<open>trace_class A\<close>
    by (rule trace_norm_bounded)
  from \<open>A \<le> B\<close> and \<open>A \<ge> 0\<close>
  have \<open>B \<ge> 0\<close>
    by simp
  have \<open>cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) \<le> cmod (x \<bullet>\<^sub>C (abs_op B *\<^sub>V x))\<close> for x
    using \<open>A \<le> B\<close>
    unfolding less_eq_cblinfun_def
    using \<open>A \<ge> 0\<close> \<open>B \<ge> 0\<close> 
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos)
  then show \<open>trace_norm A \<le> trace_norm B\<close>
    using \<open>trace_class A\<close> \<open>trace_class B\<close>
    by (auto intro!: infsum_mono 
        simp add: trace_norm_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
qed



lemma norm_cblinfun_mono_trace_class:
  fixes A B :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
  using assms
  apply transfer
  apply (rule trace_norm_cblinfun_mono)
  by auto

lemma trace_norm_butterfly: \<open>trace_norm (butterfly a b) = (norm a) * (norm b)\<close>
  for a b :: \<open>_ :: chilbert_space\<close>
proof -
  have \<open>trace_norm (butterfly a b) = trace (abs_op (butterfly a b))\<close>
    by (simp flip: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace (selfbutter b)\<close>
    by (simp add: abs_op_butterfly scaleR_scaleC trace_scaleC del: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace ((vector_to_cblinfun b :: complex \<Rightarrow>\<^sub>C\<^sub>L _)* o\<^sub>C\<^sub>L vector_to_cblinfun b)\<close>
    apply (subst butterfly_def)
    apply (subst circularity_of_trace)
    by simp_all
  also have \<open>\<dots> = (norm a / norm b) * (b \<bullet>\<^sub>C b)\<close>
    by simp
  also have \<open>\<dots> = (norm a) * (norm b)\<close>
    by (simp add: cdot_square_norm power2_eq_square)
  finally show ?thesis
    by (rule of_real_hom.injectivity)
qed

lemma from_trace_class_sum:
  shows \<open>from_trace_class (\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. from_trace_class (f x))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (simp_all add: plus_trace_class.rep_eq)

lemma cblinfun_norm_approx_witness_cinner:
  fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
proof (cases \<open>A = 0\<close>)
  case False
  define B where \<open>B = sqrt_op A\<close>
  define \<delta> where \<open>\<delta> = min (\<epsilon> / (2 * norm B)) (norm B)\<close>
  then have \<open>\<delta> > 0\<close>
    by (smt (verit, ccfv_threshold) B_def False Positive_Operators.sqrt_op_square assms(1) assms(2) linordered_field_class.divide_pos_pos norm_AAadj norm_eq_zero positive_hermitianI power_zero_numeral sqrt_op_pos zero_less_norm_iff)
  have \<delta>: \<open>2 * (\<delta> * norm B) - \<delta> * \<delta> \<le> \<epsilon>\<close>
  proof -
    have \<open>\<delta> \<le> \<epsilon> / (2 * norm B)\<close>
      by (simp add: \<delta>_def)
  then show ?thesis
    using assms(2) \<open>0 < \<delta>\<close>
    by (smt (verit, best) Extra_Ordered_Fields.sign_simps(19) add_diff_cancel_left' diff_diff_eq2 less_eq_real_def linorder_not_less mult_le_cancel_left_pos nice_ordered_field_class.pos_le_divide_eq)
  qed
  from cblinfun_norm_approx_witness[OF \<open>\<delta> > 0\<close>]
  obtain \<psi> where bound: \<open>norm B - \<delta> \<le> norm (B *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
    by auto
  have \<open>complex_of_real (norm A - \<epsilon>) = (norm B)\<^sup>2 - \<epsilon>\<close>
    by (metis B_def Positive_Operators.sqrt_op_square assms(1) norm_AAadj positive_hermitianI sqrt_op_pos)
  also have \<open>\<dots> \<le> (norm B - \<delta>)^2\<close>
    apply (rule complex_of_real_mono)
    using \<delta> by (simp add: power2_eq_square left_diff_distrib right_diff_distrib)
  also have \<open>\<dots> \<le> (norm (B *\<^sub>V \<psi>))^2\<close>
    apply (rule complex_of_real_mono)
    apply (rule power_mono)
    apply (rule bound)
    by (auto simp: \<delta>_def)
  also have \<open>\<dots> = B \<psi> \<bullet>\<^sub>C B \<psi>\<close>
    by (simp add: cdot_square_norm)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C A \<psi>\<close>
    by (metis B_def Positive_Operators.sqrt_op_square assms(1) cblinfun_apply_cblinfun_compose cinner_adj_right positive_hermitianI sqrt_op_pos)
  finally show ?thesis
    using \<open>norm \<psi> = 1\<close> by auto
next
  case True
  with \<open>\<epsilon> > 0\<close> show ?thesis
    by (auto intro!: any_norm_exists)
qed

lemma cblinfun_norm_approx_witness_cinner':
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using chilbert_space_axioms True assms
    by (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
  then have \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma clinear_from_trace_class[iff]: \<open>clinear from_trace_class\<close>
  apply (rule clinearI; transfer)
  by auto

lemma bounded_clinear_from_trace_class[bounded_clinear]:
  \<open>bounded_clinear (from_trace_class :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    apply (rule bounded_clinearI[where K=1]; transfer)
    by (auto intro!: norm_leq_trace_norm[internalize_sort' 'a] chilbert_space_axioms True)
next
  case False
  then have zero: \<open>A = 0\<close> for A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (rule not_not_singleton_cblinfun_zero)
  show ?thesis
    apply (rule bounded_clinearI[where K=1])
    by (subst zero, simp)+
qed

lemma has_sum_mono_neutral_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>has_sum_in cweak_operator_topology f A a\<close> and "has_sum_in cweak_operator_topology g B b"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  have \<psi>_eq: \<open>\<psi> \<bullet>\<^sub>C a \<psi> \<le> \<psi> \<bullet>\<^sub>C b \<psi>\<close> for \<psi>
  proof -
    from assms(1)
    have sumA: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<psi>) has_sum \<psi> \<bullet>\<^sub>C a \<psi>) A\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from assms(2)
    have sumB: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C g x \<psi>) has_sum \<psi> \<bullet>\<^sub>C b \<psi>) B\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from sumA sumB
    show ?thesis
      apply (rule has_sum_mono_neutral_complex)
      using assms(3-5)
      by (auto simp: less_eq_cblinfun_def)
  qed
  then show \<open>a \<le> b\<close>
    by (simp add: less_eq_cblinfun_def)
qed

lemma has_sum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>has_sum_in cweak_operator_topology f A a\<close> 
    by (auto intro!: wot_weaker_than_sot_limitin sot_weaker_than_norm_limitin 
        simp: has_sum_def has_sum_in_def)
  moreover
  from assms(2) have "has_sum_in cweak_operator_topology g B b"
    by (auto intro!: wot_weaker_than_sot_limitin sot_weaker_than_norm_limitin 
        simp: has_sum_def has_sum_in_def)
  ultimately show ?thesis
    apply (rule has_sum_mono_neutral_wot)
    using assms by auto
qed

lemma has_sum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>((\<lambda>x. from_trace_class (f x)) has_sum from_trace_class a) A\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  moreover
  from assms(2)
  have \<open>((\<lambda>x. from_trace_class (g x)) has_sum from_trace_class b) B\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  ultimately have \<open>from_trace_class a \<le> from_trace_class b\<close>
    apply (rule has_sum_mono_neutral_cblinfun)
    using assms by (auto simp: less_eq_trace_class.rep_eq)
  then show ?thesis
    by (auto simp: less_eq_trace_class.rep_eq)
qed



lemma has_sum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_cblinfun by force

lemma has_sum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_traceclass by force

lemma infsum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_cblinfun)

lemma infsum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_traceclass)

lemma infsum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_infsum has_sum_mono_neutral_cblinfun)

lemma infsum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_mono_neutral_traceclass summable_iff_has_sum_infsum by blast

instance trace_class :: (chilbert_space, chilbert_space) ordered_complex_vector
  apply (intro_classes; transfer)
  by (auto intro!: scaleC_left_mono scaleC_right_mono)

lemma Abs_trace_class_geq0I: \<open>0 \<le> Abs_trace_class t\<close> if \<open>trace_class t\<close> and \<open>t \<ge> 0\<close>
  using that by (simp add: zero_trace_class.abs_eq less_eq_trace_class.abs_eq eq_onp_def)

(* TODO replace original *) thm norm_leq_trace_norm
lemma norm_leq_trace_norm: \<open>norm t \<le> trace_norm t\<close> if \<open>trace_class t\<close> 
  for t :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    apply (rule norm_leq_trace_norm[internalize_sort' 'a, where t=t])
    using that chilbert_space_axioms True by auto
next
  case False
  then have x0: \<open>x = 0\<close> for x :: 'a
    by (simp add: class.not_singleton_def)
  have \<open>t = 0\<close>
    apply (rule cblinfun_eqI)
    apply (subst x0)
    by simp
  then show ?thesis 
    by simp
qed

(* TODO move to Trace_Class *)
lift_definition tc_compose :: \<open>('b::chilbert_space, 'c::chilbert_space) trace_class 
                               \<Rightarrow> ('a::chilbert_space, 'b) trace_class \<Rightarrow> ('a,'c) trace_class\<close> is
    cblinfun_compose
  by (simp add: trace_class_comp_left)

lemma norm_tc_compose:
  \<open>norm (tc_compose a b) \<le> norm a * norm b\<close>
proof transfer
  fix a :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'c\<close>
  assume \<open>a \<in> Collect trace_class\<close> and tc_b: \<open>b \<in> Collect trace_class\<close>
  then have \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
    by (simp add: trace_norm_comp_left)
  also have \<open>\<dots> \<le> trace_norm a * trace_norm b\<close>
    using tc_b by (auto intro!: mult_left_mono norm_leq_trace_norm)
  finally show \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * trace_norm b\<close>
    by -
qed


lift_definition trace_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> complex\<close> is trace.

lemma trace_tc_plus: \<open>trace_tc (a + b) = trace_tc a + trace_tc b\<close>
  apply transfer by (simp add: trace_plus)

lemma trace_tc_scaleC: \<open>trace_tc (c *\<^sub>C a) = c *\<^sub>C trace_tc a\<close>
  apply transfer by (simp add: trace_scaleC)

lemma trace_tc_norm: \<open>norm (trace_tc a) \<le> norm a\<close>
  apply transfer by auto

lemma bounded_clinear_trace_tc[bounded_clinear, simp]: \<open>bounded_clinear trace_tc\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp: trace_tc_scaleC trace_tc_plus intro!: trace_tc_norm)


lemma trace_norm_pos: \<open>trace_norm A = trace A\<close> if \<open>A \<ge> 0\<close>
  by (metis abs_op_id_on_pos that trace_abs_op)

lemma norm_tc_pos: \<open>norm A = trace_tc A\<close> if \<open>A \<ge> 0\<close>
   using that apply transfer by (simp add: trace_norm_pos)

lemma from_trace_class_pos: \<open>from_trace_class A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close>
  by (simp add: less_eq_trace_class.rep_eq)

lemma infsum_tc_norm_bounded_abs_summable:
  fixes A :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'b::chilbert_space) trace_class\<close>
  assumes pos: \<open>\<And>x. x \<in> M \<Longrightarrow> A x \<ge> 0\<close>
  assumes bound_B: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> M \<Longrightarrow> norm (\<Sum>x\<in>F. A x) \<le> B\<close>
  shows \<open>A abs_summable_on M\<close>
proof -
  have \<open>(\<Sum>x\<in>F. norm (A x)) = norm (\<Sum>x\<in>F. A x)\<close> if \<open>F \<subseteq> M\<close> for F
  proof -
    have \<open>complex_of_real (\<Sum>x\<in>F. norm (A x)) = (\<Sum>x\<in>F. complex_of_real (trace_norm (from_trace_class (A x))))\<close>
      by (simp add: norm_trace_class.rep_eq trace_norm_pos)
    also have \<open>\<dots> = (\<Sum>x\<in>F. trace (from_trace_class (A x)))\<close>
      using that pos by (auto intro!: sum.cong simp add: trace_norm_pos less_eq_trace_class.rep_eq)
    also have \<open>\<dots> = trace (from_trace_class (\<Sum>x\<in>F. A x))\<close>
      by (simp add: from_trace_class_sum trace_sum)
    also have \<open>\<dots> = norm (\<Sum>x\<in>F. A x)\<close>
      by (smt (verit, ccfv_threshold) calculation norm_of_real norm_trace_class.rep_eq sum_norm_le trace_leq_trace_norm)
    finally show ?thesis
      using of_real_hom.injectivity by blast
  qed
  with bound_B have bound_B': \<open>(\<Sum>x\<in>F. norm (A x)) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> M\<close> for F
    by (metis that(1) that(2))
  then show \<open>A abs_summable_on M\<close>
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: bdd_aboveI)
qed

lemma abs_op_geq: \<open>abs_op a \<ge> a\<close> if [simp]: \<open>a* = a\<close>
proof -
  define A P where \<open>A = abs_op a\<close> and \<open>P = Proj (kernel (A + a))\<close>
  have [simp]: \<open>A \<ge> 0\<close>
    by (simp add: A_def)
  then have [simp]: \<open>A* = A\<close>
    using positive_hermitianI by fastforce
  have aa_AA: \<open>a o\<^sub>C\<^sub>L a = A o\<^sub>C\<^sub>L A\<close>
    by (metis A_def \<open>A* = A\<close> abs_op_square that)
  have [simp]: \<open>P* = P\<close>
    by (simp add: P_def adj_Proj)
  have Aa_aA: \<open>A o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L A\<close>
    by (metis (full_types) A_def lift_cblinfun_comp(2) abs_op_def positive_cblinfun_squareI sqrt_op_commute that)

  have \<open>(A-a) \<psi> \<bullet>\<^sub>C (A+a) \<phi> = 0\<close> for \<phi> \<psi>
    by (simp add: adj_minus that \<open>A* = A\<close> aa_AA Aa_aA cblinfun_compose_add_right cblinfun_compose_minus_left
        flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
  then have \<open>(A-a) \<psi> \<in> space_as_set (kernel (A+a))\<close> for \<psi>
    by (metis \<open>A* = A\<close> adj_plus call_zero_iff cinner_adj_left kernel_memberI that)
  then have P_fix: \<open>P o\<^sub>C\<^sub>L (A-a) = (A-a)\<close>
    by (simp add: P_def Proj_fixes_image cblinfun_eqI)
  then have \<open>P o\<^sub>C\<^sub>L (A-a) o\<^sub>C\<^sub>L P = (A-a) o\<^sub>C\<^sub>L P\<close>
    by simp
  also have \<open>\<dots> = (P o\<^sub>C\<^sub>L (A-a))*\<close>
    by (simp add: adj_minus \<open>A* = A\<close> that \<open>P* = P\<close>)
  also have \<open>\<dots> = (A-a)*\<close>
    by (simp add: P_fix)
  also have \<open>\<dots> = A-a\<close>
    by (simp add: \<open>A* = A\<close> that adj_minus)
  finally have 1: \<open>P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P = A - a\<close>
    by -
  have 2: \<open>P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P = 0\<close>
    by (simp add: P_def cblinfun_compose_assoc)
  have \<open>A - a = P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P + P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P\<close>
    by (simp add: 1 2)
  also have \<open>\<dots> = sandwich P (2 *\<^sub>C A)\<close>
    by (simp add: sandwich_apply cblinfun_compose_minus_left cblinfun_compose_minus_right
        cblinfun_compose_add_left cblinfun_compose_add_right scaleC_2 \<open>P* = P\<close>) 
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: sandwich_pos scaleC_nonneg_nonneg simp: less_eq_complex_def)
  finally show \<open>A \<ge> a\<close>
    by auto
qed

lemma abs_op_geq_neq: \<open>abs_op a \<ge> - a\<close> if \<open>a* = a\<close>
  by (metis abs_op_geq abs_op_uminus adj_uminus that)

lemma trace_norm_uminus[simp]: \<open>trace_norm (-a) = trace_norm a\<close>
  by (metis abs_op_uminus of_real_eq_iff trace_abs_op)

(* TODO: remove [simp] from trace_class_uminus *)
lemma trace_class_uminus_iff[simp]: \<open>trace_class (-a) =  trace_class a\<close>
  by (auto simp add: trace_class_def)
lemma trace_norm_triangle_minus: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a - b) \<le> trace_norm a + trace_norm b\<close>
  using trace_norm_triangle[of a \<open>-b\<close>]
  by auto

lemma trace_norm_abs_op[simp]: \<open>trace_norm (abs_op t) = trace_norm t\<close>
  by (simp add: trace_norm_def)

lemma
  fixes t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  shows cblinfun_decomp_4pos: \<open>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>  (is ?thesis1)
  and trace_class_decomp_4pos: \<open>trace_class t \<Longrightarrow>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> trace_class t1 \<and> trace_class t2 \<and> trace_class t3 \<and> trace_class t4
               \<and> trace_norm t1 \<le> trace_norm t \<and> trace_norm t2 \<le> trace_norm t \<and> trace_norm t3 \<le> trace_norm t \<and> trace_norm t4 \<le> trace_norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close> (is \<open>_ \<Longrightarrow> ?thesis2\<close>)
proof -
  define th ta where \<open>th = (1/2) *\<^sub>C (t + t*)\<close> and \<open>ta = (-\<i>/2) *\<^sub>C (t - t*)\<close>
  have th_herm: \<open>th* = th\<close>
    by (simp add: adj_plus th_def)
  have \<open>ta* = ta\<close>
    by (simp add: adj_minus ta_def scaleC_diff_right adj_uminus)
  have \<open>t = th + \<i> *\<^sub>C ta\<close>
    by (smt (verit, ccfv_SIG) add.commute add.inverse_inverse complex_i_mult_minus complex_vector.vector_space_assms(1) complex_vector.vector_space_assms(3) diff_add_cancel group_cancel.add2 i_squared scaleC_half_double ta_def th_def times_divide_eq_right)
  define t1 t2 where \<open>t1 = (abs_op th + th) /\<^sub>R 2\<close> and \<open>t2 = (abs_op th - th) /\<^sub>R 2\<close>
  have \<open>t1 \<ge> 0\<close>
    using abs_op_geq_neq[OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t1_def intro!: scaleR_nonneg_nonneg)
  have \<open>t2 \<ge> 0\<close>
    using abs_op_geq[OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t2_def intro!: scaleR_nonneg_nonneg)
  have \<open>th = t1 - t2\<close>
    apply (simp add: t1_def t2_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  define t3 t4 where \<open>t3 = (abs_op ta + ta) /\<^sub>R 2\<close> and \<open>t4 = (abs_op ta - ta) /\<^sub>R 2\<close>
  have \<open>t3 \<ge> 0\<close>
    using abs_op_geq_neq[OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t3_def intro!: scaleR_nonneg_nonneg)
  have \<open>t4 \<ge> 0\<close>
    using abs_op_geq[OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t4_def intro!: scaleR_nonneg_nonneg)
  have \<open>ta = t3 - t4\<close>
    apply (simp add: t3_def t4_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  have decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    by (simp add: \<open>t = th + \<i> *\<^sub>C ta\<close> \<open>th = t1 - t2\<close> \<open>ta = t3 - t4\<close> scaleC_diff_right)
  from decomp \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
  show ?thesis1
    by auto
  show ?thesis2 if \<open>trace_class t\<close>
  proof -
    have \<open>trace_class th\<close> \<open>trace_class ta\<close>
      by (auto simp add: th_def ta_def
          intro!: \<open>trace_class t\<close> trace_class_scaleC trace_class_plus trace_class_minus trace_class_uminus trace_class_adj)
    then have tc: \<open>trace_class t1\<close> \<open>trace_class t2\<close> \<open>trace_class t3\<close> \<open>trace_class t4\<close>
      by (auto simp add: t1_def t2_def t3_def t4_def scaleR_scaleC intro!: trace_class_scaleC)
    have tn_th: \<open>trace_norm th \<le> trace_norm t\<close>
      using trace_norm_triangle[of t \<open>t*\<close>] 
      by (auto simp add: that th_def trace_norm_scaleC)
    have tn_ta: \<open>trace_norm ta \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of t \<open>t*\<close>] 
      by (auto simp add: that ta_def trace_norm_scaleC)
    have tn1: \<open>trace_norm t1 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t1_def trace_norm_scaleC scaleR_scaleC)
    have tn2: \<open>trace_norm t2 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t2_def trace_norm_scaleC scaleR_scaleC)
    have tn3: \<open>trace_norm t3 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t3_def trace_norm_scaleC scaleR_scaleC)
    have tn4: \<open>trace_norm t4 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t4_def trace_norm_scaleC scaleR_scaleC)
    from decomp tc \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close> tn1 tn2 tn3 tn4
    show ?thesis2
      by auto
  qed
qed

lemma trace_class_decomp_4pos':
  fixes t :: \<open>('a::chilbert_space,'a) trace_class\<close>
  shows \<open>\<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> norm t1 \<le> norm t \<and> norm t2 \<le> norm t \<and> norm t3 \<le> norm t \<and> norm t4 \<le> norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>
proof -
  from trace_class_decomp_4pos[of \<open>from_trace_class t\<close>, OF trace_class_from_trace_class]
  obtain t1' t2' t3' t4'
    where *: \<open>from_trace_class t = t1' - t2' + \<i> *\<^sub>C t3' - \<i> *\<^sub>C t4'
               \<and> trace_class t1' \<and> trace_class t2' \<and> trace_class t3' \<and> trace_class t4'
               \<and> trace_norm t1' \<le> trace_norm (from_trace_class t) \<and> trace_norm t2' \<le> trace_norm (from_trace_class t) \<and> trace_norm t3' \<le> trace_norm (from_trace_class t) \<and> trace_norm t4' \<le> trace_norm (from_trace_class t) 
               \<and> t1' \<ge> 0 \<and> t2' \<ge> 0 \<and> t3' \<ge> 0 \<and> t4' \<ge> 0\<close>
    by auto
  then obtain t1 t2 t3 t4 where
    t1234: \<open>t1' = from_trace_class t1\<close> \<open>t2' = from_trace_class t2\<close> \<open>t3' = from_trace_class t3\<close> \<open>t4' = from_trace_class t4\<close>
    by (metis from_trace_class_cases mem_Collect_eq)
  with * have n1234: \<open>norm t1 \<le> norm t\<close> \<open>norm t2 \<le> norm t\<close> \<open>norm t3 \<le> norm t\<close> \<open>norm t4 \<le> norm t\<close>
    by (metis norm_trace_class.rep_eq)+
  have t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    using * unfolding t1234 
    by (auto simp: from_trace_class_inject
        simp flip: scaleC_trace_class.rep_eq plus_trace_class.rep_eq minus_trace_class.rep_eq)
  have pos1234: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
    using * unfolding t1234 
    by (auto simp: less_eq_trace_class_def)
  from t_decomp pos1234 n1234
  show ?thesis
    by blast
qed

thm bounded_clinear_trace_duality
lemma bounded_clinear_trace_duality': \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (a o\<^sub>C\<^sub>L t))\<close> for t :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
    apply (auto simp add: cblinfun_compose_add_left trace_class_comp_right trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

lemma infsum_nonneg_cblinfun:
  fixes f :: "'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_cblinfun)
  using assms by (auto simp: infsum_not_exists)

lemma infsum_nonneg_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_neutral_traceclass)
  using assms by (auto simp: infsum_not_exists)

lemma sandwich_tc_compose: \<open>sandwich_tc (A o\<^sub>C\<^sub>L B) = sandwich_tc A o\<^sub>C\<^sub>L sandwich_tc B\<close>
  apply (rule cblinfun_eqI)
  apply (rule from_trace_class_inject[THEN iffD1])
  apply (transfer fixing: A B)
  by (simp add: sandwich_compose)

lemma sandwich_tc_0_left[simp]: \<open>sandwich_tc 0 = 0\<close>
  by (metis (no_types, opaque_lifting) cblinfun.zero_left cblinfun_eqI linorder_not_le norm_sandwich_tc norm_scaleC norm_zero power2_eq_square scaleC_left.zero zero_less_norm_iff)


lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)


lemma sandwich_scaleC_left: \<open>sandwich (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich e\<close>
  by (auto intro!: cblinfun_eqI simp: sandwich_apply cnj_x_x abs_complex_def)

lemma sandwich_scaleR_left: \<open>sandwich (r *\<^sub>R e) = r^2 *\<^sub>R sandwich e\<close>
  by (simp add: scaleR_scaleC sandwich_scaleC_left flip: of_real_power)

lemma sandwich_tc_scaleC_left: \<open>sandwich_tc (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich_tc e\<close>
  apply (rule cblinfun_eqI)
  apply (rule from_trace_class_inject[THEN iffD1])
  by (simp add: from_trace_class_sandwich_tc scaleC_trace_class.rep_eq
      sandwich_scaleC_left)

lemma sandwich_tc_scaleR_left: \<open>sandwich_tc (r *\<^sub>R e) = r^2 *\<^sub>R sandwich_tc e\<close>
  by (simp add: scaleR_scaleC sandwich_tc_scaleC_left flip: of_real_power)

(* TODO move *)
lift_definition tc_tensor :: \<open>('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class \<Rightarrow> 
      (('a \<times> 'c) ell2, ('b \<times> 'd) ell2) trace_class\<close> is
  tensor_op
  by (auto intro!: trace_class_tensor)


lemma infsum_product:
  fixes f :: \<open>'a \<Rightarrow> 'c :: {topological_semigroup_mult,division_ring,banach}\<close>
  assumes \<open>(\<lambda>(x, y). f x * g y) summable_on X \<times> Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: infsum_cmult_right' infsum_cmult_left' flip: infsum_Sigma'_banach)

lemma infsum_product':
  fixes f :: \<open>'a \<Rightarrow> 'c :: {banach,times,real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>f abs_summable_on X\<close>
  assumes \<open>g abs_summable_on Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: abs_summable_times infsum_cmult_right infsum_cmult_left abs_summable_summable flip: infsum_Sigma'_banach)

(* TODO move *)
lemma trace_norm_tensor: \<open>trace_norm (a \<otimes>\<^sub>o b) = trace_norm a * trace_norm b\<close>
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)


(* TODO move *)
lemma bounded_cbilinear_tc_tensor: \<open>bounded_cbilinear tc_tensor\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  by (auto intro!: exI[of _ 1]
      simp: trace_norm_tensor tensor_op_left_add tensor_op_right_add tensor_op_scaleC_left tensor_op_scaleC_right)
lemmas bounded_clinear_tc_tensor_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_tensor]
lemmas bounded_clinear_tc_tensor_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_tensor]


(* TODO move *)
lemma bounded_cbilinear_tc_compose: \<open>bounded_cbilinear tc_compose\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  apply (auto intro!: exI[of _ 1] simp: cblinfun_compose_add_left cblinfun_compose_add_right)
  by (meson Unsorted_HSTP.norm_leq_trace_norm dual_order.trans mult_right_mono trace_norm_comp_right trace_norm_nneg)
lemmas bounded_clinear_tc_compose_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_compose]
lemmas bounded_clinear_tc_compose_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_compose]

(* TODO move *)
lemma tc_tensor_scaleC_left: \<open>tc_tensor (c *\<^sub>C a) b = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_left)
lemma tc_tensor_scaleC_right: \<open>tc_tensor a (c *\<^sub>C b) = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_right)
  
(* TODO move *)
lemma comp_tc_tensor: \<open>tc_compose (tc_tensor a b) (tc_tensor c d) = tc_tensor (tc_compose a c) (tc_compose b d)\<close>
  apply transfer'
  by (rule comp_tensor_op)

(* TODO move *)
lift_definition tc_butterfly :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) trace_class\<close>
  is butterfly
  by simp

(* TODO move *)
lemma norm_tc_butterfly: \<open>norm (tc_butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>)
  by (simp add: trace_norm_butterfly)

(* TODO move *)
lemma norm_tc_tensor: \<open>norm (tc_tensor a b) = norm a * norm b\<close>
  apply transfer'
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)


lemma comp_tc_butterfly[simp]: \<open>tc_compose (tc_butterfly a b) (tc_butterfly c d) = (b \<bullet>\<^sub>C c) *\<^sub>C tc_butterfly a d\<close>
  apply transfer'
  by simp


lemma infsum_single: 
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "infsum f A = (if i\<in>A then f i else 0)"
  apply (subst infsum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto



(* TODO move *)
lemma summable_on_diff:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector"  (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) summable_on A\<close>
  using summable_on_add[where f=f and g=\<open>\<lambda>x. - g x\<close>] summable_on_uminus[where f=g]
  using assms by auto

lemma tc_tensor_pos: \<open>tc_tensor a b \<ge> 0\<close> if \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close>
  for a :: \<open>('a ell2,'a ell2) trace_class\<close> and b :: \<open>('b ell2,'b ell2) trace_class\<close>
  using that apply transfer'
  by (rule tensor_op_pos)

(* TODO move *)
lemma tc_butterfly_pos[simp]: \<open>0 \<le> tc_butterfly \<psi> \<psi>\<close>
  apply transfer
  by simp




end
