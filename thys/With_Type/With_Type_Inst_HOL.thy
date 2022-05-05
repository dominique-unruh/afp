theory With_Type_Inst_HOL
  imports With_Type HOL.Real_Vector_Spaces
begin

setup \<open>With_Type.add_relator_global \<^type_name>\<open>list\<close>
  (fn ctxt => fn mk => fn \<^Type>\<open>filter T\<close> => \<^Term>\<open>list_all2 \<open>mk T\<close>\<close> ctxt)\<close>

lemma itself_transfer[with_type_transfer_rules]:
  \<open>Transfer.Rel rel_itself TYPE('a) TYPE('b)\<close>
  by (simp add: RelI rel_itself.simps)


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.finite\<close>\<close>
thm with_type_transfer_Finite_Set_class_finite
(* TODO: should not be for an applied class.finite *)

lemma aux3:
  includes lifting_syntax
  assumes \<open>Transfer.Rel R A (B TYPE('a))\<close>
  shows \<open>Transfer.Rel (rel_itself ===> R) (\<lambda>_. A) B\<close>
  by (metis Rel_def assms rel_funI rel_itself.cases)

declare with_type_transfer_Finite_Set_class_finite[THEN aux3[where B=\<open>class.finite\<close>], with_type_transfer_rules]
thm with_type_transfer_Finite_Set_class_finite[THEN aux3[where B=\<open>class.finite\<close>], with_type_transfer_rules]

local_setup \<open>define_stuff \<^here> \<^class>\<open>finite\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semigroup_add\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>semigroup_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_semigroup_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_semigroup_add\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>ab_semigroup_add\<close>\<close>

declare with_type_ab_semigroup_add_class_transfer[
    unfolded with_type_ab_semigroup_add_class_def fst_conv snd_conv with_type_ab_semigroup_add_class_rel_def,
    transfer_rule]
declare class.comm_monoid_add_axioms_def[with_type_simps]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_add\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_monoid_add\<close>\<close>


lemma tmp:
  includes lifting_syntax
  assumes \<open>(rel_prod R S ===> T) g (case_prod f)\<close>
  shows \<open>(R ===> S ===> T) (curry g) f\<close>
  using assms rel_funD by fastforce

lemma tmp3:
  includes lifting_syntax
  assumes \<open>(rel_prod R1 (rel_prod R2 R3)  ===> T) g (\<lambda>(x,y,z). f x y z)\<close>
  shows \<open>(R1 ===> R2 ===> R3 ===> T) (\<lambda>x y z. g (x,y,z)) f\<close>
  using assms rel_funD by fastforce

lemma tmp4:
  includes lifting_syntax
  assumes \<open>(rel_prod R1 (rel_prod R2 (rel_prod R3 R4))  ===> T) g (\<lambda>(x,y,z,w). f x y z w)\<close>
  shows \<open>(R1 ===> R2 ===> R3 ===> R4 ===> T) (\<lambda>x y z w. g (x,y,z,w)) f\<close>
  using assms rel_funD by fastforce

lemmas with_type_comm_monoid_add_class_transfer'[transfer_rule] = with_type_comm_monoid_add_class_transfer[
    unfolded with_type_comm_monoid_add_class_def fst_conv snd_conv with_type_comm_monoid_add_class_rel_def,
    THEN tmp]
declare class.ab_group_add_axioms_def[with_type_simps]

(* declare[[show_types]] *)
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_group_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_group_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ab_group_add\<close>\<close>

(* ML \<open>
Thm.all_axioms_of \<^theory> |> filter (fn (name,thm) => 
    case Thm.prop_of thm of
      Const(\<^const_name>\<open>Pure.eq\<close>,_) $ lhs $ _ => 
         (case head_of lhs of Const(n,_) => n=\<^const_name>\<open>inverse\<close>
                               | _ => false)
     | _ => false)
\<close> *)

(* ML \<open>
get_raw_definitions \<^context> \<^const_name>\<open>inverse_rat_inst.inverse_rat\<close>\<close> *)


lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun (=) (rel_fun r (rel_fun r r))) If If\<close>
  using If_transfer RelI' by blast

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun (rel_fun A B) (rel_fun (rel_fun C D) (rel_fun (rel_fun B C) (rel_fun A D)))) map_fun map_fun\<close>
  by (rule Transfer.transfer_raw)

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>inverse_rat_inst.inverse_rat\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>inverse\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.sgn_div_norm\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>sgn_div_norm\<close>\<close>



local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.dist_norm\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>dist_norm\<close>\<close>

declare fun_eq_iff[with_type_simps]

lemma Domainp_rel_filter:
  assumes \<open>Domainp r = S\<close>
  shows \<open>Domainp (rel_filter r) F \<longleftrightarrow> (F \<le> principal (Collect S))\<close>
proof (intro iffI, elim Domainp.cases, hypsubst)
  fix G 
  assume \<open>rel_filter r F G\<close>
  then obtain Z where rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    and ZF: "map_filter_on {(x, y). r x y} fst Z = F" 
    and "map_filter_on {(x, y). r x y} snd Z = G"
    using rel_filter.simps by blast
  show \<open>F \<le> principal (Collect S)\<close>
    using rZ apply (auto simp flip: ZF assms intro!: filter_leI 
        simp: eventually_principal eventually_map_filter_on)
    by (smt (verit, best) DomainPI case_prod_beta eventually_elim2)
next
  assume asm: \<open>F \<le> principal (Collect S)\<close>
  define Z where \<open>Z = inf (filtercomap fst F) (principal {(x, y). r x y})\<close>
  have rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: Z_def eventually_inf_principal)
  moreover 
  have \<open>(\<forall>\<^sub>F x in Z. P (fst x) \<and> (case x of (x, xa) \<Rightarrow> r x xa)) = eventually P F\<close> for P
    using asm apply (auto simp add: le_principal Z_def eventually_inf_principal eventually_filtercomap)
    by (smt (verit, del_insts) DomainpE assms eventually_elim2)
  then have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    by (simp add: filter_eq_iff eventually_map_filter_on rZ)
  ultimately show \<open>Domainp (rel_filter r) F\<close>
    by (auto simp: Domainp_iff intro!: exI rel_filter.intros)
qed

lemma top_filter_parametric':
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  shows \<open>rel_filter r (principal (Collect S)) top\<close>
proof (rule rel_filter.intros)
  define Z where \<open>Z = principal {(x,y). r x y}\<close>
  show \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: eventually_principal Z_def)
  show \<open>map_filter_on {(x, y). r x y} fst Z = principal (Collect S)\<close>
    using \<open>Domainp r = S\<close> by (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
  show \<open>map_filter_on {(x, y). r x y} snd Z = top\<close>
    apply (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
    by (metis assms(2) right_totalE)
qed



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


declare prod.Domainp_rel[with_type_simps]

setup \<open>With_Type.add_relator_global \<^type_name>\<open>filter\<close>
  (fn ctxt => fn mk => fn \<^Type>\<open>filter T\<close> => \<^Term>\<open>rel_filter \<open>mk T\<close>\<close> ctxt)\<close>

declare prod.right_total_rel[with_type_transfer_rules]

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun (rel_set A) (rel_filter A)) principal principal\<close>
  by (simp add: RelI' principal_parametric)

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>Bex\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>image\<close>\<close>

lemma [with_type_transfer_rules]: \<open>Domainp (rel_filter R) = (\<lambda>F. F \<le> principal (Collect S))\<close> if \<open>Domainp R = S\<close>
  using Domainp_rel_filter[where r=R, OF that]
  by presburger

declare right_total_rel_filter [with_type_transfer_rules]
declare bi_unique_rel_filter [with_type_transfer_rules]

declare Inf_filter_parametric'[add_Rel, with_type_transfer_rules]

declare eventually_parametric[add_Rel, with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.uniformity_dist\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>uniformity_dist\<close>\<close>

declare Ball_transfer[add_Rel, with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.open_uniformity\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>open_uniformity\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.metric_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.metric_space\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>metric_space\<close>\<close>

declare prod_filter_parametric [add_Rel, with_type_transfer_rules]
declare le_filter_parametric [add_Rel, with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>uniform_space.cauchy_filter\<close>\<close>

lemma [with_type_transfer_rules]: \<open>is_equality r \<Longrightarrow> is_equality (rel_filter r)\<close>
  by (rule relator_eq_raw)

declare filtermap_parametric [add_Rel, with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>uniform_space.Cauchy\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>filterlim\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>topological_space.nhds\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>topological_space.convergent\<close>\<close>

declare right_total_fun [with_type_transfer_rules]
declare right_unique_eq [with_type_transfer_rules]

declare left_unique_eq [with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_space\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_space\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_vector\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_normed_vector\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semigroup_mult\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semigroup_mult\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.monoid_mult_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.monoid_mult\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>monoid_mult\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.zero_neq_one\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>zero_neq_one\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.division_ring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.division_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>division_ring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_semigroup_mult_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_semigroup_mult\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ab_semigroup_mult\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_ring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_mult_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_mult\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_monoid_mult\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_ring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_ring_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.mult_zero\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>mult_zero\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_0\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.field_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>field\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.preorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>preorder\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>order\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_semigroup_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ab_semigroup_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_group_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ab_group_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_algebra_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_algebra\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_algebra_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_algebra_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_algebra_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_normed_algebra\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_algebra_1_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_algebra_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_normed_algebra_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_top_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_top\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>order_top\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_bot_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_bot\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>order_bot\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semilattice_sup_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semilattice_sup\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semilattice_sup\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semilattice_inf_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semilattice_inf\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semilattice_inf\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>lattice\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.bounded_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>bounded_lattice\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_lattice\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.no_top_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.no_top\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>no_top\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.no_bot_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.no_bot\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>no_bot\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_comm_monoid_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_semiring\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cancel_ab_semigroup_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cancel_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>cancel_ab_semigroup_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_cancel_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_cancel_ab_semigroup_add\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring_0\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.zero_less_one_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.zero_less_one\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>zero_less_one\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_no_zero_divisors_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_no_zero_divisors\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_no_zero_divisors\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.idom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>idom\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.idom_abs_sgn_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.idom_abs_sgn\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>idom_abs_sgn\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.dense_order_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.dense_order\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>dense_order\<close>\<close>

(* local_setup \<open>define_stuff \<^here> \<^class>\<open>size\<close>\<close> (* TODO: better error. Probably from a Class.rules call *) *)


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.abs_if\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>abs_if\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.equal\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>equal\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.enum\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>enum\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linorder_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linorder\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.wellorder_axioms\<close>\<close> (* TODO: insert left/right_unique into environment in transfer thm generation *)
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.wellorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>wellorder\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.numeral\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>numeral\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.monoid_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>monoid_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_numeral\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_numeral\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>comp\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>id\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>semiring_1.of_nat\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_char_0_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_char_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_char_0\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring_1\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.distrib_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.distrib_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>distrib_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.dense_linorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>dense_linorder\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>Complete_Partial_Order.chain\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ccpo_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ccpo\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ccpo\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cancel_semigroup_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cancel_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>cancel_semigroup_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.group_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.group_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>group_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.neg_numeral\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>neg_numeral\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cancel_comm_monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>cancel_comm_monoid_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_diff_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_monoid_diff\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_monoid_diff\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_0_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_0_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_1_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_1_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_char_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_char_0\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_0_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring_0_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_1_cancel_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_1_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring_1_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_modulo_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_modulo\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_modulo\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_parity_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_parity\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_parity\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_parity\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_parity\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_bits_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_bits\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_bits\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_semiring_0\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_comm_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_cancel_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_cancel_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.check_all\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>check_all\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_nonzero_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_nonzero_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_nonzero_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_1_no_zero_divisors\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_1_no_zero_divisors\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semidom\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_ab_semigroup_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unbounded_dense_linorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unbounded_dense_linorder\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_cancel_comm_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_cancel_comm_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.bounded_semilattice_inf_top\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>bounded_semilattice_inf_top\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.bounded_lattice_top\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>bounded_lattice_top\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.bounded_semilattice_sup_bot\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>bounded_semilattice_sup_bot\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.bounded_lattice_bot\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>bounded_lattice_bot\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.boolean_algebra_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.boolean_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>boolean_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.topological_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>topological_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t0_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t0_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>t0_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t1_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t1_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>t1_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t2_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t2_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>t2_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t3_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t3_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>t3_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t4_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.t4_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>t4_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.perfect_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.perfect_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>perfect_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_topology_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.order_topology\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>order_topology\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.uniform_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.uniform_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>uniform_space\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.discrete_topology_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.discrete_topology\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>discrete_topology\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linorder_topology\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linorder_topology\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.canonically_ordered_monoid_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.canonically_ordered_monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>canonically_ordered_monoid_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.dioid\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>dioid\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_bit_operations_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_bit_operations\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_bit_operations\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_bit_operations_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_bit_operations\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_bit_operations\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.strict_ordered_ab_semigroup_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.strict_ordered_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>strict_ordered_ab_semigroup_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.strict_ordered_comm_monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>strict_ordered_comm_monoid_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_cancel_comm_monoid_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_cancel_comm_monoid_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_semigroup_add_imp_le_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_semigroup_add_imp_le\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ab_semigroup_add_imp_le\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_cancel_comm_monoid_diff\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_cancel_comm_monoid_diff\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_no_zero_divisors_cancel_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_no_zero_divisors_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_no_zero_divisors_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom_divide_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom_divide\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semidom_divide\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.algebraic_semidom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>algebraic_semidom\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom_modulo\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semidom_modulo\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_no_zero_divisors\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_no_zero_divisors\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_1_no_zero_divisors\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_1_no_zero_divisors\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom_divide_unit_factor_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semidom_divide_unit_factor\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semidom_divide_unit_factor\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.normalization_semidom_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.normalization_semidom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>normalization_semidom\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_gcd_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_gcd\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_gcd\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ring_gcd\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ring_gcd\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_Gcd_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_Gcd\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_Gcd\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_div_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_div_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>euclidean_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_cancel_ab_semigroup_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_cancel_ab_semigroup_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.normalization_semidom_multiplicative_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.normalization_semidom_multiplicative\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>normalization_semidom_multiplicative\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semiring_gcd_mult_normalize\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>semiring_gcd_mult_normalize\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.first_countable_topology_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.first_countable_topology\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>first_countable_topology\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.banach\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>banach\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_div_algebra_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_div_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_normed_div_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_semiring_cancel_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_semiring_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>euclidean_semiring_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_semigroup_monoid_add_imp_le\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ab_semigroup_monoid_add_imp_le\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semiring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_semiring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_comm_ring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semiring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_semiring_1\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_ab_group_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_ab_group_add\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_group_add_abs_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ab_group_add_abs\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ab_group_add_abs\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_ring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ring_abs_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ring_abs\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ring_abs\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semiring_strict_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semiring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_semiring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_ring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_ring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semiring_1_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_semiring_1_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_comm_semiring_strict_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_comm_semiring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_comm_semiring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semidom_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_semidom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_semidom\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_real_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_real_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_real_vector\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_with_nat_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_with_nat\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_semiring_with_nat\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_numeral_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_numeral\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_semiring_numeral\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_ring_with_nat\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_ring_with_nat\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_1_cancel_crossproduct_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.comm_semiring_1_cancel_crossproduct\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>comm_semiring_1_cancel_crossproduct\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.idom_divide\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>idom_divide\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.idom_modulo\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>idom_modulo\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.field_char_0\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>field_char_0\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.field_abs_sgn\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>field_abs_sgn\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_idom_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_idom\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_idom\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linordered_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linordered_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>euclidean_ring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.archimedean_field_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.archimedean_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>archimedean_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.floor_ceiling_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.floor_ceiling\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>floor_ceiling\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.real_normed_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>real_normed_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.euclidean_ring_cancel\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>euclidean_ring_cancel\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_ring_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_ring\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_ring\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unique_euclidean_semiring_with_bit_operations\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unique_euclidean_semiring_with_bit_operations\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.conditionally_complete_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.conditionally_complete_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>conditionally_complete_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.finite_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.finite_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>finite_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_distrib_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_distrib_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_distrib_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.finite_distrib_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>finite_distrib_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_boolean_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_boolean_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.conditionally_complete_linorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>conditionally_complete_linorder\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_linorder\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_linorder\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linear_continuum_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linear_continuum\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linear_continuum\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.linear_continuum_topology\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>linear_continuum_topology\<close>\<close>




ML \<open>
fun print_untransferred_classes ctxt except = let
  val thy = Proof_Context.theory_of ctxt
  val classes = Sign.all_classes thy
  val untransferred = filter (fn class =>
        is_none (With_Type.get_with_type_info_by_class ctxt class)  (* Not transferred_axioms *)
        andalso not (is_none (fst (Class.rules thy class))) (* Not an axiomless class *)
        andalso not (member (op=) except class) (* Not explicitly excluded *)
      ) classes
  val _ = tracing ("Total number of classes: " ^ string_of_int (length classes))
  val _ = tracing ("Number of untransferred classes: " ^ string_of_int (length untransferred))
  val _ = tracing ("Untransferred classes:\n")
  val _ = List.app (fn class => tracing ("class " ^ Syntax.string_of_sort ctxt [class])) untransferred
  in untransferred end
\<close>


ML \<open>
print_untransferred_classes \<^context> []
\<close>


end (* theory *)
