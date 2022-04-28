theory With_Type_Inst_HOL
  imports With_Type HOL.Real_Vector_Spaces
begin


ML \<open>
Class.rules \<^theory> \<^class>\<open>finite\<close>
\<close>

lemma itself_transfer[with_type_transfer_rules]:
  \<open>Transfer.Rel rel_itself TYPE('a) TYPE('b)\<close>
  by (simp add: RelI rel_itself.simps)


ML \<open>
Thm.all_axioms_of \<^theory> |> filter (fn (n,th) => String.isSubstring "finite" n andalso String.isSubstring "class" n)
\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.finite\<close>\<close>
thm with_type_transfer_Finite_Set_class_finite
(* TODO: should not be for an applied class.finite *)

lemma aux3:
  includes lifting_syntax
  assumes \<open>Transfer.Rel R A (B TYPE('a))\<close>
  shows \<open>Transfer.Rel (rel_itself ===> R) (\<lambda>_. A) B\<close>
  by (metis Rel_def assms rel_funI rel_itself.cases)

declare with_type_transfer_Finite_Set_class_finite[THEN aux3[where B=\<open>class.finite\<close>], with_type_transfer_rules]

schematic_goal xx:
\<open>(bi_unique (?r::?'b \<Rightarrow> ?'c \<Rightarrow> bool) \<Longrightarrow> right_total ?r \<Longrightarrow> Domainp ?r = (\<lambda>x. x \<in> S) \<Longrightarrow> 
  bi_unique ((?r7))) \<Longrightarrow> True\<close>
  by simp

ML \<open>
Thm.assumption NONE 1
@{thm xx}
\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>finite\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.semigroup_add\<close>\<close>
thm with_type_transfer_Groups_class_semigroup_add

thm with_type_transfer_rules

local_setup \<open>define_stuff \<^here> \<^class>\<open>semigroup_add\<close>\<close>

(*   shows \<open>rel_fun (rel_fun r (rel_fun r r)) (=) ?X
          (\<lambda>plus. \<forall>a b c. plus (plus a b) c = plus a (plus b c))\<close>  *)


(* TODO: should not be needed *)
declare with_type_semigroup_add_class_transfer[
    unfolded with_type_semigroup_add_class_def fst_conv snd_conv with_type_semigroup_add_class_rel_def,
    transfer_rule]
declare class.ab_semigroup_add_axioms_def[with_type_simps]

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

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_group_add_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ab_group_add\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ab_group_add\<close>\<close>



(* local_setup \<open>define_stuff \<^here> \<^class>\<open>scaleR\<close>\<close> *)
(* local_setup \<open>define_stuff \<^here> \<^class>\<open>norm\<close>\<close> *)
(* local_setup \<open>define_stuff \<^here> \<^class>\<open>sgn\<close>\<close> *)
(* local_setup \<open>define_stuff \<^here> \<^class>\<open>minus\<close>\<close> *)
(* local_setup \<open>define_stuff \<^here> \<^class>\<open>open\<close>\<close> *)
(* local_setup \<open>define_stuff \<^here> \<^class>\<open>uniformity\<close>\<close> *)

ML \<open>
Thm.all_axioms_of \<^theory> |> filter (fn (name,thm) => 
    case Thm.prop_of thm of
      Const(\<^const_name>\<open>Pure.eq\<close>,_) $ lhs $ _ => 
         (case head_of lhs of Const(n,_) => n=\<^const_name>\<open>inverse\<close>
                               | _ => false)
     | _ => false)
\<close>

ML \<open>
get_raw_definitions \<^context> \<^const_name>\<open>inverse_rat_inst.inverse_rat\<close>\<close>

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (=) x x\<close>
  by (simp add: Rel_eq_refl)

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun (=) (rel_fun r (rel_fun r r))) If If\<close>
  using If_transfer RelI' by blast

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>inverse_rat_inst.inverse_rat\<close>\<close>
(* 
Solve this by:
- Applying bi_unique (=), right_total (=), Domainp (=) = ... whenever the rhs type has not typ vars
 *)

ML \<open>
get_raw_definitions \<^context> \<^const_name>\<open>inverse\<close>
\<close>

ML \<open>
val defs = Thm.all_axioms_of \<^theory> |> List.filter (fn (name,thm) => 
    Thm.prop_of thm |> exists_Const (fn (c,_) => c=\<^const_name>\<open>inverse\<close>))

\<close>


  by ERROR: "inverse is overloaded, where do we get the right def?"

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>inverse\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.sgn_div_norm\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>sgn_div_norm\<close>\<close>
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

local_setup \<open>define_stuff \<^here> \<^class>\<open>uniformity_dist\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>open_uniformity\<close>\<close>

lemmas with_type_uniformity_dist_class_transfer'[transfer_rule] = with_type_uniformity_dist_class_transfer[
    unfolded with_type_uniformity_dist_class_def fst_conv snd_conv with_type_uniformity_dist_class_rel_def,
    THEN tmp]
lemmas with_type_open_uniformity_class_transfer'[transfer_rule] = with_type_open_uniformity_class_transfer[
    unfolded with_type_open_uniformity_class_def fst_conv snd_conv with_type_open_uniformity_class_rel_def,
    THEN tmp]
declare class.metric_space_axioms_def[with_type_simps]


local_setup \<open>define_stuff \<^here> \<^class>\<open>metric_space\<close>\<close>

lemmas with_type_metric_space_class_transfer'[transfer_rule] = with_type_metric_space_class_transfer[
    unfolded with_type_metric_space_class_def fst_conv snd_conv with_type_metric_space_class_rel_def,
    THEN tmp3]
declare class.complete_space_axioms_def[with_type_simps]

local_setup \<open>
local_note \<^binding>\<open>uniform_space_class_Cauchy_uniform_raw\<close>
(Thm.axiom \<^theory> "Topological_Spaces.uniform_space.Cauchy_uniform_raw")
\<close>

local_setup \<open>
local_note \<^binding>\<open>uniform_space_class_cauchy_filter_def_raw\<close>
(Thm.axiom \<^theory> "Topological_Spaces.uniform_space.cauchy_filter_def_raw")
\<close>

term uniform_space.cauchy_filter

lemma uniform_space_cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>(rel_filter (rel_prod r r) ===> rel_filter r ===> (\<longleftrightarrow>)) uniform_space.cauchy_filter uniform_space.cauchy_filter\<close>
  unfolding uniform_space_class_cauchy_filter_def_raw
  by transfer_prover

lemma uniform_space_Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>(rel_filter (rel_prod r r) ===> ((=) ===> r) ===> (\<longleftrightarrow>)) uniform_space.Cauchy uniform_space.Cauchy\<close>
  using filtermap_parametric[transfer_rule] apply fail?
  unfolding uniform_space_class_Cauchy_uniform_raw
  by transfer_prover

local_setup \<open>
local_note \<^binding>\<open>topological_space_nhds_def_raw\<close>
(Thm.axiom \<^theory> "Topological_Spaces.topological_space.nhds_def_raw")
\<close>

lemma topological_space_nhds_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>((rel_set r ===> (\<longleftrightarrow>)) ===> r ===> rel_filter r)  topological_space.nhds topological_space.nhds\<close>
  by simp

local_setup \<open>
local_note \<^binding>\<open>topological_space_convergent_def_raw\<close>
(Thm.axiom \<^theory> "Topological_Spaces.topological_space.convergent_def_raw")
\<close>

lemma topological_space_convergent_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>((rel_set r ===> (\<longleftrightarrow>)) ===> ((=) ===> r) ===> (\<longleftrightarrow>))  topological_space.convergent topological_space.convergent\<close>
  using filtermap_parametric[transfer_rule] apply fail?
  unfolding topological_space_convergent_def_raw
  apply transfer_prover_start
     
apply transfer_step+
  by transfer_prover
  term topological_space.convergent

local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_space\<close>\<close>

end (* theory *)
