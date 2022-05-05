theory With_Type_Inst_Complex_Bounded_Operators
  imports With_Type_Inst_HOL Complex_Bounded_Operators.Complex_Bounded_Linear_Function
begin

lemma [with_type_transfer_rules]:
  includes lifting_syntax
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  assumes \<open>bi_unique s\<close>
  shows \<open>Transfer.Rel ((r ===> s) ===> (r ===> s) ===> (=)) (\<lambda>f g. \<forall>x. S x \<longrightarrow> f x = g x) (=)\<close>
  apply (rule RelI)
  apply (rule rel_funI)
  apply (rule rel_funI)
  by (smt (z3) DomainPI Domainp.cases assms(1) assms(2) assms(3) bi_uniqueDl bi_unique_right_unique 
      rel_fun_def right_uniqueD right_unique_fun)

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.scaleC\<close>\<close>

local_setup \<open>define_stuff \<^here> \<^class>\<open>scaleC\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_vector\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_normed_vector\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_inner_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_inner\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_inner\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cbanach\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>cbanach\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.chilbert_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>chilbert_space\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ceuclidean_space_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ceuclidean_space\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ceuclidean_space\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>is_ortho_set\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.onb_enum_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.onb_enum\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>onb_enum\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>scaleC_prod_inst.scaleC_prod\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>scaleC\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>cspan\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cfinite_dim_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.cfinite_dim\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>cfinite_dim\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.basis_enum_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.basis_enum\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>basis_enum\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_algebra_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_algebra_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_algebra_1\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_div_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_div_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_complex_vector_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_complex_vector\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_complex_vector\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_normed_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_algebra_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_normed_algebra_1\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_div_algebra\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_normed_div_algebra\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complex_normed_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complex_normed_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.not_singleton\<close>\<close>
(* TODO see finite for the same problem *)
declare with_type_transfer_Extra_General_class_not_singleton[THEN aux3[where B=\<open>class.not_singleton\<close>], with_type_transfer_rules]
thm with_type_transfer_Extra_General_class_not_singleton[THEN aux3[where B=\<open>class.not_singleton\<close>], with_type_transfer_rules]
local_setup \<open>define_stuff \<^here> \<^class>\<open>not_singleton\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complemented_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complemented_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complemented_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_complemented_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_complemented_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.orthocomplemented_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.orthocomplemented_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>orthocomplemented_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_orthocomplemented_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_orthocomplemented_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.orthomodular_lattice_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.orthomodular_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>orthomodular_lattice\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.complete_orthomodular_lattice\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>complete_orthomodular_lattice\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.unbounded_dense_order\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>unbounded_dense_order\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.partial_abs_if\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>partial_abs_if\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_1\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_semiring_1\<close>\<close>

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_strict_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_semiring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_semiring_1_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_semiring_1_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_semiring_strict_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_comm_semiring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_comm_semiring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_ring_strict\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_ring_strict\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.ordered_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>ordered_field\<close>\<close>


local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.nice_ordered_field_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.nice_ordered_field\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>nice_ordered_field\<close>\<close>

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (list_all2 R) [] []\<close>
  by (simp add: Rel_def)

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun R (rel_fun (list_all2 R) (list_all2 R))) (#) (#)\<close>
  by (simp add: RelI' list.ctr_transfer(2))
declare list.bi_unique_rel [with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.one_dim_axioms\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>class.one_dim\<close>\<close>
local_setup \<open>define_stuff \<^here> \<^class>\<open>one_dim\<close>\<close>


ML \<open>
print_untransferred_classes \<^context> []
\<close>

end
