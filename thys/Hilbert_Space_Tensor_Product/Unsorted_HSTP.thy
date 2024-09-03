theory Unsorted_HSTP
  imports Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    Tensor_Product.Hilbert_Space_Tensor_Product
    Jordan_Normal_Form.Matrix
    Complex_Bounded_Operators.Extra_Jordan_Normal_Form
    Complex_Bounded_Operators.Cblinfun_Matrix
    Partial_Trace
    Tensor_Product_Code
    Von_Neumann_Algebras
begin

(* TODO move everything *)

unbundle cblinfun_notation Finite_Cartesian_Product.no_vec_syntax jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Coset.kernel










end
