section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports
    Complex_Bounded_Operators.Complex_L2
    Misc_Tensor_Product  
    "HOL-Library.Function_Algebras" 
    "HOL-ex.Sketch_and_Explore" 
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

(* TODO: remvoe these from Registers.Misc *)
abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"

unbundle no_cblinfun_notation

end
