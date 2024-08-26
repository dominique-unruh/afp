theory Generalize_Constants
  imports Main  "HOL-Types_To_Sets.Types_To_Sets"
begin

lemma bla: \<open>a + b + c + d = (b + c) + (a + d)\<close> for a :: \<open>'a :: ab_semigroup_add\<close>
  by (metis ab_semigroup_add_class.add_ac(1) add.commute)

ML_file \<open>generalize_constants.ML\<close>


ML \<open>
open Generalize_Constants
\<close>


ML \<open>
val a = TVar(("'a",0), \<^sort>\<open>type\<close>)
val gen_const_thm = @{thm bla[internalize_sort \<open>'a::ab_semigroup_add\<close>]}
val gen_const_opts: options = {
  constant = \<^const_name>\<open>plus\<close>,
  typ = a --> a --> a,
  free = "plus"
}
\<close>

thm Binomial.Incl_Excl_def

ML \<open>
;;
generalize_constant_thm gen_const_opts gen_const_thm
\<close>



end
