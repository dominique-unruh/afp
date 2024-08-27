theory Generalize_Constants_Proofs
  imports Main "HOL-Types_To_Sets.Types_To_Sets" Rewrite_Proofs
begin

lemma bla: \<open>a + b + c + d = (b + c) + (a + d)\<close> for a :: \<open>'a :: ab_semigroup_add\<close>
  by (metis ab_semigroup_add_class.add_ac(1) add.commute)


ML \<open>
type gen_const_options = {
  constant: string,
  typ: typ,
  free: string
}\<close>


ML \<open>
val gen_const_thm = @{thm bla[internalize_sort \<open>'a::ab_semigroup_add\<close>, where 'a='b]}
val gen_const_opts: gen_const_options = {
  constant = \<^const_name>\<open>plus\<close>,
  typ = \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>,
  free = "plus"
}
\<close>

ML \<open>
fun generalize_constant_term (options: gen_const_options) t = let
  fun gen_const (Const (name,T)) =
        if name = #constant options andalso T = #typ options then SOME (Free (#free options, T))
        else NONE
    | gen_const (t as Free (name,T)) =
        if name = #free options then raise TERM ("generalize_constant_term: collision of free variable name", [t])
        else NONE
    | gen_const _ = NONE
  in
    map_aterms (Same.function gen_const) t
  end
\<close>



ML \<open>          
(* fun rewrite_term t = subst_atomic [(\<^term>\<open>Num.num.One\<close>, \<^term>\<open>Num.num.Bit1 Num.num.One\<close>)] t *)
val rewrite_term = generalize_constant_term gen_const_opts
val rewriter: Rewrite_Proofs.rewriter = {
  want_Appt = fn _ => fn _ => fn orig_left => fn orig_right => ((), rewrite_term orig_left, rewrite_term orig_right),
  apply_Appt = fn ctxt => fn _ => fn left => fn right => Thm.forall_elim (Thm.cterm_of ctxt right) left,
  want_App = fn _ => fn _ => fn orig_left => fn orig_right => ((), rewrite_term orig_left, rewrite_term orig_right),
  apply_App = fn ctxt => fn _ => fn left => fn right => Thm.implies_elim left right,
  want_AbsP = fn _ => fn _ => fn orig_concl => fn orig_hyp => ((), rewrite_term orig_concl, rewrite_term orig_hyp)
}
\<close>

(* 

(5672000) PThm ""
  Proven: \<And>a b c d. OFCLASS(?'b1, ab_semigroup_add_class) \<Longrightarrow> a + b + c + d = b + c + (a + d)
  Thm prop: OFCLASS(?'a, ab_semigroup_add_class) \<Longrightarrow> ?a + ?b + ?c + ?d = ?b + ?c + (?a + ?d)
  Proven inside: OFCLASS(?'a, ab_semigroup_add_class) \<Longrightarrow> ?a + ?b + ?c + ?d = ?b + ?c + (?a + ?d)
  Goal: \<And>a b c d. OFCLASS('x1998097157'b_1, ab_semigroup_add_class) \<Longrightarrow> a + b + c + d = b + c + (a + d) 

 *)

ML \<open>
local
  val prf = gen_const_thm |> Rewrite_Proofs.prooft_of_thm
  val options = {max_pthms = Unsynchronized.ref 1}
in
  val thm = prf |> Rewrite_Proofs.rewrite_proof \<^context> rewriter options (Rewrite_Proofs.prop_of_prooft prf |> rewrite_term)
end
\<close>

end
