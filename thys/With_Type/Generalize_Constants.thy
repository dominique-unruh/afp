theory Generalize_Constants
  imports Main "HOL-Types_To_Sets.Types_To_Sets"
begin

(* ML \<open>Proofterm.proofs := 6\<close> *)

lemma bla: \<open>a + b + c + d = (b + c) + (a + d)\<close> for a :: \<open>'a :: ab_semigroup_add\<close>
  by (metis ab_semigroup_add_class.add_ac(1) add.commute)


ML \<open>
type gen_const_options = {
  constant: string,
  typ: typ,
  free: string
}
\<close>


ML \<open>
val gen_const_thm = @{thm bla[internalize_sort \<open>'a::ab_semigroup_add\<close>]}
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
datatype prooft =
     PTBound of term * int
   | PTAbst of term * string * typ * prooft
   | PTAbsP of term * string * term * prooft
   | PTAppt of term * prooft * term
   | PTApp of term * prooft * prooft
   | PTHyp of term
   | PTAxm of term * string * term * typ list
   | PTClass of term * typ * class
   | PTOracle of term * string * term * typ list
   | PTThm of term * Proofterm.thm_header * Proofterm.thm_body
\<close>

ML \<open>
fun prop_of_prooft (PTBound (t,_)) = t
  | prop_of_prooft (PTAbst (t,_,_,_)) = t
  | prop_of_prooft (PTAbsP (t,_,_,_)) = t
  | prop_of_prooft (PTAppt (t,_,_)) = t
  | prop_of_prooft (PTApp (t,_,_)) = t
  | prop_of_prooft (PTHyp t) = t
  | prop_of_prooft (PTAxm (t,_,_,_)) = t
  | prop_of_prooft (PTOracle (t,_,_,_)) = t
  | prop_of_prooft (PTThm (t,_,_)) = t
  | prop_of_prooft (PTClass (t,_,_)) = t
\<close>

ML \<open>
fun pr t = Syntax.string_of_term \<^context> t |> tracing
\<close>


ML \<open>
fun lookup_thm thy =
  let val tab = Symtab.build (Global_Theory.all_thms_of thy true |> fold_rev Symtab.update) in
    fn s =>
      (case Symtab.lookup tab s of
        NONE => error ("Unknown theorem " ^ quote s)
      | SOME thm => thm)
  end;
val lookup = lookup_thm \<^theory>
\<close>

ML \<open>
val add_type_variables = (fold_types o fold_atyps) (insert (op =));
fun type_variables_of t = rev (add_type_variables t []);
fun prop_of_atom prop Ts =
  subst_atomic_types (type_variables_of prop ~~ Ts) (Proofterm.forall_intr_variables_term prop);
\<close>

ML \<open>
val head_norm = Envir.head_norm Envir.init
fun make_prooft' _ (PThm (header as {prop, types=SOME Ts, ...}, body)) : prooft =
       PTThm (prop_of_atom prop Ts, header, body)
  | make_prooft' _ (PAxm (name, prop, SOME Ts)) =
       PTAxm (prop_of_atom prop Ts, name, prop, Ts)
  | make_prooft' Hs (PBound i) = PTBound (nth Hs i, i)
  | make_prooft' Hs (Abst (name, SOME T, prf)) = let
      val prf' = make_prooft' Hs prf
    in PTAbst (Logic.all_const T $ (Abs (name, T, prop_of_prooft prf')), name, T, prf') end
  | make_prooft' Hs (AbsP (name, SOME t, prf)) = let
      val prf' = make_prooft' (t :: Hs) prf
    in PTAbsP (Logic.mk_implies (t, prop_of_prooft prf'), name, t, prf') end
  | make_prooft' Hs (prf % SOME t) = let
      val prf' = make_prooft' Hs prf
      val prop =  (case head_norm (prop_of_prooft prf') of Const ("Pure.all", _) $ f => f $ t
                      | _ => raise ERROR "make_prooft': all expected")
    in PTAppt (prop, prf', t) end
  | make_prooft' Hs (prf1 %% prf2) = let
      val prf1' = make_prooft' Hs prf1
      val prf2' = make_prooft' Hs prf2
      val prop = (case head_norm (prop_of_prooft prf1') of Const ("Pure.imp", _) $ _ $ Q => Q
                      | _ => raise ERROR "make_prooft': ==> expected")
    in PTApp (prop, prf1', prf2') end
  | make_prooft' _ (Hyp t) = PTHyp t
  | make_prooft' _ (PClass (T,class)) = PTClass (Logic.mk_of_class (T,class), T, class)
  | make_prooft' _ (Oracle (name, prop, SOME Ts)) = PTOracle (prop_of_atom prop Ts, name, prop, Ts)
  | make_prooft' _ prf = raise ERROR "make_prooft': partial proof"
fun make_prooft thy prop prf = prf
  |> Proofterm.expand_proof thy Proofterm.expand_name_empty
  |> Proofterm.reconstruct_proof thy prop
  |> Proofterm.freeze_thaw_prf |> fst
  |> make_prooft' []
fun prooft_of_thm thm = make_prooft (Thm.theory_of_thm thm) (Thm.prop_of thm) (Thm.proof_of thm)
\<close>


ML \<open>
type aux = unit
type options = {
    want_Appt: Proof.context -> term -> term -> term -> aux * term * term,
    apply_Appt: Proof.context -> aux -> thm -> term -> thm,
    want_App: Proof.context -> term -> term -> term -> aux * term * term
  }
\<close>

ML \<open>
\<^term>\<open>3\<close>
\<close>


ML \<open>          
(* fun rewrite_term t = subst_atomic [(\<^term>\<open>Num.num.One\<close>, \<^term>\<open>Num.num.Bit1 Num.num.One\<close>)] t *)
val rewrite_term = generalize_constant_term gen_const_opts
val options: options = {
  want_Appt = fn _ => fn target => fn orig_left => fn orig_right => ((), rewrite_term orig_left, rewrite_term orig_right),
  apply_Appt = fn ctxt => fn aux => fn left => fn right => Thm.forall_elim (Thm.cterm_of ctxt right) left,
  want_App = fn _ => fn target => fn orig_left => fn orig_right => ((), rewrite_term orig_left, rewrite_term orig_right)
}
\<close>



ML \<open>
fun fake prop = Skip_Proof.make_thm \<^theory> prop
fun pr t = Syntax.string_of_term \<^context> t |> tracing

fun rewrite_proof ctxt (options:options) = let
  fun rew prop (PTThm (prop', header, body)) =
        (tracing "PThm"; pr prop; pr prop'; fake prop)
    | rew prop (PTAppt (_, prf, t')) = let
        val (aux, prop'', t'') = #want_Appt options ctxt prop (prop_of_prooft prf) t'
        val _ = () (* TODO: check whether   prop'' $ t''   equiv  prop *)
        val thm'' = rew prop'' prf
        val _ = \<^print> (thm'', Thm.cterm_of ctxt prop'', Thm.cterm_of ctxt t'')
      in #apply_Appt options ctxt aux thm'' t'' end
    | rew prop (PTApp (prop', prf1, prf2)) = let
        val (aux, prop1, prop2) = #want_App options ctxt prop (prop_of_prooft prf1) (prop_of_prooft prf2)
        val _ = () (* TODO check *)
        val thm1 = rew prop1 prf1
        val thm2 = rew prop2 prf2
        val _ = \<^print> (Thm.cterm_of ctxt prop)
      in fake prop end
    | rew prop (PTClass (prop', T, class)) = let
        val _ = prop = prop' orelse raise TERM ("rewrite_proof: changing PClass prop not supported", [prop, prop'])
        val _ = Sign.of_sort (Proof_Context.theory_of ctxt) (T, [class]) orelse raise ERROR ("thm_of_proof: bad PClass proof " ^
                  Syntax.string_of_term ctxt (Logic.mk_of_class (T, class)))
        val thm = Thm.of_class (Thm.ctyp_of ctxt T, class)
      in thm end
    | rew prop prf = raise TERM ("rewrite_proof: " ^ \<^make_string> prf, [prop])
  in rew end
\<close>


ML \<open>
val prf = gen_const_thm
  |> prooft_of_thm
  |> rewrite_proof \<^context> options (Thm.prop_of gen_const_thm |> rewrite_term)
\<close>





ML \<open>
(* val result1 = generalize_constant_term options (Thm.prop_of thm) *)
(* val result = generalize_constant_thm \<^context> options thm *)
(* val result = generalize_constant_proof \<^context> options prf |> Proof_Checker.thm_of_proof (Thm.theory_of_thm thm) *)
\<close>


end