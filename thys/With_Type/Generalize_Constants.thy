theory Generalize_Constants
  imports Main "HOL-Types_To_Sets.Types_To_Sets"
begin

ML \<open>Proofterm.proofs := 6\<close>

lemma bla: \<open>a + b + c + d = (b + c) + (a + d)\<close> for a :: \<open>'a :: ab_semigroup_add\<close>
  by (metis ab_semigroup_add_class.add_ac(1) add.commute)



ML \<open>
val a = TVar(("'a",0), \<^sort>\<open>type\<close>)
\<close>

ML \<open>
type options = {
  constant: string,
  typ: typ,
  free: string
}
\<close>

ML \<open>
fun generalize_constant_term (options: options) t = let
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
val refl = @{thm refl[where 'a='b]}
val prf = Proofterm.reconstruct_proof (Thm.theory_of_thm refl) (Thm.prop_of refl) (Thm.proof_of refl)


\<close>



ML \<open>
open ZTerm
\<close>


ML \<open>
fun generalize_constant_proof ctxt options MinProof = error "MinProof"
  | generalize_constant_proof ctxt options (prf as PBound _) = prf
  | generalize_constant_proof ctxt options (Abst (name,T,prf)) = 
      Abst (name,T, generalize_constant_proof ctxt options prf)
  | generalize_constant_proof ctxt options (AbsP (_, NONE, _)) = error "AbsP NONE"
  | generalize_constant_proof ctxt options (AbsP (n, SOME t, prf)) = 
      AbsP (n, SOME (generalize_constant_term options t), generalize_constant_proof ctxt options prf)
  | generalize_constant_proof ctxt options (_ % NONE) = error "% NONE"
  | generalize_constant_proof ctxt options (prf % SOME t) =
      generalize_constant_proof ctxt options prf %
        SOME (generalize_constant_term options t)
  | generalize_constant_proof ctxt options (prf1 %% prf2) = 
      generalize_constant_proof ctxt options prf1 %%
          generalize_constant_proof ctxt options prf2
  | generalize_constant_proof ctxt options (Hyp _) = error "Hyp"
  | generalize_constant_proof ctxt options (prf as PAxm (name,t,_)) = let
      val t' = generalize_constant_term options t
      val _ = t = t' orelse raise TERM ("generalize_constant_proof: PAxm " ^ name, [t]) 
      in prf end
  | generalize_constant_proof ctxt options (prf as PClass _) = prf
  | generalize_constant_proof ctxt options (Oracle _) = error "Oracle"
  | generalize_constant_proof ctxt options (prf as PThm (header,_)) =
      Oracle ("generalize_constant_proof: " ^ #name header, #prop header, #types header)
\<close>


(* ML \<open>
fun generalize_constant_thm ctxt (options: options) thm = let
    val old_prop = Thm.prop_of thm
    val old_hyps = Thm.hyps_of thm
    val new_prop = generalize_constant_term options old_prop
    val new_hyps = map (generalize_constant_term options) old_hyps
    val _ = null (Thm.tpairs_of thm) orelse error "nyi: tpairs"
    val _ = old_prop = new_prop andalso old_hyps = new_hyps
               andalso raise Same.SAME
    val _ = tracing ("generalize_constant_thm: " ^ Syntax.string_of_term ctxt old_prop ^ "\n                      -> " ^ Syntax.string_of_term ctxt new_prop)
    fun fake () = Skip_Proof.make_thm (Thm.theory_of_thm thm) new_prop
    val new_thm = case Thm.proof_of thm of 
        MinProof => error "MinProof"
      | PBound _ => error "PBound"
      | Abst _ => error "Abst"
      | AbsP (_,NONE,_) => error "AbsP NONE"
      | AbsP (name, SOME t, prf) => fake()
      | prf1 %% prf2 => error "%%"
      | prf % t => error "%"
      | Hyp _ => error "Hyp"
      | PAxm _ => error "PAxm"
      | PClass _ => error "PClass"
      | Oracle _ => error "Oracle"
      | PThm _ => error "PThm"
  in
    new_thm
  end
  handle Same.SAME => thm
\<close> *)



ML \<open>
val thm = @{thm bla[internalize_sort \<open>'a::ab_semigroup_add\<close>]}
val options: options = {
  constant = \<^const_name>\<open>plus\<close>,
  typ = a --> a --> a,
  free = "plus"
}

(* val prf = Thm.proof_of thm 
    |> Proofterm.reconstruct_proof (Thm.theory_of_thm thm) (Thm.prop_of thm)
    |> Proofterm.expand_proof (Thm.theory_of_thm thm) Proofterm.expand_name_empty
    |> Proofterm.freeze_thaw_prf |> fst
    |> generalize_constant_proof \<^context> options
val reconstruct = Proof_Checker.thm_of_proof (Thm.theory_of_thm thm) prf *)
fun recon ctxt t ZDummy = 
    (tracing ("ZDummy " ^ Syntax.string_of_term ctxt t);
    Skip_Proof.make_thm (Proof_Context.theory_of ctxt) t)
  | recon ctxt t (ZConstp (name, t', _, _)) = 
    (tracing ("ZConstp " ^ \<^make_string> name ^ ": " ^ Syntax.string_of_term ctxt t);
    Skip_Proof.make_thm (Proof_Context.theory_of ctxt) t)
  | recon ctxt t (ZBoundp 0) = 
    (tracing ("ZBoundp: " ^ Syntax.string_of_term ctxt t);
    Skip_Proof.make_thm (Proof_Context.theory_of ctxt) t)
  | recon ctxt t (ZHyp _) =
    Thm.assume (Thm.cterm_of ctxt t)
(* val result = recon \<^context> (Thm.prop_of thm) (Thm.zproof_of thm) *)
;;
Thm.zproof_of thm
\<close>


ML \<open>
(* val result1 = generalize_constant_term options (Thm.prop_of thm) *)
val result = generalize_constant_thm \<^context> options thm
(* val result = generalize_constant_proof \<^context> options prf |> Proof_Checker.thm_of_proof (Thm.theory_of_thm thm) *)
\<close>


end