structure Rewrite_Proofs = struct

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

val add_type_variables = (fold_types o fold_atyps) (insert (op =));
fun type_variables_of t = rev (add_type_variables t []);
fun prop_of_atom prop Ts =
  subst_atomic_types (type_variables_of prop ~~ Ts) (Proofterm.forall_intr_variables_term prop);

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
      val prop =  (case head_norm (prop_of_prooft prf') of Const ("Pure.all", _) $ f => betapply (f, t)
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
  |> Proofterm.expand_proof thy Proofterm.expand_name_empty (* Does this do anything? *)
  |> Proofterm.reconstruct_proof thy prop
  (* |> Proofterm.freeze_thaw_prf |> fst *)
  |> make_prooft' []
fun prooft_of_thm thm = make_prooft (Thm.theory_of_thm thm) (Thm.prop_of thm) (Thm.proof_of thm)

type aux = unit
type rewriter = {
    want_Appt: Proof.context -> term (* target *) -> term -> term -> aux * term * term,
    apply_Appt: Proof.context -> aux -> thm -> term -> thm,
    want_App: Proof.context -> term -> term -> term -> aux * term * term,
    apply_App: Proof.context -> aux -> thm -> thm -> thm,
    want_AbsP: Proof.context -> term (* target *) -> term (* orig concl *) -> term (* orig hyp *) -> aux * term * term
  }

type options = {
  max_pthms: int Unsynchronized.ref
}

(* fun convert_thm prop thm : thm = let
      val thm_prop = Thm.prop_of thm
  in 
    if prop = thm_prop then thm
    else if prop aconv thm_prop then Thm.renamed_prop prop thm
    else raise TERM ("convert_thm", [prop, Thm.prop_of thm])
  end *)
(* TODO: Can be seriously optimized *)
fun convert_thm ctxt prop thm = let
  open Conv
  val cprop = Thm.cterm_of ctxt prop
  val eq1 = (Thm.beta_conversion true then_conv Thm.eta_conversion) (Thm.cprop_of thm)
  val eq2 = (Thm.beta_conversion true then_conv Thm.eta_conversion) cprop
  val eq = Thm.transitive eq1 (Thm.symmetric eq2)
  val thm' = Thm.equal_elim eq thm
in 
  thm'
end

fun has_varsT (Type(_,Ts)) = exists has_varsT Ts
  | has_varsT (TVar _) = true
  | has_varsT _ = false

fun has_vars (t $ u) = has_vars t orelse has_vars u
  | has_vars (Free (_,T)) = has_varsT T
  | has_vars (Const (_,T)) = has_varsT T
  | has_vars (Var _) = true
  | has_vars (Abs(_,T,body)) = has_varsT T orelse has_vars body
  | has_vars (Bound _) = false

fun fake prop = Skip_Proof.make_thm \<^theory> prop

fun rewrite_proof ctxt (rewriter:rewriter) (options:options) goal prf = let
  fun pr label t = label ^ ": " ^ Syntax.string_of_term ctxt t |> tracing
  fun term_str t = Syntax.string_of_term ctxt t
  (* fun term_str t = \<^make_string> t *)
  val int_str = string_of_int
  val var_pfx = "x" ^ int_str (Random.random_range 0 1000000000000)
  fun mk_var_name (name,index) = var_pfx ^ name ^ "_" ^ int_str index
  fun mk_tvar_name (name,index) = "'" ^ var_pfx ^ name ^ "_" ^ int_str index
  val thy = Proof_Context.theory_of ctxt
  val freezeT_same = Term.map_atyps_same (fn TVar (indexname,T) => TFree (mk_tvar_name indexname, T) | _ => raise Same.SAME)
  val freezeT = Same.commit freezeT_same
  val freeze = map_aterms (fn Var (indexname,T) => Free (mk_var_name indexname, T) | _ => raise Same.SAME)
                 #> map_types freezeT_same
  fun guard id f = \<^try>\<open>f ()
        catch e => error ("rewrite_proof, processing " ^ int_str id ^ ": " ^ \<^make_string> e)\<close>

  fun sanity_want prop = let
      val _ = fastype_of prop = \<^typ>\<open>prop\<close>
          orelse raise TYPE ("rewrite_proof: sanity check failed", [fastype_of prop], [prop])
      val _ = has_vars prop
          andalso (\<^print> prop; \<^print> (Term.add_vars prop []) ; raise TERM ("rewrite_proof: sanity check failed", [prop]))
      val cprop = Thm.cterm_of ctxt prop
    in () end
  fun sanity id Hs prop thm = let
      (* val _ = (tracing "sanity"; \<^print> prop; \<^print> (Thm.prop_of thm); \<^print> (Thm.prop_of thm = prop)) *)
      val _ = Thm.prop_of thm =  prop 
          orelse raise TERM ("rewrite_proof: sanity check failed @ " ^ int_str id, [Thm.prop_of thm, prop])
      val _ = null (Thm.tpairs_of thm) 
          orelse raise TERM ("rewrite_proof: sanity check failed @ " ^ int_str id, [Thm.prop_of thm])
      val _ = subset (fn (t,(_,u)) => t=u) (Thm.hyps_of thm, Hs)
          orelse raise TERM ("rewrite_proof: sanity check (hyps) failed @ " ^ int_str id, Thm.prop_of thm :: Thm.hyps_of thm)
      val shyps = Thm.shyps_of thm
      val _ = null shyps orelse shyps = [\<^sort>\<open>type\<close>]
            orelse raise TERM ("rewrite_proof: sanity check failed, shyps = " ^ \<^make_string> (Thm.shyps_of thm), [Thm.prop_of thm])
    in () end
  fun rew id Hs goal (PTThm (proven, header, body)) = 
      if ! (#max_pthms options) <= 0 then let
          val result_thm = fake goal
          val result_thm = convert_thm ctxt goal result_thm
          val _ = sanity id Hs goal result_thm
        in result_thm end
      else let
          val _ = #max_pthms options := ! (#max_pthms options) - 1
          val thm_prop = #prop header
(*           val prf = body |> Proofterm.thm_body_proof_open
              |> Proofterm.reconstruct_proof (Proof_Context.theory_of ctxt) thm_prop
              |> Proofterm.freeze_thaw_prf |> fst
              |> \<^make_string> |> warning *)
          val prf = make_prooft thy thm_prop (Proofterm.thm_body_proof_open body)
          val _ = tracing ("(" ^ int_str id ^ ") PThm \"" ^ #name header ^ "\"\n  Proven: " ^
                    term_str proven ^ "\n  Thm prop: " ^ term_str thm_prop ^ "\n  Proven inside: " ^
                    term_str (prop_of_prooft prf) ^ "\n  Goal: " ^ 
                    term_str goal)



          val result_thm = fake goal
          val result_thm = convert_thm ctxt goal result_thm
          val _ = sanity id Hs goal result_thm
        in result_thm end
    | rew id Hs goal (PTAppt (_, head_prf, arg)) = let
        val head_frozen = freeze (prop_of_prooft head_prf)
        val arg_frozen = freeze arg
        val (aux, head_wanted, arg_wanted) = #want_Appt rewriter ctxt goal head_frozen arg_frozen
        val id_head = serial ()
        val _ = tracing ("(" ^ int_str id ^ ") Appt (" ^ 
                    term_str head_frozen ^ ") (" ^ term_str arg_frozen ^ ")\n    [" ^ 
                    term_str goal ^ "]\n    \<rightarrow> (" ^ term_str head_wanted ^ ")@" ^ int_str id_head ^
                    " (" ^ term_str arg_wanted ^ ")")
        val _ = sanity_want head_wanted
        val head_thm = rew id_head Hs head_wanted head_prf
        val result_thm = guard id (fn () => #apply_Appt rewriter ctxt aux head_thm arg_wanted)
        val result_thm = convert_thm ctxt goal result_thm
        val _ = sanity id Hs goal result_thm
      in result_thm end
    | rew id Hs goal (PTApp (_, head_prf, arg_prf)) = let
        val head_frozen = freeze (prop_of_prooft head_prf)
        val arg_frozen = freeze (prop_of_prooft arg_prf)
        val (aux, head_wanted, arg_wanted) = #want_App rewriter ctxt goal head_frozen arg_frozen
        val id_head = serial ()
        val id_arg = serial ()
        val _ = tracing ("(" ^ int_str id ^ ") App (" ^
                    term_str head_frozen ^ ") (" ^ term_str arg_frozen ^ ")\n    [" ^ 
                    term_str goal ^ "]\n    \<rightarrow> (" ^ term_str head_wanted ^ ")@" ^ int_str id_head ^ " (" ^ term_str arg_wanted ^ ")@" ^ int_str id_arg)
        val _ = sanity_want head_wanted
        val _ = sanity_want arg_wanted
        val head_thm = rew id_head Hs head_wanted head_prf
        val arg_thm = rew id_arg Hs arg_wanted arg_prf
        val result_thm = guard id (fn () => #apply_App rewriter ctxt aux head_thm arg_thm)
        val result_thm = convert_thm ctxt goal result_thm
        val _ = sanity id Hs goal result_thm
      in result_thm end
    | rew id Hs goal (PTClass (have_prop, T, class)) = let
        val have_prop_frozen = freeze have_prop
        val T_frozen = freezeT T
        val _ = goal = have_prop_frozen orelse raise TERM ("rewrite_proof: changing PClass prop not supported", [goal, have_prop])
        val _ = Sign.of_sort (Proof_Context.theory_of ctxt) (T_frozen, [class]) orelse raise ERROR ("rewrite_proof: bad PClass proof " ^
                  Syntax.string_of_term ctxt (Logic.mk_of_class (T_frozen, class)))
        val result_thm = Thm.of_class (Thm.ctyp_of ctxt T_frozen, class)
        val result_thm = convert_thm ctxt goal result_thm
        val _ = sanity id Hs goal result_thm
      in result_thm end
    | rew id Hs goal (PTAbsP (_, name, hyp, concl_prf)) = let
        (* have_prop = "arg \<Longrightarrow> prop_of body_prf", body_prf is allowed to use arg as a PBound*)
        val hyp_frozen = freeze hyp
        val concl_frozen = freeze (prop_of_prooft concl_prf)
        val (aux, want_concl, want_hyp) = #want_AbsP rewriter ctxt goal concl_frozen hyp_frozen
        val id_concl = serial ()
        val id_hyp = serial ()
        val _ = tracing ("(" ^ int_str id ^ ") AbsP " ^ name ^ " (" ^ 
                    term_str concl_frozen ^ ") (" ^ term_str hyp_frozen ^ ")\n    [" ^ 
                    term_str goal ^ "]\n    \<rightarrow> (" ^ term_str want_concl ^ ")@" ^ int_str id_concl ^ " (" ^ term_str want_hyp ^ ")@ " ^ int_str id_hyp)
        val _ = sanity_want want_concl
        val _ = sanity_want want_hyp
        val concl_thm = rew id_concl ((id_hyp, want_hyp) :: Hs) want_concl concl_prf
        val result_thm = Thm.implies_intr (Thm.cterm_of ctxt want_hyp) concl_thm
        val result_thm = convert_thm ctxt goal result_thm
        val _ = sanity id Hs goal result_thm
      in result_thm end
    | rew _ _ goal (PTHyp hyp) =
        (* Can Hyp's occur in normalized proofs? *)
        raise TERM ("rewrite_proof: PTHyp not supported", [goal, hyp])
    | rew _ Hs goal (PTBound (have_prop, i)) = let
        val (id_hyp, hyp) = nth Hs i
        val _ = hyp = goal
                  orelse raise TERM ("rewrite_proof: PTBound with unexpected prop (stemming from " ^ int_str id_hyp ^ ")", [hyp, goal, have_prop])
        val result_thm = Thm.assume (Thm.cterm_of ctxt hyp)
      in result_thm end
    | rew _ Hs goal prf = raise TERM ("rewrite_proof: " ^ \<^make_string> prf, [goal])
  in rew 0 [] (freeze goal) prf end


end