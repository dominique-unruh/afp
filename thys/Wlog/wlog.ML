structure Wlog : sig

val wlog : Position.T -> (* Position (for bindings and markup) *)
           binding * term -> (* New assumption *)
           term -> (* Goal to operate on *)
           (binding * string * typ) list -> (* Generalizing *)
           (string * thm list) list -> (* Assumptions to keep *)
           bool -> (* internal (as in Proof.show, Proof.have) *)
           Proof.state -> Proof.state

val wlog_cmd : Position.T -> binding * string -> string -> binding list -> 
               (Facts.ref * Token.src list) list -> bool -> Proof.state -> Proof.state

end = struct

(* Returns a marked-up string printing the `binding`, so that it's ctrl-clickable.
   `entity` is the name of the kind of entity the markup claims this referent to (e.g., "fact") *)
fun print_entity_binding entity binding = 
  Pretty.marks_str ([Position.entity_markup entity (Binding.name_of binding, Binding.pos_of binding)], Binding.name_of binding) |> Pretty.string_of

(* Returns a marked-up string printing the `binding`, so that it's ctrl-clickable and refers to a fact.
   (This fact does not need to actually exist (yet).) *)
val print_fact_binding = print_entity_binding Markup.factN

(* Pretty prints a term as a multi-line statement. (Prefixed by `heading`) *)
fun print_term_as_statement ctxt heading term : string = 
  Element.pretty_statement ctxt heading (Thm.assume (Thm.cterm_of ctxt term)) |> Pretty.string_of

(* Prefix put in front of "recovered" facts. *)
val wlog_recovered_facts_prefix = "wlog"

(* Creates a binding based on the long name `name` prefixed by `qualifier`.
   Strips "local" and "local.wlog" off first. *)
fun binding_within qualifier pos name = let
  val (path, name) = split_last (Long_Name.explode name)
  val path = case path of "local" :: path => path | path => path
  val path = case path of p :: ps => if p = wlog_recovered_facts_prefix then ps else ps | ps => ps 
  val binding = Binding.make (name,pos)
      |> fold_rev (fn qualifier => fn b => Binding.qualify true qualifier b) path
      |> Binding.qualify true qualifier
in binding end

(* Proves premise i using facts if possible. Otherwise, just leaves it in place. *)
fun prove_prem_if_possible ctxt facts i thm = let
  val prem = nth (Thm.prems_of thm) (i-1)
  val candidates = Facts.could_unify facts prem |> map fst
  val result = solve_tac ctxt candidates i thm |> Seq.pull |> Option.map fst
in case result of SOME thm => thm | NONE => thm end


(* Given a theorem thm, replaces all occurrences of the free vars "fixes" by the free vars "fixed".
   For any hypothesis of thm that is not a fact in the context "ctxt", a premise is added to the theorem.
   (Thus, the resulting theorem will be valid in "ctxt")

   fixes is a list of (_,n,T) where n is the var name and T the type

   fixed is a list of variable names (types will be the same).
 *)
fun translate_thm ctxt fixes fixed thm = 
  let val hyps = Thm.chyps_of thm
      (* Make all hypotheses of thm into premises (using \<Longrightarrow>) *)
      val thm = fold_rev Thm.implies_intr hyps thm
      val idx = Thm.maxidx_of thm + 1
      (* Replace all free vars in "fixes" by schematic vars of the same name *)
      val thm = Thm.generalize (Names.empty, map #2 fixes |> Names.make_set) idx thm
      (* And now replace those schematic vars by the free variables in `fixes` *)
      val thm = thm |> Thm.instantiate (TVars.empty,
        map2 (fn (_,n,T) => fn m => (((n,idx),T), Thm.cterm_of ctxt (Free (m,T)))) fixes fixed |> Vars.make)
      val facts = Proof_Context.facts_of ctxt
      (* And now prove all the assumptions (that were hypotheses) where this is possible by applying a fact from the context. *)
      val thm = fold (prove_prem_if_possible ctxt facts) (length hyps downto 1) thm
   in thm end


(* We only support negation of bools here (not something like "\<And>P. t \<Longrightarrow> P") because it is not clear
   how to prove negation_tac below otherwise. *)
fun negate _ (Const(@{const_name Trueprop},_) $ t) = HOLogic.mk_Trueprop (HOLogic.mk_not t)
  | negate ctxt t = error ("The wlog-assumption must be of type bool (i.e., don't use \<Longrightarrow>, \<And>, &&&). You specified: " ^ Syntax.string_of_term ctxt t)


(* When: current goal=X, thm=\<not>Y\<Longrightarrow>X, hyp_thm="Y\<Longrightarrow>A\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow>A\<^sub>n\<Longrightarrow>X", assms=[A1,\<dots>,A\<^sub>n].
   Then: This tactic proves the current goal.

   (Number of subgoals is expected to be 1.) *)
fun wlog_aux_tac ctxt thm hyp_thm assms = 
  (* Goal: X *)
  resolve_tac ctxt (@{thms HOL.case_split}) 1
  (* Goal: ?P\<Longrightarrow>X, \<not>?P\<Longrightarrow>X  *)
  THEN solve_tac ctxt [thm] 2
  (* Goal: Y\<Longrightarrow>X  *)
  THEN resolve_tac ctxt [hyp_thm] 1
  (* Goal: Y\<Longrightarrow>Y, A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  THEN assume_tac ctxt 1
  (* Goal: A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  THEN ALLGOALS (fn i => (@{print} (assms,i); resolve_tac ctxt [nth assms (i-1)] i))

(* 
wlog wlogassmname: \<open>wlogassm\<close> goal G generalizing x y z keeping fact1 fact2
  [\<dots> your proof \<dots>]

(Defaults: goal ?thesis generalizing <nothing> keeping <nothing>)

translates roughly to:

  presume hypothesis[case_names wlogassmname fact1 fact2]:
    \<open>\<And>x y z. \<lbrakk>wlogassm; fact1; fact2\<rbrakk> \<Longrightarrow> G\<close>
  have \<open>G\<close> if negation: \<open>\<not> wlogassm\<close>
    [\<dots> your proof \<dots>]
  then show \<open>G\<close>
    [\<dots> autogenerated proof \<dots>]
next
  fix x y z
  (* Below, in all terms, occurrences of the free variables x y z renamed to the new x y z as those could be internally different. *)
  let ?wlog_goal = \<open>[what ?thesis was before]\<close>
  let ?x = \<open>[what ?x was before]\<close> (* for each ?x that was defined before; with occurrences of x y z renamed to the fixed x y z *)
  assume wlogassmname: \<open>wlogassm\<close>  
  assume fact1: \<open>fact1\<close>
  assume fact2: \<open>fact2\<close>
  have lost.xxx: \<open>assms \<Longrightarrow> xxx\<close> 
     (* For any fact xxx: \<open>xxx\<close> that was present in the proof before the wlog command.
         assms are the assumptions that were present in the context before "next" (e.g., via assume command).
         (Assumptions that still hold, e.g., "fact1", "fact2", are removed automatically from assms.) *)
    [\<dots> proof carried over \<dots>]

*)
fun wlog (pos:Position.T)  (* Position where the wlog-command was entered *)
         (newassm_name, newassm)  (* New assumption added wlog *)
         (goal: term)  (* Which goal to work on (should be something that "show" accepts. *)
         (fixes: (binding*string*typ) list) (* Variables to be generalized *)
         (assms: (string*thm list) list)  (* Assumptions to keep *)
         (int: bool)  (* internal (as in Proof.show, Proof.have) *)
         (state: Proof.state) : Proof.state =
  let
      (* initial_ctxt: context at the beginning of the execution. (Does not change much until the `next` command.) *)
      val initial_ctxt = Proof.context_of state
      (* flat_assms: List of (name,i,t) where t are all assumptions, with i an index to distinguish several propositions in the same fact. (i=0 if there is only one).
                     Those assumption are `newassm`, and the assumptions from `assms`*)
      val flat_assms = assms |> map (fn (name,thms) => 
                 case thms of [th] => [(name,0,Thm.prop_of th)]
                           | _ => map_index (fn (i,thm) => (name,i+1,Thm.prop_of thm)) thms) |> List.concat
      val flat_assms = (Binding.name_of newassm_name, 0, newassm) :: flat_assms
      (* hyp: \<And>x1\<dots>xn. A1\<Longrightarrow>A2\<Longrightarrow>...\<Longrightarrow>An\<Longrightarrow>`goal`, where [A1\<dots>An]=flat_assms, [x1\<dots>xn]=fixes *)
      val hyp = Logic.list_implies (map #3 flat_assms, goal)
      val hyp = fold (fn (_,a,T) => fn t => Logic.all_const T $ (Term.absfree (a,T) t)) fixes hyp
      (* case_names: essentially the attribute [case_names A1 \<dots> An] *)
      fun idx_name (name, 0) = name
        | idx_name (name, i) = name ^ "_" ^ string_of_int i
      val case_names = map (fn (name,i,_) => idx_name(name,i)) flat_assms
      val case_names = Rule_Cases.cases_hyp_names case_names (map (K []) case_names)
      (* negated_newassm: newassm, but negated (with error message in case newassm is not a boolean). *)
      val negated_newassm = negate initial_ctxt newassm
      (* Print helpful information for the user. *)
      val _ = Output.information ("Please prove that \"" ^ print_fact_binding newassm_name ^ "\" can be assumed w.l.o.g.\nYou may use the following facts:\n" ^
            print_term_as_statement initial_ctxt "hypothesis:" hyp ^ "\n" ^ print_term_as_statement initial_ctxt "negation:" negated_newassm)

      (* presume hypothesis[case_names \<dots>]: \<open>\<And>x1\<dots>xn. A1\<Longrightarrow>A2\<Longrightarrow>...\<Longrightarrow>An\<Longrightarrow>`goal`\<close> *)
      val state = Proof.presume [] [] [((Binding.make ("hypothesis", pos), [case_names]), [(hyp,[])])] state
      (* hyp_thm: the fact `hypothesis` *)
      val hyp_thm = Proof.the_fact state

      (* Code executed after the user-given proof of the `have` command below. *)
      fun after_qed _ state = 
      let 
          (* proven_thm: the theorem that was just proven
             (`after_qed` also gets that theorem as an argument, but in an unsuitable form for us. The assumptions are replaced by hypotheses.) *)
          val proven_thm = Proof.the_fact state
          (* show \<open>`goal`\<close> *)
          val (_,state) = Proof.show true NONE (fn _ => I) [] [] 
                             [((Binding.empty,[]),[(goal,[])])] int state
          (* Prove this goal using `negation_tac` and `hyp_thm` and `assms`. *)
          val state = Proof.apply (Method.Basic (fn ctxt => 
              (Method.SIMPLE_METHOD (wlog_aux_tac ctxt proven_thm hyp_thm (assms |> map snd |> List.concat)))),
                      Position.no_range) state
              |> Seq.the_result "internal error: negation_tac failed"
          val state = Proof.local_done_proof state
          (* next (Isar command) *)
          val state = Proof.next_block state
          (* fix x1 \<dots> xn (Isar command) *)
          val (fixed,state) = Proof.map_context_result (Proof_Context.add_fixes (map (fn (a,_,T) => (a,SOME T,NoSyn)) fixes)) state
          (* renamed_fixed: Helper function to rename occurrences of `fixes` by `fixed`.
             Note: `fixes` are the fixed variables x1\<dots>xn from before "next", 
                   while `fixed` are those fixed variables as returned by the "fix" command.
                   They look the same to the user but may be internally different. *)
          val rename_fixed = Term.subst_free (map2 (fn (_,a,T) => fn b => (Free (a,T), Free(b,T))) fixes fixed)
          (* Find all let-bindings ("let ?x = \<dots>") from before the wlog-command (in initial_ctxt), and reintroduce them.
             (Remember to rename the fixed variables!) *)
          val let_bindings = Variable.binds_of initial_ctxt |> Vartab.dest
          val state = fold (fn (name,(_,t)) => Proof.map_context (Variable.bind_term (name,rename_fixed t))) let_bindings state
          (* let ?wlog_goal = `goal` *)
          val state = Proof.map_context (Variable.bind_term (("wlog_goal",0), rename_fixed goal)) state
          (* assume A1: \<open>A1\<close> and \<dots> and An: \<open>An\<close> *)
          val state = fold (fn (name,assm) => fn state => 
                        Proof.assume [] [] [((Binding.name name,[]), map (fn t => (rename_fixed (Thm.prop_of t),[])) assm)] state) assms state
          (* TODO: define fact "wlog.assms" to contain all these assumptions *)
          (* Detect all facts that were already proven in this proof and that are now lost.
             (By comparing with the facts in `initial_ctxt`.) *)
          val facts = Proof_Context.facts_of initial_ctxt
          val lost_facts = Facts.dest_static false [Proof_Context.facts_of (Proof.context_of state)] facts
                  |> filter (fn (name,_) => name <> "local.this")
          (* Reintroduce those facts in the present proof block.
             (With added name prefix "wlog".)
             Those facts may depend on hypotheses that are not valid in the present proof block.
             Therefore they are processed using `translate_thm` that gets rid of them.
             (Either discharges them with local facts or makes them into premises.) *)
          val state = Proof.note_thmss (map (fn (name,thms) => ((binding_within wlog_recovered_facts_prefix pos name, []),
                        [(map (translate_thm (Proof.context_of state) fixes fixed) thms, [])])) lost_facts) state
          (* TODO: Print some info to the user about these recovered facts. *)
          (* assume new_assmname: \<open>newassm\<close> *)
          val state = Proof.assume [] [] [((newassm_name,[]),[(rename_fixed newassm,[])])] state (* Should be last in order to override "this" *)
      in state end

      (* have \<open>G\<close> if negation: \<open>\<not> newassm\<close>.
         After this, the user can write their proof, and then control flow continues in `after_qed` above. *)
      val (_,state) = Proof.have true NONE after_qed [] 
             [((Binding.make ("negation", pos),[]), [(negated_newassm, [])])]
             [((Binding.empty,[]), [(goal,[])])] int state
  in state end

(* See `fun wlog` above for documentation-comments.
   This is the corresponding Isar-command (i.e., includes parsing of strings etc.). *)
fun wlog_cmd (pos: Position.T)
             ((bind,stmt) : Binding.binding * string)
             (goal: string)
             (fixes : binding list)
             (assms : (Facts.ref * Token.src list) list)
             int state =
  let val ctxt = Proof.context_of state
      val stmt = Syntax.read_prop ctxt stmt                                 
      val assms' = map (fn (fact,_) => (Facts.ref_name fact, Proof_Context.get_fact ctxt fact)) assms
      val goal' = Syntax.read_prop ctxt goal
      val constr = Variable.constraints_of ctxt |> #1
      val fixes' = map (fn b => let val internal = Variable.lookup_fixed ctxt (Binding.name_of b) |> Option.valOf
                                    val T = Vartab.lookup constr (internal,~1) |> Option.valOf
                                in (b,internal,T) end) fixes
  in wlog pos (bind,stmt) goal' fixes' assms' int state end                 

(* Parser for the Isar-command "wlog". *)
val wlog_parser = (Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty -- Parse.prop) -- 
                  (Scan.optional (@{keyword "goal"} |-- Parse.prop) "?thesis") --
                  (Scan.optional (@{keyword "generalizing"} |-- Scan.repeat Parse.binding) []) --
                  (Scan.optional (@{keyword "keeping"} |-- Parse.thms1) [])
                  |> Parse.position

(* Declare the Isar-command "wlog", to essentially invoke the function `wlog` defined above. *)
val _ =
  Outer_Syntax.command @{command_keyword wlog} "Adds an assumption that holds without loss of generality"
    (wlog_parser >> (fn ((((stmt,goal),fixes),assms),pos) => Toplevel.proof' (wlog_cmd pos stmt goal fixes assms)));

end
