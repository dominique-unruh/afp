structure With_Type : sig 
type with_type_info = {
  class: class,
  rep_class_data: string,
  rep_class_data_thm: thm option, (* Of the form \<open>rep_class_axioms = (const,const)\<close> *)
  with_type_compat_rel: thm, (* with_type_compat_rel (fst rep_class_data) S (snd rep_class_data)
                                The two occurrences of rep_class_data must have different ?'abs *)
  transfer: thm option (* bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd rep_class_data r ===> (\<longleftrightarrow>)) (fst rep_class_data (Collect (Domainp r))) class.class *)
                       (* The two occurrences of rep_class_data must have different ?'abs *)
                       (* class.class is the class-predicate-constant (e.g. semigroup_add.class), possibly curried (e.g. \<lambda>(x,y,z). const x y z) *)
}

val add_with_type_info_global : with_type_info -> theory -> theory
val add_with_type_info_generic : with_type_info -> Context.generic -> Context.generic

val morphism : Morphism.morphism -> with_type_info -> with_type_info

val with_type_cancel : Proof.context -> thm -> thm

val with_type_parse_translation : Proof.context -> term list -> term

val add_relator_global : string -> (Proof.context -> (typ -> term) -> typ -> term) -> theory -> theory

val get_relator : Proof.context -> string -> (Proof.context -> (typ -> term) -> typ -> term) option

val get_with_type_info_by_class : Proof.context -> class -> with_type_info option

(* Debug only *)
val get_all_type_info : Proof.context -> { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table, relators: (Proof.context -> (typ -> term) -> typ -> term) Symtab.table }

end = struct

val protect_conv = Conv.rewr_conv (@{thm Pure.prop_def[symmetric]})
val unprotect_conv = Conv.rewr_conv (@{thm Pure.prop_def})
fun protect_thm thm = Conv.fconv_rule protect_conv thm 
fun unprotect_thm thm = Conv.fconv_rule unprotect_conv thm 

fun unify_prems_12 thm = (@{thm distinct_prems_rl_protected} OF [protect_thm thm]) |> unprotect_thm

type with_type_info = {
  class: class,
  rep_class_data: string,
  rep_class_data_thm: thm option,
  with_type_compat_rel: thm, 
  transfer: thm option
}

fun morphism m ({class, rep_class_data, rep_class_data_thm, with_type_compat_rel, transfer} : with_type_info) : with_type_info =
  {class=class, rep_class_data=rep_class_data, 
    rep_class_data_thm = Option.map (Morphism.thm m) rep_class_data_thm,
    with_type_compat_rel = Morphism.thm m with_type_compat_rel,
    transfer = Option.map (Morphism.thm m) transfer}

structure With_Type_Data = Generic_Data (
  type T = { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table,
             relators: (Proof.context -> (typ -> term) -> typ -> term) Symtab.table }
  val empty = { by_class = Symtab.empty, by_const = Symtab.empty, relators = Symtab.empty }
  fun merge ({by_class, by_const, relators}, {by_class=by_class', by_const=by_const', relators=relators'}) =
    {by_class = Symtab.merge (K true) (by_class, by_class'),
     by_const = Symtab.merge (K true) (by_const, by_const'),
     relators = Symtab.merge (K true) (relators, relators')}
)

fun check_with_type_info _ _ = ()

fun add_with_type_info_generic data context = (check_with_type_info context data;
  With_Type_Data.map (fn {by_class, by_const, relators} => 
    {by_class = Symtab.update (#class data, data) by_class,
     by_const = Symtab.update (#rep_class_data data, data) by_const,
     relators = relators}) context
)
val add_with_type_info_global = Context.theory_map o add_with_type_info_generic

fun get_with_type_info_by_const_generic context const = 
  Symtab.lookup (With_Type_Data.get context |> #by_const) const
val get_with_type_info_by_const = get_with_type_info_by_const_generic o Context.Proof

fun get_with_type_info_by_class_generic context class = 
  Symtab.lookup (With_Type_Data.get context |> #by_class) class
val get_with_type_info_by_class = get_with_type_info_by_class_generic o Context.Proof

fun get_all_type_info ctxt = With_Type_Data.get (Context.Proof ctxt)

(* Like Unoverload_Type.unoverload_type, but works if the theorem contains assumptions from the current context. *)
fun unoverload_type_local ctxt tvars thm = let
  val hyps = Assumption.all_assms_of ctxt |> map Thm.term_of
  val tvars_hyps = fold Term.add_tvars hyps [] |> map fst
  val bad_tvars = inter (op=) (distinct (op=) tvars_hyps) tvars
  val _ = null bad_tvars orelse
          raise THM ("unoverload_type_local: context assumptions contain type variables " ^
                String.concatWith ", " (map string_of_indexname bad_tvars) ^
                " that we are trying to unoverload", 0, [thm])
  val global_ctxt = Proof_Context.init_global (Proof_Context.theory_of ctxt)
  val thm' = Proof_Context.export ctxt global_ctxt [thm] |> hd
  val thm'' = Unoverload_Type.unoverload_type (Context.Proof ctxt) tvars thm'
  val skip_nprems = Thm.nprems_of thm'' - Thm.nprems_of thm'
  val _ = skip_nprems >= 0 orelse error ("unoverload_type_local: skip_nprems is negative")
  fun remove_hyp (i,hyp) thm : thm = case Seq.pull (solve_tac ctxt [hyp] (i+skip_nprems+1) thm) of
    NONE => raise THM ("unoverload_type_local: solving assumption failed", i+skip_nprems+1, [thm,hyp])
  | SOME (thm,_) => thm
  val thm''' = fold remove_hyp (Assumption.all_prems_of ctxt |> map_index I |> rev) thm''
  in thm''' end

fun with_type_cancel ctxt thm = let
  val (const, abs_type) = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type _ _ abs _\<close> $ Const(const,_) $ _ $ _) => (const,abs)
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type constant ...)", [t])
  
  val abs_type_name = case abs_type of
    TVar (n,_) => n
    | _ => raise TYPE ("with_type_cancel: abstract type must be a type variable (?'something)", [abs_type], [Thm.prop_of thm])
  
  val info = get_with_type_info_by_const ctxt const |> the
  
  (* "with_type CR ?Sp ?P \<Longrightarrow>
      \<exists>Rep Abs. type_definition Rep Abs (fst ?Sp) \<Longrightarrow> \<exists>x. class.name' x" *)
  (* Here class.name' is class.name, possibly uncurried (e.g., \<lambda>(x,y,z) class.name' x y z) *)
  (* May be NONE *)
  val with_type_class_axioms = case #transfer info of SOME transfer => 
        (@{thm with_type_class_axioms} OF [transfer, #with_type_compat_rel info])
        |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd |> SOME
    | NONE => NONE
  
  (* class.name (\<dots> using ?'abs::type) \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  (* class.name part may be absent for some type classes *)
  val unoverloaded = unoverload_type_local ctxt [abs_type_name] thm

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> \<exists>x::?'abs_params2. class.name' x *)
  (* May be NONE *)
  val ex_class = Option.map (fn th => th OF [thm]) with_type_class_axioms

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> class.name' (SOME \<dots>) *)
  (* May be NONE *)
  val class_some = Option.map (fn thm => @{thm someI_ex} OF [thm]) ex_class

  open Conv
  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> class.name \<dots> \<dots> \<dots> *)
  (* May be NONE *)
  val uncurry_conv = repeat_conv (rewr_conv @{thm case_prod_beta[THEN eq_reflection]}) |> HOLogic.Trueprop_conv |> implies_concl_conv
  val class_some_uncurried = Option.map (fconv_rule uncurry_conv) class_some

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  val unoverloaded' = case class_some_uncurried of SOME thm => unoverloaded OF [thm] | NONE => unoverloaded
  
  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) [POSSIBLY TWICE!] \<Longrightarrow> P *)
  val no_with_type = @{thm with_type_prepare_cancel} OF [unoverloaded']
  
  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> P *)
  val no_repetition = 
    if Thm.nprems_of no_with_type = 2 then unify_prems_12 no_with_type else no_with_type

  val _ = Thm.nprems_of no_repetition = 1 orelse raise THM ("with_type_cancel: could not remove duplicate premise", 0, [no_repetition])

  (* fst Sp \<noteq> {} \<Longrightarrow> P *)
  val removed_abs_type = Local_Typedef.cancel_type_definition no_repetition
  
  (* fst Sp \<noteq> {} *)
  val non_empty = @{thm with_type_nonempty} OF [thm]
  val final_thm = removed_abs_type OF [non_empty]
  in
  final_thm
  end

fun with_type_parse_translation ctxt [typ_term, carrier, ops, prop] = let
  val (typname_raw,sort) = case typ_term of 
    Const ("_ofsort", _) $ Free (_, _) $ Free _ =>
      raise TERM ("with_type_parse_translation: abstract type must be annotated with a type class", [typ_term])
    | Const ("_ofsort", _) $ (Const ("_ofsort", _) $ Free (n, _) $ Free _) $ sort => (n, sort)
    | _ => (\<^print> typ_term;
         raise TERM ("parse_transtation _with_type: first argument must be a type variable", [typ_term]))
  val typname = if typname_raw = "" then raise TERM ("parse_transtation _with_type: empty type variable name", [typ_term])
      else if not (String.isPrefix "'" typname_raw) then raise TERM ("parse_transtation _with_type: type variable name does not start with '", [typ_term])
      else String.extract (typname_raw,1,NONE)
  val class = case Syntax_Phases.decode_sort sort of [class] => class
                        | sort => error ("with_type_parse_translation: abstract type must be annotated with a single class, not " ^ Syntax.string_of_sort ctxt sort)
  val info = case get_with_type_info_by_class ctxt class of SOME info => info
              | NONE => error ("with_type_parse_translation: class "^ Syntax.string_of_sort ctxt [class] ^" not registered for use with \<forall>\<^sub>\<tau>")
  val typ = TFree("'" ^ typname, [class])
  val rep = Free("rep_" ^ typname, dummyT)
  val abs = Free("abs_" ^ typname, dummyT)
  val prop = Syntax_Trans.abs_tr [rep, Syntax_Trans.abs_tr [abs, prop]]
  val propT = (typ --> dummyT) --> (dummyT --> typ) --> HOLogic.boolT
  val prop = Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ prop $ Syntax_Phases.term_of_typ ctxt propT
  in Const(\<^const_name>\<open>with_type\<close>, dummyT) $ Const(#rep_class_data info, dummyT) $ 
        (Const(\<^const_name>\<open>Pair\<close>, dummyT) $ carrier $ ops) $ prop end

  | with_type_parse_translation ctxt [typ_term, carrier, prop] = with_type_parse_translation ctxt [typ_term, carrier, \<^term>\<open>()\<close>, prop]
  | with_type_parse_translation _ Ts = raise TERM ("with_type_parse_translation: called with wrong number of arguments", Ts)

fun map_relators_generic f = With_Type_Data.map (fn {by_class, by_const, relators} => 
    {by_class = by_class, by_const = by_const, relators = f relators})

val get_relators_generic = With_Type_Data.get #> #relators

fun add_relator_generic typ_name f = map_relators_generic (Symtab.insert (K false) (typ_name, f))

fun add_relator_global typ_name f = Context.theory_map (add_relator_generic typ_name f)

fun get_relator_generic context typ_name = Symtab.lookup (get_relators_generic context) typ_name
fun get_relator ctxt = get_relator_generic (Context.Proof ctxt)

end
