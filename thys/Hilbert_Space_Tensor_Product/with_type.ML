structure With_Type : sig 
type with_type_info = {
  class: class,
  rep_class_data: string,
  rep_class_data_thm: thm option, (* Of the form \<open>rep_class_axioms = (const,const)\<close> *)
  with_type_compat_rel: thm, (* with_type_compat_rel (fst rep_class_data) S (snd rep_class_data)
                                The two occurrences of rep_class_data must have different ?'abs *)
  transfer: thm option (* bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd rep_class_data r ===> (\<longleftrightarrow>)) (fst rep_class_data (Collect (Domainp r))) class.class *)
                       (* The two occurrence of rep_class_data must have different ?'abs *)
}

val add_with_type_info_global : with_type_info -> theory -> theory
val add_with_type_info_generic : with_type_info -> Context.generic -> Context.generic

val morphism : Morphism.morphism -> with_type_info -> with_type_info

val with_type_cancel : Proof.context -> thm -> thm

val with_type_parse_translation : Proof.context -> term list -> term

(* Debug only *)
val get_all_type_info : Proof.context -> { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table }

end = struct

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
  type T = { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table }
  val empty = { by_class = Symtab.empty, by_const = Symtab.empty }
  fun merge ({by_class,by_const}, {by_class=by_class',by_const=by_const'}) =
    {by_class = Symtab.merge (K true) (by_class, by_class'),
     by_const = Symtab.merge (K true) (by_const, by_const') }
)

fun check_with_type_info _ _ = ()

fun add_with_type_info_generic data context = (check_with_type_info context data;
  With_Type_Data.map (fn {by_class,by_const} => 
    {by_class = Symtab.update (#class data, data) by_class,
     by_const = Symtab.update (#rep_class_data data, data) by_const}) context
)
val add_with_type_info_global = Context.theory_map o add_with_type_info_generic

fun get_with_type_info_by_const_generic context const = 
  Symtab.lookup (With_Type_Data.get context |> #by_const) const
val get_with_type_info_by_const = get_with_type_info_by_const_generic o Context.Proof

fun get_with_type_info_by_class_generic context class = 
  Symtab.lookup (With_Type_Data.get context |> #by_class) class
val get_with_type_info_by_class = get_with_type_info_by_class_generic o Context.Proof

fun get_all_type_info ctxt = With_Type_Data.get (Context.Proof ctxt)

fun with_type_cancel ctxt thm = let
  val (const, abs_type) = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type _ _ abs _\<close> $ Const(const,_) $ _ $ _) => (const,abs)
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type constant ...)", [t])
  
  val abs_type_name = case abs_type of
    TVar (n,_) => n
    | _ => raise TYPE ("with_type_cancel: abstract type must be a type variable (?'something)", [abs_type], [Thm.prop_of thm])
  
  val info = get_with_type_info_by_const ctxt const |> the
  
  (* "with_type CR ?Sp ?P \<Longrightarrow>
      \<exists>Rep Abs. type_definition Rep Abs (fst ?Sp) \<Longrightarrow> \<exists>x. class.name x" *)
  (* May be NONE *)
  val with_type_class_axioms = case #transfer info of SOME transfer => 
        (@{thm with_type_class_axioms} OF [transfer, #with_type_compat_rel info])
        |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd |> SOME
    | NONE => NONE
  
  (* class.name (\<dots> using ?'abs::type) \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  (* class.name part may be absent for some type classes *)
  val unoverloaded = Unoverload_Type.unoverload_type (Context.Proof ctxt) [abs_type_name] thm

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> \<exists>x::?'abs_params2. class.name x *)
  (* May be NONE *)
  val ex_class = Option.map (fn th => th OF [thm]) with_type_class_axioms

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> class.name (SOME \<dots>) *)
  (* May be NONE *)
  val class_some = Option.map (fn thm => @{thm someI_ex} OF [thm]) ex_class
  
  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  val unoverloaded' = case class_some of SOME thm => unoverloaded OF [thm] | NONE => unoverloaded
  
  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) [TWICE!] \<Longrightarrow> P *)
  val no_with_type = @{thm with_type_prepare_cancel} OF [unoverloaded']
  
  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> P *)
  val no_repetition = Tactic.distinct_subgoals_tac no_with_type |> Seq.hd

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
    Const ("_ofsort", _) $ Free (n, _) $ Free _ =>
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

end
