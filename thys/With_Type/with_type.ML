structure With_Type : sig 
type with_type_info = {
  class: class,
  rep_class: string,
  rep_rel: string,
  (* rep_class_data_thm: thm option, (* Of the form \<open>rep_class_axioms = (const,const)\<close> *) *)
  with_type_compat_rel: thm, (* with_type_compat_rel rep_class S rep_rel;
                                rep_class/rep_rel must have different ?'abs *)
  transfer: thm option (* bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (rep_rel r ===> (\<longleftrightarrow>)) (rep_class (Collect (Domainp r))) class.class *)
                       (* rep_class/rep_rel must have different ?'abs *)
                       (* class.class is the class-predicate-constant (e.g. semigroup_add.class), possibly uncurried (e.g. \<lambda>(x,y,z). const x y z) *)
}

val add_with_type_info_global : with_type_info -> theory -> theory
(* TODO: check whether the theorems are correct *)

val add_with_type_info_generic : with_type_info -> Context.generic -> Context.generic

val morphism : Morphism.morphism -> with_type_info -> with_type_info

val with_type_cancel : Proof.context -> thm -> thm

val with_type_parse_translation : Proof.context -> term list -> term

val with_type_print_translation : Proof.context -> term list -> term

val get_with_type_info_by_class : Proof.context -> class -> with_type_info option

(* Debug only *)
val get_all_type_info : Proof.context -> {
  by_class: with_type_info Symtab.table,
  by_const: with_type_info Symtab.table }

end = struct

val protect_conv = Conv.rewr_conv (@{thm Pure.prop_def[symmetric]})
val unprotect_conv = Conv.rewr_conv (@{thm Pure.prop_def})
fun protect_thm thm = Conv.fconv_rule protect_conv thm 
fun unprotect_thm thm = Conv.fconv_rule unprotect_conv thm 

fun unify_prems_12 thm = (@{thm distinct_prems_rl_protected} OF [protect_thm thm]) |> unprotect_thm

type with_type_info = {
  class: class,
  rep_class: string,
  rep_rel: string,
  (* rep_class_data_thm: thm option, *)
  with_type_compat_rel: thm, 
  transfer: thm option
}

fun morphism m ({class, rep_class, rep_rel, with_type_compat_rel, transfer} : with_type_info) : with_type_info =
  {class=class, rep_class=rep_class, rep_rel=rep_rel, 
    (* rep_class_data_thm = Option.map (Morphism.thm m) rep_class_data_thm, *)
    with_type_compat_rel = Morphism.thm m with_type_compat_rel,
    transfer = Option.map (Morphism.thm m) transfer}

structure With_Type_Data = Generic_Data (
  type T = { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table }
  val empty = { by_class = Symtab.empty, by_const = Symtab.empty }
  fun merge ({by_class, by_const}, {by_class=by_class', by_const=by_const'}) =
    {by_class = Symtab.merge (K true) (by_class, by_class'),
     by_const = Symtab.merge (K true) (by_const, by_const')}
)

fun check_with_type_info _ _ = ()

fun add_with_type_info_generic data context = (check_with_type_info context data;
  With_Type_Data.map (fn {by_class, by_const} => 
    {by_class = Symtab.update (#class data, data) by_class,
     by_const = Symtab.update (#rep_class data, data) by_const}) context
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
  val chyps = Thm.chyps_of thm
  val hyps = map Thm.term_of chyps
  val tvars_hyps = fold Term.add_tvars hyps [] |> map fst
  val bad_tvars = inter (op=) (distinct (op=) tvars_hyps) tvars
  val _ = null bad_tvars orelse
          raise THM ("unoverload_type_local: context assumptions contain type variables " ^
                String.concatWith ", " (map string_of_indexname bad_tvars) ^
                " that we are trying to unoverload", 0, [thm])
  val thm_no_assm = fold Thm.implies_intr chyps thm
  val (tfree_subst, thm_no_tfree) = Thm.varifyT_global' TFrees.empty thm_no_assm 
  val thm_unover = Unoverload_Type.unoverload_type (Context.Proof ctxt) tvars thm_no_tfree
  val skip_nprems = Thm.nprems_of thm_unover - Thm.nprems_of thm_no_tfree
  val _ = skip_nprems >= 0 orelse error ("unoverload_type_local: skip_nprems is negative")
  val _ = forall (fn ((_,s1),(_,s2)) => s1 = s2) tfree_subst orelse
            error ("unoverload_type_local: Thm.varifyT_global' returned inconsistent sorts")
  val tfree_subst' = map (fn ((n,s),nis) => (nis, TFree (n,s) |> Thm.ctyp_of ctxt)) tfree_subst |> TVars.make
  val thm_tfree = Thm.instantiate (tfree_subst', Vars.empty) thm_unover
  val all_prems = Assumption.all_prems_of ctxt
  fun remove_hyp i thm : thm = case Seq.pull (solve_tac ctxt all_prems (i+skip_nprems+1) thm) of
    NONE => raise THM ("unoverload_type_local: solving assumption failed", i+skip_nprems+1, thm :: all_prems)
  | SOME (thm,_) => thm
  val thm''' = fold remove_hyp (hyps |> map_index fst |> rev) thm_tfree
  in thm''' end

fun with_type_cancel ctxt thm = let
  fun debug (pos : Position.T) m = if true then tracing (Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) "\<^here>" ^ " " ^ m ()) else ()

  val _ = debug\<^here> (fn _ => "thm = " ^ \<^make_string> thm)
  
  (* like thm, but with 'abs replaced by ?'abs, unless it's already a schematic variable *)
  val thm = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type _ _ abs _\<close> $ _ $ _ $ _) =>
         (case abs of
            TVar _ => thm
          | TFree (n,T) => Thm.generalize (Names.make1_set n, Names.empty) (Thm.maxidx_of thm + 1) thm
          | _ => raise TYPE ("with_type_cancel: bound type must be a type variable", [abs], [Thm.prop_of thm]))
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type ...)", [t])
  val _ = debug\<^here> (fn _ => "thm (after generalizing) = " ^ \<^make_string> thm)

  val (const_class, const_rel, rep_type, abs_type, P) = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type rep _ abs _\<close>
                            $ (\<^Const_>\<open>Pair _ _\<close> $ Const(const_class, _) $ Const(const_rel, _))
                            $ _ $ P)
             => (const_class, const_rel, rep, abs, P)
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type (constant,constant) ...)", [t])
  val _ = debug\<^here> (fn _ => "const_class = " ^ \<^make_string> const_class ^ "; const_rel = " ^ \<^make_string> const_rel ^ "; abs_type = " ^ \<^make_string> abs_type ^ "; P = " ^ \<^make_string> P)

  val _ = let val P' = betapplys (P, [Free("Rep", abs_type --> rep_type), Free("Abs", rep_type --> abs_type)])  in
            exists_type (exists_subtype (fn T => T=abs_type)) P'
              andalso raise TYPE ("with_type_cancel: body contains bound type", [abs_type], [P']) end

  val abs_type_name = case abs_type of
    TVar (n,_) => n
    | _ => raise TYPE ("with_type_cancel: abstract type must be a type variable (?'something)", [abs_type], [Thm.prop_of thm])
  val _ = debug\<^here> (fn _ => "abs_type_name = " ^ \<^make_string> abs_type_name)
  
  val info = get_with_type_info_by_const ctxt const_class |> the
  val _ = #rep_rel info = const_rel orelse raise TERM ("with_type_cancel: expected relator " ^ #rep_rel info ^ " instead of " ^ const_rel, [Thm.prop_of thm])

  (* "with_type (C,R) (?S,?p) ?P \<Longrightarrow>
      \<exists>Rep Abs. type_definition Rep Abs ?S \<Longrightarrow> \<exists>x. class.name' x" *)
  (* Here class.name' is class.name, possibly uncurried (e.g., \<lambda>(x,y,z) class.name x y z) *)
  (* May be NONE *)
  val with_type_class_axioms = case #transfer info of SOME transfer => 
        (@{thm with_type_class_axioms} OF [transfer, #with_type_compat_rel info])
        |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd |> SOME
    | NONE => NONE
  val _ = debug\<^here> (fn _ => "with_type_class_axioms = " ^ \<^make_string> with_type_class_axioms)
 
  (* class.name (\<dots> using ?'abs::type) \<Longrightarrow> with_type (C,R) (S,p) (\<lambda>_ _. P) *)
  (* class.name part may be absent for some type classes *)
  val unoverloaded = unoverload_type_local ctxt [abs_type_name] thm
  val _ = debug\<^here> (fn _ => "unoverloaded = " ^ \<^make_string> unoverloaded)
  val _ = case Thm.nprems_of unoverloaded of
            0 => is_none with_type_class_axioms orelse raise THM ("with_type_cancel: unoverloading produced no `class.name` premise, but #transfer is not NONE", 0, [unoverloaded])
          | 1 => is_none with_type_class_axioms andalso raise THM ("with_type_cancel: unoverloading produced a `class.name` premise, but #transfer is NONE", 0, [unoverloaded])

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> \<exists>x::?'abs_params2. class.name' x *)
  (* May be NONE *)
  val ex_class = Option.map (fn th => th OF [thm]) with_type_class_axioms
  val _ = debug\<^here> (fn _ => "ex_class = " ^ \<^make_string> ex_class)

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> class.name' (SOME \<dots>) *)
  (* May be NONE *)
  val class_some = Option.map (fn thm => @{thm someI_ex} OF [thm]) ex_class
  val _ = debug\<^here> (fn _ => "class_some = " ^ \<^make_string> class_some)

  open Conv
  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> class.name \<dots> \<dots> \<dots> *)
  (* May be NONE *)
  val uncurry_conv = repeat_conv (rewr_conv @{thm case_prod_beta[THEN eq_reflection]}) |> HOLogic.Trueprop_conv |> implies_concl_conv
  val class_some_uncurried = Option.map (fconv_rule uncurry_conv) class_some
  val _ = debug\<^here> (fn _ => "class_some_uncurried = " ^ \<^make_string> class_some_uncurried)

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  val unoverloaded' = case class_some_uncurried of SOME thm => unoverloaded OF [thm] | NONE => unoverloaded
  val _ = debug\<^here> (fn _ => "unoverloaded' = " ^ \<^make_string> unoverloaded')

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S [POSSIBLY TWICE!] \<Longrightarrow> P *)
  val no_with_type = @{thm with_type_prepare_cancel} OF [unoverloaded']
  val _ = debug\<^here> (fn _ => "no_with_type = " ^ \<^make_string> no_with_type)

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> P *)
  val no_repetition = 
    if Thm.nprems_of no_with_type = 2 then unify_prems_12 no_with_type else no_with_type
  val _ = debug\<^here> (fn _ => "no_repetition = " ^ \<^make_string> no_repetition)

  val _ = Thm.nprems_of no_repetition = 1 orelse raise THM ("with_type_cancel: could not remove duplicate premise", 0, [no_repetition])

  (* S \<noteq> {} \<Longrightarrow> P *)
  val removed_abs_type = Local_Typedef.cancel_type_definition no_repetition
  val _ = debug\<^here> (fn _ => "removed_abs_type = " ^ \<^make_string> removed_abs_type)
  
  (* S \<noteq> {} *)
  val non_empty = @{thm with_type_nonempty} OF [thm]
  val _ = debug\<^here> (fn _ => "non_empty = " ^ \<^make_string> non_empty)
  val final_thm = removed_abs_type OF [non_empty]
  val _ = debug\<^here> (fn _ => "final_thm = " ^ \<^make_string> final_thm)
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
  (* The "Config.put show_sorts true" is necessary because otherwise "term_of_typ" ignores sorts. *)
  val prop = Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ prop $ Syntax_Phases.term_of_typ (Config.put show_sorts true ctxt) propT
  in Const(\<^const_name>\<open>with_type\<close>, dummyT) $ HOLogic.mk_prod (Const(#rep_class info, dummyT), Const(#rep_rel info, dummyT)) $ 
        (Const(\<^const_name>\<open>Pair\<close>, dummyT) $ carrier $ ops) $ prop end

  | with_type_parse_translation ctxt [typ_term, carrier, prop] = with_type_parse_translation ctxt [typ_term, carrier, \<^term>\<open>()\<close>, prop]
  | with_type_parse_translation _ Ts = raise TERM ("with_type_parse_translation: called with wrong number of arguments", Ts)

fun with_type_print_translation ctxt args = raise TERM ("with_type_print_translation: nyi", [])


end
