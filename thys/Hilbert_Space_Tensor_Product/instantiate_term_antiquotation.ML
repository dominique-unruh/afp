structure Instantiate_Term_Antiquotation = struct

(* Reads term.
- unspecified types are made into tvars
- vars and tvars are allowed (and stay what they are) 
- Edge case: if there are explicitly specified tvars with index \<ge> 1, and no unspecified types, then things are muddled up
*)
fun read_term_schematic' ctxt str = let
  val t = Syntax.parse_term ctxt str
  val tfrees = Term.add_tfrees t [] |> map fst |> filter (String.isPrefix "'")
  val t = Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t
  val idx = Term.maxidx_of_term t + 1
  fun map_tfree (T as TFree(n,s)) = if List.exists (fn n' => n=n') tfrees then T else TVar((n,idx),s)
    | map_tfree T = T
  val t = map_types (map_atyps map_tfree) t
in t end

fun antiquotation_Term range src ctxt = let
  val (source,ctxt) = Token.syntax (Scan.lift Parse.embedded_input) src ctxt
  val symbols = source |> Input.source_explode
  fun symbol_pos_list_to_string syms = 
      Input.source true (Symbol_Pos.implode syms) (Symbol_Pos.range syms)
      |> Syntax.implode_input
  fun replace [] map _ result = (map, rev result |> symbol_pos_list_to_string)
    | replace (sym::syms) map counter result =
        if Symbol_Pos.symbol sym = Symbol.open_
        then let val (cartouche,rest) = Symbol_Pos.scan_cartouche "XXXXX" (sym::syms)
                 val varname = "\<XX>" ^ string_of_int counter ^ "\<YY>"
                 val ml = ML_Lex.read_symbols (Symbol_Pos.cartouche_content cartouche)
                 val map = Symtab.insert (K true) (varname, ml) map
                 val var = "?" ^ varname ^ " " |> Symbol_Pos.explode0
                 val pad_length = length cartouche - length var
                 val _ = pad_length >= 0 orelse 
                            error ("ML fragment " ^ symbol_pos_list_to_string cartouche ^ Position.here (snd sym) ^ " too short. Please pad (e.g., with spaces)")
                 val var = var @ replicate pad_length (" ", Position.none)
             in replace rest map (counter+1) (rev var @ result) end
        else replace syms map counter (sym::result)
  val (ml_map,str) = replace symbols Symtab.empty 0 []
  val term = read_term_schematic' ctxt str
  val ml_term = ML_Syntax.atomic (ML_Syntax.print_term term)
  val (map_antiquot,ctxt) = fold_map (fn (name,ml) => fn ctxt => let val (decl,ctxt) = ML_Context.expand_antiquotes ml ctxt in ((name,decl),ctxt) end)
                              (Symtab.dest ml_map) ctxt
  fun decl ctxt = let
    val map_antiquot' = map_antiquot |> map (fn (name,decl) => (name, decl ctxt))
    val ml_subst = ML_Syntax.print_list  
        (fn (name,(_,inline)) => ML_Syntax.print_pair (ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_int) ML_Lex.flatten ((name,0),inline))
        map_antiquot'
(* TODO: we convert the term to cterm each time. Should be done once using the env *)
(* TODO: use own function for instantiating more quickly? (By preprocessing which vars have which types and hence instantiating without having to go through the whole thm-instantiate stuff) *)
    val ml_code = "(fn inst => fn t => fn ctxt => Thm.reflexive (Thm.cterm_of ctxt t) |> Drule.infer_instantiate ctxt (List.map (Library.apsnd (Thm.cterm_of ctxt)) inst) |> Thm.rhs_of |> Thm.term_of) " 
        (* ^ ML_Context.struct_name ctxt ^ ".ML_context " -- Cannot use this context because the terms we put in must be checked with a current context *) ^ ml_subst ^ " " ^ ml_term
        |> ML_Syntax.atomic |> ML_Lex.tokenize_range range
    val env = map_antiquot' |> map (fn (_,(env,_)) => env) |> flat
    in (env, ml_code) end
in (decl, ctxt) end


end