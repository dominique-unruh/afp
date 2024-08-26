structure Generalize_Constants : sig

type options = {
  constant: string,
  typ: typ,
  free: string
}

val generalize_constant_term : options -> term -> term
val generalize_constant_thm : options -> thm -> thm


end = struct

type options = {
  constant: string,
  typ: typ,
  free: string
}

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

fun safety_check thy options = let
  val axioms = Thm.all_axioms_of thy
  val const_name = #constant options
  fun find_occurrences occur (t $ u) = find_occurrences (find_occurrences occur u) t
    | find_occurrences occur (Abs(_,_,t)) = find_occurrences occur t
    | find_occurrences occur (Const(name,T)) = if name = const_name then T :: occur else occur
    | find_occurrences occur _ = occur
  fun check_axiom (name,thm) = let
  (* TODO safety checks *)
    (* val _ = writeln name *)
    val occurrences = find_occurrences [] (Thm.prop_of thm)
    val occurrences = sort_distinct Term_Ord.typ_ord occurrences
    val _ = app (fn t => (\<^print> (name,t); ())) occurrences
  in () end
  val _ = List.app check_axiom axioms
in () end

val (_, generalize_constants_oracle) =
  Theory.setup_result (Thm.add_oracle (Binding.make ("generalize_constants", \<^here>), I));

fun generalize_constant_thm (options: options) thm = let
  val thy = Thm.theory_of_thm thm
  val _ = safety_check thy options
  val orig_prop_ct = Thm.cprop_of thm
  val new_prop = generalize_constant_term options (Thm.term_of orig_prop_ct)
  val new_prop_ct = Thm.global_cterm_of thy new_prop
  val implication_ct = Thm.apply (Thm.apply \<^cterm>\<open>Pure.imp\<close> orig_prop_ct) new_prop_ct
  val implication_thm = generalize_constants_oracle implication_ct
  val thm' = Thm.elim_implies thm implication_thm
in thm' end

end