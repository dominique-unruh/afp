theory With_Type_Inst_HOL
  imports With_Type
begin

subsection \<open>Finite\<close>

definition with_type_class_finite :: \<open>('a set \<Rightarrow> unit \<Rightarrow> bool) \<times> (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (unit \<Rightarrow> unit \<Rightarrow> bool))\<close>
  where \<open>with_type_class_finite = (\<lambda>F _. finite F, \<lambda>_. (=))\<close>

lemma finite_transfer'[unfolded case_prod_unfold]:
  includes lifting_syntax
  fixes r :: \<open>'rep\<Rightarrow>'abs\<Rightarrow>bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(snd with_type_class_finite r ===> (\<longleftrightarrow>)) (fst with_type_class_finite (Collect (Domainp r))) (\<lambda>_::unit. class.finite TYPE('abs))\<close>
  unfolding class.finite_def with_type_class_finite_def fst_conv
  by transfer_prover

lemma with_type_compat_rel_finite': \<open>with_type_compat_rel (fst with_type_class_finite) S (snd with_type_class_finite)\<close>
  by (auto simp: with_type_class_finite_def with_type_compat_rel_def)

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>finite\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_finite\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_finite'},
  rep_class_data_thm = NONE,
  transfer = SOME @{thm finite_transfer'}
}
\<close>

subsection \<open>Semigroup, additive\<close>

subsection \<open>XXX\<close>

local_setup \<open>
  define_stuff \<^here> \<^class>\<open>semigroup_add\<close>
\<close>
print_theorems

(* ML \<open>val (relationT, relationR, relationD, relationThm) = get_relation_thm \<^context> \<^class>\<open>semigroup_add\<close>\<close> *)

(* abbreviation \<open>with_type_semigroup_add_class_rel \<equiv> with_type_semigroup_add_class_rel\<close> *)

(* local_setup \<open>local_def \<^binding>\<open>with_type_semigroup_add_class_rel\<close> (Type.legacy_freeze relationR)\<close> *)
(* thm with_type_semigroup_add_class_rel_def *)

(* local_setup \<open>local_note \<^binding>\<open>with_type_semigroup_add_class_has_dom\<close> relationThm\<close> *)

ML \<open>
(* Reads term.
- unspecified types are made into tvars
- vars and tvars are allowed (and stay what they are) 
- Edge case: if there are explicitly specified tvars with index \<ge> 1, and no unspecified types, then things are muddled up
*)
(* fun read_term_schematic' ctxt str = let
  val t = Proof_Context.read_term_pattern ctxt str
  val idx = Term.maxidx_of_term t
  fun map_tvar (T as TVar((n,i),s)) = if i=idx then TFree(n,s) else T
    | map_tvar T = T
  val t' = t |> map_types (map_atyps map_tvar)
in (idx,t' |> Thm.cterm_of ctxt) end *)
\<close>

ML \<open>
fun read_term_schematic' ctxt str = let
  val t = Syntax.parse_term ctxt str
  val tfrees = Term.add_tfrees t [] |> map fst |> filter (String.isPrefix "'")
  val t = Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t
  val idx = Term.maxidx_of_term t + 1
  fun map_tfree (T as TFree(n,s)) = if List.exists (fn n' => n=n') tfrees then T else TVar((n,idx),s)
    | map_tfree T = T
  val t = map_types (map_atyps map_tfree) t
in t end
\<close>

ML Syntax.read_term

declare[[show_types]]

ML \<open>
read_term_schematic' \<^context> "(X, ?X3 :: 'a \<times> 'b \<times> ?'c \<times> ?'b1)"
;;
Proof_Context.read_term_schematic \<^context> "(X, ?X3 :: 'a \<times> 'b \<times> ?'c \<times> ?'b1)"
\<close>


ML \<open>
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
    val ml_code = "(fn ctxt => fn inst => fn t => Thm.reflexive (Thm.cterm_of ctxt t) |> infer_instantiate ctxt (map (apsnd (Thm.cterm_of ctxt)) inst) |> Thm.rhs_of |> Thm.term_of) " 
        ^ ML_Context.struct_name ctxt ^ ".ML_context " ^ ml_subst ^ " " ^ ml_term
        |> ML_Syntax.atomic |> ML_Lex.tokenize_range range
    val env = map_antiquot' |> map (fn (_,(env,_)) => env) |> flat
    in (env, ml_code) end
in (decl, ctxt) end
\<close>

setup \<open>
ML_Context.add_antiquotation \<^binding>\<open>Term\<close> true antiquotation_Term
\<close>

ML \<open>
\<^Term>\<open>(1) + \<open>Free("a",\<^typ>\<open>int\<close>)\<close>\<close>
|> Thm.cterm_of \<^context>
\<close>

ML \<open>
Drule.abs_def
\<close>


ML \<open>
fun create_transfer_thm ctxt class rel_const rel_const_def_thm = let
  val thy = Proof_Context.theory_of ctxt
  val (class_const, _) = get_params_of_class thy class
  val class_const_def_thm = Proof_Context.get_thm ctxt ((class_const |> dest_Const |> fst) ^ "_def") |> Drule.abs_def
  val class_const = subst_TVars [(("'a",0), TFree("'abs",\<^sort>\<open>type\<close>))] class_const
  val goal = \<^Term>\<open>Trueprop ((rel_fun (\<open>rel_const\<close> r) (\<longleftrightarrow>)) ?X \<open>class_const\<close>)\<close>
  val bi_unique = \<^prop>\<open>bi_unique (r :: 'rep \<Rightarrow> 'abs \<Rightarrow> bool)\<close>
  val right_total = \<^prop>\<open>right_total (r :: 'rep \<Rightarrow> 'abs \<Rightarrow> bool)\<close>
  val domain_r = \<^prop>\<open>Domainp (r :: 'rep \<Rightarrow> 'abs \<Rightarrow> bool) = (\<lambda>x. x \<in> S)\<close>
  val _ = goal |> Thm.cterm_of ctxt
  open Conv
  fun tac {context=ctxt, prems=[bi_unique, right_total, domain_r]} =
    Raw_Simplifier.rewrite_goal_tac ctxt [rel_const_def_thm, class_const_def_thm] 1
    THEN 
    Transfer.transfer_prover_tac (ctxt |> Thm.proof_attributes [Transfer.transfer_add] bi_unique |> snd
                                       |> Thm.proof_attributes [Transfer.transfer_add] right_total |> snd
                                       |> Thm.proof_attributes [Transfer.transfer_domain_add] domain_r |> snd) 1
    | tac _ = raise Match (* Should not happen *)
  val thm = Goal.prove ctxt ["r","S"] [bi_unique, right_total, domain_r] goal tac
  val transferred = thm
    |> Thm.concl_of |> HOLogic.dest_Trueprop
    |> dest_comb |> fst |> dest_comb |> snd
    |> lambda (Var(("S",0),HOLogic.mk_setT (TVar(("'rep",0),\<^sort>\<open>type\<close>))))
  in
    (transferred, thm)
  end
;;
val (transferred,thm) = create_transfer_thm \<^context> \<^class>\<open>semigroup_add\<close>
   \<^Const>\<open>with_type_semigroup_add_class_rel \<open>TFree("'rep",\<^sort>\<open>type\<close>)\<close> \<open>TFree("'abs",\<^sort>\<open>type\<close>)\<close>\<close>
   @{thm with_type_semigroup_add_class_rel_def}
\<close>

thm class.semigroup_add_def[abs_def]

ML \<open>
Proof_Context.read_term_pattern \<^context> "(X, ?X :: 'a \<times> 'b \<times> ?'c \<times> ?'b1)"
\<close>


ML \<open>
HOLogic.mk_case_prod \<^term>\<open>(\<lambda>x y z. undefined)\<close>
\<close>


(* schematic_goal with_type_semigroup_add_class_transfer0:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close> 
  assumes [transfer_domain_rule]: \<open>Domainp r = (\<lambda>x. x \<in> S)\<close>
  shows \<open>(with_type_semigroup_add_class_rel r ===> (\<longleftrightarrow>)) ?X (\<lambda>plus. class.semigroup_add plus)\<close>
  unfolding class.semigroup_add_def
  unfolding with_type_semigroup_add_class_rel_def
  by transfer_prover
thm with_type_semigroup_add_class_transfer0[of r S]

ML \<open>
val transferred = @{thm with_type_semigroup_add_class_transfer0} 
  |> Thm.concl_of |> HOLogic.dest_Trueprop
  |> dest_comb |> fst |> dest_comb |> snd
  |> lambda (Var(("S",0),HOLogic.mk_setT (TVar(("'a",0),\<^sort>\<open>type\<close>))))
  (* |> Thm.cterm_of \<^context>  *)
\<close> *)

local_setup \<open>local_def \<^binding>\<open>with_type_semigroup_add_class_pred'\<close> (Type.legacy_freeze transferred) #> snd\<close>
thm with_type_semigroup_add_class_pred'_def

definition \<open>with_type_semigroup_add_class_pred == (\<lambda>S p. with_type_semigroup_add_class_dom S p \<and> with_type_semigroup_add_class_pred' S p)\<close>

definition with_type_semigroup_add_class where
  \<open>with_type_semigroup_add_class \<equiv> (with_type_semigroup_add_class_pred, with_type_semigroup_add_class_rel)\<close>

local_setup \<open>
local_note \<^binding>\<open>with_type_semigroup_add_class_transfer0\<close> thm
\<close>

lemma aux: 
  includes lifting_syntax
  assumes class1_def: \<open>class1 == (class1P, class1R)\<close>
  assumes class2_def: \<open>class2 == (class2P, class2R)\<close>
  assumes class2P_def: \<open>class2P \<equiv> \<lambda>S p. D S p \<and> pred' S p\<close>
  assumes pred'_def: \<open>pred' \<equiv> pred''\<close>
  assumes wthd: \<open>with_type_has_domain class1R D\<close>
  assumes 1: \<open>\<And>S. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> Domainp r = (\<lambda>x. x \<in> S) \<Longrightarrow>
               (class1R r ===> (=)) (pred'' S) class_const\<close>
  assumes r_assms: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(snd class1 r ===> (\<longleftrightarrow>)) (fst class2 (Collect (Domainp r))) class_const\<close>
  unfolding class1_def class2_def fst_conv snd_conv class2P_def pred'_def
  apply (rule with_type_split_aux)
   apply (rule 1)
     apply (rule r_assms)
     apply (rule r_assms)
   apply auto[1]
  using wthd
  by (simp add: r_assms(1) r_assms(2) with_type_has_domain_def)

ML \<open>
val with_type_semigroup_add_class_transfer = 
(@{thm aux} OF @{thms
with_type_semigroup_add_class_def with_type_semigroup_add_class_def
with_type_semigroup_add_class_pred_def with_type_semigroup_add_class_pred'_def
with_type_semigroup_add_class_has_dom}
OF @{thms with_type_semigroup_add_class_transfer0})
|> Thm.eq_assumption 1
|> Thm.eq_assumption 1
|> Thm.eq_assumption 1

\<close>

local_setup \<open>local_note \<^binding>\<open>with_type_semigroup_add_class_transfer\<close> with_type_semigroup_add_class_transfer\<close>

(* lemma with_type_semigroup_add_class_transfer:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes \<open>bi_unique r\<close> \<open>right_total r\<close> 
  defines \<open>(C1 :: (('rep set \<Rightarrow> ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<Rightarrow> bool) \<times> _)) == with_type_semigroup_add_class\<close>
  defines \<open>(C2 :: _ \<times> (('rep \<Rightarrow> 'abs' \<Rightarrow> bool) \<Rightarrow> ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<Rightarrow> ('abs' \<Rightarrow> 'abs' \<Rightarrow> 'abs') \<Rightarrow> bool)) == with_type_semigroup_add_class\<close>
  shows \<open>(snd C1 r ===> (\<longleftrightarrow>)) (fst C2 (Collect (Domainp r))) (\<lambda>plus. class.semigroup_add plus)\<close>
  unfolding C1_def C2_def
  apply (rule aux)
         apply (rule with_type_semigroup_add_class_def)
        apply (rule with_type_semigroup_add_class_def)
       apply (rule with_type_semigroup_add_class_pred_def)
      apply (rule with_type_semigroup_add_class_pred'_def)
     apply (rule with_type_semigroup_add_class_has_dom)
    apply (rule with_type_semigroup_add_class_transfer0)
       apply assumption
      apply assumption
     apply assumption
   apply (rule assms)
  apply (rule assms)
  by -
 *)

lemma xxxxx:
  assumes has_dom: \<open>with_type_has_domain class2R D\<close>
  assumes class1_def: \<open>class1 == (class1P, class1R)\<close>
  assumes class2_def: \<open>class2 == (class2P, class2R)\<close>
  assumes class1P_def: \<open>class1P \<equiv> \<lambda>S p. D S p \<and> pred' S p\<close>
  shows \<open>with_type_compat_rel (fst class1) S (snd class2)\<close>
  using has_dom
  by (simp add: with_type_has_domain_def with_type_compat_rel_def class1_def class2_def class1P_def)

lemma with_type_compat_rel_semigroup_on':
  shows \<open>with_type_compat_rel (fst with_type_semigroup_add_class) S (snd with_type_semigroup_add_class)\<close>
  apply (rule xxxxx)
  apply (rule with_type_semigroup_add_class_has_dom)
    apply (rule with_type_semigroup_add_class_def)
    apply (rule with_type_semigroup_add_class_def)
  by (rule with_type_semigroup_add_class_pred_def)

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>semigroup_add\<close>,
    rep_class_data = \<^const_name>\<open>with_type_semigroup_add_class\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm with_type_semigroup_add_class_transfer}
  }
\<close>

(* subsection \<open>Semigroup, additive\<close>

definition semigroup_on :: \<open>'rep set \<Rightarrow> ('rep\<Rightarrow>'rep\<Rightarrow>'rep) \<Rightarrow> bool\<close> where
  \<open>semigroup_on S p \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. p x y \<in> S) \<and> 
      (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. p (p x y) z = p x (p y z))\<close>

definition with_type_semigroup_add_class where
  \<open>with_type_semigroup_add_class = (semigroup_on, \<lambda>r. rel_fun r (rel_fun r r))\<close>

lemma semigroup_on_transfer: 
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (semigroup_on (Collect (Domainp r))) class.semigroup_add\<close>
  unfolding semigroup_on_def class.semigroup_add_def
  apply (rule with_type_split_aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto

lemma with_type_compat_rel_semigroup_on: 
  includes lifting_syntax
  shows \<open>with_type_compat_rel semigroup_on S (\<lambda>r. r ===> r ===> r)\<close>
  by (simp add: Domainp_rel_fun_iff bi_unique_left_unique semigroup_on_def with_type_compat_rel_def)

lemma semigroup_on_transfer': 
  includes lifting_syntax
  shows \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd with_type_semigroup_add_class r ===> (\<longleftrightarrow>)) (fst with_type_semigroup_add_class (Collect (Domainp r))) class.semigroup_add\<close>
  by (auto simp add: with_type_semigroup_add_class_def intro!: semigroup_on_transfer)

lemma with_type_compat_rel_semigroup_on': \<open>with_type_compat_rel (fst with_type_semigroup_add_class) S (snd with_type_semigroup_add_class)\<close>
  by (simp add: with_type_compat_rel_semigroup_on with_type_semigroup_add_class_def)

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>semigroup_add\<close>,
    rep_class_data = \<^const_name>\<open>with_type_semigroup_add_class\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>
 *)

subsection \<open>Example\<close>

experiment
begin

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>

lemma carrier_nonempty: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup: \<open>with_type_semigroup_add_class_pred carrier carrier_plus\<close>
  by (auto simp: with_type_semigroup_add_class_pred_def
      with_type_semigroup_add_class_dom_def with_type_semigroup_add_class_pred'_def carrier_def carrier_plus_def)

lemma example_semigroup2:
  shows \<open>\<forall>\<^sub>\<tau> 'abs::semigroup_add = carrier with carrier_plus. undefined (3::nat)\<close>
  apply (rule with_typeI)
  apply (simp_all add: with_type_semigroup_add_class_def)
     apply (rule carrier_nonempty)
    apply (rule carrier_semigroup)
   apply (metis fst_conv snd_conv with_type_semigroup_add_class_def with_type_compat_rel_semigroup_on')
proof -
  include lifting_syntax
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>type_definition Rep Abs carrier\<close>
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    using \<open>type_definition Rep Abs carrier\<close> bi_unique_def r_def type_definition.Rep_inject by fastforce
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume \<open>with_type_semigroup_add_class_rel (\<lambda>x y. x = Rep y) carrier_plus pls\<close>
  then have [transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
    by (simp add: r_def with_type_semigroup_add_class_rel_def)
  have \<open>pls x y = pls y x\<close> for x y
    apply transfer
    sorry
  show \<open>undefined 3\<close>
    sorry
qed

lemma example_type:
  includes lifting_syntax
  shows \<open>with_type with_type_class_type undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs). undefined (3::nat))\<close>
  sorry

lemma example_finite:
  includes lifting_syntax
  shows \<open>with_type with_type_class_finite undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::finite). undefined (3::nat))\<close>
  sorry

ML \<open>
With_Type.with_type_cancel \<^context> @{thm example_semigroup2}
\<close>

end (* experiment *)

end (* theory *)
