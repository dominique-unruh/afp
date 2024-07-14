theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets" Misc_With_Type Instantiate_Term_Antiquotation
    "HOL-Eisbach.Eisbach"
  keywords "with_type_case" :: prf_asm % "proof"
begin

definition with_type_compat_rel where
  \<open>with_type_compat_rel C S R \<longleftrightarrow> 
      (\<forall>r rp. bi_unique r \<longrightarrow> right_total r \<longrightarrow> S = Collect (Domainp r) \<longrightarrow> C S rp \<longrightarrow> Domainp (R r) rp)\<close>

text \<open>
\<^term>\<open>S\<close> -- the carrier set of the representation of the type

\<^term>\<open>rep_ops\<close> -- operations of the representation type (i.e., operations like addition or similar)

\<^term>\<open>C\<close> -- the properties that \<^term>\<open>R\<close> and \<^term>\<open>rep_ops\<close> are guaranteed to satisfy
(basically, the type-class definition)

\<^term>\<open>R\<close> -- transfers a relation \<^term>\<open>r\<close> between representation and abstract type to a relation
between representation operations and abstract operations (\<^term>\<open>r\<close> is always bi-unique and right-total)

\<^term>\<open>P\<close> -- the predicate that we claim holds.
It can work on the type \<^typ>\<open>'abs\<close> (which is type-classed) but it also gets \<^term>\<open>Rep\<close> and \<^term>\<open>Abs\<close>
so that it can transfer things back and forth.

If \<^term>\<open>P\<close> does not contain \<^typ>\<open>'abs\<close>, we can erase the \<^term>\<open>with_type\<close> using the \<open>Types_To_Sets\<close> mechanism.
See lemma \<open>erasure_example\<close> below.


The intuitive meaning of \<^term>\<open>with_type (C,R) (S,rep_ops) P\<close> is that \<^term>\<open>P\<close> holds for
any type \<^typ>\<open>'t\<close> that that can be represented by a concrete representation (S,rep_ops)
and that has a type class matching the specification (C,R).
\<close>
definition \<open>with_type = (\<lambda>(C,R) (S,rep_ops) P. S\<noteq>{} \<and> C S rep_ops \<and> with_type_compat_rel C S R
    \<and> (\<forall>Rep Abs abs_ops. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs))\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> ('rep \<Rightarrow> 'abs) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep_ops\<close>

definition \<open>WITH_TYPE_CLASS_type S ops = True\<close>
definition \<open>WITH_TYPE_REL_type r = (=)\<close>

(* definition with_type_type_class where \<open>with_type_type_class = ((\<lambda>_ (_::unit). True), (\<lambda>_. (=)))\<close> *)

lemma with_type_compat_rel_type: \<open>with_type_compat_rel WITH_TYPE_CLASS_type S WITH_TYPE_REL_type\<close>
  by (simp add: WITH_TYPE_REL_type_def WITH_TYPE_CLASS_type_def with_type_compat_rel_def Domainp_iff)

(* Demonstration *)
lemma \<open>with_type (WITH_TYPE_CLASS_type,WITH_TYPE_REL_type) (S,()) P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>
  by (auto simp: with_type_def WITH_TYPE_REL_type_def WITH_TYPE_CLASS_type_def with_type_compat_rel_def)

lemma with_typeI:
  fixes Sp :: \<open>'a set \<times> 'c\<close> and CR
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C S p\<close>
  assumes \<open>with_type_compat_rel C S R\<close>
  assumes \<open>\<And>Rep Abs abs_ops. type_definition Rep Abs S \<Longrightarrow> R (\<lambda>x y. x = Rep y) p abs_ops \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type (C,R) (S,p) P\<close>
  using assms
  by (auto simp add: with_type_def case_prod_beta)

lemma with_type_mp: 
  assumes \<open>with_type (C,R) (S,p) P\<close>
  assumes \<open>\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> C S p \<Longrightarrow> P Rep Abs \<Longrightarrow> Q Rep Abs\<close>
  shows \<open>with_type (C,R) (S,p) Q\<close>
  using assms by (auto simp add: with_type_def case_prod_beta)

lemma with_type_nonempty: \<open>with_type CR (S,p) P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def case_prod_beta)

lemma with_type_prepare_cancel:
  fixes Sp :: \<open>'rep set \<times> _\<close>
  assumes wt: \<open>with_type CR (S,p) (\<lambda>_ (_::'rep\<Rightarrow>'abs). P)\<close>
  assumes ex: \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs S)\<close>
  shows P
proof -
  define C R where \<open>C = fst CR\<close> and \<open>R = snd CR\<close>
  with ex obtain Rep :: \<open>'abs\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [simp]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    using r_def td typedef_bi_unique apply blast
    by (simp add: r_def right_totalI)
  have Sr: \<open>S = Collect (Domainp r)\<close>
    using type_definition.Rep[OF td] 
    apply (auto simp: r_def intro!: DomainPI)
    apply (subst type_definition.Abs_inverse[OF td])
    by auto
  from wt have nice: \<open>with_type_compat_rel C S R\<close> and \<open>C S p\<close>
    by (simp_all add: with_type_def R_def C_def case_prod_beta)
  from nice[unfolded with_type_compat_rel_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = Rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from td abs_ops wt
  show P
    by (auto simp: with_type_def case_prod_beta R_def)
qed

(* lemma Domainp_rel_fun_iff: (* TODO: use Domainp_pred_fun_eq instead *)
  includes lifting_syntax
  assumes \<open>left_unique R\<close>
  shows \<open>Domainp (R ===> S) p \<longleftrightarrow> (\<forall>x. Domainp R x \<longrightarrow> Domainp S (p x))\<close>
  using Domainp_pred_fun_eq[OF assms, of S]
  by auto *)

lemma with_type_class_axioms:
  includes lifting_syntax
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and CR :: \<open>_ \<times> (('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool))\<close>
    and Sp
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>with_type_compat_rel C S R2\<close>
  assumes wt: \<open>with_type (C,R) (S,p) P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs_ops2. axioms x\<close>
proof -
  from ex obtain Rep :: \<open>'abs2\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r x y = (x = Rep y)\<close> for x y
  have bi_unique_r: \<open>bi_unique r\<close>
    using bi_unique_def td type_definition.Rep_inject r_def by fastforce
  have right_total_r: \<open>right_total r\<close>
    by (simp add: right_totalI r_def)
  have right_total_R[transfer_rule]: \<open>right_total (r ===> r ===> r)\<close>
    by (meson bi_unique_r right_total_r bi_unique_alt_def right_total_fun)
  note trans = trans[OF bi_unique_r, OF right_total_r, transfer_rule]

  from td
  have rS: \<open>Collect (Domainp r) = S\<close>
    apply (auto simp: r_def Domainp_iff type_definition.Rep)
    by (meson type_definition.Rep_cases)

  from wt have sg: \<open>C S p\<close>
    by (simp_all add: with_type_def case_prod_beta)

  with nice have \<open>Domainp (R2 r) p\<close>
    by (simp add: bi_unique_r with_type_compat_rel_def rS right_total_r)
  
  with sg
  have \<open>\<exists>x :: 'abs_ops2. axioms x\<close>
    apply (transfer' fixing: R2 S p)
    using apply_rsp' local.trans rS by fastforce
  
  then obtain abs_plus :: 'abs_ops2 
    where abs_plus: \<open>axioms abs_plus\<close>
    apply atomize_elim by auto

  then show ?thesis
    by auto
qed

ML_file "with_type.ML"

attribute_setup cancel_with_type = 
  \<open>Thm.rule_attribute [] (With_Type.with_type_cancel o Context.proof_of) |> Scan.succeed\<close>
  \<open>Transforms (\<forall>\<^sub>\<tau> 't=\<dots>. P) into P\<close>

(* ML \<open>
fun generalize typ ctxt thm = 
    Thm.generalize (Names.make1_set typ, Names.empty) 0 thm
 |> \<^print>
\<close>


attribute_setup generalize = 
  \<open>Scan.lift Parse.typ >> (fn typ => Thm.rule_attribute [] (generalize typ o Context.proof_of))\<close>
  \<open>TODO\<close>
 *)

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>type\<close>,
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_type\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_type\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_type},
  (* rep_class_data_thm = NONE, *)
  transfer = NONE
}
\<close>

syntax "_with_type" :: "type \<Rightarrow> 'a => 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_. _" [0,0,10] 10)
syntax "_with_type_with" :: "type \<Rightarrow> 'a => args \<Rightarrow> 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_ with _. _" [0,0,10] 10)
parse_translation \<open>[
  (\<^syntax_const>\<open>_with_type\<close>, With_Type.with_type_parse_translation),
  (\<^syntax_const>\<open>_with_type_with\<close>, With_Type.with_type_parse_translation)
]\<close>

(* print_translation \<open>[ (\<^const_syntax>\<open>with_type\<close>, With_Type.with_type_print_translation) ]\<close> *)


term \<open>\<forall>\<^sub>\<tau> 't::type = N. (rep_t = rep_t)\<close>
(* term \<open>\<forall>\<^sub>\<tau>'t::type = N with pls. (rep_t = rep_t)\<close> *)

named_theorems with_type_intros

lemma [with_type_intros]: \<open>WITH_TYPE_CLASS_type S ops\<close>
  by (simp add: WITH_TYPE_CLASS_type_def)

declare with_type_compat_rel_type[with_type_intros]

method with_type_intro = rule with_typeI; (intro with_type_intros)?
(* method with_type_mp = rule with_type_mp; (intro with_type_intros)? *)




ML \<open>
fun subst_all u (\<^Const_>\<open>Pure.all _\<close> $ t) = betapply (t, u)

fun absT_name T = case T of TFree(name, _) => String.extract (name, 1, NONE) | _ => "t"

exception ERROR_IN_TACTIC of unit -> string
fun with_type_mp_tac pos facts (ctxt, st) = let
    val fact = case facts of [fact] => fact
            | _ => raise THM ("with_type_mp: expected exactly one fact", 1, facts)
    val rule = @{thm with_type_mp} OF [fact]
    val (repT, absT, C, S, ops, P) = case Thm.cprem_of st 1 |> Thm.term_of of
             \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type repT rep_opsT absT abs_opsT\<close> 
                                    $ (\<^Const_>\<open>Pair _ _\<close> $ C $ _) $ (\<^Const_>\<open>Pair _ _\<close> $ S $ ops) $ P)
                   => (repT, absT, C, S, ops, P)
             | _ => raise ERROR_IN_TACTIC (fn _ => "with_type_mp: goal of the wrong form")
    val rep_name = "rep_" ^ absT_name absT
    val abs_name = "abs_" ^ absT_name absT
    val rep = Free(rep_name, absT --> repT)
    val abs = Free(abs_name, repT --> absT)
    val st = case SINGLE (resolve_tac ctxt [rule] 1) st of SOME st => st
              | NONE => raise ERROR_IN_TACTIC (fn _ => "with_type_mp: could not apply with_type_mp")
(*     val prems_of_subgoal = Thm.cprem_of st 1 |> Thm.term_of |> subst_all rep |> subst_all abs
        |> Logic.strip_imp_prems *)
    val _ = Thm.cprems_of st |> \<^print>
    val prems_of_subgoal = Thm.cprem_of st (Thm.nprems_of st) |> Thm.term_of |> Logic.strip_assums_hyp
          |> map (fn t => Abs(rep_name, absT --> repT, Abs(abs_name, repT --> absT, t)))
    val assm_typedef :: assm_class :: assm_prem :: _ = prems_of_subgoal
        (* Thm.cprem_of st 1 |> Thm.term_of |> Term. *)
    val rule_case = Rule_Cases.Case {
          fixes = [(Binding.make (rep_name, pos), absT --> repT), (Binding.make (abs_name, pos), repT --> absT)],
          assumes = [("typedef", [assm_typedef]), ("class", [assm_class]), ("premise", [assm_prem])], 
          binds = [(("concl",0), SOME P)],
          cases = []}
    val ctxt = Proof_Context.update_cases [("with_type_mp", SOME rule_case)] ctxt
  (* TODO: Add to context the following info:
    - 'abs, 'rep types
    - carrier set S, ops
    - C
    - the mp premise
   *)
  in
    Seq.single (ctxt, st) |> Seq.make_results
  end
  handle ERROR_IN_TACTIC error => Seq.single (Seq.Error error)
\<close>


method_setup with_type_mp = \<open>Scan.succeed () >> 
  (fn (_) => fn ctxt => CONTEXT_METHOD (fn facts =>
      Method.RUNTIME (with_type_mp_tac \<^here> facts)))\<close>



ML \<open>
fun with_type_case_cmd args state : Proof.state = let
    (* val ctxt = Proof.context_of state; *)
(*     val case_mp = Proof_Context.check_case ctxt true ("with_type_mp", pos) []
    val (assms, state) = Proof.map_context_result (Proof_Context.apply_case case_mp) state *)
    val state = Proof.case_ ((Binding.empty, []), (("with_type_mp", Position.none), args)) state
    val thm_type_def = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.typedef")
    val thm_class = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.class")
    val thm_premise = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.premise")
    val (rep, abs, S) = case Thm.prop_of thm_type_def of
        \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>type_definition _ _\<close> $ rep $ abs $ S) => (rep,abs,S)
    val \<^Type>\<open>fun absT _\<close> = fastype_of rep
    val state = Interpretation.interpret
              ([(\<^locale>\<open>type_definition\<close>,(("type_definition_" ^ absT_name absT,true), (Expression.Positional [SOME rep, SOME abs, SOME S], [])))],
              [(Binding.make ("i_dont_know_where_this_ends_up", Position.none), NONE, NoSyn)]) state
    val state = Proof.local_future_terminal_proof 
                    (((Method.Basic (Method.fact [thm_type_def]), Position.no_range), NONE)) state
    val state = Proof.set_facts [thm_type_def, thm_class, thm_premise] state
  in state end
\<close>

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with_type_case\<close> "TODO"
    (Scan.repeat (Parse.maybe Parse.binding) >> (fn args => Toplevel.proof (with_type_case_cmd args)))
(* TODO: print informative text *)
\<close>

lemma 
  assumes \<open>finite X\<close>
  shows True
  using assms
proof -
  note [[show_types, show_sorts]]
  fix T :: \<open>'a set\<close> and yy xx :: 't
  have \<open>\<forall>\<^sub>\<tau> 't::type = T.
        yy = (xx :: 't)\<close> if \<open>x = 3\<close>
    sorry
  then
  have \<open>\<forall>\<^sub>\<tau> 't::type = T.
        undefined rep_t xx = (yy :: 't)\<close>
  proof with_type_mp
    show \<open>x = 3\<close>sorry
    with_type_case R A
    
    show ?concl
      sorry
  qed
  (* note this[cancel_with_type] *)
qed simp


end
