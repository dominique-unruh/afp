theory With_Type_Inst_Complex_Bounded_Operators
  imports With_Type_Inst_HOL Complex_Bounded_Operators.Complex_Bounded_Linear_Function
begin

subsection \<open>Complex vector space\<close>
ML"open Class;;"
ML \<open>
these_params \<^theory> \<^sort>\<open>complex_vector\<close>
\<close>
ML \<open>
Axclass.get_info \<^theory> \<^class>\<open>complex_vector\<close>
\<close>

ML \<open>rules \<^theory> \<^class>\<open>complex_vector\<close> |> fst
\<close>

unbundle lifting_syntax


term with_type_compat_rel

term conversep


lemma part_equivp_rel_square: 
  assumes \<open>right_total r\<close> and \<open>right_unique r\<close>
  shows \<open>part_equivp (rel_square r)\<close>
proof (rule part_equivpI)
  from \<open>right_total r\<close>
  show \<open>\<exists>x. rel_square r x x\<close>
    by (metis conversep_iff rel_square_def relcompp.intros right_total_def)
  show \<open>symp (rel_square r)\<close>
    by (simp add: converse_relcompp rel_square_def symp_conv_conversep_eq)
  from \<open>right_unique r\<close>
  show \<open>transp (rel_square r)\<close>
    apply (auto simp: rel_square_def intro!: relcomppI transpI)
    by (metis right_uniqueD)
qed



(* definition \<open>with_type_compat_rel' C S R \<longleftrightarrow> 
    (\<forall>r. right_unique r \<longrightarrow> right_total r \<longrightarrow> 
        right_unique (R r) \<and> right_total (R r) \<and> C (Collect (Domainp r)) = Domainp (R r))\<close> *)

(* lemma xxx_prod:
  assumes \<open>with_type_compat_rel' C1 S R1\<close>
  assumes \<open>with_type_compat_rel' C2 S R2\<close>
  shows \<open>with_type_compat_rel' (\<lambda>S. pred_prod (C1 S) (C2 S)) S (\<lambda>r. rel_prod (R1 r) (R2 r))\<close>
  using assms
  by (auto simp: with_type_compat_rel'_def with_type_compat_rel_def prod.Domainp_rel
      prod.bi_unique_rel prod.right_total_rel prod.right_unique_rel) *)

(* lemma \<open>Domainp (r1 ===> r2) f \<longleftrightarrow> (\<forall>x. Domainp r1 x \<longrightarrow> Domainp r2 (f x)) \<and> (\<forall>x y. xxx)\<close>
proof (intro iffI allI impI)
  fix x
  assume \<open>Domainp (r1 ===> r2) f\<close>
  then obtain g where fg: \<open>(r1 ===> r2) f g\<close>
    by auto
  assume \<open>Domainp r1 x\<close>
  then obtain y where xy: \<open>r1 x y\<close>
    by auto
  from fg[unfolded rel_fun_def, rule_format, OF xy]
  show \<open>Domainp r2 (f x)\<close>
    by auto
next
  assume asm: \<open>\<forall>x. Domainp r1 x \<longrightarrow> Domainp r2 (f x)\<close>
  have \<open>\<exists>g. \<forall>x. r1 x y \<longrightarrow> r2 (f x) g\<close> for y
    by -
  then show \<open>Domainp (r1 ===> r2) f\<close>
    unfolding Domainp_iff rel_fun_def by metis *)


(* lemma xxx_fun:
  assumes \<open>with_type_compat_rel' C1 S R1\<close>
  assumes \<open>with_type_compat_rel' C2 S R2\<close>
  shows \<open>with_type_compat_rel' (\<lambda>S. pred_fun (C1 S) (C2 S)) S (\<lambda>r. rel_fun (R1 r) (R2 r))\<close>
  using assms apply (auto simp: with_type_compat_rel'_def with_type_compat_rel_def  Domainp_pred_fun_eq
      bi_unique_left_unique intro!: right_total_fun right_unique_fun)
    apply (subst Domainp_pred_fun_eq)
  using right_unique_fun apply auto[1]
   defer
  thm Domainp_pred_fun_eq
  apply rule
  apply (intro allI impI)
    apply (subst Domainp_pred_fun_eq)
  using assms(1) bi_unique_left_unique with_type_compat_rel'_def apply blastx


  using assms
  apply (auto simp: with_type_compat_rel'_def with_type_compat_rel_def  Domainp_pred_fun_eq
      bi_unique_left_unique
      intro: bi_unique_fun
      dest!: allI )
    apply (subst Domainp_pred_fun_eq)
     apply (auto simp: bi_unique_left_unique)
  defer

  apply (simp add: bi_unique_left_unique)
  using assms(1) bi_unique_left_unique with_type_compat_rel'_def apply blastx *)

schematic_goal
  fixes S :: \<open>'rep set\<close>
  shows \<open>with_type_compat_xxx (?R :: ('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> (((real \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   (complex \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   'rep \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> real) \<times>
   ('rep \<Rightarrow> real) \<times> ('rep \<Rightarrow> 'rep) \<times> ('rep \<times> 'rep) filter \<times> ('rep set \<Rightarrow> bool) \<times> ('rep \<Rightarrow> 'rep \<Rightarrow> complex)) \<Rightarrow> ?'absparam \<Rightarrow> bool))
?RR\<close>
  using [[show_types]]
  (* using with_type_compat_xxx_eq[where 'a=real] *)
   apply (rule with_type_compat_xxx
      with_type_compat_xxx_eq[where 'a=real]
 with_type_compat_xxx_eq[where 'a=complex]
      with_type_compat_xxx_eq[where 'a=bool]
      )+
  by -


(* (real \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   (complex \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   'rep \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep) \<times>
   ('rep \<Rightarrow> 'rep \<Rightarrow> real) \<times>
   ('rep \<Rightarrow> real) \<times> ('rep \<Rightarrow> 'rep) \<times> ('rep \<times> 'rep) filter \<times> ('rep set \<Rightarrow> bool) \<times> ('rep \<Rightarrow> 'rep \<Rightarrow> complex) *)


(* ML \<open>
(* Takes a type T. Returns:
 * - relation transformer R (with free var r)
 * - domain definition D (with free var S)
 * - thm: with_type_compat_rel (\<lambda>S p. C S) S (\<lambda>r. R) \<and> with_type_rel_pres (\<lambda>r. R)
 *)
fun get_relation_for_type ctxt T = let
  fun has_tvar (TVar _) = true
    | has_tvar (Type (_,Ts)) = exists has_tvar Ts
    | has_tvar _ = false
  in if has_tvar T then
\<close> *)



term rel_filter
term rel_prod

ML \<open>
val (relationT, relationR, relationD, relationThm) = get_relation_thm \<^context> \<^class>\<open>complex_vector\<close>
\<close>


(* term rel_filter
term rel_prod
ML \<open>
fun get_relation thy class = let
  fun dest_relT (Type("fun", [T1, Type("fun", [T2, _])])) = (T1,T2)
  fun mk_rel_fun r1 r2 = let val (r1a,r1b) = dest_relT (fastype_of r1) val (r2a,r2b) = dest_relT (fastype_of r2) in
                               \<^Const>\<open>rel_fun r1a r1b r2a r2b\<close> $ r1 $ r2 end
  fun mk_rel_filter r = let val (ra,rb) = dest_relT (fastype_of r) in
                               \<^Const>\<open>rel_filter ra rb\<close> $ r end
  fun mk_rel_prod r1 r2 = let val (r1a,r1b) = dest_relT (fastype_of r1) val (r2a,r2b) = dest_relT (fastype_of r2) in
                               \<^Const>\<open>rel_prod r1a r1b r2a r2b\<close> $ r1 $ r2 end
  fun mk_rel_set r = let val (ra,rb) = dest_relT (fastype_of r) in
                               \<^Const>\<open>rel_set ra rb\<close> $ r end
  val relT = TFree(("'rep"),\<^sort>\<open>type\<close>) --> TFree(("'abs"),\<^sort>\<open>type\<close>) --> HOLogic.boolT
  val rel_var = Free("r", relT)
  fun has_tvar (TVar _) = true
    | has_tvar (Type (_,Ts)) = exists has_tvar Ts
    | has_tvar _ = false
  fun mk_relation' (TVar(("'a",0),_)) = rel_var
    | mk_relation' (Type("fun", [T1, T2])) = mk_rel_fun (mk_relation T1) (mk_relation T2)
    | mk_relation' (Type(\<^type_name>\<open>filter\<close>, [T])) = mk_rel_filter (mk_relation T)
    | mk_relation' (Type(\<^type_name>\<open>prod\<close>, [T1,T2])) = mk_rel_prod (mk_relation T1) (mk_relation T2)
    | mk_relation' (Type(\<^type_name>\<open>set\<close>, [T])) = mk_rel_set (mk_relation T)
    | mk_relation' T = raise TYPE ("mk_relation", [T], [])
  and mk_relation T = if has_tvar T then mk_relation' T else HOLogic.eq_const T
  val relations = get_params_of_class thy class |> map (fn (_,_,T) => T) |> map mk_relation
  fun mk_rel_prods [] = \<^term>\<open>(=) :: unit \<Rightarrow> unit \<Rightarrow> bool\<close>
    | mk_rel_prods [r] = r
    | mk_rel_prods (r::rs) = mk_rel_prod r (mk_rel_prods rs)
  val relation = mk_rel_prods relations |> lambda rel_var
in
  relation
end
;;
get_relation \<^theory> \<^class>\<open>complex_inner\<close>
\<close> *)

local_setup
\<open>
Local_Theory.define ((\<^binding>\<open>with_type_class_complex_vector_rel\<close>, Mixfix.NoSyn), 
      ((\<^binding>\<open>with_type_class_complex_vector_rel_def\<close>, []), Type.legacy_freeze relationR))
#> snd
\<close>

local_setup
\<open>
Local_Theory.define ((\<^binding>\<open>with_type_class_complex_vector_dom\<close>, Mixfix.NoSyn), 
      ((\<^binding>\<open>with_type_class_complex_vector_dom_def\<close>, []), Type.legacy_freeze relationD))
#> snd
\<close>


thm with_type_class_complex_vector_rel_def
term with_type_class_complex_vector_dom

definition \<open>with_type_class_complex_vector_pred S p \<longleftrightarrow> with_type_class_complex_vector_dom S p \<and> undefined ''rest'' p\<close>

definition with_type_class_complex_vector where
  \<open>with_type_class_complex_vector = (with_type_class_complex_vector_pred,
                                     with_type_class_complex_vector_rel)\<close>

schematic_goal with_type_class_complex_vector_transfer: 
  includes lifting_syntax
  shows \<open> 
    (snd with_type_class_complex_vector r ===> (\<longleftrightarrow>)) ?X 
    (\<lambda>(scaleR, scaleC, plus, zero, minus, uminus). class.complex_vector scaleR scaleC plus zero minus uminus)\<close>
  unfolding with_type_class_complex_vector_def with_type_class_complex_vector_pred_def fst_conv snd_conv
    class.complex_vector_def class.complex_vector_axioms_def
  apply transfer_prover_start
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  thm class.comm_monoid_add_def
  apply (rule with_type_split_aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto x
  apply (auto simp add: intro!: semigroup_on_transfer) x
  by -

lemma with_type_compat_rel_conj1I:
  assumes \<open>with_type_compat_rel A S R\<close>
  shows \<open>with_type_compat_rel (\<lambda>S p. A S p \<and> B S p) S R\<close>
  using assms by (auto simp: with_type_compat_rel_def)

lemma with_type_compat_relI_weak_leq:
  assumes \<open>\<And>r. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> C (Collect (Domainp r)) \<le> Domainp (R r)\<close>
  shows \<open>with_type_compat_rel C S R\<close>
  unfolding with_type_compat_rel_def
  using assms by auto

(* lemma xxx:
  assumes \<open>a \<le> Domainp r1\<close> \<open>b \<le> Domainp r2\<close>
  shows \<open>(\<lambda>x. a (fst x) \<and> b (snd x)) \<le> Domainp (rel_prod r1 r2)\<close>
  unfolding prod.Domainp_rel 
  using assms by auto

lemma xxx2:
  assumes \<open>bi_unique r\<close>
  assumes \<open>a \<le> Domainp r1\<close> \<open>b \<le> Domainp r2\<close>
  shows \<open>(\<lambda>f. \<forall>y. r1 xa b \<longrightarrow> Domainp r2 (f xa)) \<le> Domainp (rel_fun r1 r2)\<close>
  unfolding prod.Domainp_rel 
  apply (subst Domainp_pred_fun_eq)
  unfolding pred_fun_def
  apply auto
  using assms by auto *)

lemma \<open>eventually P (map_filter_on S id F) = xxx\<close>
  apply (subst eventually_map_filter_on)
  oops

lemma xxx_rel_filter: 
  assumes \<open>bi_unique r\<close> and \<open>right_total r\<close>
  shows \<open>Domainp (rel_filter r) = (\<lambda>F. \<forall>\<^sub>F x in F. Domainp r x)\<close>
  unfolding rel_filter.simps Domainp_iff
proof (rule ext, rule iffI)
  fix F
  assume \<open>\<exists>G Z. (\<forall>\<^sub>F (x, y) in Z. r x y) \<and>
          map_filter_on {(x, y). r x y} fst Z = F \<and> map_filter_on {(x, y). r x y} snd Z = G\<close>
  then show \<open>\<forall>\<^sub>F x in F. Ex (r x)\<close>
    apply (auto intro!: ext case_prod_unfold simp: eventually_map_filter_on)
    using eventually_elim2 by fastforce
next
  fix F
  assume asm: \<open>\<forall>\<^sub>F x in F. Ex (r x)\<close>
  define S where \<open>S = Collect (Domainp r)\<close>
  have FS: \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
    by (smt (verit, best) DomainPI S_def asm eventually_mono mem_Collect_eq)
  from assms obtain f where rf: \<open>r = (\<lambda>x y. x = f y)\<close>
    by (metis (no_types, opaque_lifting) bi_unique_def right_totalE)
  have [simp]: \<open>x \<in> S \<Longrightarrow> x = f (inv f x)\<close> for x
    by (metis Domainp_iff S_def f_inv_into_f mem_Collect_eq rangeI rf)
  define Z where \<open>Z = map_filter_on S (\<lambda>x. (x, inv f x)) F\<close>
  have id_F: \<open>map_filter_on S (\<lambda>x. x) F = F\<close>
    by (smt (z3) FS eventually_elim2 eventually_map_filter_on filter_eq_iff)

  have \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    using asm 
    apply (auto simp add: Domainp_iff eventually_map_filter_on Z_def S_def)
    by (smt (verit, best) rf eventually_elim2 f_inv_into_f rangeI)
  moreover have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    unfolding Z_def
    apply (subst map_filter_on_comp)
    by (auto simp: FS o_def id_F rf)
  ultimately show \<open>\<exists>G Z. (\<forall>\<^sub>F (x, y) in Z. r x y) \<and>
          map_filter_on {(x, y). r x y} fst Z = F \<and> map_filter_on {(x, y). r x y} snd Z = G\<close>
    by auto
qed

(* schematic_goal 
  assumes [transfer_rule, simp]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  defines [symmetric, simp]: \<open>S == Domainp r\<close>
  shows \<open>xxx p = Domainp (with_type_class_complex_vector_rel r) p\<close>
  unfolding with_type_class_complex_vector_rel_def
  apply (simp add: prod.Domainp_rel Domainp_pred_fun_eq)+
  apply (subst Domainp_pred_fun_eq) apply transfer_step
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply transfer_step
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique bi_unique_rel_set)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (subst Domainp_pred_fun_eq)
   apply (simp add: bi_unique_left_unique)
  apply (simp add: pred_prod_beta Domain_eq_top)
  apply (subst xxx_rel_filter)
    apply (simp add: prod.bi_unique_rel)
   apply (simp add: prod.right_total_rel)
  apply (simp add: prod.Domainp_rel Domainp_pred_fun_eq)
  
  apply (simp add: Domain_eq_top)

  apply (simp only: prod.Domainp_rel Domainp_pred_fun_eq[OF \<open>left_unique r\<close>])
  thm Domainp_pred_fun_eq[OF \<open>left_unique r\<close>]
  apply (rule xxx)
  apply (intro xxx) 
  oops *)

ML \<open>
val ctxt  = \<^context>
val ([thm],ctxt0) = Assumption.add_assumes [\<^cprop>\<open>1==2\<close>] ctxt
val x = Assumption.export false ctxt0 ctxt thm
\<close>
thm xxx_rel_filter

lemma pred_fun_top[simp]: \<open>pred_fun A \<top> = \<top>\<close>
  by auto

lemma pred_prod_top[simp]: \<open>pred_prod \<top> \<top> = \<top>\<close>
  by auto

ML \<open>
local
val ctxt = \<^context>
val ct = \<^cterm>\<open>Domainp (with_type_class_complex_vector_rel r)\<close>
val def = @{thm with_type_class_complex_vector_rel_def}
val ([bi_unique,right_total], ctxt') = Assumption.add_assumes [\<^cprop>\<open>bi_unique r\<close>, \<^cprop>\<open>right_total r\<close>] ctxt
(* val left_unique = bi_unique RS @{thm bi_unique_left_unique} *)
val simps = [def,bi_unique,right_total] @ 
@{thms prod.Domainp_rel
 left_unique_eq prod.right_total_rel prod.bi_unique_rel prod.pred_True
 Domainp_pred_fun_eq
 left_unique_rel_set
 bi_unique_left_unique Domainp_set
 xxx_rel_filter pred_fun_top pred_prod_top
 Domain_eq_top}
val ctxt' = Raw_Simplifier.clear_simpset ctxt' addsimps simps
fun prover ctxt = SINGLE (ALLGOALS (simp_tac ctxt)
                    THEN ALLGOALS (SUBGOAL (fn (t,_) => (warning ("subgoal: " ^ Syntax.string_of_term ctxt t); no_tac))))
val eq = Raw_Simplifier.rewrite_cterm (false,false,false) prover
          ctxt' ct
val rhs = Thm.rhs_of eq
in
val _ = Syntax.string_of_term ctxt (Thm.term_of rhs) |> writeln
(* val eq = Raw_Simplifier.rewrite ctxt' false simps ct *)
end
\<close>



schematic_goal with_type_compat_rel_complex_vector:
  \<open>with_type_compat_rel ?X S (snd with_type_class_complex_vector)\<close>
  unfolding with_type_class_complex_vector_def fst_conv snd_conv with_type_class_complex_vector_pred_def[abs_def]
  apply (rule with_type_compat_rel_conj1I)
  apply (rule with_type_compat_relI_weak_leq)
  unfolding with_type_class_complex_vector_rel_def
  subgoal for r 

  apply (rule xxx) x

  apply (subst Domainp_rel_fun_iff)

  apply (simp add: with_type_class_complex_vector_def Domainp_rel_fun_iff bi_unique_left_unique semigroup_on_def with_type_compat_rel_def)
  by -


setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>complex_vector\<close>,
    rep_class_data = \<^const_name>\<open>with_type_class_complex_vector\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>




subsection \<open>Complex Hilbert space\<close>



definition with_type_class_chilbert_space where
  \<open>with_type_class_chilbert_space = (undefined, \<lambda>r. rel_fun r (rel_fun r r))\<close>

setup \<open>
  With_Type.add_with_type_info_global {
    class = \<^class>\<open>chilbert\<close>,
    rep_class_data = \<^const_name>\<open>with_type_class_semigroup_add\<close>,
    with_type_compat_rel = @{thm with_type_compat_rel_semigroup_on'},
    rep_class_data_thm = NONE,
    transfer = SOME @{thm semigroup_on_transfer'}
  }
\<close>



end
