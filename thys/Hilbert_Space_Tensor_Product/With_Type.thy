theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets" Misc_With_Type Instantiate_Term_Antiquotation
begin

definition with_type_compat_rel where \<open>with_type_compat_rel C S R \<longleftrightarrow> (\<forall>r rp. bi_unique r \<longrightarrow> right_total r \<longrightarrow> S = Collect (Domainp r) \<longrightarrow> C S rp \<longrightarrow> (Domainp (R r) rp))\<close>

text \<open>
\<^term>\<open>S\<close> -- the carrier set of the representation of the type

\<^term>\<open>rep_ops\<close> -- operations of the representation type (i.e., operations like addition on the set or similar)

\<^term>\<open>R\<close> -- transfers a relation \<^term>\<open>r\<close> between representation and abstract type to a relation between representation operations and abstract operations
(\<^term>\<open>r\<close> is always bi-unique and right-total)

\<^term>\<open>P\<close> -- the predicate that we claim holds.
It can work on the type \<^typ>\<open>'abs\<close> (which is type-classed) but it also gets the relation \<^term>\<open>r\<close>
so that it can transfer things back and forth.
(We could also give \<^term>\<open>P\<close> just \<^term>\<open>Rep\<close> instead of the relation. Maybe simpler?)

If \<^term>\<open>P\<close> does not contain \<^typ>\<open>'abs\<close>, we can erase the \<^term>\<open>with_type\<close> using the \<open>Types_To_Sets\<close> mechanism.
See lemma \<open>erasure_example\<close> below.
\<close>
definition \<open>with_type = (\<lambda>(C,R) (S,rep_ops) P. S\<noteq>{} \<and> C S rep_ops \<and> with_type_compat_rel C S R
    \<and> (\<forall>Rep Abs abs_ops. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs))\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> ('rep \<Rightarrow> 'abs) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep_ops\<close>

definition with_type_class_type where \<open>with_type_class_type = ((\<lambda>_ (_::unit). True), (\<lambda>_. (=)))\<close>

lemma with_type_compat_rel_type: \<open>with_type_compat_rel (fst with_type_class_type) S (snd with_type_class_type)\<close>
  by (simp add: with_type_class_type_def with_type_compat_rel_def Domainp_iff)

(* Demonstration *)
lemma \<open>with_type with_type_class_type (S,()) P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>
  by (auto simp: with_type_def with_type_class_type_def with_type_compat_rel_def)

lemma with_typeI:
  fixes Sp :: \<open>'a set \<times> 'c\<close> and CR
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C S p\<close>
  assumes \<open>with_type_compat_rel C S R\<close>
  assumes \<open>\<And>Rep Abs abs_ops. type_definition Rep Abs S \<Longrightarrow> R (\<lambda>x y. x = Rep y) p abs_ops \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type CR Sp P\<close>
  using assms
  by (auto simp add: with_type_def case_prod_beta)

lemma with_type_mp: 
  assumes \<open>with_type CR (S,p) P\<close>
  shows \<open>(\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> fst CR S p \<Longrightarrow> P Rep Abs \<Longrightarrow> Q Rep Abs) \<Longrightarrow> with_type CR (S,p) Q\<close>
  using assms by (auto simp add: with_type_def case_prod_beta)

lemma with_type_nonempty: \<open>with_type CR Sp P \<Longrightarrow> fst Sp \<noteq> {}\<close>
  by (simp add: with_type_def case_prod_beta)

lemma with_type_prepare_cancel:
  fixes Sp :: \<open>'rep set \<times> _\<close>
  assumes wt: \<open>with_type CR Sp (\<lambda>_ (_::'rep\<Rightarrow>'abs). P)\<close>
  assumes ex: \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs (fst Sp))\<close>
  shows P
proof -
  define S p C R where \<open>S = fst Sp\<close> and \<open>p = snd Sp\<close> and \<open>C = fst CR\<close> and \<open>R = snd CR\<close>
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
    by (simp_all add: with_type_def p_def R_def S_def C_def case_prod_beta)
  from nice[unfolded with_type_compat_rel_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = Rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from td abs_ops wt
  show P
    by (auto simp: with_type_def case_prod_beta S_def p_def R_def)
qed

lemma Domainp_rel_fun_iff: (* TODO: use Domainp_pred_fun_eq instead *)
  includes lifting_syntax
  assumes \<open>left_unique R\<close>
  shows \<open>Domainp (R ===> S) p \<longleftrightarrow> (\<forall>x. Domainp R x \<longrightarrow> Domainp S (p x))\<close>
  using Domainp_pred_fun_eq[OF assms, of S]
  by auto

lemma with_type_split_aux:
  includes lifting_syntax
  assumes \<open>(R ===> (\<longleftrightarrow>)) A B\<close>
  assumes \<open>\<And>x. Domainp R x \<Longrightarrow> C x\<close>
  shows \<open>(R ===> (\<longleftrightarrow>)) (\<lambda>x. C x \<and> A x) B\<close>
  by (smt (verit) DomainPI assms(1) assms(2) rel_fun_def)

lemma bi_unique_left_unique: \<open>bi_unique R \<Longrightarrow> left_unique R\<close>
  by (simp add: bi_unique_alt_def)
lemma bi_unique_right_unique: \<open>bi_unique R \<Longrightarrow> right_unique R\<close>
  by (simp add: bi_unique_alt_def)

lemma with_type_class_axioms:
  includes lifting_syntax
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and CR :: \<open>_ \<times> (('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool))\<close>
    and Sp
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>with_type_compat_rel C S R2\<close>
  assumes wt: \<open>with_type CR Sp P\<close>
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
    by (simp_all add: with_type_def C_def S_def p_def case_prod_beta)

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

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>type\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_type\<close>,
  with_type_compat_rel = @{thm with_type_compat_rel_type},
  rep_class_data_thm = NONE,
  transfer = NONE
}
\<close>

syntax "_with_type" :: "type \<Rightarrow> 'a => 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_. _" [0,0,10] 10)
syntax "_with_type_with" :: "type \<Rightarrow> 'a => args \<Rightarrow> 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_ with _. _" [0,0,10] 10)
parse_translation \<open>[
  (\<^syntax_const>\<open>_with_type\<close>, With_Type.with_type_parse_translation),
  (\<^syntax_const>\<open>_with_type_with\<close>, With_Type.with_type_parse_translation)
]\<close>

term \<open>\<forall>\<^sub>\<tau>'t::type = N. (rep_t = rep_t)\<close>
(* term \<open>\<forall>\<^sub>\<tau>'t::type = N with pls. (rep_t = rep_t)\<close> *)


subsection \<open>Automatic configuration of new class\<close>

ML \<open>
fun dest_args args (t $ u) = dest_args (u :: args) t
  | dest_args args hd = (hd,args)
\<close>

ML \<open>
fun curry_term [] t = Abs("", \<^typ>\<open>unit\<close>, t)
  | curry_term [_] t = t
  | curry_term args t = let
    fun add_args 0 t = t
      | add_args n t = add_args (n-1) (t $ Bound (n-1))
    fun curry [] t = error "unreachable code"
      | curry [(name,T)] t = Abs (name, T, t)
      | curry ((name,T)::args) t = HOLogic.mk_case_prod (Abs (name, T, curry args t))
    val result = curry args (add_args (length args) t) |> \<^print>
    in result end
;;
curry_term [("i",\<^typ>\<open>int\<close>), ("n",\<^typ>\<open>nat\<close>), ("b", \<^typ>\<open>bool\<close>)] \<^term>\<open>undefined :: int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> string\<close>
|> Thm.cterm_of \<^context>
\<close>

ML \<open>
\<^term>\<open>(\<lambda>(x,y,z). undefined x y z)\<close>
\<close>

term \<open>(\<lambda>(x,y,z). undefined x y)\<close>

ML \<open>
fun get_params_of_class thy class = let
val (const,params_ordered) = Class.rules thy class |> fst |> the |> Thm.prop_of |> HOLogic.dest_Trueprop |> dest_args []
val class_params = Class.these_params thy [class]
val final_params = params_ordered |> map (fn Const (const,T) => 
    get_first (fn (name,(_,(const',_))) => if const=const' then SOME (name,const,T) else NONE) class_params |> the)
val const_curried = curry_term (map (fn (n,_,T) => (n,T)) final_params) const
in
  (const_curried,final_params)
end
;;
get_params_of_class \<^theory> \<^class>\<open>group_add\<close> |> fst |> Thm.cterm_of \<^context>
\<close>


definition \<open>with_type_compat_xxx R RR \<longleftrightarrow> (\<forall>r. right_unique r \<longrightarrow> right_total r \<longrightarrow>
  right_unique (R r) \<and> right_total (R r) \<and> rel_square (R r) = RR (rel_square r))\<close>

definition \<open>with_type_has_domain R D \<longleftrightarrow> (\<forall>r. bi_unique r \<longrightarrow> right_total r \<longrightarrow>
  Domainp (R r) = D (Collect (Domainp r)))\<close>

definition \<open>equal_onp A x y \<longleftrightarrow> (x = y \<and> x\<in>A)\<close>

lemma equal_onp_Domainp: 
  assumes \<open>left_unique r\<close>
  shows \<open>equal_onp (Collect (Domainp r)) = rel_square r\<close>
  using assms 
  by (auto intro!: ext simp: equal_onp_def Domainp_iff rel_square_def left_unique_def)

lemma with_type_has_domain_xxx:
  assumes \<open>with_type_compat_xxx R RR\<close>
  shows \<open>with_type_has_domain R (\<lambda>D. Domainp (RR (equal_onp D)))\<close>
  using assms
  apply (auto simp add: with_type_has_domain_def with_type_compat_xxx_def equal_onp_Domainp
      bi_unique_left_unique bi_unique_right_unique)
  by (metis Domainp_rel_square bi_unique_right_unique)


named_theorems with_type_compat_xxx

lemma with_type_compat_xxx_prodI[with_type_compat_xxx]:
  assumes \<open>with_type_compat_xxx R1 RR1\<close>
  assumes \<open>with_type_compat_xxx R2 RR2\<close>
  shows \<open>with_type_compat_xxx (\<lambda>r. rel_prod (R1 r) (R2 r)) (\<lambda>rr. rel_prod (RR1 rr) (RR2 rr))\<close>
  using assms unfolding with_type_compat_xxx_def
  by (auto simp add: prod.right_unique_rel prod.right_total_rel rel_square_def 
      simp flip: prod.rel_compp prod.rel_conversep)

lemma rel_square_rel_fun:
  includes lifting_syntax
  assumes \<open>right_unique b\<close> \<open>right_total b\<close>
  shows \<open>rel_square (a ===> b) = rel_square a ===> rel_square b\<close>
proof (intro ext iffI)
  fix f g
  assume \<open>rel_square (a ===> b) f g\<close>
  then show \<open>(rel_square a ===> rel_square b) f g\<close>
    by (smt (verit, del_insts) OO_def conversep_iff rel_fun_def rel_square_def)
next
  fix f g
  assume ab2_fg: \<open>(rel_square a ===> rel_square b) f g\<close>
  have \<open>\<exists>z. \<forall>x. a x y \<longrightarrow> b (f x) z \<and> b (g x) z\<close> for y
  proof (cases \<open>\<exists>x. a x y\<close>)
    case True
    then obtain x0 where \<open>a x0 y\<close>
      by auto
    with ab2_fg obtain z where \<open>b (f x0) z\<close> and \<open>b (g x0) z\<close>
      by (metis (mono_tags, opaque_lifting) OO_def apply_rsp' conversep_iff rel_square_def)
    have \<open>b (f x) z\<close> and \<open>b (g x) z\<close> if \<open>a x y\<close> for x
    proof -
      have \<open>rel_square a x x0\<close>
        by (metis \<open>a x0 y\<close> conversepI rel_square_def relcomppI that)
      then have \<open>rel_square b (f x) (g x0)\<close>
        by (meson ab2_fg rel_fun_def)
      with \<open>b (g x0) z\<close>
      have \<open>(rel_square b OO b) (f x) z\<close>
        by auto
      with \<open>right_unique b\<close> \<open>right_total b\<close> show \<open>b (f x) z\<close>
        by (metis (no_types, opaque_lifting) OO_eq antisym rel_square_def relcompp_assoc right_total_alt_def right_unique_alt_def)

      have \<open>rel_square a x0 x\<close>
        by (metis \<open>a x0 y\<close> conversepI rel_square_def relcomppI that)
      then have \<open>rel_square b (f x0) (g x)\<close>
        by (meson ab2_fg rel_fun_def)
      with \<open>right_unique b\<close> \<open>right_total b\<close> have \<open>rel_square b (g x) (f x0)\<close>
        by (metis converse_relcompp conversepI conversep_conversep rel_square_def)
      with \<open>b (f x0) z\<close>
      have \<open>(rel_square b OO b) (g x) z\<close>
        by blast
      with \<open>right_unique b\<close> \<open>right_total b\<close> show \<open>b (g x) z\<close>
        by (metis (no_types, opaque_lifting) OO_eq antisym rel_square_def relcompp_assoc right_total_alt_def right_unique_alt_def)
    qed
    then show ?thesis
      by blast
  next
    case False
    then show ?thesis 
      by auto
  qed
  then show \<open>rel_square (a ===> b) f g\<close>
    by (metis (mono_tags, opaque_lifting) conversep_iff rel_fun_def rel_square_def relcomppI)
qed


lemma with_type_compat_xxx_funI[with_type_compat_xxx]:
  fixes R1 :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> _\<close>
    and R2 :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> _\<close>
  assumes \<open>with_type_compat_xxx R1 RR1\<close>
  assumes \<open>with_type_compat_xxx R2 RR2\<close>
  shows \<open>with_type_compat_xxx (\<lambda>r. rel_fun (R1 r) (R2 r)) (\<lambda>rr. rel_fun (RR1 rr) (RR2 rr))\<close>
  using assms by (auto simp: with_type_compat_xxx_def rel_square_rel_fun intro: right_unique_fun right_total_fun)


lemma rel_square_rel_set: \<open>rel_square (rel_set a) = rel_set (rel_square a)\<close>
  by (auto simp: rel_square_def simp flip: rel_set_conversep rel_set_OO)

lemma with_type_compat_xxx_setI[with_type_compat_xxx]:
  fixes R1 :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> _\<close>
    and R2 :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> _\<close>
  assumes \<open>with_type_compat_xxx R RR\<close>
  shows \<open>with_type_compat_xxx (\<lambda>r. rel_set (R r)) (\<lambda>rr. rel_set (RR rr))\<close>
  using assms 
  by (auto simp: with_type_compat_xxx_def rel_square_rel_set intro: right_unique_rel_set right_total_rel_set)


lemma with_type_compat_xxx_idI[with_type_compat_xxx]:
  \<open>with_type_compat_xxx (\<lambda>r. r) (\<lambda>rr. rr)\<close>
  by (simp add: with_type_compat_xxx_def)

lemma with_type_compat_xxx_eq:
  \<open>with_type_compat_xxx (\<lambda>_::'rep\<Rightarrow>'abs\<Rightarrow>bool. ((=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)) (\<lambda>_. (=))\<close>
  by (simp add: with_type_compat_xxx_def right_total_eq right_unique_eq)

lemma rel_square_rel_filter[with_type_compat_xxx]: 
  assumes \<open>right_unique r\<close> and \<open>right_total r\<close>
  shows \<open>rel_square (rel_filter r) = rel_filter (rel_square r)\<close>
  by (simp add: rel_square_def flip: rel_filter_conversep rel_filter_distr)

lemma with_type_compat_xxx_filterI[with_type_compat_xxx]:
  assumes \<open>with_type_compat_xxx R RR\<close>
  shows \<open>with_type_compat_xxx (\<lambda>r. rel_filter (R r)) (\<lambda>rr. rel_filter (RR rr))\<close>
  using assms 
  by (auto simp: with_type_compat_xxx_def rel_square_rel_filter intro: right_unique_rel_filter right_total_rel_filter)

lemma Domainp_equal_onp[simp]: \<open>Domainp (equal_onp S) = (\<lambda>x. x\<in>S)\<close>
  by (auto intro!: ext simp: Domainp_iff equal_onp_def)

lemma Domainp_rel_fun_equal_onp: 
  includes lifting_syntax
  shows \<open>Domainp (equal_onp S ===> r) f = (\<forall>x\<in>S. Domainp r (f x))\<close>
  by (auto simp add: Domainp_pred_fun_eq equal_onp_def left_unique_def)

ML \<open>
(* Returns (T,R,D,thm) where:
  T is the type of the type of parameters of the type representation
  R (term) is a function that maps a relation between representation and abstract type
    into a relation between representation parameters and abstract parameters
  D (term) is a function that maps a representation domain to the set of representation parameters 
  thm says "with_type_has_domain R D"
*)
fun get_relation_thm ctxt class = let
  open Conv
  fun has_tvar (TVar _) = true
    | has_tvar (Type (_,Ts)) = exists has_tvar Ts
    | has_tvar _ = false
  val rep_paramT0 = get_params_of_class (Proof_Context.theory_of ctxt) class |> snd |> map (fn (_,_,T) => T) |> HOLogic.mk_tupleT
  val repT = TFree("'rep",\<^sort>\<open>type\<close>)
  val rep_paramT = TVar(("'rep_param",0),\<^sort>\<open>type\<close>)
  val absT = TFree("'abs",\<^sort>\<open>type\<close>)
  val abs_paramT = typ_subst_TVars [(("'a",0), absT)] rep_paramT0
(*   val goal = \<^Const>\<open>with_type_compat_xxx repT absT rep_paramT abs_paramT\<close>
        $ Var(("R",0), (repT --> absT --> HOLogic.boolT) --> (rep_paramT --> abs_paramT --> HOLogic.boolT))
        $ Var(("RR",0), (repT --> repT --> HOLogic.boolT) --> (rep_paramT --> rep_paramT --> HOLogic.boolT))
      |> HOLogic.mk_Trueprop *)
  val goal = \<^Const>\<open>with_type_has_domain repT absT rep_paramT abs_paramT\<close>
                $ Var(("R",0), (repT --> absT --> HOLogic.boolT) --> (rep_paramT --> abs_paramT --> HOLogic.boolT))
                $ Var(("D",0), HOLogic.mk_setT repT --> rep_paramT --> HOLogic.boolT)
      |> HOLogic.mk_Trueprop
  val thms =  Named_Theorems.get ctxt \<^named_theorems>\<open>with_type_compat_xxx\<close>
  fun dest_with_type_compat_xxx (\<^Const_>\<open>Trueprop\<close> $ 
               (\<^Const_>\<open>with_type_compat_xxx \<open>TFree _\<close> \<open>TFree _\<close> \<open>TVar _\<close> T\<close> $ Var _ $ Var _)) 
          = T
    | dest_with_type_compat_xxx t = raise TERM ("get_relation_thm", [t])
  fun dest_with_type_has_domain (\<^Const_>\<open>Trueprop\<close> $ 
               (\<^Const_>\<open>with_type_has_domain \<open>TVar _\<close> \<open>TVar _\<close> T _\<close> $ R $ D)) 
          = (T,R,D)
    | dest_with_type_has_domain t = raise TERM ("get_relation_thm/dest_with_type_has_domain", [t])
  fun tac0 ctxt = SUBGOAL (fn (t,i) => 
      let val T = dest_with_type_compat_xxx t in
      if not (exists_subtype (fn subT => subT = absT) T) then
        resolve_tac ctxt @{thms with_type_compat_xxx_eq} i
      else
        ((resolve_tac ctxt thms ORELSE' (fn _ => fn _ => raise TYPE ("get_relation_thm", [T], [t])))
        THEN_ALL_NEW tac0 ctxt) i end)
  fun tac ctxt = resolve_tac ctxt @{thms with_type_has_domain_xxx} 1 THEN tac0 ctxt 1
  val thm = Goal.prove ctxt [] [] goal (fn {context,...} => tac context)
  val simp_rules = @{thms Domainp_rel_fun_equal_onp[abs_def] Domainp_equal_onp}
  val thm = thm |> fconv_rule (Simplifier.rewrite ((clear_simpset ctxt) addsimps simp_rules)
                               |> arg_conv(*Trueprop*) |> arg_conv)
  val (T,R,D) = dest_with_type_has_domain (Thm.prop_of thm)
in
  (T,R,D,thm)
end
\<close>

ML \<open>fun local_def binding t = Local_Theory.define ((binding, Mixfix.NoSyn), ((Binding.suffix_name "_def" binding, []), t))
     #> (fn ((const,(_,thm)),lthy) => (const,thm,lthy))\<close>

ML \<open>fun local_note binding thm = Local_Theory.note ((binding,[]), [thm]) #> snd\<close>
     (* #> (fn ((_,[thm]), lthy) => (thm,lthy))\<close> *)

ML \<open>
(* rel_const must use 'rep, 'abs *)
fun create_transfer_thm ctxt class rel_const rel_const_def_thm = let
  val thy = Proof_Context.theory_of ctxt
  val (class_const, _) = get_params_of_class thy class
  val class_const_def_thm = Proof_Context.get_thm ctxt ((class_const |> dest_Const |> fst) ^ "_def") |> Drule.abs_def
  val class_const = subst_TVars [(("'a",0), TFree("'abs",\<^sort>\<open>type\<close>))] class_const
  val goal = \<^Term>\<open>Trueprop ((rel_fun (\<open>rel_const\<close> r) (\<longleftrightarrow>)) ?X \<open>class_const\<close>)\<close> ctxt
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
    |> lambda (Var(("S",0),HOLogic.mk_setT (TFree("'rep",\<^sort>\<open>type\<close>))))
  in
    (transferred, thm)
  end

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

lemma xxxxx:
  assumes has_dom: \<open>with_type_has_domain class2R D\<close>
  assumes class1_def: \<open>class1 \<equiv> (class1P, class1R)\<close>
  assumes class2_def: \<open>class2 \<equiv> (class2P, class2R)\<close>
  assumes class1P_def: \<open>class1P \<equiv> \<lambda>S p. D S p \<and> pred' S p\<close>
  shows \<open>with_type_compat_rel (fst class1) S (snd class2)\<close>
  using has_dom
  by (simp add: with_type_has_domain_def with_type_compat_rel_def class1_def class2_def class1P_def)



ML \<open>

fun define_stuff pos class lthy = let
  open Conv
  val (_,R,D,has_dom_thm) = get_relation_thm lthy class
  val binding = Binding.make ("with_type_" ^ Class.class_prefix class, pos)
  val (rel_const,rel_def,lthy) = local_def (Binding.suffix_name "_rel" binding) (Type.legacy_freeze R) lthy
  val (dom_const,dom_def,lthy) = local_def (Binding.suffix_name "_dom" binding) (Type.legacy_freeze D) lthy
  fun gen_thm lthy = Morphism.thm (Local_Theory.target_morphism lthy)
  fun gen_term lthy = Morphism.term (Local_Theory.target_morphism lthy)
  fun gen_sym_thm lthy thm = gen_thm lthy thm |> Thm.symmetric
  val has_dom_thm' = has_dom_thm |> fconv_rule (rewr_conv (gen_sym_thm lthy rel_def) |> arg1_conv(*r*) |> arg_conv(*Trueprop*))
                 |> fconv_rule (rewr_conv (gen_sym_thm lthy dom_def) |> arg_conv(*d*) |> arg_conv(*Trueprop*))
  val ((* has_dom_thm'', *)lthy) = local_note (Binding.suffix_name "_has_dom" binding) has_dom_thm' lthy
  val (transferred,transfer_thm) = create_transfer_thm lthy class rel_const rel_def
  val (pred'_const,pred'_def,lthy) = local_def (Binding.suffix_name "_pred'" binding) (Type.legacy_freeze transferred) lthy
  val (pred_const,pred_def,lthy) = local_def (Binding.suffix_name "_pred" binding) 
        (\<^Term>\<open>(\<lambda>S p. \<open>dom_const\<close> S p \<and> \<open>pred'_const\<close> S p)\<close> lthy) lthy
  val (wt_class_const,wt_class_def,lthy) = local_def binding (HOLogic.mk_prod (pred_const, rel_const)) lthy
  val transfer_thm' = (@{thm aux} OF [gen_thm lthy wt_class_def, gen_thm lthy wt_class_def,
      gen_thm lthy pred_def, gen_thm lthy pred'_def, has_dom_thm'] OF [gen_thm lthy transfer_thm])
        |> Thm.eq_assumption 1 |> Thm.eq_assumption 1 |> Thm.eq_assumption 1
  val ((* transfer_thm'', *)lthy) = local_note (Binding.suffix_name "_transfer" binding) transfer_thm' lthy
  val with_compat_rel_thm = @{thm xxxxx} OF (map (gen_thm lthy) [has_dom_thm', wt_class_def, wt_class_def, pred_def])
  val lthy = local_note (Binding.suffix_name "_rel_compat" binding) with_compat_rel_thm lthy
val _ = wt_class_const |> gen_term lthy |> dest_Const |> fst |> \<^print>
  val info : With_Type.with_type_info = {
    class = class,
    rep_class_data = wt_class_const |> gen_term lthy |> dest_Const |> fst,
    with_type_compat_rel = gen_thm lthy with_compat_rel_thm,
    rep_class_data_thm = NONE, (* TODO put something here? *)
    transfer = SOME (gen_thm lthy transfer_thm')
  }
  val lthy = Local_Theory.declaration {syntax=false, pervasive=true} (fn m => fn context =>
    With_Type.add_with_type_info_generic (With_Type.morphism m info) context) lthy 
in
  lthy
end
\<close>


end
