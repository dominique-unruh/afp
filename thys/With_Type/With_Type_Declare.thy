theory With_Type_Declare
  imports With_Type
begin

subsection \<open>Automatic configuration of new class\<close>

lemma bi_unique_left_unique: \<open>bi_unique R \<Longrightarrow> left_unique R\<close>
  by (simp add: bi_unique_alt_def)
lemma bi_unique_right_unique: \<open>bi_unique R \<Longrightarrow> right_unique R\<close>
  by (simp add: bi_unique_alt_def)


ML \<open>
structure With_Type_Declare_Data = Generic_Data (
  type T = { relators: (Proof.context -> (typ -> term) -> typ -> term) Symtab.table }
  val empty = { relators = Symtab.empty }
  fun merge ({relators}, {relators=relators'}) =
    {relators = Symtab.merge (K true) (relators, relators')}
)

fun map_relators_generic f = With_Type_Declare_Data.map (fn {relators} => 
    {relators = f relators})

val get_relators_generic = With_Type_Declare_Data.get #> #relators

fun add_relator_generic typ_name f = map_relators_generic (Symtab.insert (K false) (typ_name, f))

fun add_relator_global typ_name f = Context.theory_map (add_relator_generic typ_name f)

fun get_relator_generic context typ_name = Symtab.lookup (get_relators_generic context) typ_name
fun get_relator ctxt = get_relator_generic (Context.Proof ctxt)


\<close>


ML \<open>
(* TODO: check if Term.strip_comb is a replacement *)
fun dest_args args (t $ u) = dest_args (u :: args) t
  | dest_args args hd = (hd,args)
\<close>

ML \<open>
fun curry_term [] t = Abs("", \<^typ>\<open>unit\<close>, t)
  | curry_term [_] t = t
  | curry_term args t = let
    fun add_args 0 t = t
      | add_args n t = add_args (n-1) (t $ Bound (n-1))
    fun curry [] _ = error "unreachable code"
      | curry [(name,T)] t = Abs (name, T, t)
      | curry ((name,T)::args) t = HOLogic.mk_case_prod (Abs (name, T, curry args t))
    val result = curry args (add_args (length args) t)
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
  val (const,params_ordered) = Class.rules thy class |> fst |> the |> Thm.prop_of
      |> map_types (map_type_tvar (fn (ni,_) => TVar (ni,\<^sort>\<open>type\<close>)))
      |> HOLogic.dest_Trueprop |> dest_args []
  val class_params = Class.these_params thy [class]
  val no_params = null class_params
  val final_params = 
    if no_params then []
    else params_ordered |> map (fn Const (const,T) =>
      get_first (fn (name,(_,(const',_))) => if const=const' then SOME (name,const,T) else NONE) class_params |> the)
  val const_curried = 
    if no_params then Abs("", \<^typ>\<open>unit\<close>, const $ Logic.mk_type (TVar(("'a",0),\<^sort>\<open>type\<close>)))
    else curry_term (map (fn (n,_,T) => (n,T)) final_params) const
in
  (const,const_curried,final_params)
end
;;
get_params_of_class \<^theory> \<^class>\<open>group_add\<close> |> #2 |> Thm.cterm_of \<^context>
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

named_theorems with_type_simps

ML \<open>
fun has_tvar (TVar _) = true
  | has_tvar (Type (_,Ts)) = exists has_tvar Ts
  | has_tvar _ = false
fun has_var_tvar (t$u) = has_var_tvar t orelse has_var_tvar u
  | has_var_tvar (Abs(_,T,body)) = has_tvar T orelse has_var_tvar body
  | has_var_tvar (Const(_,T)) = has_tvar T
  | has_var_tvar (Free(_,T)) = has_tvar T
  | has_var_tvar (Var(_,T)) = true
  | has_var_tvar (Bound _) = false
fun has_tvar' (t$u) = has_tvar' t orelse has_tvar' u
  | has_tvar' (Abs(_,T,body)) = has_tvar T orelse has_tvar' body
  | has_tvar' (Const(_,T)) = has_tvar T
  | has_tvar' (Free(_,T)) = has_tvar T
  | has_tvar' (Var(_,T)) = has_tvar T
  | has_tvar' (Bound _) = false
\<close>


inductive rel_itself :: \<open>'a itself \<Rightarrow> 'b itself \<Rightarrow> bool\<close> 
  where \<open>rel_itself TYPE('a) TYPE('b)\<close>


ML \<open>
fun mk_relation_for_tfree name_fun (n,s) = 
  let val (r,rep,_) = name_fun n in (r, TFree(rep,s) --> TFree(n,s) --> HOLogic.boolT) end
  (* ("r"^n, TFree("'rep"^n,s) --> TFree(n,s) --> HOLogic.boolT) *)
fun mk_relation_replaceT name_fun = 
  map_type_tfree (fn (n,s) => let val (_,rep,_) = name_fun n in TFree(rep,s) end)
fun mk_relation_for_type ctxt name_fun (T:typ) = let
  fun mk T' = case T' of
    TFree(n,s) => mk_relation_for_tfree name_fun (n,s) |> Free
    | Type(_, []) => HOLogic.eq_const T'
    | \<^Type>\<open>itself T\<close> => 
        let val T' = mk_relation_replaceT name_fun T
        in \<^Const>\<open>rel_itself T' T\<close> end
    | Type(name, _) => (case get_relator ctxt name of
                         NONE => raise TYPE("mk_relation_for_type: don't know how to handle type " ^ name, [T,T'], [])
                        | SOME f => \<^try>\<open>f ctxt mk T'
                                    catch e as TYPE _ => raise e
                                         | e => raise TYPE("mk_relation_for_type: handler for type " ^ name ^ " failed with exception " ^ Runtime.exn_message e, [T,T'], [])\<close>)
    | TVar _ => raise TYPE("mk_relation_for_type: encountered schematic type var", [T,T'], [])
  in mk T end
\<close>

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
  val rep_paramT0 = get_params_of_class (Proof_Context.theory_of ctxt) class |> #3 |> map (fn (_,_,T) => T) |> HOLogic.mk_tupleT
  val repT = TFree("'rep",\<^sort>\<open>type\<close>)
 val rep_paramT = TVar(("'rep_param",0),\<^sort>\<open>type\<close>) 
  val absT = TFree("'abs",\<^sort>\<open>type\<close>)
  val abs_paramT = typ_subst_TVars [(("'a",0), absT)] rep_paramT0
  (* val rep_paramT = typ_subst_TVars [(("'a",0), repT)] rep_paramT0 *)
(*   val goal = \<^Const>\<open>with_type_compat_xxx repT absT rep_paramT abs_paramT\<close>
        $ Var(("R",0), (repT --> absT --> HOLogic.boolT) --> (rep_paramT --> abs_paramT --> HOLogic.boolT))
        $ Var(("RR",0), (repT --> repT --> HOLogic.boolT) --> (rep_paramT --> rep_paramT --> HOLogic.boolT))
      |> HOLogic.mk_Trueprop *)
(*   fun name_fun "'abs" = ("r", "'rep", "S")
  val R = mk_relation_for_type ctxt name_fun abs_paramT |> absfree ("r", \<^typ>\<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>)
        (* |> Type.varify_global TFrees.empty |> snd *)
       |> \<^print> *)
  val goal = \<^Const>\<open>with_type_has_domain repT absT rep_paramT abs_paramT\<close>
                 $ Var(("R",0), (repT --> absT --> HOLogic.boolT) --> (rep_paramT --> abs_paramT --> HOLogic.boolT)) 
                (* $ R *)
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
  val simp_rules = @{thms Domainp_rel_fun_equal_onp[abs_def] Domainp_equal_onp} @ (Proof_Context.get_thms ctxt \<^named_theorems>\<open>with_type_simps\<close>)
  val thm = thm |> fconv_rule (Simplifier.rewrite ((clear_simpset ctxt) addsimps simp_rules)
                               |> arg_conv |> HOLogic.Trueprop_conv)
  val (T,R,D) = dest_with_type_has_domain (Thm.prop_of thm)
in
  (T,R,D,thm)
end
\<close>

ML \<open>fun local_def binding t = Local_Theory.define ((binding, Mixfix.NoSyn), ((Binding.suffix_name "_def" binding, []), t))
     #> (fn ((const,(_,thm)),lthy) => (const,thm,lthy))\<close>

ML \<open>fun local_note binding thm = Local_Theory.note ((binding,[]), [thm]) #> snd\<close>
     (* #> (fn ((_,[thm]), lthy) => (thm,lthy))\<close> *)



lemma aux1: 
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes \<open>right_total r\<close>
  assumes \<open>Domainp r = (\<lambda>x. x \<in> S)\<close>
  shows \<open>(rel_set r) S (UNIV :: 'abs set)\<close>
  using assms right_total_UNIV_transfer by fastforce

lemma aux2:
  assumes \<open>(rel_fun R1 R2) X' Y\<close>
  assumes \<open>X == X'\<close>
  shows \<open>(rel_fun R1 R2) X Y\<close>
  by (simp add: assms(1) assms(2))

declare [[eta_contract=false]]

ML \<open>
fun def_ext def = case def |> Thm.prop_of of
  \<^Const_>\<open>Pure.eq _\<close> $ (_ $ Var((name,_),_)) $ _ =>
      Thm.abstract_rule name (Thm.lhs_of def |> Thm.dest_comb |> snd) def 
        |> Conv.fconv_rule Thm.eta_conversion
        |> def_ext
  | _ => def
;;
def_ext @{thm class.comm_monoid_add_def}
\<close>


ML \<open>
(* Returns the definitions of constant `const`, in the following form (if possible):

  `const` TYPE(?'a) ... TYPE(?'n) == stuff

  (I.e., all non-TYPE arguments are moved into stuff)

  and with no sort constraints.
 *)
fun get_raw_definitions ctxt (const:string) = let
  val thy = Proof_Context.theory_of ctxt
  val defs = Thm.all_axioms_of thy |> filter (fn (name,thm) => 
    case Thm.prop_of thm of
      Const(\<^const_name>\<open>Pure.eq\<close>,_) $ lhs $ _ => 
         (case head_of lhs of Const(n,_) => n=const
                               | _ => false)
     | _ => false)
    |> map snd
  val _ = null defs andalso error ("Could not find definition of " ^ const)
  val defs = map def_ext defs
in defs end;;
get_raw_definitions \<^context> \<^const_name>\<open>fst\<close>
;;
get_raw_definitions \<^context> \<^const_name>\<open>class.semigroup_add\<close>
;;
get_raw_definitions \<^context> \<^const_name>\<open>inverse\<close>
\<close>

ML \<open>
fun has_tfree (TFree _) = true
  | has_tfree (Type (_, Ts)) = exists has_tfree Ts
  | has_tfree _ = false
\<close>

setup \<open>
   add_relator_global \<^type_name>\<open>fun\<close> (fn ctxt => fn mk => fn \<^Type>\<open>fun T U\<close> => \<^Term>\<open>rel_fun \<open>mk T\<close> \<open>mk U\<close>\<close> ctxt)
#> add_relator_global \<^type_name>\<open>prod\<close> (fn ctxt => fn mk => fn \<^Type>\<open>prod T U\<close> => \<^Term>\<open>rel_prod \<open>mk T\<close> \<open>mk U\<close>\<close> ctxt)
#> add_relator_global \<^type_name>\<open>set\<close> (fn ctxt => fn mk => fn \<^Type>\<open>set T\<close> => \<^Term>\<open>rel_set \<open>mk T\<close>\<close> ctxt)
\<close>



ML \<open>
fun sortify [] = \<^sort>\<open>type\<close>
  | sortify s = s
fun unvarify_sortify ctxt thm = let
  val tvars = Thm.add_tvars thm TVars.empty
  val inst = TVars.map (fn ((n,0),s) => fn _ => TFree (n,sortify s) |> Thm.ctyp_of ctxt) tvars
  val thm = Thm.instantiate (inst, Vars.empty) thm
in thm end
;;
unvarify_sortify \<^context> (get_raw_definitions \<^context> \<^const_name>\<open>fst\<close> |> hd)
\<close>

ML \<open>
(* Maps tvars to tfrees and sort {} to type *)
val unvarify_sortify' = map_types (map_type_tvar (fn ((n,0),s) => TFree (n,sortify s)))
\<close>

ML \<open>
(* Maps tvars to tfrees, and vars to frees, and sort {} to type *)
val unvarify_sortify'' = 
  unvarify_sortify' #>
  map_aterms (fn Var((v,0),T) => Free(v,T) | t as Var _ => raise TERM ("unvarify_sortify''", [t]) | t => t)
\<close>


lemma RelI:
  assumes \<open>R X Y\<close>
  shows \<open>Transfer.Rel R X Y\<close>
  by (simp add: Rel_def assms)

named_theorems with_type_transfer_rules

lemma with_type_transfer_Ex[with_type_transfer_rules]:
  includes lifting_syntax
  assumes \<open>right_total A\<close>
  assumes \<open>Domainp A = S\<close>
  shows \<open>Transfer.Rel (rel_fun (rel_fun A (=)) (=)) (Bex (Collect S)) Ex\<close>
  by (metis Rel_def assms(1) assms(2) right_total_Ex_transfer)

lemma with_type_transfer_Collect[with_type_transfer_rules]:
  includes lifting_syntax
  assumes \<open>right_total A\<close>
  assumes \<open>Domainp A = S\<close>
  shows \<open>Transfer.Rel (rel_fun (rel_fun A (=)) (rel_set A)) (\<lambda>P. {x. P x \<and> S x}) Collect\<close>
  by (smt (verit, best) Collect_cong Rel_abs Rel_app Rel_def assms(1) assms(2) right_total_Collect_transfer)

lemma with_type_transfer_UNIV[with_type_transfer_rules]:
  includes lifting_syntax
  assumes \<open>right_total A\<close>
  assumes \<open>Domainp A = S\<close>
  shows \<open>Transfer.Rel (rel_set A) (Collect S) UNIV\<close>
  by (metis Rel_def assms(1) assms(2) right_total_UNIV_transfer)

ML \<open>
fun trace_tac ctxt pos str tac i st = let
  val _ = tracing (str ^ Position.here pos ^ " " ^ string_of_int i ^ " " ^ (Thm.cprem_of st i |> Thm.term_of |> Syntax.string_of_term ctxt))
  fun after st' = let
    val new_goals = Thm.prems_of st' |> drop (i-1) |> take (Thm.nprems_of st' - Thm.nprems_of st + 1)
             |> map (Syntax.string_of_term ctxt)
    val _ = tracing (str ^ " -> " ^ String.concatWith "\n" new_goals)
    in Seq.single st end
  in (tac i THEN after) st end
\<close>


ML \<open>
  infix 1 THEN_ALL_BUT_FIRST_NEW
  fun (tac1 THEN_ALL_BUT_FIRST_NEW tac2) i st =
    st |> (tac1 i THEN (fn st' =>
      Seq.INTERVAL tac2 (i + 1) (i + Thm.nprems_of st' - Thm.nprems_of st) st'));

\<close>

ML \<open>
fun error_tac ctxt msg i = SUBGOAL (fn (t,_) => error (msg (Syntax.string_of_term ctxt t))) i
\<close>


ML \<open>
fun create_transfer_for_term ctxt name_fun (term:term) = let
(* val _ = \<^print> (Thm.cterm_of ctxt term) *)
  open Conv
  val _ = has_var_tvar term andalso raise TERM ("create_transfer_for_term: contains schematic (term/type) variables", [term])
  (* val _ = has_tvar' term andalso raise TERM ("create_transfer_for_term: contains schematic type variables", [term]) *)
  val rules = Proof_Context.get_thms ctxt \<^named_theorems>\<open>with_type_transfer_rules\<close> 
                |> rev (* 'rev' has the effect that later rules take priority *)
  val rel = mk_relation_for_type ctxt name_fun (fastype_of term)
  val basic_rels = Term.add_tfrees term [] |> map (mk_relation_for_tfree name_fun)
  (* val basic_rels = Term.add_frees rel [] *)
  fun S_of_rT_name T = T |> range_type |> domain_type |> dest_TFree |> fst |> name_fun |> #3
  fun S_of_rT T  = Free(S_of_rT_name T, domain_type T --> HOLogic.boolT)
  fun S_of_r (_,T) = S_of_rT T
  val assms = basic_rels |> map (fn r =>
      [\<^Term>\<open>Trueprop (bi_unique \<open>Free r\<close>)\<close> ctxt, \<^Term>\<open>Trueprop (right_total \<open>Free r\<close>)\<close> ctxt,
        \<^Term>\<open>Trueprop (Domainp \<open>Free r\<close> = \<open>S_of_r r\<close>)\<close> ctxt]) |> flat
  val goal = \<^Term>\<open>Trueprop (Transfer.Rel \<open>rel\<close> ?X \<open>term\<close>)\<close> ctxt
  fun step_premise_tac ctxt prems i = 
    ((resolve_tac ctxt (prems @ rules) THEN_ALL_NEW step_premise_tac ctxt prems) ORELSE' error_tac ctxt (fn t => "NYI: "^t)) i (* TODO: do something about "NYI" *)
  fun instantiate_rel_tac ctxt = SUBGOAL (fn (t,i) => 
      let val vars = case t of (\<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>Transfer.Rel _ _\<close> $ rel $ _ $ _)) => Term.add_vars rel []
          val inst = map (fn (ni, T) => (ni, mk_relation_for_type ctxt name_fun (T |> range_type |> domain_type) |> Thm.cterm_of ctxt)) vars
          val tac = infer_instantiate ctxt inst |> PRIMITIVE
      in tac end)
  fun step_tac ctxt prems =
    CONVERSION Thm.eta_conversion
     THEN'
     instantiate_rel_tac ctxt
     THEN'
     ((* trace_tac ctxt \<^here> "resolve_tac" *) (resolve_tac ctxt rules)
      (* ORELSE' (resolve_tac ctxt @{thms RelI} THEN' resolve_tac ctxt rules) *)
      ORELSE' error_tac ctxt (fn t => "No transfer rule found for " ^ t))
     THEN_ALL_NEW step_premise_tac ctxt prems
  fun split3s [] = []
    | split3s (x::y::z::rest) = (x,y,z) :: split3s rest
    | split3s _ = raise Match (* Should not happen *)
  fun tac {context=ctxt, prems, ...} = let
      (* We add `left_unique r` and `right_unique r` to the premises because many rules have only one of them as premise *)
    val prems = prems |> split3s |> map (fn (bi_unique, right_total, domain) =>
      [bi_unique, right_total, domain, @{thm bi_unique_left_unique} OF [bi_unique], @{thm bi_unique_right_unique} OF [bi_unique]])
      |> flat
    in
    (resolve_tac ctxt @{thms RelI}
     THEN'
     ((Transfer.transfer_prover_start_tac ctxt)
       THEN_ALL_BUT_FIRST_NEW
       step_tac ctxt prems)
     THEN'
     resolve_tac ctxt @{thms refl}) 1
    end
(* val _ = \<^print> ((map fst basic_rels @ map (S_of_rT_name o snd) basic_rels), map (Thm.cterm_of ctxt) assms, Thm.cterm_of ctxt goal) *)
  val thm = Goal.prove ctxt (map fst basic_rels @ map (S_of_rT_name o snd) basic_rels) assms goal tac
in thm end
\<close>

lemmas RelI' = RelI[of \<open>rel_fun _ _\<close>]


attribute_setup add_Rel = 
  \<open>let val Rel_rule = Thm.symmetric @{thm Rel_def}
       fun Rel_conv ct = let
            val (cT, cT') = Thm.dest_funT (Thm.ctyp_of_cterm ct)
            val (cU, _) = Thm.dest_funT cT'
         in Thm.instantiate' [SOME cT, SOME cU] [SOME ct] Rel_rule end
(*        fun nprems (Const(\<^const_name>\<open>implies\<close>, _) $ _ $ t) = nprems t + 1
         | nprems _ = 0 
       fun final_concl_conv conv ct = Conv.concl_conv (nprems (Thm.term_of ct)) conv ct *)
       fun final_concl_conv conv ct = case Thm.term_of ct of
         Const(\<^const_name>\<open>Pure.imp\<close>,_) $ _ $ _ => Conv.implies_concl_conv (final_concl_conv conv) ct
         | _ => conv ct
       (* val final_concl_conv = Conv.implies_concl_conv *)
       val add_Rel = 
          Rel_conv |> Conv.fun_conv |> Conv.fun_conv |> HOLogic.Trueprop_conv |> final_concl_conv
            |> Conv.fconv_rule
       fun add_Rel' ctxt thm = let val thm' = add_Rel thm
                                   val _ = tracing ("[add_Rel] rewrote to: " ^ (thm' |> Thm.prop_of |> Syntax.string_of_term ctxt))
                               in thm' end
  in Thm.rule_attribute [] (add_Rel' o Context.proof_of) |> Scan.succeed end\<close>
  \<open>Adds Transfer.Rel to a theorem (if possible)\<close>

declare eq_transfer[add_Rel, with_type_transfer_rules]
declare case_prod_transfer[add_Rel, with_type_transfer_rules]
declare prod.bi_unique_rel[with_type_transfer_rules] thm prod.bi_unique_rel

ML \<open>
fun create_transfers_for_const ctxt (const_name:string) = let
  open Conv
  val defs = get_raw_definitions ctxt const_name (*  |> unvarify_sortify lthy *)
  val _ = tracing "Found raw definitions:"
  val _ = List.app (fn thm => thm |> Thm.prop_of |> Syntax.string_of_term ctxt |> tracing) defs
  (* val const = def |> Thm.lhs_of |> Thm.term_of *)
  fun do_one def = let
    val term = def |> Thm.rhs_of |> Thm.term_of |> unvarify_sortify'
    val thm = create_transfer_for_term ctxt (fn n => ("r"^n,"'rep"^n,"S"^n)) term
    val thm = thm |> fconv_rule (rewr_conv (Thm.symmetric def) |> arg_conv |> arg_conv |> concl_conv ~1)
    in thm end
  in map do_one defs end
;;
create_transfers_for_const \<^context> \<^const_name>\<open>fst\<close>
\<close>

ML \<open>
fun bind_transfers_for_const pos (const_name:string) lthy = let
  val thms = create_transfers_for_const lthy const_name
  fun do_one (i,thm) lthy = let
    val thm_name = "with_type_transfer_" ^ String.translate (fn #"." => "_" | c => String.str c) const_name
    val thm_name = if i=0 then thm_name else thm_name ^ "_" ^ string_of_int i
    val binding = Binding.make (thm_name, pos)
    val _ = tracing ("lemma " ^ thm_name ^ "[with_type_transfer_rules]: \<open>" ^ Thm.string_of_thm lthy thm ^ "\<close>")
    val (_,lthy) = Local_Theory.note ((binding, @{attributes [with_type_transfer_rules]}), [thm]) lthy
    in lthy end
  in fold_index do_one thms lthy end
\<close>

declare Lifting_Set.member_transfer[add_Rel, with_type_transfer_rules] thm Lifting_Set.member_transfer

lemma [with_type_transfer_rules]: 
  includes lifting_syntax
  assumes \<open>right_total r\<close>
  assumes \<open>Domainp r = S\<close>
  shows \<open>Transfer.Rel ((r ===> (=)) ===> (=)) (Ball (Collect S)) All\<close>
  using RelI' assms(1) assms(2) right_total_All_transfer by blast

thm right_total_All_transfer
declare right_total_eq[with_type_transfer_rules]
declare bi_unique_rel_set[with_type_transfer_rules]
declare right_total_rel_set[with_type_transfer_rules]

lemma [with_type_transfer_rules]: \<open>Domainp T = DT1 \<Longrightarrow> Domainp (rel_set T) = (\<lambda>A. Ball A DT1)\<close>
  using Domainp_set by auto

lemma [with_type_transfer_rules]: \<open>Domainp T1 = DT1 \<Longrightarrow> Domainp T2 = DT2 \<Longrightarrow> Domainp (rel_prod T1 T2) = pred_prod DT1 DT2\<close>
  using prod.Domainp_rel by auto

(* lemma [with_type_transfer_rules]: \<open>is_equality T1 \<Longrightarrow> Domainp T2 = DT2 \<Longrightarrow> Domainp (rel_fun T1 T2) = pred_fun (\<lambda>_. True) DT2\<close>
  using fun.Domainp_rel
  by (metis is_equality_def) *)

lemma [with_type_transfer_rules]: \<open>left_unique T \<Longrightarrow> Domainp T = DT \<Longrightarrow> Domainp S = DS \<Longrightarrow> Domainp (rel_fun T S) = pred_fun DT DS\<close>
  using Domainp_pred_fun_eq by auto

lemma [with_type_transfer_rules]: \<open>Domainp (=) = (\<lambda>_. True)\<close>
  by auto
(* lemma [with_type_transfer_rules]: \<open>Domainp (=) = (\<lambda>x. x \<in> UNIV)\<close>
  by auto *)
declare bi_unique_eq [with_type_transfer_rules]

(* declare Rel_eq_refl[with_type_transfer_rules] *)

lemma is_equality_Rel_eq_refl[with_type_transfer_rules]: \<open>is_equality R \<Longrightarrow> Transfer.Rel R x x\<close>
  by (rule transfer_raw)

(* ML \<open>create_transfers_for_const \<^context> \<^const_name>\<open>disj\<close>\<close> *)

lemma [with_type_transfer_rules]: \<open>Transfer.Rel (rel_fun A (rel_fun B (rel_prod A B))) Pair Pair\<close>
  by (simp add: Pair_transfer RelI')
lemma [with_type_transfer_rules]: \<open>is_equality A \<Longrightarrow> is_equality B \<Longrightarrow> is_equality (rel_fun A B)\<close>
  by (rule relator_eq_raw)
lemma [with_type_transfer_rules]: \<open>is_equality A \<Longrightarrow> is_equality B \<Longrightarrow> is_equality (rel_prod A B)\<close>
  by (rule relator_eq_raw)
lemma [with_type_transfer_rules]: \<open>is_equality A \<Longrightarrow> is_equality (rel_set A)\<close>
  by (rule relator_eq_raw)
declare is_equality_eq[with_type_transfer_rules]

local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>fst\<close>\<close>
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>snd\<close>\<close>
(* local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>disj\<close>\<close> (* TODO: Should this even be transferred? There is no free type variable here! *) *)
(* thm with_type_transfer_HOL_disj *)
local_setup \<open>bind_transfers_for_const \<^here> \<^const_name>\<open>insert\<close>\<close>

declare Lifting_Set.empty_transfer[add_Rel, with_type_transfer_rules]
declare Lifting_Set.finite_transfer[add_Rel, with_type_transfer_rules]


ML \<open>
(* rel_const must use 'rep, 'abs *)
fun create_transfer_thm ctxt class (* rel_const rel_const_def_thm *) = let
  val thy = Proof_Context.theory_of ctxt
  val (class_const, class_const_curried, _) = get_params_of_class thy class
  (* val class_const_def_thm = Proof_Context.get_thm ctxt ((class_const |> dest_Const |> fst) ^ "_def") |> Drule.abs_def *)
  val class_const_curried = subst_TVars [(("'a",0), TFree("'abs",\<^sort>\<open>type\<close>))] class_const_curried
  fun name_fun "'abs" = ("r", "'rep", "S")
  val thm = create_transfer_for_term ctxt name_fun class_const_curried
  val transferred = thm
    |> Thm.concl_of |> HOLogic.dest_Trueprop
    |> dest_comb |> fst |> dest_comb |> snd
    |> unvarify_sortify'
    |> lambda (Var(("S",0), TFree("'rep",\<^sort>\<open>type\<close>) --> HOLogic.boolT))
  (* Check if all is right: *)
  val tfrees = Term.add_tfrees transferred []
  val _ = tfrees = [("'rep",\<^sort>\<open>type\<close>)]
            orelse raise TERM ("create_transfer_thm: transferred term contains type variables besides 'rep", [transferred, Thm.prop_of thm])
  in
    (transferred, thm)
  end

\<close>

lemma with_type_split_aux:
  includes lifting_syntax
  assumes \<open>(R ===> (\<longleftrightarrow>)) A B\<close>
  assumes \<open>\<And>x. Domainp R x \<Longrightarrow> C x\<close>
  shows \<open>(R ===> (\<longleftrightarrow>)) (\<lambda>x. C x \<and> A x) B\<close>
  by (smt (verit) DomainPI assms(1) assms(2) rel_fun_def)


lemma aux: 
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes class1_def: \<open>class1 \<equiv> (class1P, class1R)\<close>
  assumes class2_def: \<open>class2 \<equiv> (class2P, class2R)\<close>
  assumes class2P_def: \<open>class2P \<equiv> \<lambda>S p. D S p \<and> pred' (\<lambda>x. x \<in> S) p\<close>
  (* assumes pred'_def: \<open>pred' \<equiv> pred''\<close> *)
  (* assumes class1R_def: \<open>class1R \<equiv> class1R'\<close> *)
  assumes wthd: \<open>with_type_has_domain class1R D\<close>
  assumes 1: \<open>\<And>S. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> Domainp r = S \<Longrightarrow>
               Transfer.Rel (class1R r ===> (=)) (pred' S) class_const\<close>
  (* assumes class1R_same: \<open>class1R' = class1R''\<close> *)
  assumes r_assms: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(snd class1 r ===> (\<longleftrightarrow>)) (fst class2 (Collect (Domainp r))) class_const\<close>

  unfolding class1_def class2_def fst_conv snd_conv class2P_def (* pred'_def class1R_def *)
  apply (rule with_type_split_aux)
   (* apply (unfold class1R_same) *)
   apply (rule 1[unfolded Rel_def])
     apply (rule r_assms)
     apply (rule r_assms)
   apply auto[1]
  using wthd
  by (simp add: (* class1R_def class1R_same *) r_assms(1) r_assms(2) with_type_has_domain_def)


lemma xxxxx:
  assumes has_dom: \<open>with_type_has_domain class2R D\<close>
  assumes class1_def: \<open>class1 \<equiv> (class1P, class1R)\<close>
  assumes class2_def: \<open>class2 \<equiv> (class2P, class2R)\<close>
  assumes class1P_def: \<open>class1P \<equiv> \<lambda>S p. D S p \<and> pred' S p\<close>
  shows \<open>with_type_compat_rel (fst class1) S (snd class2)\<close>
  using has_dom
  by (simp add: with_type_has_domain_def with_type_compat_rel_def class1_def class2_def class1P_def)


ML \<open>
val define_stuff_goal = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern \<^context>)
  "bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (rel_fun (snd ?class1 r) (\<longleftrightarrow>)) (fst ?class2 (Collect (Domainp r))) ?class_const"
\<close>

ML \<open>
fun force_fail pos description tac =
  tac ORELSE (fn st => error (description ^ Position.here pos ^ ": " ^ (Thm.cprem_of st 1 |> \<^make_string>)))
\<close>


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
  val has_dom_thm' = has_dom_thm |> fconv_rule (rewr_conv (gen_sym_thm lthy rel_def) |> arg1_conv(*r*) |> HOLogic.Trueprop_conv)
                 |> fconv_rule (rewr_conv (gen_sym_thm lthy dom_def) |> arg_conv(*d*) |> HOLogic.Trueprop_conv)
  val ((* has_dom_thm'', *)lthy) = local_note (Binding.suffix_name "_has_dom" binding) has_dom_thm' lthy
  val (transferred,transfer_thm) = create_transfer_thm lthy class (* rel_const rel_def *)
  val (pred'_const,pred'_def,lthy) = local_def (Binding.suffix_name "_pred'" binding) (Type.legacy_freeze transferred) lthy
  val (pred_const,pred_def, lthy) = local_def (Binding.suffix_name "_pred" binding)
        (\<^Term>\<open>(\<lambda>S p. \<open>dom_const\<close> S p \<and> \<open>pred'_const\<close> (\<lambda>x. x \<in> S) p)\<close> lthy) lthy
  val (wt_class_const,wt_class_def,lthy) = local_def binding (HOLogic.mk_prod (pred_const, rel_const)) lthy

  (* fun ctxt_conv conv_f conv ctxt = conv_f (conv ctxt) *)
  val rel_def_gen = gen_thm lthy rel_def
  val dom_def_gen = gen_thm lthy dom_def
  val pred'_def_gen = gen_thm lthy pred'_def
  val wt_class_def_gen = gen_thm lthy wt_class_def

  val transfer_thm' = Goal.prove lthy ["r"] [] define_stuff_goal
    (fn {context=ctxt,...} => 
  resolve_tac ctxt @{thms aux} 1 |> force_fail \<^here> "internal error"
  THEN solve_tac ctxt [wt_class_def_gen] 1 |> force_fail \<^here> "internal error"
  THEN solve_tac ctxt [wt_class_def_gen] 1 |> force_fail \<^here> "internal error"
  THEN solve_tac ctxt [gen_thm lthy pred_def] 1 |> force_fail \<^here> "internal error"
  THEN CONVERSION (top_sweep_conv (fn _ => rewr_conv rel_def_gen) ctxt) 1 |> force_fail \<^here> "internal error"
  THEN CONVERSION (top_sweep_conv (fn _ => rewr_conv dom_def_gen) ctxt) 1 |> force_fail \<^here> "internal error"
  THEN solve_tac ctxt [has_dom_thm] 1 |> force_fail \<^here> "internal error"
  THEN CONVERSION (top_sweep_conv (fn _ => rewr_conv rel_def_gen) ctxt) 1 |> force_fail \<^here> "internal error"
  THEN CONVERSION (top_sweep_conv (fn _ => rewr_conv pred'_def_gen) ctxt) 1 |> force_fail \<^here> "internal error"
  THEN solve_tac ctxt [transfer_thm] 1 |> force_fail \<^here> "internal error"
  THEN assume_tac ctxt 1 |> force_fail \<^here> "internal error"
  THEN assume_tac ctxt 1 |> force_fail \<^here> "internal error")

  val lthy = local_note (Binding.suffix_name "_transfer" binding) transfer_thm' lthy
  val with_compat_rel_thm = @{thm xxxxx} OF (map (gen_thm lthy) [has_dom_thm', wt_class_def, wt_class_def, pred_def])
  val lthy = local_note (Binding.suffix_name "_rel_compat" binding) with_compat_rel_thm lthy
  val info : With_Type.with_type_info = {
    class = class,
    rep_class_data = wt_class_const |> gen_term lthy |> dest_Const |> fst,
    with_type_compat_rel = gen_thm lthy with_compat_rel_thm,
    rep_class_data_thm = NONE, (* TODO put something here? *)
    transfer = SOME (gen_thm lthy transfer_thm')
  }
  val lthy = Local_Theory.declaration {syntax=false, pervasive=true, pos=pos} (fn m => fn context =>
    With_Type.add_with_type_info_generic (With_Type.morphism m info) context) lthy 
in
  lthy
end
\<close>



end
