(* Collecting stuff to move here *)
theory Tmp_Move
  imports
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    "HOL-Types_To_Sets.T2_Spaces"
    Conditional_Transfer_Rule.CTR
    Types_To_Sets_Extension.SML_Topological_Space
    Types_To_Sets_Extension.SML_Groups
    Types_To_Sets_Extension.VS_Vector_Spaces
begin

declare [[show_sorts=false]]
\<comment> \<open>\<^theory>\<open>HOL-Types_To_Sets.T2_Spaces\<close> leaves @{attribute show_sorts} enabled.\<close>

unbundle lattice_syntax

subsection \<open>Retrieving axioms\<close>

attribute_setup axiom = \<open>Scan.lift Parse.name >> (fn name => Thm.rule_attribute [] 
    (fn context => fn _ => Thm.axiom (Context.theory_of context) name))\<close>
  \<comment> \<open>Retrieves an axiom by name. E.g., write @{thm [source] [[axiom HOL.refl]]}.
      The fully qualified name is required.\<close>

subsection \<open>\<open>class.semigroup_add\<close>\<close>

(* (* TODO minimize assumptions *)
ctr relativization
  synthesis 
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close> 
    and [transfer_rule]: "right_total A"
    and [transfer_rule]: "bi_unique A"
  trp (?'a A)
in class.semigroup_add_def *)

(* definition \<open>semigroup_add_on A plus \<longleftrightarrow>
        (\<forall>a\<in>A.
           \<forall>b\<in>A. \<forall>c\<in>A. plus (plus a b) c = plus a (plus b c))\<close>
  for A plus

lemma semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (=))  
    (semigroup_add_on (Collect (Domainp T)))
    class.semigroup_add"
  unfolding class.semigroup_add_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: semigroup_add_on_def[abs_def]) *)

(* lemma semigroup_add_on_typeclass[simp]: 
  \<open>semigroup_add_on V (+)\<close> for V :: \<open>_::semigroup_add set\<close>
  by (auto simp: semigroup_add_on_def ordered_field_class.sign_simps) *)

subsection \<open>\<open>class.ab_semigroup_add\<close>\<close>

(* ctr relativization
  synthesis 
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close> 
    and [transfer_rule]: "right_total A"
    and [transfer_rule]: "bi_unique A"
  trp (?'a A)
in class.ab_semigroup_add_def
 *)

thm ab_semigroup_add_ow_def

(* definition \<open>ab_semigroup_add_on A plus \<longleftrightarrow>
        semigroup_add_on A plus \<and>
        (\<forall>a\<in>A. \<forall>b\<in>A. plus a b = plus b a)\<close>
  for A plus

lemma ab_semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (=))  
    (ab_semigroup_add_on (Collect (Domainp T)))
    class.ab_semigroup_add"
  unfolding class.ab_semigroup_add_def class.ab_semigroup_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: ab_semigroup_add_on_def[abs_def]) *)

(* lemma ab_semigroup_add_on_typeclass[simp]: \<open>ab_semigroup_add_on V (+)\<close> for V :: \<open>_::ab_semigroup_add set\<close>
  by (auto simp: ab_semigroup_add_on_def Groups.add_ac) *)

subsection \<open>\<open>class.comm_monoid_add\<close>\<close>

(* definition \<open>comm_monoid_add_on A plus zero \<longleftrightarrow>
        ab_semigroup_add_on A plus \<and> (\<forall>a\<in>A. plus zero a = a)\<close>
  for A plus zero

lemma comm_monoid_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T ===> (=))  
    (comm_monoid_add_on (Collect (Domainp T)))
    class.comm_monoid_add"
  unfolding class.comm_monoid_add_def class.comm_monoid_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: comm_monoid_add_on_def[abs_def])

lemma comm_monoid_add_on_typeclass[simp]: \<open>comm_monoid_add_on V (+) 0\<close> for V :: \<open>_::comm_monoid_add set\<close>
  by (auto simp: comm_monoid_add_on_def) *)

subsection \<open>\<open>class.ab_group_add\<close>\<close>

(* definition \<open>ab_group_add_on A plus zero minus uminus \<longleftrightarrow>
        comm_monoid_add_on A plus zero \<and>
        (\<forall>a\<in>A. plus (uminus a) a = zero) \<and>
        (\<forall>a\<in>A. \<forall>b\<in>A. minus a b = plus a (uminus b))\<close>
  for A plus zero minus uminus

lemma ab_group_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (=))  
    (ab_group_add_on (Collect (Domainp T)))
    class.ab_group_add"
  unfolding class.ab_group_add_def class.ab_group_add_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: ab_group_add_on_def[abs_def]) *)

(* lemma ab_group_add_on_typeclass[simp]: \<open>ab_group_add_on V (+) 0 (-) uminus\<close> for V :: \<open>_::ab_group_add set\<close>
  by (auto simp: ab_group_add_on_def) *)

thm ab_group_add_ow_def

subsection \<open>\<open>class.scaleC\<close>\<close>

locale scaleR_ow = 
  fixes U and scaleR :: \<open>real \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes scaleR_closed: \<open>\<forall>a \<in> U. scaleR r a \<in> U\<close>

lemma scaleR_ow_typeclass[simp]: \<open>scaleR_ow UNIV scaleR\<close> for scaleR
  by (simp add: scaleR_ow_def)

locale scaleC_ow = scaleR_ow +
  fixes scaleC
  assumes scaleC_closed: \<open>\<forall>a\<in>U. scaleC c a \<in> U\<close>
  assumes \<open>\<forall>a\<in>U. scaleR r a = scaleC (complex_of_real r) a\<close>

(* definition \<open>scaleC_on A scaleR scaleC \<longleftrightarrow> (\<forall>r. \<forall>a\<in>A. scaleR r a = scaleC (complex_of_real r) a)\<close>
  for scaleR scaleC *)

lemma class_scaleC_ow_typeclass: \<open>class.scaleC scaleR scaleC = scaleC_ow UNIV scaleR scaleC\<close> for scaleR scaleC
  by (auto simp add: class.scaleC_def scaleC_ow_def scaleC_ow_axioms_def)

lemma aux: \<open>P \<equiv> Q \<Longrightarrow> P \<equiv> (\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. f x y \<in> UNIV) \<and> Q\<close>
  by simp         

(* We would like to use `ctr parametricity in scaleR_ow_def` here but that command produces
   an unnecessary `bi_total A` assumption. Similarly for many other ctr-commands below. *)
ctr relativization
synthesis ctr_blank
assumes [transfer_rule]: \<open>bi_unique A\<close>
trp (?'a A)
in scaleR_ow_def

(* lemma scaleR_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> ((=) ===> T ===> T) ===> (=)) scaleR_ow scaleR_ow"
  unfolding scaleR_ow_def 
  by transfer_prover *)

ctr relativization
synthesis ctr_blank
assumes [transfer_rule]: \<open>bi_unique A\<close>
trp (?'a A)
in scaleC_ow_def[unfolded scaleC_ow_axioms_def]

(* lemma scaleC_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (=))  
    scaleC_ow
    scaleC_ow"
  unfolding scaleC_ow_def scaleC_ow_axioms_def
  by transfer_prover *)

(* lemma scaleC_on_typeclass[simp]: \<open>scaleC_on V ( *\<^sub>R) ( *\<^sub>C)\<close>
  by (auto simp: scaleC_ow_def scaleR_scaleC) *)

subsection \<open>\<open>class.complex_vector\<close>\<close>

lemma [simp]: \<open>VS_Groups.semigroup_add_ow = SML_Semigroups.semigroup_add_ow\<close>
  by (auto intro!: ext simp: SML_Semigroups.semigroup_add_ow_def VS_Groups.semigroup_add_ow_def
      plus_ow_def semigroup_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.ab_semigroup_add_ow = SML_Semigroups.ab_semigroup_add_ow\<close>
  by (auto intro!: ext simp: SML_Semigroups.ab_semigroup_add_ow_def VS_Groups.ab_semigroup_add_ow_def
      VS_Groups.ab_semigroup_add_ow_axioms_def SML_Semigroups.ab_semigroup_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.comm_monoid_add_ow = SML_Monoids.comm_monoid_add_ow\<close>
  by (auto intro!: ext simp: SML_Monoids.comm_monoid_add_ow_def VS_Groups.comm_monoid_add_ow_def
      VS_Groups.comm_monoid_add_ow_axioms_def SML_Semigroups.ab_semigroup_add_ow_axioms_def
      zero_ow_def neutral_ow_def SML_Monoids.comm_monoid_add_ow_axioms_def)

lemma [simp]: \<open>VS_Groups.ab_group_add_ow = SML_Groups.ab_group_add_ow\<close>
  apply (auto intro!: ext simp: SML_Groups.ab_group_add_ow_def VS_Groups.ab_group_add_ow_def
      VS_Groups.ab_group_add_ow_axioms_def minus_ow_def uminus_ow_def SML_Groups.ab_group_add_ow_axioms_def)
  by (metis SML_Monoids.comm_monoid_add_ow.axioms(1) SML_Semigroups.ab_semigroup_add_ow.axioms(1) plus_ow.plus_closed semigroup_add_ow.axioms(1))

lemma class_real_vector_with[ud_with]: \<open>class.real_vector plus zero minus uminus scaleR \<longleftrightarrow> vector_space_ow UNIV plus zero minus uminus scaleR\<close>
  for plus zero minus uminus scaleR
  by (auto simp add: class.real_vector_def ab_group_add_ow vector_space_ow_def
      class.real_vector_axioms_def vector_space_ow_axioms_def)

locale complex_vector_ow = vector_space_ow U plus zero minus uminus scaleC + scaleC_ow U scaleR scaleC
  for U scaleR scaleC plus zero minus uminus

lemma class_scaleC_with[ud_with]: \<open>class.scaleC = scaleC_ow UNIV\<close>
  by (auto intro!: ext simp: class.scaleC_def scaleC_ow_def scaleR_ow_def scaleC_ow_axioms_def)

lemma class_complex_vector_with[ud_with]: \<open>class.complex_vector scaleR scaleC plus zero minus uminus 
  \<longleftrightarrow> complex_vector_ow UNIV scaleR scaleC plus zero minus uminus\<close>
  for scaleR scaleC plus zero minus uminus
  by (auto simp: class.complex_vector_def vector_space_ow_def vector_space_ow_axioms_def
      class.complex_vector_axioms_def class.scaleC_def complex_vector_ow_def
      SML_Groups.ab_group_add_ow class_scaleC_with)

(* definition \<open>complex_vector_on A scaleR scaleC plus zero minus uminus \<longleftrightarrow>
        scaleC_on A scaleR scaleC \<and>
        ab_group_add_on A plus zero minus uminus \<and>
                 (\<forall>a. \<forall>x\<in>A. \<forall>y\<in>A. scaleC a (plus x y) = plus (scaleC a x) (scaleC a y)) \<and>
          (\<forall>a. \<forall>b. \<forall>x\<in>A. scaleC (a + b) x = plus (scaleC a x) (scaleC b x)) \<and>
         (\<forall>a. \<forall>b. \<forall>x\<in>A. scaleC a (scaleC b x) = scaleC (a * b) x) \<and> (\<forall>x\<in>A. scaleC 1 x = x)\<close>
  for A scaleR scaleC plus zero minus uminus
*)

thm class.complex_vector_def

(* ctr parametricity in vector_space_ow_axioms_def *)
(* ctr parametricity in vector_space_ow_def *)
(* 
lemma vector_space_ow[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows \<open>(rel_set T ===>
      (T ===> T ===> T) ===>
      T ===> (T ===> T ===> T) ===> (T ===> T) ===> ((=) ===> T ===> T) ===> (=))
      vector_space_ow vector_space_ow\<close>
  unfolding vector_space_ow_def vector_space_ow_axioms_def
  apply transfer_prover_start
       apply transfer_step+
 *)

(* Simplify with these theorems to (try to) change all \<open>\<forall>x. ...\<close> into \<open>\<forall>x\<in>S. ...\<close>
  to enable automated creation of parametricity rules without `bi_total` assumptions. *)
lemma make_balls:
  shows \<open>(\<forall>x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q x))\<close>
    and \<open>(\<forall>x. x \<in> S \<longrightarrow> Q x) \<longleftrightarrow> (\<forall>x\<in>S. Q x)\<close>
    and \<open>(\<forall>x\<subseteq>S. R x) \<longleftrightarrow> (\<forall>x\<in>Pow S. R x)\<close>
    and \<open>{x\<in>S. Q x} = Set.filter Q S\<close>
    and \<open>{x. x \<subseteq> S \<and> R x} = Set.filter R (Pow S)\<close>
  by auto

ctr parametricity in VS_Groups.semigroup_add_ow_def[simplified make_balls]
ctr parametricity in VS_Groups.ab_semigroup_add_ow_def[simplified VS_Groups.ab_semigroup_add_ow_axioms_def make_balls]
ctr parametricity in VS_Groups.comm_monoid_add_ow_def[simplified VS_Groups.comm_monoid_add_ow_axioms_def make_balls]
ctr parametricity in VS_Groups.ab_group_add_ow_def[simplified VS_Groups.ab_group_add_ow_axioms_def make_balls]
ctr parametricity in vector_space_ow_def[simplified vector_space_ow_axioms_def make_balls]
ctr parametricity in complex_vector_ow_def

(* lemma complex_vector_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (=))  
    complex_vector_ow
    complex_vector_ow"
  unfolding complex_vector_ow_def class.complex_vector_def class.complex_vector_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: complex_vector_ow_def[abs_def]) *)


(* lemma complex_vector_on_typeclass[simp]: 
  \<open>complex_vector_on V ( *\<^sub>R) ( *\<^sub>C) (+) 0 (-) uminus\<close> for V :: \<open>_::complex_vector set\<close>
  by (auto simp add: complex_vector_on_def complex_vector.vector_space_assms)
 *)

lemma module_on_typeclass[simp]: \<open>module_on V (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  by (auto simp add: module_on_def scaleC_add_right scaleC_add_left
      complex_vector.subspace_add complex_vector.subspace_0 complex_vector.subspace_scale)

lemma vector_space_on_typeclass[simp]: \<open>vector_space_on V (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  by (simp add: vector_space_on_def)

lemma vector_space_ow_typeclass[simp]: 
  \<open>vector_space_ow V (+) 0 (-) uminus (*\<^sub>C)\<close> if [simp]: \<open>csubspace V\<close>
  for V :: \<open>_::complex_vector set\<close>
  by (simp add: implicit_vector_space_ow)

lemma complex_vector_ow_typeclass[simp]:
  \<open>complex_vector_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus\<close> if [simp]: \<open>csubspace V\<close>
  by (auto intro!: scaleC_ow_def simp add: complex_vector_ow_def scaleC_ow_def 
      scaleC_ow_axioms_def scaleR_ow_def scaleR_scaleC complex_vector.subspace_scale)

lemma csubspace_nonempty: \<open>csubspace X \<Longrightarrow> X \<noteq> {}\<close>
  sorry

subsection \<open>class.open_uniformity\<close>

locale open_uniformity_ow = "open" "open" + uniformity uniformity
  for A "open" uniformity +
  assumes open_uniformity:
    "\<And>U. U \<subseteq> A \<Longrightarrow> open U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

ctr parametricity in open_uniformity_ow_def[simplified make_balls]

(* ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close> 
    and [transfer_rule]: "right_total A"
    and [transfer_rule]: "bi_unique A"
  trp (?'a A)
in class.open_uniformity_def *)

(* 
definition \<open>open_uniformity_on A open uniformity \<longleftrightarrow>
  (\<forall>U\<subseteq>A. open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U))\<close>
  for A "open" uniformity
*)

lemma class_open_uniformity_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_filter (rel_prod T T) ===> (=)) 
    (open_uniformity_ow (Collect (Domainp T)))
    class.open_uniformity"
  unfolding class.open_uniformity_def
  apply transfer_prover_start
  apply transfer_step+
  apply (auto intro!: ext simp: open_uniformity_ow_def)
  by blast+


lemma open_uniformity_on_typeclass[simp]: 
  fixes V :: \<open>_::open_uniformity set\<close>
  assumes \<open>closed V\<close>
  shows \<open>open_uniformity_ow V (openin (top_of_set V)) (uniformity_on V)\<close>
proof (rule open_uniformity_ow.intro, intro allI impI iffI ballI)
  fix U assume \<open>U \<subseteq> V\<close>
  assume \<open>openin (top_of_set V) U\<close>
  then obtain T where \<open>U = T \<inter> V\<close> and \<open>open T\<close>
    by (metis Int_ac(3) openin_open)
  with open_uniformity 
  have *: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> T\<close> if \<open>x \<in> T\<close> for x
    using that by blast
  have \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_inf_principal[THEN iffD2])
    using *[of x] apply (rule eventually_rev_mp)
    using \<open>U = T \<inter> V\<close> that by (auto intro!: always_eventually)
  then show \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    using that by blast
next
  fix U assume \<open>U \<subseteq> V\<close>
  assume asm: \<open>\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close>
  from asm[rule_format]
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' \<in> V \<and> y \<in> V \<and> x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    unfolding eventually_inf_principal
    apply (rule eventually_rev_mp)
    using that by (auto intro!: always_eventually)
  then have xU: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_rev_mp)
    using that \<open>U \<subseteq> V\<close> by (auto intro!: always_eventually)
  have \<open>open (-V)\<close>
    using assms by auto
  with open_uniformity
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> -V\<close> if \<open>x \<in> -V\<close> for x
    using that by blast
  then have xV: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> -V\<close> for x
    apply (rule eventually_rev_mp)
     apply (rule that)
    apply (rule always_eventually)
    by auto
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U \<union> -V\<close> for x
    using xV[of x] xU[of x] that
    by auto
  then have \<open>open (U \<union> -V)\<close>
    using open_uniformity by blast
  then show \<open>openin (top_of_set V) U\<close>
    using \<open>U \<subseteq> V\<close>
    by (auto intro!: exI simp: openin_open)
qed

subsection \<open>\<open>class.uniformity_dist\<close>\<close>

lemma top_filter_parametric':
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  shows \<open>rel_filter r (principal (Collect S)) \<top>\<close>
proof (rule rel_filter.intros)
  define Z where \<open>Z = principal {(x,y). r x y}\<close>
  show \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: eventually_principal Z_def)
  show \<open>map_filter_on {(x, y). r x y} fst Z = principal (Collect S)\<close>
    using \<open>Domainp r = S\<close> by (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
  show \<open>map_filter_on {(x, y). r x y} snd Z = \<top>\<close>
    apply (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
    by (metis assms(2) right_totalE)
qed

lemma Domainp_rel_filter:
  assumes \<open>Domainp r = S\<close>
  shows \<open>Domainp (rel_filter r) F \<longleftrightarrow> (F \<le> principal (Collect S))\<close>
proof (intro iffI, elim Domainp.cases, hypsubst)
  fix G 
  assume \<open>rel_filter r F G\<close>
  then obtain Z where rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    and ZF: "map_filter_on {(x, y). r x y} fst Z = F" 
    and "map_filter_on {(x, y). r x y} snd Z = G"
    using rel_filter.simps by blast
  show \<open>F \<le> principal (Collect S)\<close>
    using rZ apply (auto simp flip: ZF assms intro!: filter_leI 
        simp: eventually_principal eventually_map_filter_on)
    by (smt (verit, best) DomainPI case_prod_beta eventually_elim2)
next
  assume asm: \<open>F \<le> principal (Collect S)\<close>
  define Z where \<open>Z = inf (filtercomap fst F) (principal {(x, y). r x y})\<close>
  have rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: Z_def eventually_inf_principal)
  moreover 
  have \<open>(\<forall>\<^sub>F x in Z. P (fst x) \<and> (case x of (x, xa) \<Rightarrow> r x xa)) = eventually P F\<close> for P
    using asm apply (auto simp add: le_principal Z_def eventually_inf_principal eventually_filtercomap)
    by (smt (verit, del_insts) DomainpE assms eventually_elim2)
  then have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    by (simp add: filter_eq_iff eventually_map_filter_on rZ)
  ultimately show \<open>Domainp (rel_filter r) F\<close>
    by (auto simp: Domainp_iff intro!: exI rel_filter.intros)
qed

lemma Inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  (* assumes \<open>Domainp r = S\<close> *)
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_set (rel_filter r) ===> rel_filter r)
     (\<lambda>M. inf (Inf M) (principal (Collect (Domainp r))))
     Inf\<close>
proof (rule rel_funI)
  fix Fs Gs
  assume asm[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  define S where \<open>S = Domainp r\<close>
  show \<open>rel_filter r (inf (Inf Fs) (principal (Collect S))) (Inf Gs)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by (metis asm empty_iff equals0I rel_setD2)
    show ?thesis
      using assms by (simp add: True S_def \<open>Gs = {}\<close> top_filter_parametric')
  next
    case False
    then have \<open>Gs \<noteq> {}\<close>
      by (metis asm ex_in_conv rel_setD1)
    have dom: \<open>Domainp (rel_filter r) F = (F \<le> principal (Collect S))\<close> for F
      by (simp add: Domainp_rel_filter S_def)
    have 1: \<open>(rel_filter r)
       (Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F})
       (Inf Gs)\<close> (is \<open>(rel_filter r) ?I _\<close>)
      unfolding Inf_filter_def[abs_def]
      by transfer_prover
    have \<open>F \<le> principal (Collect S)\<close> if \<open>F \<in> Fs\<close> for F
      by (meson DomainPI asm dom rel_setD1 that)
    have \<open>?I = (inf (Inf Fs) (principal (Collect S)))\<close>
      unfolding dom Inf_filter_def
      apply auto
      apply (rule antisym)
      apply auto
        apply (simp add: Collect_mono_iff Sup_subset_mono)
      apply (metis (no_types, lifting) Sup_least mem_Collect_eq)
      by (smt (verit, del_insts) Collect_mono False Sup_subset_mono \<open>\<And>Fa. Fa \<in> Fs \<Longrightarrow> Fa \<le> principal (Collect S)\<close> bot.extremum_unique dual_order.refl inf.bounded_iff order_trans subsetI)
    show ?thesis
      using "1" \<open>Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F} = inf (Inf Fs) (principal (Collect S))\<close> by fastforce
  qed
qed


locale uniformity_dist_ow = dist dist + uniformity uniformity for U dist uniformity +
  assumes uniformity_dist: "uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>U\<times>U. dist x y < e})"


(* definition \<open>transfer_bounded_Collect B P = {x\<in>B. P x}\<close>
lemma transfer_bounded_Collect_parametricity[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set T ===> (T ===> bool) ===> rel_set T) transfer_bounded_Collect transfer_bounded_Collect\<close> *)

definition \<open>transfer_Times A B = A \<times> B\<close>
lemma transfer_Times_parametricity[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set T ===> rel_set U ===> rel_set (rel_prod T U)) transfer_Times transfer_Times\<close>
  by (auto intro!: rel_funI simp add: transfer_Times_def rel_set_def)

definition \<open>transfer_bounded_filter_Inf B M = Inf M \<sqinter> principal B\<close>
lemma Inf_transfer_bounded_filter_Inf: \<open>Inf M = transfer_bounded_filter_Inf UNIV M\<close>
  by (metis inf_top.right_neutral top_eq_principal_UNIV transfer_bounded_filter_Inf_def)

lemma Inf_bounded_transfer_bounded_filter_Inf:
  assumes \<open>\<And>F. F \<in> M \<Longrightarrow> F \<le> principal B\<close>
  assumes \<open>M \<noteq> {}\<close>
  shows \<open>Inf M = transfer_bounded_filter_Inf B M\<close>
  by (simp add: Inf_less_eq assms(1) assms(2) inf_absorb1 transfer_bounded_filter_Inf_def)

lemma filtermap_cong: 
  assumes \<open>\<forall>\<^sub>F x in F. f x = g x\<close>
  shows \<open>filtermap f F = filtermap g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_filtermap)
  by (smt (verit, del_insts) assms eventually_elim2)


lemma filtermap_INF_eq: 
  assumes inj_f: \<open>inj_on f X\<close>
  assumes B_nonempty: \<open>B \<noteq> {}\<close>
  assumes F_bounded: \<open>\<And>b. b\<in>B \<Longrightarrow> F b \<le> principal X\<close>
  shows \<open>filtermap f (\<Sqinter> (F ` B)) = (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
proof (rule antisym)
  show \<open>filtermap f (\<Sqinter> (F ` B)) \<le> (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
    by (rule filtermap_INF)
  define f1 where \<open>f1 = inv_into X f\<close>
  have f1f: \<open>x \<in> X \<Longrightarrow> f1 (f x) = x\<close> for x
    by (simp add: inj_f f1_def)
  have ff1: \<open>x \<in> f ` X \<Longrightarrow> x = f (f1 x)\<close> for x
    by (simp add: f1_def f_inv_into_f)

  have \<open>filtermap f (F b) \<le> principal (f ` X)\<close> if \<open>b \<in> B\<close> for b
    by (metis F_bounded filtermap_mono filtermap_principal that)
  then have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> (\<Sqinter>b\<in>B. principal (f ` X))\<close>
    by (simp add: INF_greatest INF_lower2) 
  also have \<open>\<dots> = principal (f ` X)\<close>
    by (simp add: B_nonempty)
  finally have \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x \<in> f ` X\<close>
    using B_nonempty le_principal by auto
  then have *: \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x = f (f1 x)\<close>
    apply (rule eventually_mono)
    by (simp add: ff1)

  have \<open>\<forall>\<^sub>F x in F b. x \<in> X\<close> if \<open>b \<in> B\<close> for b
    using F_bounded le_principal that by blast
  then have **: \<open>\<forall>\<^sub>F x in F b. f1 (f x) = x\<close> if \<open>b \<in> B\<close> for b
    apply (rule eventually_mono)
    using that by (simp_all add: f1f)

  have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) = filtermap f (filtermap f1 (\<Sqinter>b\<in>B. filtermap f (F b)))\<close>
    apply (simp add: filtermap_filtermap)
    using * by (rule filtermap_cong[where f=id, simplified])
  also have \<open>\<dots> \<le> filtermap f (\<Sqinter>b\<in>B. filtermap f1 (filtermap f (F b)))\<close>
    apply (rule filtermap_mono)
    by (rule filtermap_INF)
  also have \<open>\<dots> = filtermap f (\<Sqinter>b\<in>B. F b)\<close>
    apply (rule arg_cong[where f=\<open>filtermap _\<close>])
    apply (rule INF_cong, rule refl)
    unfolding filtermap_filtermap
    using ** by (rule filtermap_cong[where g=id, simplified])
  finally show \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> filtermap f (\<Sqinter> (F ` B))\<close>
    by -
qed

lemma filtermap_inf_eq:
  assumes \<open>inj_on f X\<close>
  assumes \<open>F1 \<le> principal X\<close>
  assumes \<open>F2 \<le> principal X\<close>
  shows \<open>filtermap f (F1 \<sqinter> F2) = filtermap f F1 \<sqinter> filtermap f F2\<close>
proof -
  have \<open>filtermap f (F1 \<sqinter> F2) = filtermap f (INF F\<in>{F1,F2}. F)\<close>
    by simp
  also have \<open>\<dots> = (INF F\<in>{F1,F2}. filtermap f F)\<close>
    apply (rule filtermap_INF_eq[where X=X])
    using assms by auto
  also have \<open>\<dots> = filtermap f F1 \<sqinter> filtermap f F2\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma map_filter_on_cong:
  assumes [simp]: \<open>\<forall>\<^sub>F x in F. x \<in> D\<close>
  assumes \<open>\<And>x. x \<in> D \<Longrightarrow> f x = g x\<close>
  shows \<open>map_filter_on D f F = map_filter_on D g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_map_filter_on)
  apply (rule eventually_subst)
  apply (rule always_eventually)
  using assms(2) by auto 

lemma transfer_bounded_filter_Inf_parametric[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>(rel_set r ===> rel_set (rel_filter r) ===> rel_filter r)
     transfer_bounded_filter_Inf transfer_bounded_filter_Inf\<close>
proof (intro rel_funI, unfold transfer_bounded_filter_Inf_def)
  fix BF BG assume BFBG[transfer_rule]: \<open>rel_set r BF BG\<close>
  fix Fs Gs assume FsGs[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  define D R where \<open>D = Collect (Domainp r)\<close> and \<open>R = Collect (Rangep r)\<close>
  
  have \<open>rel_set r D R\<close>
    by (smt (verit) D_def DomainPI DomainpE R_def RangePI Rangep.simps ctr_simps_mem_Collect_eq rel_setI)
  with \<open>bi_unique r\<close>
  obtain f where \<open>R = f ` D\<close> and [simp]: \<open>inj_on f D\<close> and rf0: \<open>x\<in>D \<Longrightarrow> r x (f x)\<close> for x
    using bi_unique_rel_set_lemma
    by metis
  have rf: \<open>r x y \<longleftrightarrow> x \<in> D \<and> f x = y\<close> for x y
    apply (auto simp: rf0)
    using D_def apply auto[1]
    using D_def assms bi_uniqueDr rf0 by fastforce

  from BFBG
  have \<open>BF \<subseteq> D\<close>
    by (metis D_def Domainp.simps Domainp_set ctr_simps_mem_Collect_eq subsetI)

  have G: \<open>G = filtermap f F\<close> if \<open>rel_filter r F G\<close> for F G
    using that proof cases
    case (1 Z)
    then have Z[simp]: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
      by -
    then have \<open>filtermap f F = filtermap f (map_filter_on {(x, y). r x y} fst Z)\<close>
      using 1 by simp
    also have \<open>\<dots> = map_filter_on {(x, y). r x y} (f \<circ> fst) Z\<close>
      unfolding map_filter_on_UNIV[symmetric]
      apply (subst map_filter_on_comp)
      using Z by simp_all
    also have \<open>\<dots> = G\<close>
      apply (simp add: o_def rf)
      apply (subst map_filter_on_cong[where g=snd])
      using Z apply (rule eventually_mono)
      using 1 by (auto simp: rf)
    finally show ?thesis
      by simp
  qed

  have rf_filter: \<open>rel_filter r F G \<longleftrightarrow> F \<le> principal D \<and> filtermap f F = G\<close> for F G
    apply (intro iffI conjI)
      apply (metis D_def DomainPI Domainp_rel_filter)
    using G apply simp
    by (metis D_def Domainp_iff Domainp_rel_filter G)

  have FD: \<open>F \<le> principal D\<close> if \<open>F \<in> Fs\<close> for F
    by (meson FsGs rel_setD1 rf_filter that)

  from BFBG
  have [simp]: \<open>BG = f ` BF\<close>
    by (auto simp: rel_set_def rf)

  from FsGs
  have [simp]: \<open>Gs = filtermap f ` Fs\<close>
    using G apply (auto simp: rel_set_def rf)
    by fastforce

  show \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (\<Sqinter> Gs \<sqinter> principal BG)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by transfer
    have \<open>rel_filter r (principal BF) (principal BG)\<close>
      by transfer_prover
    with True \<open>Gs = {}\<close> show ?thesis
      by simp
  next
    case False
    note False[simp]
    then have [simp]: \<open>Gs \<noteq> {}\<close>
      by transfer
    have \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (filtermap f (\<Sqinter> Fs \<sqinter> principal BF))\<close>
      apply (rule rf_filter[THEN iffD2])
      by (simp add: \<open>BF \<subseteq> D\<close> le_infI2)
    then show ?thesis
      using FD \<open>BF \<subseteq> D\<close>
      by (simp add: Inf_less_eq 
          flip: filtermap_inf_eq[where X=D] filtermap_INF_eq[where X=D] flip: filtermap_principal)
  qed
qed

(* 

definition \<open>transfer_bounded_Inf B S = Inf (B \<inter> S)\<close>
thm transfer_bounded_Inf_def
term transfer_bounded_Inf

 *)
lemma uniformity_dist_ow_def2:
  fixes U dist uniformity
  shows "uniformity_dist_ow U dist uniformity \<longleftrightarrow> 
          uniformity = transfer_bounded_filter_Inf (transfer_Times U U)
              ((\<lambda>e. principal (Set.filter (\<lambda>(x,y). dist x y < e) (transfer_Times U U))) ` {0<..})"
  unfolding uniformity_dist_ow_def transfer_Times_def[symmetric] make_balls case_prod_unfold
    prod.collapse
  apply (subst Inf_bounded_transfer_bounded_filter_Inf[where B=\<open>U\<times>U\<close>])
  by (auto simp: transfer_Times_def)

(* (* `ctr parametricity in uniformity_dist_ow_def` says `Unexpected format. Not of form Const (HOL.Trueprop, _) $ _`
   so we do things by hand. *)
lemma class_uniformity_dist_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (=)) 
    uniformity_dist_ow uniformity_dist_ow"
  unfolding uniformity_dist_ow_def2 transfer_Times_def[symmetric] make_balls case_prod_unfold
    prod.collapse
  apply transfer_prover_start
              apply transfer_step+
  by simp
 *)

ctr parametricity in uniformity_dist_ow_def2

(* definition \<open>uniformity_dist_on A dist uniformity \<longleftrightarrow>
        uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>A\<times>A. dist x y < e})\<close>
  for dist uniformity *)

thm class.uniformity_dist_def

(* lemma class_uniformity_dist_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (=)) 
    (uniformity_dist_ow (Collect (Domainp T)))
    class.uniformity_dist"
  unfolding class.uniformity_dist_def 
  apply transfer_prover_start
  apply transfer_step+
  apply (intro ext)
  apply (simp add: case_prod_unfold pred_prod_beta uniformity_dist_ow_def
        flip: INF_inf_const2)
  apply (rule arg_cong[where f=\<open>\<lambda>\<gamma>. _ = (INF x\<in>_. principal (\<gamma> x))\<close>])
  by (auto intro!: ext simp: prod.Domainp_rel) *)


lemma uniformity_dist_on_typeclass[simp]: \<open>uniformity_dist_ow V dist (uniformity_on V)\<close> for V :: \<open>_::uniformity_dist set\<close>
  apply (auto simp add: uniformity_dist_ow_def uniformity_dist simp flip: INF_inf_const2)
  apply (subst asm_rl[of \<open>\<And>x. Restr {(xa, y). dist xa y < x} V = {(xa, y). xa \<in> V \<and> y \<in> V \<and> dist xa y < x}\<close>, rule_format])
  by auto

subsection \<open>\<open>class.sgn_div_norm\<close>\<close>

locale sgn_ow =
  fixes U and sgn :: \<open>'a \<Rightarrow> 'a\<close>
  assumes sgn_closed: \<open>\<forall>a\<in>U. sgn a \<in> U\<close>

ctr parametricity in sgn_ow_def

(* lemma sgn_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T) ===> (=))  
    sgn_ow sgn_ow"
  unfolding sgn_ow_def
  by transfer_prover *)

locale sgn_div_norm_ow = scaleR_ow U scaleR + norm norm + sgn_ow U sgn for U norm sgn scaleR +
  assumes sgn_div_norm: "\<forall>x\<in>U. sgn x = scaleR (inverse (norm x)) x"

(* definition \<open>sgn_div_norm_on A sgn norm scaleR
                  \<longleftrightarrow> (\<forall>x\<in>A. sgn x = scaleR (inverse (norm x)) x)\<close>
  for A sgn norm scaleR *)

ctr parametricity in sgn_div_norm_ow_def[unfolded sgn_div_norm_ow_axioms_def]

lemma sgn_div_norm_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_set T ===> (T ===> (=)) ===> (T ===> T) ===> ((=) ===> T ===> T) ===> (=))  
    sgn_div_norm_ow sgn_div_norm_ow"
  unfolding sgn_div_norm_ow_def sgn_div_norm_ow_axioms_def
  by transfer_prover

lemma sgn_div_norm_on_typeclass[simp]: 
  fixes V :: \<open>_::sgn_div_norm set\<close>
  assumes \<open>\<And>v r. v\<in>V \<Longrightarrow> scaleR r v \<in> V\<close>
  shows \<open>sgn_div_norm_ow V norm sgn (*\<^sub>R)\<close> 
  using assms 
  by (auto simp add: sgn_ow_def sgn_div_norm_ow_axioms_def scaleR_ow_def sgn_div_norm_ow_def sgn_div_norm)

subsection \<open>\<open>class.dist_norm\<close>\<close>

ctr parametricity in minus_ow_def[unfolded make_balls]

locale dist_norm_ow = dist dist + norm norm + minus_ow U minus for U dist norm minus +
  assumes dist_norm: "\<forall>x\<in>U. \<forall>y\<in>U. dist x y = norm (minus x y)"

ctr parametricity in dist_norm_ow_def[unfolded dist_norm_ow_axioms_def]

(* ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close> 
    and [transfer_rule]: "right_total A"
    and [transfer_rule]: "bi_unique A"
  trp (?'a A)
in class.dist_norm_def *)

(* 
definition \<open>dist_norm_on A minus dist norm \<longleftrightarrow>
  (\<forall>x\<in>A. \<forall>y\<in>A. dist x y = norm (minus x y))\<close>
  for A minus dist norm

lemma dist_norm_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=)) ===> (=))  
    (dist_norm_on (Collect (Domainp T)))
    class.dist_norm"
  unfolding class.dist_norm_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: dist_norm_on_def[abs_def]) *)

lemma dist_norm_ow_typeclass[simp]: 
  fixes A :: \<open>_::dist_norm set\<close>
  assumes \<open>\<And>a b. \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a - b \<in> A\<close>
  shows \<open>dist_norm_ow A dist norm (-)\<close> 
  by (auto simp add: assms dist_norm_ow_def minus_ow_def dist_norm_ow_axioms_def dist_norm)

subsection \<open>\<open>class.complex_inner\<close>\<close>

thm class.complex_inner_def

locale complex_inner_ow = complex_vector_ow U scaleR scaleC plus zero minus uminus
  + dist_norm_ow U dist norm minus + sgn_div_norm_ow U norm sgn scaleR
  + uniformity_dist_ow U dist uniformity
  + open_uniformity_ow U "open" uniformity
  for U scaleR scaleC plus zero minus uminus dist norm sgn uniformity "open" +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes "\<forall>x\<in>U. \<forall>y\<in>U. cinner x y = cnj (cinner y x)"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. cinner (plus x y) z = cinner x z + cinner y z"
    and "\<forall>x\<in>U. \<forall>y\<in>U. cinner (scaleC r x) y = cnj r * cinner x y"
    and "\<forall>x\<in>U. 0 \<le> cinner x x"
    and "\<forall>x\<in>U. cinner x x = 0 \<longleftrightarrow> x = zero"
    and "\<forall>x\<in>U. norm x = sqrt (cmod (cinner x x))"


(* definition \<open>complex_inner_on A scaleR scaleC plusa zeroa minus uminus dist norm sgn uniformity open cinner \<longleftrightarrow>
        (vector_space_ow A plusa zeroa minus uminus scaleC \<and>
         scaleC_ow A scaleR scaleC \<and>
         dist_norm_on A minus dist norm \<and>
         sgn_div_norm_on A sgn norm scaleR) \<and>
        uniformity_dist_on A dist uniformity \<and>
class.open_uniformity.transferred A open uniformity \<and>
        ((\<forall>x\<in>A. \<forall>y\<in>A. cinner x y = cnj (cinner y x)) \<and>
         (\<forall>x\<in>A.
             \<forall>y\<in>A.
                \<forall>z\<in>A. cinner (plusa x y) z = cinner x z + cinner y z) \<and>
         (\<forall>r. \<forall>x\<in>A.
                 \<forall>y\<in>A. cinner (scaleC r x) y = cnj r * cinner x y)) \<and>
        (\<forall>x\<in>A. 0 \<le> cinner x x) \<and>
        (\<forall>x\<in>A. (cinner x x = 0) = (x = zeroa)) \<and>
        (\<forall>x\<in>A. norm x = sqrt (cmod (cinner x x)))\<close>
  for A scaleR scaleC plusa zeroa minus uminus dist norm sgn uniformity "open" cinner *)

(* Does manage *)
(* ctr parametricity in complex_inner_ow_def[unfolded complex_inner_ow_axioms_def] *)

lemma complex_inner_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T 
          ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
          ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
          ===> (T ===> T ===> (=)) ===> (=)) complex_inner_ow complex_inner_ow\<close>
  unfolding complex_inner_ow_def complex_inner_ow_axioms_def
  by transfer_prover

lemma complex_inner_ow_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes [simp]: \<open>closed V\<close> \<open>csubspace V\<close>
  shows \<open>complex_inner_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  apply (auto intro!: complex_vector_ow_typeclass dist_norm_ow_typeclass sgn_div_norm_on_typeclass
      simp: complex_inner_ow_def cinner_simps complex_vector.subspace_diff complex_inner_ow_axioms_def
      scaleR_scaleC complex_vector.subspace_scale 
      simp flip: norm_eq_sqrt_cinner)
  by -

subsection \<open>\<open>is_ortho_set.with\<close>\<close>

definition (in complex_inner_ow) is_ortho_set where \<open>is_ortho_set x S \<longleftrightarrow> 
  ((\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> cinner x y = 0) \<and> zero \<notin> S)\<close>

(* ud is_ortho_set is_ortho_set *)

ctr parametricity in [[axiom Tmp_Move.complex_inner_ow.is_ortho_set_def_raw, where ?'a='a and ?'b='b]]

(* ctr relativization
  synthesis ctr_simps
  assumes [transfer_rule]: "bi_unique A"
  trp (?'a A)
in is_ortho_set_ow: is_ortho_set.with_def *)

subsection \<open>\<open>class.metric_space\<close>\<close>

locale metric_space_ow = uniformity_dist_ow U dist uniformity + open_uniformity_ow U "open" uniformity
  for U dist uniformity "open" +
  assumes "\<forall>x \<in> U. \<forall>y \<in> U. dist x y = 0 \<longleftrightarrow> x = y"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. dist x y \<le> dist x z + dist y z"

ctr parametricity in metric_space_ow_def[unfolded metric_space_ow_axioms_def]

(* 
definition \<open>metric_space_on A dist uniformity open \<longleftrightarrow>
        uniformity_dist_on A dist uniformity \<and>
        open_uniformity_on A open uniformity \<and>
        (\<forall>x\<in>A. (\<forall>y\<in>A. (dist x y = 0) \<longleftrightarrow> (x = y))) \<and>
        (\<forall>x\<in>A. (\<forall>y\<in>A. (\<forall>z\<in>A. dist x y \<le> dist x z + dist y z)))\<close>
  for A dist uniformity "open"
*)

(* lemma class_metric_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    (metric_space_ow (Collect (Domainp T)))
    class.metric_space"
  unfolding class.metric_space_def class.metric_space_axioms_def
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: metric_space_ow_def[abs_def] metric_space_ow_axioms_def) *)

lemma metric_space_ow_typeclass[simp]:
  fixes V :: \<open>_::metric_space set\<close>
  assumes \<open>closed V\<close>
  shows \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
  by (auto simp: assms metric_space_ow_def metric_space_ow_axioms_def class.metric_space_axioms_def dist_triangle2)

subsection \<open>\<open>topological_space.nhds\<close>\<close>

ud topological_space.nhds topological_space.nhds

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close>
    and [transfer_rule]: "right_total A" "bi_unique A"
  trp (?'a A)
in topological_space.nhds.with_def


(* Without the prepocessing, rule has too strong conditions like `(?A2.0 ===> rel_filter ?A3.0 ===> ?A4.0) (\<sqinter>) (\<sqinter>)` *)
ctr parametricity in topological_space.nhds.with.transferred_def[folded transfer_bounded_filter_Inf_def, unfolded make_balls]

(* lemma topological_space_nhds_with_transferred_def_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> A ===> rel_filter A) topological_space.nhds.with.transferred topological_space.nhds.with.transferred\<close>
  unfolding topological_space.nhds.with.transferred_def
transfer_bounded_filter_Inf_def[symmetric] make_balls
  apply transfer_prover_start
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_step

  term  topological_space.nhds.with.transferred *)

ud nhds nhds

lemma fix_Domainp: \<open>Domainp X = (\<lambda>x. x\<in>Collect (Domainp X))\<close>
  by auto

declare topological_space.nhds.with.transferred.transfer[OF fix_Domainp, transfer_rule]

lemma nhds_on_topology[simp]: \<open>topological_space.nhds.with.transferred (topspace T) (openin T) x = nhdsin T x\<close> if \<open>x \<in> topspace T\<close>
  using that apply (auto intro!: ext simp add: topological_space.nhds.with.transferred_def[abs_def] nhdsin_def[abs_def])
   apply (subst INF_inf_const2[symmetric])
  using openin_subset by (auto intro!: INF_cong)

subsection \<open>\<open>filterlim\<close>\<close>

(* TODO: duplicated with Misc_Tensor_Product *)
lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover


subsection \<open>\<open>topological_space.convergent\<close>\<close>

ud topological_space.convergent topological_space.convergent
(* ud convergent convergent *)

definition \<open>convergent' X = (\<exists>L\<in>\<Union>(Collect open). filterlim X (nhds L) sequentially)\<close>
lemma [ud_with]: \<open>convergent = convergent'\<close>
  unfolding convergent'_def convergent_def
  apply (subst asm_rl[of \<open>\<Union> (Collect open) = UNIV\<close>])
  by auto

ud convergent convergent'

ctr relativization
synthesis ctr_simps
assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close>
  and [transfer_rule]: "right_total A" "bi_unique A"
in thm convergent.with_def[unfolded ud_with]



(* We don't do the following because it just defines a new constant that is equal to `topological_space.convergent` *)
(* ud convergent convergent *)
(* The following basically has the effect of the `ud` *)
declare topological_space_class.convergent_dict[ud_with]

lemma \<open>topological_space.convergent open X \<longleftrightarrow> (\<exists>L. filterlim X (topological_space.nhds open L) sequentially)\<close> for "open" X
  unfolding [[axiom Topological_Spaces.topological_space.convergent_def_raw]]
  oops

(* Fails *)
(* ctr relativization
synthesis ctr_simps
assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close>
  and [transfer_rule]: "right_total A" "bi_unique A"
in convergent.with_def *)

definition \<open>convergent_ow S = (\<lambda>open X.
        \<exists>L\<in>\<Union> {x. x \<subseteq> S \<and> open x}.
           filterlim X (topological_space.nhds.with.transferred S open L) sequentially)\<close>

lemma convergent_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows \<open>((rel_set A ===> (=)) ===> ((=) ===> A) ===> (=)) (convergent_ow (Collect (Domainp A))) convergent.with\<close>
  unfolding convergent.with_def convergent_ow_def
  apply transfer_prover_start
        apply transfer_step+
  by (simp add: conj_commute Ball_Collect)

ctr parametricity in filterlim_def

(* Too restrictive rule (has an equality in the last argument of `convergent_ow` *)
(* ctr parametricity in convergent_ow_def[unfolded make_balls] *)

lemma convergent_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]:  "bi_unique A"
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> ((=) ===> A) ===> (=)) 
             convergent_ow convergent_ow\<close>
  unfolding convergent_ow_def make_balls
  by transfer_prover


thm [[axiom Topological_Spaces.topological_space.convergent_def_raw]]

(* ctr parametricity in [[axiom Topological_Spaces.topological_space.convergent_def_raw]] *)

(* ctr relativization
synthesis ctr_simps
in thm [[axiom Topological_Spaces.topological_space.convergent_def_raw, where 'a=\<open>'a\<close>]]

definition \<open>convergent_with_transferred A open X = (\<exists>L\<in>A. filterlim X (topological_space.nhds.with.transferred A open L) sequentially)\<close>
  for A "open" X

lemma topological_space_convergent_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]:  "bi_unique T"
  shows "(rel_set T ===> (rel_set T ===> (=)) ===> ((=) ===> T) ===> (=))
    topological_space.convergent topological_space.convergent"
  unfolding [[axiom Topological_Spaces.topological_space.convergent_def_raw]] topological_space.nhds.with
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: convergent_with_transferred_def[abs_def]) *)

(*
lemma convergent_transfer[transfer_rule]:
  includes lifting_syntax
  (* assumes [transfer_domain_rule]: \<open>Domainp T = (\<lambda>x. x \<in> U)\<close> *)
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> ((=) ===> T) ===> (=)) 
    (convergent_with_transferred (Collect (Domainp T)))
    topological_space.convergent"
  unfolding [[axiom Topological_Spaces.topological_space.convergent_def_raw]] topological_space.nhds.with
  apply transfer_prover_start
      apply transfer_step+
  by (simp add: convergent_with_transferred_def[abs_def])
 *)

(* TODO: Duplicated with Misc_Tensor_Product *)
lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin 
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)

(* lemma convergent_on_topology[simp]:
  \<open>convergent_with_transferred (topspace T) (openin T) f \<longleftrightarrow> (\<exists>l. limitin T f l sequentially)\<close>
  by (auto simp: convergent_with_transferred_def simp flip: filterlim_nhdsin_iff_limitin)

lemma convergent_on_typeclass[simp]:
  \<open>convergent_with_transferred V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. limitin (top_of_set V) f l sequentially)\<close>
  by (simp add: flip: convergent_on_topology) *)

subsection \<open>\<open>uniform_space.cauchy_filter\<close>\<close>

lemma cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: (* "right_total T" *) "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> rel_filter T ===> (=)) 
    uniform_space.cauchy_filter
    uniform_space.cauchy_filter"
  unfolding [[axiom Topological_Spaces.uniform_space.cauchy_filter_def_raw]]
  by transfer_prover

subsection \<open>\<open>uniform_space.Cauchy\<close>\<close>

lemma Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: (* "right_total T" *) "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> ((=) ===> T) ===> (=)) 
    uniform_space.Cauchy
    uniform_space.Cauchy"
  unfolding [[axiom Topological_Spaces.uniform_space.Cauchy_uniform_raw]]
  using filtermap_parametric[transfer_rule] apply fail?
  by transfer_prover

subsection \<open>\<open>class.complete_space\<close>\<close>

locale complete_space_ow = metric_space_ow U dist uniformity "open"
  for U dist uniformity "open" +
  assumes \<open>range X \<subseteq> U \<longrightarrow> uniform_space.Cauchy uniformity X \<longrightarrow> convergent_ow U open X\<close>

(* definition \<open>complete_space_on A dist uniformity open \<longleftrightarrow>
        metric_space_on A dist uniformity open \<and>
        (\<forall>X. (\<forall>n. X n \<in> A) \<longrightarrow>
            uniform_space.Cauchy uniformity X \<longrightarrow> convergent_on A open X)\<close>
  for A dist uniformity "open" *)

(* definition \<open>transfer_funcset A B = {f. f ` A \<subseteq> B}\<close>
lemma transfer_funcset: \<open>A \<rightarrow> B = transfer_funcset A B\<close>
  by (simp add: image_subset_iff_funcset transfer_funcset_def)

definition \<open>transfer_ball_funcset A B P \<longleftrightarrow> (\<forall>f. f ` A \<subseteq> B \<longrightarrow> P f)\<close> *)

definition \<open>transfer_ball_range A P \<longleftrightarrow> (\<forall>f. range f \<subseteq> A \<longrightarrow> P f)\<close>
(* TODO: add symmetric def to make_balls *)

lemma Domainp_conversep: \<open>Domainp (conversep R) = Rangep R\<close>
  by (auto simp add: Domainp_iff[abs_def])

lemma conversep_rel_fun:
  includes lifting_syntax
  shows \<open>(T ===> U)\<inverse>\<inverse> = (T\<inverse>\<inverse>) ===> (U\<inverse>\<inverse>)\<close>
  by (auto simp: rel_fun_def)

lemma transfer_ball_range_parametric'[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>right_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof (intro rel_funI impI, rename_tac A B P Q)
  fix A B P Q
  assume [transfer_rule]: \<open>rel_set U A B\<close>
  assume TUPQ[transfer_rule]: \<open>((T ===> U) ===> (\<longrightarrow>)) P Q\<close>
  assume \<open>transfer_ball_range A P\<close>
  then have Pf: \<open>P f\<close> if \<open>range f \<subseteq> A\<close> for f
    unfolding transfer_ball_range_def using that by auto
  have \<open>Q g\<close> if \<open>range g \<subseteq> B\<close> for g
  proof -
    from that \<open>rel_set U A B\<close>
    have \<open>Rangep (T ===> U) g\<close>
      apply (auto simp add: conversep_rel_fun Domainp_pred_fun_eq simp flip: Domainp_conversep)
      apply (simp add: Domainp_conversep)
      by (metis Rangep.simps range_subsetD rel_setD2)
    then obtain f where TUfg[transfer_rule]: \<open>(T ===> U) f g\<close>
      by blast
    from that have \<open>range f \<subseteq> A\<close>
      by transfer
    then have \<open>P f\<close>
      by (simp add: Pf)
    then show \<open>Q g\<close>
      by (metis TUfg TUPQ rel_funD)
  qed
  then show \<open>transfer_ball_range B Q\<close>
  by (simp add: transfer_ball_range_def)
qed

lemma transfer_ball_range_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof -
  have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    using assms(1) assms(2) assms(3) bi_unique_alt_def transfer_ball_range_parametric' by blast
  then have 1: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by auto

  have \<open>(rel_set (U\<inverse>\<inverse>) ===> ((T\<inverse>\<inverse> ===> U\<inverse>\<inverse>) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule transfer_ball_range_parametric')
    using assms(1) bi_unique_alt_def bi_unique_conversep apply blast
    by auto
  then have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule_tac conversepD[where r=\<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>)\<close>])
    by (simp add: conversep_rel_fun del: conversep_iff)
  then have 2: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by (auto simp: rev_implies_def)

  from 1 2 show ?thesis
    apply (auto intro!: rel_funI simp: conversep_iff[abs_def])
     apply (smt (z3) rel_funE)
    by (smt (verit) rel_funE rev_implies_def)
qed

(* lemma transfer_ball_funcset_parametric'[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close> \<open>bi_total T\<close> (* TODO minimize *)
  shows \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_funcset transfer_ball_funcset\<close>
proof (intro rel_funI impI, rename_tac AP AQ BP BQ P Q)
  have [simp]: \<open>left_unique T\<close> \<open>right_unique T\<close> \<open>left_total T\<close> \<open>right_total T\<close>
    by -
  fix AP AQ BP BQ P Q
  assume TA: \<open>rel_set T AP AQ\<close>
  assume UB: \<open>rel_set U BP BQ\<close>
  assume TUPQ: \<open>((T ===> U) ===> (\<longrightarrow>)) P Q\<close>
  assume \<open>transfer_ball_funcset AP BP P\<close>
  then have Pf: \<open>P f\<close> if \<open>f ` AP \<subseteq> BP\<close> for f
    unfolding transfer_ball_funcset_def using that by auto
  have \<open>Q g\<close> if \<open>g ` AQ \<subseteq> BQ\<close> for g
  proof -
    from that
    have \<open>Rangep (T ===> U) g\<close>
      apply (auto simp add: conversep_rel_fun Domainp_pred_fun_eq simp flip: Domainp_conversep)
      apply (simp add: Domainp_conversep)
  try0
  by -

      apply (subst Domainp_pred_fun_eq)
       apply simp
      apply simp
      apply simp
      thm fun.rel_conversep
      apply (subst fun.rel_conversep[symmetric])
      apply (rule_tac Rangep.intros)
      by -
    then obtain f where TUfg: \<open>(T ===> U) f g\<close>
      by blast
    then have \<open>f ` AP \<subseteq> BP\<close>
      try0
      by -
    then have \<open>P f\<close>
      by (simp add: Pf)
    then show \<open>Q g\<close>
      by (metis TUPQ TUfg apply_rsp')
  qed
  then show \<open>transfer_ball_funcset AQ BQ Q\<close>
    by (simp add: transfer_ball_funcset_def)
qed

lemma transfer_ball_funcset_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_total T\<close> (* TODO minimize *)
  shows \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) transfer_ball_funcset transfer_ball_funcset\<close>
proof -
  have 1: \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_funcset transfer_ball_funcset\<close>
    by -
  then have 2: \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_funcset transfer_ball_funcset\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by auto
    
  have 3: \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (rev_implies)) ===> (rev_implies)) transfer_ball_funcset transfer_ball_funcset\<close>
    by -
  then have 4: \<open>(rel_set T ===> rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (rev_implies)) transfer_ball_funcset transfer_ball_funcset\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by (auto simp: rev_implies_def)

  from 2 4 show ?thesis
    apply (auto intro!: rel_funI)
     apply (smt (z3) rel_funE)
    by (smt (verit) rel_funE rev_implies_def)
qed

lemma Pi_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_total T\<close>
  shows \<open>(rel_set T ===> rel_set U ===> rel_set (T ===> U)) transfer_funcset transfer_funcset\<close>
proof (intro rel_funI rel_setI)
  fix A1 A2 assume \<open>rel_set T A1 A2\<close>
  fix B1 B2 assume \<open>rel_set U B1 B2\<close>
  fix f2 assume \<open>f2 \<in> transfer_funcset A2 B2\<close>
  define DT RT where \<open>DT = Collect (Domainp T)\<close> and \<open>RT = Collect (Rangep T)\<close>
(*   have \<open>rel_set T UNIV UNIV\<close>
    by (simp add: UNIV_transfer assms(2))
  from bi_unique_rel_set_lemma[OF \<open>bi_unique T\<close> \<open>rel_set T UNIV UNIV\<close>]
  obtain m where \<open>UNIV = range m\<close> and [simp]: \<open>inj m\<close> and Tm: \<open>T x (m x)\<close> for x
    by auto
  then have \<open>\<exists>x'. U x' (f2 (m x))\<close> for x
  sledgehammer
  try0
  by -

  proof -
    have \<open>m x \<in> RT\<close>
  using \<open>RT = m ` DT\<close> that by blast
  try0
  by -
  then have \<open>f2 (m x) \<in> \<close>
    by -
  then obtain f1 where Uf1f2: \<open>U (f1 x) (f2 (m x))\<close> if \<open>x \<in> DT\<close> for x
    apply atomize_elim
    by metis
    apply (intro choice allI)
  sledgehammer
  try0
  by -
  then have \<open>U (f1 x) (f2 y)\<close> if \<open>T x y\<close> for x y
    using DT_def Tm assms bi_uniqueDr that by fastforce


  sledgehammer x
  try0
  by -
 *)
  obtain m where \<open>A2 = m ` A1\<close> and [simp]: \<open>inj_on m A1\<close> and Tm: \<open>x\<in>A1 \<Longrightarrow> T x (m x)\<close> for x
    using bi_unique_rel_set_lemma
    by (metis \<open>rel_set T A1 A2\<close> assms)
  have \<open>\<exists>x'. U x' (f2 (m x))\<close> if \<open>x \<in> A1\<close> for x
    by -
  then obtain f1a where Uf1f2: \<open>U (f1a x) (f2 (m x))\<close>(*  and \<open>f2 x \<in> B2\<close> *) if \<open>x \<in> A1\<close> for x
    apply atomize_elim 
    by metis
  then have \<open>U (f1a x) (f2 y)\<close> if \<open>T x y\<close> and \<open>x \<in> A1\<close> for x y
    by (metis Tm assms bi_uniqueDr that(1) that(2))
  

  obtain f2b where \<open>U (f1 x) (f2b y)\<close> if \<open>T x y\<close> for x y
  sledgehammer x
  try0
  by -
  define f2 where \<open>f2 x = \<close>

  then have \<open>f2 \<in> transfer_funcset A2 B2\<close>
    by (metis funcsetI transfer_funcset)
  moreover have \<open>(T ===> U) f1 f2\<close>
  proof (rule rel_funI)
    fix x y assume \<open>T x y\<close>
    then have \<open>x \<in> A1\<close>
  sledgehammer
  try0
  by -
  then obtain x' where \<open>x' \<in> A2\<close> and \<open>m x' = x\<close>
    using \<open>A1 = m ` A2\<close> by blast
  then show \<open>U (f1 x) (f2 y)\<close>
  sledgehammer
  try0
  by -

  
  ultimately show \<open>\<exists>f2\<in>transfer_funcset A2 B2. (T ===> U) f1 f2\<close>
    by metis


  unfolding Pi_def *)

(* TODO not good enough *)
(* ctr parametricity in complete_space_ow_def[unfolded make_balls transfer_ball_range_def[symmetric]] *)

lemma complete_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    complete_space_ow complete_space_ow"
  unfolding complete_space_ow_def complete_space_ow_axioms_def make_balls  transfer_ball_range_def[symmetric]
  by transfer_prover

lemma complete_space_as_set[simp]: \<open>complete (space_as_set V)\<close> for V :: \<open>_::cbanach ccsubspace\<close>
  by (simp add: complete_eq_closed)

lemma complete_space_on_typeclass[simp]:
  fixes V :: \<open>_::uniform_space set\<close>
  assumes \<open>complete V\<close>
  shows \<open>complete_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
proof (rule complete_space_ow.intro)
  show \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
    apply (rule metric_space_ow_typeclass)
    by (simp add: assms complete_imp_closed)
  have \<open>\<exists>l. limitin (top_of_set V) X l sequentially\<close>
    if XV: \<open>\<And>n. X n \<in> V\<close> and cauchy: \<open>uniform_space.Cauchy (uniformity_on V) X\<close> for X
  proof -
    from cauchy
    have \<open>uniform_space.cauchy_filter (uniformity_on V) (filtermap X sequentially)\<close>
      by (simp add: [[axiom Topological_Spaces.uniform_space.Cauchy_uniform_raw]])
    then have \<open>cauchy_filter (filtermap X sequentially)\<close>
      by (auto simp: cauchy_filter_def [[axiom Topological_Spaces.uniform_space.cauchy_filter_def_raw]])
    then have \<open>Cauchy X\<close>
      by (simp add: Cauchy_uniform)
    with \<open>complete V\<close> XV obtain l where l: \<open>X \<longlonglongrightarrow> l\<close> \<open>l \<in> V\<close>
      apply atomize_elim
      by (meson completeE)
    with XV l show ?thesis
      by (auto intro!: exI[of _ l] simp: convergent_def limitin_subtopology)
  qed
  then show \<open>complete_space_ow_axioms V (uniformity_on V) (openin (top_of_set V))\<close>
    apply (auto simp: complete_space_ow_axioms_def complete_imp_closed assms)
  by -
qed

subsection \<open>\<open>class.chilbert_space\<close>\<close>

locale chilbert_space_ow = complex_inner_ow + complete_space_ow

(* definition \<open>chilbert_space_on A scaleR scaleC plus zero minus uminus dist norm sgn uniformity open cinner \<longleftrightarrow>
        complex_inner_on A scaleR scaleC plus zero minus uminus dist norm sgn
         uniformity open cinner \<and>
        complete_space_on A dist uniformity open\<close>
  for  A scaleR scaleC plus zero minus uminus dist norm sgn uniformity "open" cinner
*)

lemma class_chilbert_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T
      ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
      ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
      ===> (T ===> T ===> (=)) ===> (=)) 
chilbert_space_ow chilbert_space_ow"
  unfolding class.chilbert_space_def chilbert_space_ow_def
  by transfer_prover

lemma chilbert_space_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>complete V\<close> \<open>csubspace V\<close>
  shows \<open>chilbert_space_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn
     (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  by (auto intro!: chilbert_space_ow.intro complex_inner_ow_typeclass
      simp: assms complete_imp_closed)

lemma chilbert_space_add_ow[ud_with]:
  \<open>class.chilbert_space = chilbert_space_ow UNIV\<close>
  by (simp add: class.chilbert_space_def chilbert_space_ow_def ud_with)

subsection \<open>\<open>hull\<close>\<close>

definition \<open>hull_on A S s = \<Inter> {x. (S x \<and> s \<subseteq> x) \<and> x \<subseteq> A} \<inter> A\<close>

lemma hull_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T ===> rel_set T) 
    (hull_on (Collect (Domainp T)))
    (hull)"
  unfolding hull_def
  apply transfer_prover_start
      apply transfer_step+
  apply (intro ext)
  by (auto simp: hull_on_def)


subsection \<open>\<open>cspan.with\<close>\<close>

ud cspan cspan



(* unoverload_definition complex_vector.span_def *)

(* definition \<open>cspan_on A zero plus scaleC = hull_on A (module.subspace.with zero plus scaleC)\<close>
  for A zero plus scaleC

lemma cspan_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "(T ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> rel_set T) 
    (cspan_on (Collect (Domainp T)))
    cspan.with"
  unfolding cspan.with_def
  apply transfer_prover_start
    apply transfer_step+
  by (auto intro!: ext simp: cspan_on_def) *)

(* TODO Trivial *)
lemma cspan_on_typeclass: \<open>span.with 0 (+) (*\<^sub>C) B = cspan B\<close>
  by (metis cspan.with)

subsubsection \<open>\<^const>\<open>closure\<close>\<close>

(* unoverload_definition closure_def[unfolded islimpt_def] *)

thm closure_def
thm islimpt_def
thm closure.with_def

(* definition closure_on_with where \<open>closure_on_with A opn S = 
  S \<union> {x\<in>A. \<forall>T\<subseteq>A. x \<in> T \<longrightarrow> opn T \<longrightarrow> (\<exists>y\<in>S. y \<in> T \<and> y \<noteq> x)}\<close>

lemma closure_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T ===> rel_set T)
         (closure_on_with (Collect (Domainp T))) closure.with"
  unfolding closure.with_def closure_on_with_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Pow_def Ball_Collect[symmetric] Ball_def Bex_def mem_Collect_eq
  by blast *)

lemma closure_on_with_typeclass[simp]: 
  \<open>closure_ow X (openin (top_of_set X)) S = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
proof -
  have \<open>closure_ow X (openin (top_of_set X)) S = (top_of_set X) closure_of S \<union> S\<close>
    apply (simp add: closure_ow_def islimpt_ow_def closure_of_def)
    apply safe
     apply (meson PowI openin_imp_subset)
    by auto
  also have \<open>\<dots> = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
    by (simp add: closure_of_subtopology)
  finally show ?thesis
    by -
qed

subsection \<open>\<open>is_onb.with\<close>\<close>

(* definition \<open>is_onb_on U E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = U\<close>

lemma [ud_with]: \<open>is_onb = is_onb_on UNIV\<close>
  unfolding is_onb_def is_onb_on_def apply transfer by auto *)

(*  definition (* TODO make hidden *)
  \<open>is_onb_no_ccsubspace E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = UNIV\<close>
lemma is_onb_with[ud_with]: \<open>is_onb = is_onb_no_ccsubspace\<close>
  unfolding is_onb_def is_onb_no_ccsubspace_def apply transfer by auto 
 *)
(*
lemma is_onb_def_no_ccsubspace:
  \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = UNIV\<close>
  unfolding is_onb_def apply transfer by simp 
*)

definition (* TODO make hidden *)
  \<open>is_onb_no_ccsubspace E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> closure (cspan E) = UNIV\<close>
lemma [ud_with]:
  \<open>is_onb = is_onb_no_ccsubspace\<close>
  unfolding is_onb_def is_onb_no_ccsubspace_def apply transfer by auto

(* ud is_onb_no_ccsubspace is_onb_no_ccsubspace *)

ud is_onb_no_ccsubspace is_onb_no_ccsubspace
(* 
declare is_ortho_set.with[unoverload_def]
declare cspan.with[unoverload_def]
declare closure.with[unoverload_def]
unoverload_definition is_onb_def_no_ccsubspace
print_theorems
declare is_onb.with[ud_with] *)

declare closure_ow.transfer[OF fix_Domainp, transfer_rule]

ctr relativization
  synthesis ctr_simps
  assumes [transfer_rule]: "bi_unique A" "right_total A"
in thm is_onb_no_ccsubspace.with_def

schematic_goal [transfer_rule]:
  includes lifting_syntax
  fixes A :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows "(((=) ===> A ===> A) ===> (A ===> A ===> A) ===> (rel_set A ===> (=)) ===> (A ===> (=)) ===> (A ===> A ===> (=)) ===> T ===> rel_set T ===> (=))
   (?X::_) is_onb_no_ccsubspace.with"
  unfolding is_onb_no_ccsubspace.with_def
  apply transfer_prover_start
            apply transfer_step+
  by transfer_prover

(* ctr relativization
  synthesis ctr_simps 
  assumes [transfer_domain_rule]: \<open>Domainp A = (\<lambda>x. x\<in>U)\<close> 
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "bi_unique A"
  trp (?'a A)
in is_onb.with_def *)

(* thm is_onb.with_def *)

(* definition \<open>is_onb_on A cinner zero norm open plus scaleC E \<longleftrightarrow>
        is_ortho_set.with cinner zero E \<and>
        (\<forall>b\<in>E. norm b = 1) \<and>
        closure_on_with A open (cspan_on A zero plus scaleC E) = A\<close>
  for A cinner zero norm "open" plus scaleC E
*)

(* lemma is_onb_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T ===> (=)) ===> T ===> (T ===> (=)) ===> (rel_set T ===> (=))
     ===> (T ===> T ===> T) ===> ((=) ===> T ===> T) ===> rel_set T ===> (=)) 
    is_onb_no_ccsubspace.with
    is_onb_no_ccsubspace.with"
  using right_total_UNIV_transfer[transfer_rule] apply fail?
  unfolding is_onb.with_def 
  apply transfer_prover_start
       apply transfer_step+
  by (simp add: is_onb_on_def[abs_def]) *)


subsection \<open>Transferring a theorem\<close>

(* The original theorem: *)
print_statement orthonormal_basis_exists

lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and norm: \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
proof -
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (space_as_set V)"
    then interpret T: local_typedef \<open>space_as_set V\<close> \<open>TYPE('t)\<close>
      by unfold_locales

    note orthonormal_basis_exists
    note this[unfolded ud_with]
    note this[unoverload_type 'a]
    note this[unfolded ud_with]
    note this[where 'a='t]
    note this[untransferred]
    note this[where plus=plus and scaleC=scaleC and scaleR=scaleR and zero=0 and minus=minus
        and uminus=uminus and sgn=sgn and S=S and norm=norm and cinner=cinner and dist=dist
        and ?open=\<open>openin (top_of_set (space_as_set V))\<close>
        and uniformity=\<open>uniformity_on (space_as_set V)\<close>]
    note this[simplified Domainp_rel_filter prod.Domainp_rel T.Domainp_cr_S]
  }    
  note * = this[cancel_type_definition]
  have 1: \<open>uniformity_on (space_as_set V)
    \<le> principal (Collect (pred_prod (\<lambda>x. x \<in> space_as_set V) (\<lambda>x. x \<in> space_as_set V)))\<close>
    by (auto simp: uniformity_dist intro!: le_infI2)
  have \<open>\<exists>B\<in>{A. \<forall>x\<in>A. x \<in> space_as_set V}.
     S \<subseteq> B \<and> is_onb_on {x. x \<in> space_as_set V} (\<bullet>\<^sub>C) 0 norm (openin (top_of_set (space_as_set V))) (+) (*\<^sub>C) B\<close>
    apply (rule * )
    using \<open>S \<subseteq> space_as_set V\<close> \<open>is_ortho_set S\<close>
    by (auto simp add: simp flip: is_ortho_set.with
        intro!: complex_vector.subspace_scale real_vector.subspace_scale csubspace_is_subspace
        csubspace_nonempty complex_vector.subspace_add complex_vector.subspace_diff
        complex_vector.subspace_neg sgn_in_spaceI 1 norm)
x

  then obtain B where \<open>B \<subseteq> space_as_set V\<close> and \<open>S \<subseteq> B\<close>
    and is_onb: \<open>is_onb_on (space_as_set V) (\<bullet>\<^sub>C) 0 norm (openin (top_of_set (space_as_set V))) (+) (*\<^sub>C) B\<close>
    by auto

  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>cspan B \<inter> space_as_set V = cspan B\<close>
    by (smt (verit) basic_trans_rules(8) ccspan.rep_eq ccspan_leqI ccspan_superset complex_vector.span_span inf_absorb1 less_eq_ccsubspace.rep_eq)
  then have [simp]: \<open>space_as_set V \<inter> cspan B = cspan B\<close>
    by blast
  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>space_as_set V \<inter> closure (cspan B) = closure (cspan B)\<close>
    by (metis Int_absorb1 ccspan.rep_eq ccspan_leqI less_eq_ccsubspace.rep_eq)
  have [simp]: \<open>closure X \<union> X = closure X\<close> for X :: \<open>'z::topological_space set\<close>
    using closure_subset by blast
  
  from is_onb have \<open>is_ortho_set B\<close>
    by (auto simp: is_onb_on_def is_ortho_set.with)

  moreover from is_onb have \<open>norm x = 1\<close> if \<open>x \<in> B\<close> for x
    by (auto simp: is_onb_on_def that)

  moreover from is_onb have \<open>closure (cspan B) = space_as_set V\<close>
    by (simp add: is_onb_on_def \<open>B \<subseteq> space_as_set V\<close> cspan_on_typeclass closure_on_with_typeclass)
  then have \<open>ccspan B = V\<close>
    by (simp add: ccspan.abs_eq space_as_set_inverse)

  ultimately show ?thesis
    using \<open>S \<subseteq> B\<close> by auto
qed


end
