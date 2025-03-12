section \<open>Classical instantiation of complements\<close>

theory Axioms_Complement_Classical
  imports Laws_Classical Classical_Extra With_Type.With_Type
begin

typedef ('a, 'b::finite) complement_domain_simple = \<open>undefined :: ('a\<times>'b) set\<close>
  sorry
instance complement_domain_simple :: (type, finite) finite
  sorry

axiomatization where 
  complement_exists_simple: \<open>register F \<Longrightarrow> \<exists>G :: ('a, 'b) complement_domain_simple update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    for F :: \<open>'a update \<Rightarrow> 'b::finite update\<close>

definition same_outside :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> 'b rel\<close> where
  \<open>same_outside X = {(m,n) | m n. \<exists>a. setter X a m = n}\<close>

lemma setter_getter[simp]: \<open>setter F (getter F m) m = m\<close> if  \<open>register F\<close>
  using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
  by (simp add: valid_getter_setter_def)

lemma setter_setter[simp]: \<open>setter F a (setter F b m) = setter F a m\<close> if  \<open>register F\<close>
  using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
  by (simp add: valid_getter_setter_def)

lemma getter_setter[simp]: \<open>getter F (setter F a m) = a\<close> if \<open>register F\<close>
  using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
  by (simp add: valid_getter_setter_def)


lemma equivp_same_outside:
  assumes [iff]: \<open>register X\<close>
  shows \<open>equiv UNIV (same_outside X)\<close>
proof (intro equivI reflI transI symI)
  fix m n p :: 'b
  show \<open>(m, m) \<in> same_outside X\<close>
    by (auto intro!: exI[of _ \<open>getter X m\<close>] simp: same_outside_def valid_getter_setter_def)
  show \<open>(m, n) \<in> same_outside X\<close> if \<open>(n, m) \<in> same_outside X\<close> for n m
  proof -
    from that obtain a where \<open>m = setter X a n\<close>
      by (auto intro!: simp: same_outside_def)
    then have \<open>n = setter X (getter X n) m\<close>
      by (simp add: valid_getter_setter_def)
    then show ?thesis
      by (auto intro!: exI[of _ \<open>getter X n\<close>] simp: same_outside_def)
  qed
  show \<open>(m, p) \<in> same_outside X\<close> if \<open>(m, n) \<in> same_outside X\<close> and \<open>(n, p) \<in> same_outside X\<close>
  proof -
    from that obtain a where n: \<open>n = setter X a m\<close>
      by (auto intro!: simp: same_outside_def)
    from that obtain b where p: \<open>p = setter X b n\<close>
      by (auto intro!: simp: same_outside_def)
    from n p have \<open>p = setter X b m\<close>
      by (simp add: valid_getter_setter_def)
    then show ?thesis
      by (auto intro!: exI[of _ b] simp: same_outside_def)
  qed
qed



definition complement_domain :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> 'b set set\<close> where
  \<open>complement_domain X = UNIV // same_outside X\<close>

(* TODO move to Extra *)
lemma register_eqI_via_setter:
  assumes \<open>register F\<close> and \<open>register G\<close>
  assumes \<open>\<And>a m. setter F a m = setter G a m\<close>
  shows \<open>F = G\<close>
proof -
  note [simp] = assms
  have getter_eq: \<open>getter F m = getter G m\<close> for m
  proof -
    have \<open>getter F m = getter F (setter G (getter G m) m)\<close>
      by simp
    also have \<open>\<dots> = getter F (setter F (getter G m) m)\<close>
      using assms by simp
    also have \<open>\<dots> = getter G m\<close>
      apply (subst getter_setter)
      by simp_all
    finally show ?thesis
      by -
  qed
  have \<open>F = register_from_getter_setter (getter F) (setter F)\<close>
    by simp
  also from assms getter_eq
  have \<open>\<dots> = register_from_getter_setter (getter G) (setter G)\<close>
    by presburger
  also have \<open>\<dots> = G\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma register_pair_getter:
  assumes \<open>compatible F G\<close>
  shows \<open>getter (F;G) m = (getter F m, getter G m)\<close>
  using assms by (simp add: register_pair_def register_pair_is_valid compatible_def)

lemma register_pair_setter:
  assumes \<open>compatible F G\<close>
  shows \<open>setter (F;G) (a,b) m = setter F a (setter G b m)\<close>
  using assms by (simp add: register_pair_def register_pair_is_valid compatible_def)

lemma
  assumes \<open>register F\<close> and \<open>register G\<close>
  shows setter_compose: \<open>setter (G o F) a m = setter G (setter F a (getter G m)) m\<close>
    and getter_compose: \<open>getter (G o F) m = getter F (getter G m)\<close>
proof -
  note [[simproc del: Laws_Classical.compatibility_warn]]
  define sF gF sG gG where \<open>sF = setter F\<close> and \<open>gF = getter F\<close> and \<open>sG = setter G\<close> and \<open>gG = getter G\<close>
  from \<open>register F\<close>
  have F: \<open>F a m = (case a (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sF x m))\<close> for a m
    by (metis gF_def getter_of_register_from_getter_setter register_def register_from_getter_setter_def sF_def
        setter_of_register_from_getter_setter)
  have validF: \<open>valid_getter_setter gF sF\<close>
    by (simp add: assms(1) gF_def sF_def)
  from \<open>register G\<close>
  have G: \<open>G a m = (case a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sG x m))\<close> for a m
    by (metis gG_def getter_of_register_from_getter_setter register_def register_from_getter_setter_def sG_def
      setter_of_register_from_getter_setter)
  from \<open>register G\<close>
  have validG: \<open>valid_getter_setter gG sG\<close>
    by (simp add: gG_def sG_def)
  define s g where \<open>s a m = sG (sF a (gG m)) m\<close> and \<open>g m = gF (gG m)\<close> for a m
  have GF: \<open>(G o F) = register_from_getter_setter g s\<close>
    by (auto intro!: ext simp add: option.case_eq_if F G s_def g_def register_from_getter_setter_def)
  have valid: \<open>valid_getter_setter g s\<close>
    using validF validG by (auto simp: valid_getter_setter_def s_def g_def)
  with GF show \<open>setter (G o F) a m = s a m\<close>
    by simp
  from valid GF show \<open>getter (G o F) m = g m\<close>
    by simp
qed

lemma setter_id[simp]: \<open>setter id a m = a\<close>
  by (simp add: setter_def register_apply_def)

lemma surj_getter:
  assumes \<open>register F\<close>
  shows \<open>surj (getter F)\<close>
  apply (rule surjI[of _ \<open>\<lambda>a. setter F a undefined\<close>])
  using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
  by (simp add: valid_getter_setter_def)

lemma iso_register_injective_getter:
  assumes [iff]: \<open>register F\<close>
  shows \<open>iso_register F \<longleftrightarrow> inj (getter F)\<close>
proof (rule iffI)
  note [[simproc del: Laws_Classical.compatibility_warn]]
  assume \<open>iso_register F\<close>
  then obtain G where \<open>register G\<close> and \<open>F o G = id\<close>
    using iso_register_def by blast
  from \<open>register G\<close> assms have \<open>getter (F o G) m = getter G (getter F m)\<close> for m
    by (simp add: getter_compose)
  moreover from \<open>F o G = id\<close> have \<open>getter (F o G) m = m\<close> for m
    by (metis register_id setter_id valid_getter_setter_def valid_getter_setter_getter_setter)
  ultimately have \<open>getter G (getter F m) = m\<close> for m
    by simp
  then show \<open>inj (getter F)\<close>
    by (metis injI)
next
  note [[simproc del: Laws_Classical.compatibility_warn]]
  assume \<open>inj (getter F)\<close>
  moreover from \<open>register F\<close> have \<open>surj (getter F)\<close>
    by (simp add: surj_getter)
  define s :: \<open>'b \<Rightarrow> 'a \<Rightarrow> 'a\<close> and g :: \<open>'a \<Rightarrow> 'b\<close> where
    \<open>s a m = getter F a\<close> and \<open>g = inv (getter F)\<close> for a m
  define G where \<open>G = register_from_getter_setter g s\<close>
  have valid: \<open>valid_getter_setter g s\<close>
    using \<open>inj (getter F)\<close> \<open>surj (getter F)\<close> 
    by (simp add: valid_getter_setter_def s_def g_def surj_f_inv_f)
  then have [iff]: \<open>register G\<close>
    by (simp add: G_def)
  have [simp]: \<open>setter G = s\<close>
    by (simp add: G_def valid)
  have \<open>setter F (getter F a) m = a\<close> for a m
    apply (rule \<open>inj (getter F)\<close>[unfolded inj_def, rule_format])
    by (meson assms valid_getter_setter_def valid_getter_setter_getter_setter)
  then have FG: \<open>F \<circ> G = id\<close>
    apply (rule_tac register_eqI_via_setter)
    by (simp_all add: setter_compose s_def)
  have GF: \<open>G o F = id\<close>
    apply (rule_tac register_eqI_via_setter)
    by (simp_all add: setter_compose s_def)
  show \<open>iso_register F\<close>
    apply (rule iso_registerI)
    using assms FG GF by auto
qed

lemma complement_exists:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes [iff]: \<open>register F\<close>
  shows \<open>let 'c::type = complement_domain F in
         \<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof with_type_intro
  show \<open>complement_domain F \<noteq> {}\<close>
    by (simp add: complement_domain_def)
next
  note [[simproc del: Laws_Classical.compatibility_warn]]
  fix rep :: \<open>'c \<Rightarrow> 'b set\<close>
  assume bij_rep: \<open>bij_betw rep UNIV (complement_domain F)\<close>
(*   then interpret type_definition rep \<open>inv rep\<close> \<open>complement_domain F\<close> (* TODO needed? *)
    by (simp add: type_definition_bij_betw_iff) *)
  define S where \<open>S x y \<longleftrightarrow> (x,y) \<in> same_outside F\<close> for x y
  have rep: \<open>rep y \<in> UNIV // same_outside F\<close> for y
    by (metis bij_betw_def bij_rep complement_domain_def range_eqI)
  define g where \<open>g m = inv rep (same_outside F `` {m})\<close> for m
  define s where \<open>s a m = the_elem (setter F (getter F m) ` rep a)\<close> for a m
  define G where \<open>G = register_from_getter_setter g s\<close>
  define r where \<open>r x y \<longleftrightarrow> x \<in> rep y\<close> for x y
  include lifting_syntax

  have [transfer_rule]: \<open>(r ===> r ===> (=)) S (=)\<close>
    apply (intro rel_funI)
    by (smt (verit, best) S_def UNIV_I assms bij_betw_iff_bijections bij_rep equivp_same_outside quotient_eq_iff r_def rep)
  have [transfer_rule]: \<open>left_total r\<close>
    apply (simp add: r_def left_total_def)
  by (metis UNIV_I assms bij_betw_def bij_rep complement_domain_def equiv_class_self equivp_same_outside f_inv_into_f
      quotientI)
  have [transfer_rule]: \<open>right_total r\<close>
    using rep 
    apply (simp add: r_def right_total_def)
    using equiv_Eps_in equivp_same_outside by blast
  have [transfer_rule]: \<open>right_unique r\<close>
  proof (rule right_uniqueI)
    fix x y z
    assume \<open>r x y\<close> and \<open>r x z\<close>
    then have \<open>x \<in> rep y\<close> and \<open>x \<in> rep z\<close>
      by (auto simp: r_def)
    then have \<open>rep y = same_outside F `` {x}\<close>
      apply (rule_tac quotientE)
       apply (rule rep[of y])
      using equiv_class_eq equivp_same_outside by fastforce
    moreover from \<open>x \<in> rep z\<close> have \<open>rep z = same_outside F `` {x}\<close>
      apply (rule_tac quotientE)
       apply (rule rep[of z])
      using equiv_class_eq equivp_same_outside by fastforce
    finally have \<open>rep y = rep z\<close>
      by simp
    then show \<open>y = z\<close>
      by (metis UNIV_I bij_betw_iff_bijections bij_rep)
  qed

  have [transfer_rule]: \<open>((=) ===> r) id g\<close>
    apply (simp add: r_def g_def rel_fun_def)
    by (metis UNIV_I assms bij_betw_def bij_rep complement_domain_def equiv_class_self equivp_same_outside f_inv_into_f quotientI)
  have [transfer_rule]: \<open>(r ===> (=) ===> (=)) (\<lambda>a m. setter F (getter F m) a) s\<close>
  proof (intro rel_funI)
    fix a b and m n :: 'b
    assume \<open>r a b\<close> and \<open>m = n\<close>
    from \<open>r a b\<close> have \<open>a \<in> rep b\<close>
      by (simp add: r_def)
    have \<open>setter F (getter F n) a' = setter F (getter F m) a\<close> if \<open>a' \<in> rep b\<close> for a'
    proof -
      from \<open>a \<in> rep b\<close> have \<open>rep b = same_outside F `` {a}\<close>
        apply (rule_tac quotientE)
         apply (rule rep[of b])
        using equiv_class_eq equivp_same_outside by fastforce
      moreover from \<open>a' \<in> rep b\<close> have \<open>rep b = same_outside F `` {a'}\<close>
        apply (rule_tac quotientE)
         apply (rule rep[of b])
        using equiv_class_eq equivp_same_outside by fastforce
      ultimately have \<open>(a,a') \<in> same_outside F\<close>
        using that by blast
      then obtain c where \<open>setter F c a = a'\<close>
        by (auto simp: same_outside_def)

      then have \<open>setter F (getter F n) a' = setter F (getter F n) (setter F c a)\<close>
        by simp
      also have \<open>\<dots> = setter F (getter F n) a\<close>
        using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
        by (simp add: valid_getter_setter_def)
      also have \<open>\<dots> = setter F (getter F m) a\<close>
        by (simp add: \<open>m = n\<close>)
      finally show \<open>setter F (getter F n) a' = setter F (getter F m) a\<close>
        by -
    qed
    then
    have \<open>setter F (getter F n) ` rep b = {setter F (getter F m) a}\<close>
      using \<open>a \<in> rep b\<close> by (auto intro!: simp: s_def)
    then show \<open>setter F (getter F m) a = s b n\<close>
      by (simp add: s_def)
  qed

  
  from bij_rep have [simp]: \<open>rep (inv rep x) = x\<close> if \<open>x \<in> complement_domain F\<close> for x
    by (simp add: bij_betw_inv_into_right that)

  have sg: \<open>m = s (g m) m\<close> for m
    apply (transfer' fixing: m)
    using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
    by (simp add: valid_getter_setter_def)
  have \<open>S (id (setter F (getter F m) a)) a\<close> for m a
    using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
    by (auto intro!: exI[of _ \<open>getter F a\<close>] simp: S_def same_outside_def  valid_getter_setter_def)
  then have gs: \<open>g (s a m) = a\<close> for a m
    apply (transfer' fixing: m)
    by simp
  have ss: \<open>s a (s b m) = s a m\<close> for a b m
    apply (transfer' fixing: m)
    using valid_getter_setter_getter_setter[OF \<open>register F\<close>]
    by (simp add: valid_getter_setter_def)
  have valid: \<open>valid_getter_setter g s\<close>
    by (simp add: valid_getter_setter_def sg gs ss)
  then have [iff]: \<open>register G\<close>
    using G_def register_def by blast
  have [simp]: \<open>setter G = s\<close>
    by (simp add: G_def valid)

  from \<open>register F\<close>
  have \<open>F = register_from_getter_setter (getter F) (setter F)\<close>
    using register_def by force
  then have F_apply: \<open>F f m = (case f (getter F m) of None \<Rightarrow> None | Some a \<Rightarrow> Some (setter F a m))\<close> for f m
    by (metis register_from_getter_setter_def)
  have G_apply: \<open>G f m = (case f (g m) of None \<Rightarrow> None | Some a \<Rightarrow> Some (s a m))\<close> for f m
    by (simp add: G_def register_from_getter_setter_def)

  have \<open>S (setter F a m) m\<close> for a m
    by (auto intro!: exI[of _ \<open>getter F m\<close>] simp add: S_def same_outside_def valid_getter_setter_def)
  then have gGsF[simp]: \<open>g (setter F a m) = g m\<close> for a m
    apply (transfer' fixing: m)
    by simp
  have gFsG[simp]: \<open>getter F (s a m) = getter F m\<close> for a m
    apply (transfer' fixing: m)
    by simp
  have sFsG[simp]: \<open>setter F a (s b m) = s b (setter F a m)\<close> for a b m
    apply (transfer' fixing: m)
    by simp

  have \<open>(F f \<circ>\<^sub>m G h) m = (G h \<circ>\<^sub>m F f) m\<close> for f h m
    apply (cases \<open>h (g m)\<close>; cases \<open>f (getter F m)\<close>)
    by (auto intro!: simp add: F_apply G_apply map_comp_def)
  then have 1[iff]: \<open>compatible F G\<close>
    by (auto simp: compatible_def)

  have \<open>inj (getter (F;G))\<close>
    apply (simp add: inj_def register_pair_getter)
    by (metis G_def s_def getter_of_register_from_getter_setter valid valid_getter_setter_def)
  then
  have 2: \<open>iso_register (F;G)\<close>
    apply (rule_tac iso_register_injective_getter[THEN iffD2])
    by auto

  from 1 2
  show \<open>\<exists>G :: ('c \<Rightarrow> 'c option) \<Rightarrow> 'b \<Rightarrow> 'b option. compatible F G \<and> iso_register (F;G)\<close>
    by auto
qed

(* TODO move *)
lemma getter_setter_compatible: 
  assumes \<open>compatible F G\<close>
  shows \<open>getter F (setter G a x) = getter F x \<close>
  by (smt (verit, ccfv_SIG) Axioms_Classical.compatible_setter assms comp_eq_dest compatible_def getter_setter setter_getter)

lemma complement_unique:
  fixes F :: \<open>'f update \<Rightarrow> 'm update\<close> and G :: \<open>'g update \<Rightarrow> 'm update\<close> and H :: \<open>'h update \<Rightarrow> 'm update\<close>
  assumes \<open>compatible F G\<close> and \<open>iso_register (F;G)\<close> and \<open>compatible F H\<close> and \<open>iso_register (F;H)\<close>
  shows \<open>equivalent_registers G H\<close>
proof -
  note [[simproc del: Laws_Classical.compatibility_warn]]
  note [iff] = \<open>compatible F G\<close> \<open>compatible F H\<close>
  have [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register H\<close>
    using assms compatible_register1 compatible_register2 by auto
  define gFG gFH where \<open>gFG = getter (F;G)\<close> and \<open>gFH = getter (F;H)\<close>
  define g where \<open>g b = snd (gFG (inv gFH (undefined, b)))\<close> for b :: 'h
  define s where \<open>s a m = inv g a\<close> for a and m :: 'h
  define L where \<open>L = register_from_getter_setter g s\<close>
  from assms have \<open>bij gFG\<close>
    by (simp add: bij_betw_def gFG_def iso_register_injective_getter surj_getter)
  from assms have \<open>bij gFH\<close>
    by (simp add: bij_betw_def gFH_def iso_register_injective_getter surj_getter)

  have id_g: \<open>gFG o inv gFH = map_prod id g\<close>
  proof (rule ext)
    fix ab :: \<open>'f \<times> 'h\<close>
    obtain a b where ab: \<open>ab = (a,b)\<close>
      by fastforce
    have \<open>(gFG o inv gFH) (a,b) = (gFG o inv gFH o (\<lambda>(x,y). (a,y))) (undefined :: 'f, b)\<close>
      by simp
    also have \<open>\<dots> = (gFG o setter F a o inv gFH) (undefined, b)\<close>
    proof -
      have \<open>gFH o setter F a = (\<lambda>(x,y). (a,y)) o gFH\<close>
        by (auto intro!: ext simp: gFH_def register_pair_getter compatible_sym getter_setter_compatible)
      then have \<open>gFH o setter F a o inv gFH = (\<lambda>(x,y). (a,y))\<close>
        using \<open>bij gFH\<close>
        by (metis bij_betw_inv_into bij_def o_inv_o_cancel)
      then have *: \<open>setter F a o inv gFH = inv gFH o (\<lambda>(x,y). (a,y))\<close>
        using \<open>bij gFH\<close>
        by (metis bij_betw_def comp_assoc id_o inj_iff)
      show ?thesis
        unfolding comp_assoc
        apply (subst * )
        by simp
    qed
    also have \<open>\<dots> = (a, g b)\<close>
      by (simp add: gFG_def register_pair_getter g_def getter_setter_compatible compatible_sym)
    also have \<open>\<dots> = (map_prod id g) (a, b)\<close>
      by simp
    finally show \<open>(gFG \<circ> inv gFH) ab = map_prod id g ab\<close>
      by (simp add: ab)
  qed

  have \<open>bij g\<close>
  proof -
    have \<open>bij (gFG o inv gFH)\<close>
      by (meson \<open>bij gFG\<close> \<open>bij gFH\<close> bij_betw_def bij_betw_inv_into bij_betw_trans)
    then have \<open>bij (map_prod (id :: 'f \<Rightarrow> 'f) g)\<close>
      apply (subst id_g[symmetric])
      by blast
    then show ?thesis
      apply (intro bij_def[THEN iffD2] conjI)
       apply (metis apsnd_def bij_betw_def inj_apsnd)
      by (simp add: surj_def bij_def)
  qed

  have sg[simp]: \<open>s (g m) m = m\<close> for m
    by (metis \<open>bij g\<close> bij_betw_def inv_f_f s_def)
  have surj_gH: \<open>surj (getter H)\<close>
    by (simp add: surj_getter)
  have gs[simp]: \<open>g (s a m) = a\<close> for a m
    apply (simp add: s_def)
    by (meson \<open>bij g\<close> bij_inv_eq_iff)
  have ss[simp]: \<open>s a (s b m) = s a m\<close> for a b m
    by (simp add: s_def)
  from sg gs ss have valid: \<open>valid_getter_setter g s\<close>
    by (simp add: valid_getter_setter_def)
  then have [iff]: \<open>register L\<close>
    by (simp_all add: L_def)
  from valid have [simp]: \<open>getter L = g\<close> \<open>setter L = s\<close>
    by (simp_all add: L_def)

  have \<open>setter (H o L) a m = setter G a m\<close> for a m
  proof -
    have \<open>gFH o setter H a = (\<lambda>(x,y). (x,a)) o gFH\<close> for a
      by (auto intro!: ext simp add: gFH_def register_pair_getter getter_setter_compatible)
    then have setterH: \<open>setter H a = inv gFH o (\<lambda>(x,y). (x,a)) o gFH\<close> for a
      unfolding o_def
      by (metis \<open>bij gFH\<close> bij_inv_eq_iff comp_eq_dest)

    have \<open>setter (H o L) a m = setter H (inv g a) m\<close>
      by (simp add: setter_compose s_def)
    also have \<open>\<dots> = (inv gFH o (\<lambda>(x,y). (x, inv g a)) o gFH) m\<close>
      by (simp add: setterH)
    also have \<open>\<dots> = (inv gFH o map_prod id (inv g) o (\<lambda>(x,y). (x, a)) o gFH) m\<close>
      by (simp add: gFH_def register_pair_getter)
    also have \<open>\<dots> = (inv gFH o inv (map_prod id g) o (\<lambda>(x,y). (x, a)) o gFH) m\<close>
      by (smt (verit, ccfv_SIG) UNIV_I
          \<open>(inv gFH \<circ> (\<lambda>(x, y). (x, inv g a)) \<circ> gFH) m = (inv gFH \<circ> map_prod id (inv g) \<circ> (\<lambda>(x, y). (x, a)) \<circ> gFH) m\<close> \<open>bij gFG\<close> \<open>bij gFH\<close>
          \<open>bij g\<close> \<open>setter L = s\<close> assms(3) bij_betw_def bij_betw_def bij_betw_inv_into bij_betw_inv_into_left bij_betw_trans case_prod_Pair
          case_prod_Pair comp_assoc comp_assoc comp_assoc fst_conv gFG_def gFH_def id_apply id_g map_prod.id map_prod_simp map_prod_simp
          o_apply o_apply o_apply old.prod.case prod.sel(2) register_pair_getter surj_f_inv_f surj_f_inv_f surj_gH)
    also have \<open>\<dots> = (inv gFH o inv (gFG o inv gFH) o (\<lambda>(x,y). (x, a)) o gFH) m\<close>
      using id_g by auto
    also have \<open>\<dots> = (inv gFG o (\<lambda>(x,y). (x, a)) o gFH) m\<close>
      by (smt (z3) \<open>bij gFG\<close> \<open>bij gFH\<close> bij_betw_inv_into bij_betw_trans bij_betw_trans bij_def inj_iff inj_iff o_apply o_apply o_apply
          pointfree_idE surj_f_inv_f)
    also have \<open>\<dots> = setter G a m\<close>
      by (smt (verit, del_insts) \<open>bij gFG\<close> \<open>register G\<close> assms(1,3) bij_betw_def comp_apply gFG_def gFH_def getter_setter
          getter_setter_compatible inv_f_eq register_pair_getter split_conv)
    finally show ?thesis
      by -
  qed
  then have \<open>H o L = G\<close>
    by (auto intro!: register_eqI_via_setter)

  from \<open>bij g\<close>
  have \<open>iso_register L\<close>
    by (simp add: L_def iso_register_injective_getter valid bij_betw_def)

  show \<open>equivalent_registers G H\<close>
    using \<open>H \<circ> L = G\<close> \<open>iso_register L\<close> \<open>register H\<close> equivalent_registersI equivalent_registers_sym by blast
qed


end
