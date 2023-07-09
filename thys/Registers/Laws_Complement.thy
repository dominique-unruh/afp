section \<open>Generic laws about complements\<close>

theory Laws_Complement
  imports Laws Axioms_Complement
begin

notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

definition \<open>complements F G \<longleftrightarrow> disjoint F G \<and> iso_reference (F;G)\<close>

lemma complementsI: \<open>disjoint F G \<Longrightarrow> iso_reference (F;G) \<Longrightarrow> complements F G\<close>
  using complements_def by blast

lemma complement_exists: 
  fixes F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>
  assumes \<open>reference F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::domain = cdc F.
          \<exists>G :: 'c update \<Rightarrow> 'b update. complements F G\<close>
  by (simp add: assms complement_exists complements_def)

lemma complements_sym: \<open>complements G F\<close> if \<open>complements F G\<close>
proof (rule complementsI)
  show [simp]: \<open>disjoint G F\<close>
    using disjoint_sym complements_def that by blast
  from that have \<open>iso_reference (F;G)\<close>
    by (meson complements_def)
  then obtain I where [simp]: \<open>reference I\<close> and \<open>(F;G) o I = id\<close> and \<open>I o (F;G) = id\<close>
    using iso_reference_def by blast
  have \<open>reference (swap o I)\<close>
    using \<open>reference I\<close> reference_comp reference_swap by blast
  moreover have \<open>(G;F) o (swap o I) = id\<close>
    by (simp add: \<open>(F;G) \<circ> I = id\<close> rewriteL_comp_comp)
  moreover have \<open>(swap o I) o (G;F) = id\<close>
    by (metis (no_types, opaque_lifting) swap_swap \<open>I \<circ> (F;G) = id\<close> calculation(2) comp_def eq_id_iff)
  ultimately show \<open>iso_reference (G;F)\<close>
    using \<open>disjoint G F\<close> iso_reference_def pair_is_reference by blast
qed

definition complement :: \<open>('a::domain update \<Rightarrow> 'b::domain_with_simple_complement update) \<Rightarrow> (('a,'b) complement_domain_simple update \<Rightarrow> 'b update)\<close> where
  \<open>complement F = (SOME G :: ('a, 'b) complement_domain_simple update \<Rightarrow> 'b update. disjoint F G \<and> iso_reference (F;G))\<close>

lemma reference_complement[simp]: \<open>reference (complement F)\<close> if \<open>reference F\<close>
  using complement_exists_simple[OF that]
  by (metis (no_types, lifting) disjoint_def complement_def some_eq_imp)

lemma complement_is_complement[simp]:
  assumes \<open>reference F\<close>
  shows \<open>complements F (complement F)\<close>
  using complement_exists_simple[OF assms] unfolding complements_def
  by (metis (mono_tags, lifting) complement_def some_eq_imp)

lemma complement_unique:
  assumes \<open>complements F G\<close>
  assumes \<open>complements F G'\<close>
  shows \<open>equivalent_references G G'\<close>
  apply (rule complement_unique[where F=F])
  using assms unfolding complements_def by auto

lemma complement_unique':
  assumes \<open>complements F G\<close>
  shows \<open>equivalent_references G (complement F)\<close>
  apply (rule complement_unique[where F=F])
  using assms unfolding complements_def using disjoint_reference1 complement_is_complement complements_def by blast+

lemma disjoint_complement[simp]: \<open>reference F \<Longrightarrow> disjoint F (complement F)\<close>
  using complement_is_complement complements_def by blast

lemma complements_reference_tensor:
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close>
  shows \<open>complements (F \<otimes>\<^sub>r G) (complement F \<otimes>\<^sub>r complement G)\<close>
proof (rule complementsI)
  have sep4: \<open>separating TYPE('z::domain) {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d) |a b c d. True}\<close>
    apply (rule separating_tensor'[where A=\<open>{(a \<otimes>\<^sub>u b) |a b. True}\<close> and B=\<open>{(c \<otimes>\<^sub>u d) |c d. True}\<close>])
      apply (rule separating_tensor'[where A=UNIV and B=UNIV]) apply auto[3]
     apply (rule separating_tensor'[where A=UNIV and B=UNIV]) apply auto[3]
    by auto
  show disjoint: \<open>disjoint (F \<otimes>\<^sub>r G) (complement F \<otimes>\<^sub>r complement G)\<close>
    by (metis assms(1) assms(2) disjoint_reference_tensor complement_is_complement complements_def)
  let ?reorder = \<open>((Fst o Fst; Snd o Fst); (Fst o Snd; Snd o Snd))\<close>
  have [simp]: \<open>reference ?reorder\<close>
    by auto
  have [simp]: \<open>?reorder ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d)) = ((a \<otimes>\<^sub>u c) \<otimes>\<^sub>u (b \<otimes>\<^sub>u d))\<close> 
    for a::\<open>'t::domain update\<close> and b::\<open>'u::domain update\<close> and c::\<open>'v::domain update\<close> and d::\<open>'w::domain update\<close>
    by (simp add: reference_pair_apply Fst_def Snd_def tensor_update_mult)
  have [simp]: \<open>iso_reference ?reorder\<close>
    apply (rule iso_referenceI[of _ ?reorder]) apply auto[2]
     apply (rule reference_eqI[OF sep4]) apply auto[3]
    apply (rule reference_eqI[OF sep4]) by auto
  have \<open>(F \<otimes>\<^sub>r G; complement F \<otimes>\<^sub>r complement G) = ((F; complement F) \<otimes>\<^sub>r (G; complement G)) o ?reorder\<close>
    apply (rule reference_eqI[OF sep4])
    by (auto intro!: reference_prereference reference_comp reference_tensor_is_reference pair_is_reference
        simp: disjoint reference_pair_apply tensor_update_mult)
  moreover have \<open>iso_reference \<dots>\<close>
    apply (auto intro!: iso_reference_comp iso_reference_tensor_is_iso_reference)
    using assms complement_is_complement complements_def by blast+
  ultimately show \<open>iso_reference (F \<otimes>\<^sub>r G;complement F \<otimes>\<^sub>r complement G)\<close>
    by simp
qed

definition is_unit_reference where
  \<open>is_unit_reference U \<longleftrightarrow> complements U id\<close>

lemma reference_unit_reference[simp]: \<open>is_unit_reference U \<Longrightarrow> reference U\<close>
  by (simp add: disjoint_def complements_def is_unit_reference_def)

lemma unit_reference_disjoint[simp]: \<open>disjoint U X\<close> if \<open>is_unit_reference U\<close> \<open>reference X\<close>
  by (metis disjoint_comp_right complements_def id_comp is_unit_reference_def that(1) that(2))

lemma unit_reference_disjoint'[simp]: \<open>disjoint X U\<close> if \<open>is_unit_reference U\<close> \<open>reference X\<close>
  using disjoint_sym that(1) that(2) unit_reference_disjoint by blast

lemma disjoint_complement_left[simp]: \<open>reference X \<Longrightarrow> disjoint (complement X) X\<close>
  using disjoint_sym complement_is_complement complements_def by blast

lemma disjoint_complement_right[simp]: \<open>reference X \<Longrightarrow> disjoint X (complement X)\<close>
  using complement_is_complement complements_def by blast

lemma unit_reference_pair[simp]: \<open>equivalent_references X (U; X)\<close> if [simp]: \<open>is_unit_reference U\<close> \<open>reference X\<close>
proof -
  from complement_exists[OF \<open>reference X\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'x::domain = cdc X. equivalent_references X (U; X)\<close>
  proof (rule with_type_mp)
    note [[simproc del: disjointness_warn]]
    assume \<open>\<exists>G :: 'x update \<Rightarrow> 'b update. complements X G\<close>
    then obtain compX :: \<open>'x update \<Rightarrow> 'b update\<close> where compX: \<open>complements X compX\<close>
      by blast
    then have [simp]: \<open>reference compX\<close> \<open>disjoint X compX\<close>
      by (auto simp add: disjoint_def complements_def)

    have \<open>equivalent_references id (U; id)\<close>
      using complements_def is_unit_reference_def iso_reference_equivalent_id that(1) by blast
    also have \<open>equivalent_references \<dots> (U; (X; compX))\<close>
      apply (rule equivalent_references_pair_right)
       apply (auto intro!: unit_reference_disjoint)
      using compX complements_def by blast
    also have \<open>equivalent_references \<dots> ((U; X); compX)\<close>
      apply (rule equivalent_references_assoc)
      by auto
    finally have \<open>complements (U; X) compX\<close>
      by (auto simp: equivalent_references_def complements_def)
    moreover have \<open>equivalent_references (X; compX) id\<close>
      using compX complements_def equivalent_references_sym iso_reference_equivalent_id by blast
    ultimately show \<open>equivalent_references X (U; X)\<close>
      by (meson complement_unique compX complements_sym)
  qed
  from this[cancel_with_type]
  show \<open>equivalent_references X (U; X)\<close>
    by -
qed


lemma unit_reference_compose_left:
  assumes [simp]: \<open>is_unit_reference U\<close>
  assumes [simp]: \<open>reference A\<close>
  shows \<open>is_unit_reference (A o U)\<close>
proof -
  from complement_exists[OF \<open>reference A\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'x::domain = cdc A. is_unit_reference (A o U)\<close>
  proof (rule with_type_mp)
    note [[simproc del: disjointness_warn]]
    assume \<open>\<exists>G :: 'x update \<Rightarrow> 'c update. complements A G\<close>
    then obtain compA :: \<open>'x update \<Rightarrow> 'c update\<close> where compX: \<open>complements A compA\<close>
      by blast
    then have [simp]: \<open>reference compA\<close> \<open>disjoint A compA\<close>
      by (auto simp add: disjoint_def complements_def)

    have compat'[simp]: \<open>disjoint (A o U) (A; compA)\<close>
      apply (auto intro!: disjoint3')
      by (metis assms(1) assms(2) comp_id disjoint_comp_inner complements_def is_unit_reference_def)
    moreover have \<open>equivalent_references (A; compA) id\<close>
      using compX complements_def equivalent_references_sym iso_reference_equivalent_id by blast
    ultimately have disjoint[simp]: \<open>disjoint (A o U) id\<close>
      using equivalent_references_disjoint2 by blast

    have \<open>equivalent_references (A o U; id) (A o U; (A; compA))\<close>
      apply (auto intro!: equivalent_references_pair_right)
      using compX complements_def by auto
    also have \<open>equivalent_references \<dots> (A o U; (A o id; compA))\<close>
      by (auto intro!: equivalent_references_refl pair_is_reference)
    also have \<open>equivalent_references \<dots> ((A o U; A o id); compA)\<close>
      apply (intro equivalent_references_assoc disjoint_comp_inner)
      by auto
    also have \<open>equivalent_references \<dots> (A o (U; id); compA)\<close>
      by (metis (no_types, opaque_lifting) assms(1) assms(2) calculation complements_def equivalent_references_sym equivalent_references_trans is_unit_reference_def reference_comp_pair)
    also have \<open>equivalent_references \<dots> (A o id; compA)\<close>
      apply (intro equivalent_references_pair_left equivalent_references_comp)
        apply (auto simp: assms)
      using assms(1) equivalent_references_sym reference_id unit_reference_pair by blast
    also have \<open>equivalent_references \<dots> id\<close>
      by (simp add: \<open>equivalent_references (A;compA) id\<close>)
    finally show \<open>is_unit_reference (A o U)\<close>
      using disjoint complementsI equivalent_references_sym is_unit_reference_def iso_reference_equivalent_id by blast
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma unit_reference_compose_right:
  assumes [simp]: \<open>is_unit_reference U\<close>
  assumes [simp]: \<open>iso_reference A\<close>
  shows \<open>is_unit_reference (U o A)\<close>
proof (unfold is_unit_reference_def, rule complementsI)
  show \<open>disjoint (U \<circ> A) id\<close>
    by (simp add: iso_reference_is_reference)
  have 1: \<open>iso_reference ((U;id) \<circ> A \<otimes>\<^sub>r id)\<close>
    by (meson assms(1) assms(2) complements_def is_unit_reference_def iso_reference_comp iso_reference_id iso_reference_tensor_is_iso_reference)
  have 2: \<open>id \<circ> ((U;id) \<circ> A \<otimes>\<^sub>r id) = (U \<circ> A;id)\<close>
    by (metis assms(1) assms(2) complements_def fun.map_id is_unit_reference_def iso_reference_id iso_reference_is_reference pair_o_tensor)
  show \<open>iso_reference (U \<circ> A;id)\<close>
    using 1 2 by auto
qed

lemma unit_reference_unique:
  assumes \<open>is_unit_reference F\<close>
  assumes \<open>is_unit_reference G\<close>
  shows \<open>equivalent_references F G\<close>
proof -
  have \<open>complements F id\<close> \<open>complements G id\<close>
    using assms by (metis complements_def equivalent_references_def id_comp is_unit_reference_def)+
  then show ?thesis
    by (meson complement_unique complements_sym equivalent_references_sym equivalent_references_trans)
qed

lemma unit_reference_domains_isomorphic:
  fixes F :: \<open>'a::domain update \<Rightarrow> 'c::domain update\<close>
  fixes G :: \<open>'b::domain update \<Rightarrow> 'd::domain update\<close>
  assumes \<open>is_unit_reference F\<close>
  assumes \<open>is_unit_reference G\<close>
  shows \<open>\<exists>I :: 'a update \<Rightarrow> 'b update. iso_reference I\<close>
proof -
  have \<open>is_unit_reference ((\<lambda>d. tensor_update id_update d) o G)\<close>
    by (simp add: assms(2) unit_reference_compose_left)
  moreover have \<open>is_unit_reference ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using assms(1) reference_tensor_left unit_reference_compose_left by blast
  ultimately have \<open>equivalent_references ((\<lambda>d. tensor_update id_update d) o G) ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using unit_reference_unique by blast
  then show ?thesis
    unfolding equivalent_references_def by auto
qed


lemma id_complement_is_unit_reference[simp]: \<open>is_unit_reference (complement id)\<close>
  by (metis is_unit_reference_def complement_is_complement complements_def complements_sym equivalent_references_def id_comp reference_id)

type_synonym unit_reference_domain = \<open>(some_domain, some_domain) complement_domain_simple\<close>
definition unit_reference :: \<open>unit_reference_domain update \<Rightarrow> 'a::domain update\<close> where \<open>unit_reference = (SOME U. is_unit_reference U)\<close>

lemma unit_reference_is_unit_reference[simp]: \<open>is_unit_reference (unit_reference :: unit_reference_domain update \<Rightarrow> 'a::domain update)\<close>
proof -
  note [[simproc del: disjointness_warn]]
  let ?U = \<open>unit_reference :: unit_reference_domain update \<Rightarrow> 'a::domain update\<close>
  let ?U1 = \<open>complement id :: unit_reference_domain update \<Rightarrow> some_domain update\<close>
  from complement_exists[OF reference_id[where 'a='a]]
  have \<open>\<forall>\<^sub>\<tau> 'x::domain = cdc (id::'a update \<Rightarrow> _). is_unit_reference ?U\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G :: 'x update \<Rightarrow> 'a update. complements id G\<close>
    then obtain U2 :: \<open>'x update \<Rightarrow> 'a update\<close> where comp1: \<open>complements id U2\<close>
      by blast
    then have [simp]: \<open>reference U2\<close> \<open>disjoint id U2\<close> \<open>disjoint id U2\<close>
      by (auto simp add: disjoint_def complements_def)

    have \<open>is_unit_reference ?U1\<close> \<open>is_unit_reference U2\<close>
       apply auto by (simp add: comp1 complements_sym is_unit_reference_def)

    then obtain I :: \<open>unit_reference_domain update \<Rightarrow> 'x update\<close> where \<open>iso_reference I\<close>
      apply atomize_elim by (rule unit_reference_domains_isomorphic)
    with \<open>is_unit_reference U2\<close> have \<open>is_unit_reference (U2 o I)\<close>
      by (rule unit_reference_compose_right)
    then show \<open>is_unit_reference ?U\<close>
      by (metis someI_ex unit_reference_def)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma unit_reference_domain_tensor_unit:
  fixes U :: \<open>'a::domain update \<Rightarrow> _\<close>
  assumes \<open>is_unit_reference U\<close>
  shows \<open>\<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_reference I\<close>
  (* Can we show that I = (\<lambda>x. tensor_update id_update x) ? It would be nice but I do not see how to prove it. *)
proof -
  from complement_exists[OF reference_id[where 'a='b]]
  have \<open>\<forall>\<^sub>\<tau> 'x::domain = cdc (id :: 'b update \<Rightarrow> _). \<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_reference I\<close>
  proof (rule with_type_mp)
    note [[simproc del: disjointness_warn]]
    assume \<open>\<exists>G :: 'x update \<Rightarrow> 'b update. complements id G\<close>
    then obtain U' :: \<open>'x update \<Rightarrow> 'b update\<close> where comp: \<open>complements id U'\<close>
      by blast
    then have [simp]: \<open>reference U'\<close> \<open>disjoint id U'\<close> \<open>disjoint U' id\<close>
      by (auto simp add: disjoint_def complements_def)
    have \<open>is_unit_reference U'\<close>
      by (simp add: comp complements_sym is_unit_reference_def)

    have \<open>equivalent_references (id :: 'b update \<Rightarrow> _) (U'; id)\<close>
      using comp complements_def complements_sym iso_reference_equivalent_id by blast
    then obtain J :: \<open>'b update \<Rightarrow> (('x * 'b) update)\<close> where \<open>iso_reference J\<close>
      using equivalent_references_def iso_reference_inv by blast
    moreover obtain K :: \<open>'x update \<Rightarrow> 'a update\<close> where \<open>iso_reference K\<close>
      apply atomize_elim 
      using \<open>is_unit_reference U'\<close> assms
      by (rule unit_reference_domains_isomorphic)
    ultimately have \<open>iso_reference ((K \<otimes>\<^sub>r id) o J)\<close>
      by auto
    then show \<open>\<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_reference I\<close>
      by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by-
qed

lemma disjoint_complement_pair1:
  assumes \<open>disjoint F G\<close>
  shows \<open>disjoint F (complement (F;G))\<close>
  by (metis assms disjoint_comp_left disjoint_complement_right pair_is_reference reference_Fst reference_pair_Fst)

lemma disjoint_complement_pair2:
  assumes [simp]: \<open>disjoint F G\<close>
  shows \<open>disjoint G (complement (F;G))\<close>
proof -
  have \<open>disjoint (F;G) (complement (F;G))\<close>
    by simp
  then have \<open>disjoint ((F;G) o Snd) (complement (F;G))\<close>
    by auto
  then show ?thesis
    by (auto simp: reference_pair_Snd)
qed

lemma equivalent_complements:
  assumes \<open>complements F G\<close>
  assumes \<open>equivalent_references G G'\<close>
  shows \<open>complements F G'\<close>
  apply (rule complementsI)
   apply (metis assms(1) assms(2) disjoint_comp_right complements_def equivalent_references_def iso_reference_is_reference)
  by (metis assms(1) assms(2) complements_def equivalent_references_def equivalent_references_pair_right iso_reference_comp)

lemma complements_complement_pair:
  assumes [simp]: \<open>disjoint F G\<close>
  assumes FG': \<open>complements (F;G) FG'\<close>
  shows \<open>complements F (G; FG')\<close>
proof (rule complementsI)
  note [[simproc del: disjointness_warn]]
  have \<open>disjoint (F;G) FG'\<close>
    using FG' complements_def by auto
  then have [simp]: \<open>disjoint F FG'\<close>
    by (smt (verit)assms(1) disjointI disjoint_reference1 disjoint_reference2 id_update_right reference_of_id reference_pair_apply' swap_references)
  have [simp]: \<open>disjoint G FG'\<close>
    by (smt (verit) reference_pair_apply \<open>disjoint (F;G) FG'\<close> assms(1) disjointI disjoint_reference1 disjoint_reference2 id_update_right reference_of_id swap_references)

  have \<open>equivalent_references (F; (G; FG')) ((F;G); FG')\<close>
    apply (rule equivalent_references_assoc)
      apply simp
     apply (smt (verit) \<open>disjoint (F;G) FG'\<close> assms(1) disjointI disjoint_reference1 disjoint_reference2 id_update_right reference_of_id reference_pair_apply' swap_references)
    by (smt (verit) reference_pair_apply \<open>disjoint (F;G) FG'\<close> assms(1) disjointI disjoint_reference1 disjoint_reference2 id_update_right reference_of_id swap_references)
  also have \<open>equivalent_references \<dots> id\<close>
    by (meson assms complement_is_complement complements_def equivalent_references_sym iso_reference_equivalent_id pair_is_reference)
  finally show \<open>iso_reference (F;(G;FG'))\<close>
    using equivalent_references_sym iso_reference_equivalent_id by blast
  show \<open>disjoint F (G;FG')\<close>
    by (auto intro!: disjoint3')
qed

lemma equivalent_references_complement:
  assumes \<open>equivalent_references F G\<close>
  assumes \<open>complements F F'\<close>
  assumes \<open>complements G G'\<close>
  shows \<open>equivalent_references F' G'\<close>
  by (meson complement_unique assms(1) assms(2) assms(3) complements_sym equivalent_complements)

lemma equivalent_references_complement':
  assumes \<open>equivalent_references F G\<close>
  shows \<open>equivalent_references (complement F) (complement G)\<close>
  using assms apply (rule equivalent_references_complement)
  using assms complement_is_complement equivalent_references_reference_left equivalent_references_reference_right
  by blast+

lemma complements_complement_pair':
  assumes [simp]: \<open>disjoint F G\<close>
  assumes FG': \<open>complements (F;G) FG'\<close>
  shows \<open>complements G (F; FG')\<close>
proof -
  have \<open>equivalent_references (F;G) (G;F)\<close>
    using assms(1) equivalent_references_def iso_reference_swap pair_is_reference pair_o_swap by blast
  with FG' have *: \<open>complements (G;F) FG'\<close>
    by (meson complements_sym equivalent_complements)
  show ?thesis
    apply (rule complements_complement_pair)
    using * by (simp_all add: disjoint_sym)
qed

lemma complements_chain: 
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close>
  shows \<open>complements (F o G) (complement F; F o complement G)\<close>
proof (rule complementsI)
  show \<open>disjoint (F o G) (complement F; F o complement G)\<close>
    by auto
  have \<open>equivalent_references (F \<circ> G;(complement F;F \<circ> complement G)) (F \<circ> G;(F \<circ> complement G;complement F))\<close>
    apply (rule equivalent_referencesI[where I=\<open>id \<otimes>\<^sub>r swap\<close>])
    by (auto intro!: iso_reference_tensor_is_iso_reference simp: pair_o_tensor)
  also have \<open>equivalent_references \<dots> ((F \<circ> G;F \<circ> complement G);complement F)\<close>
    apply (rule equivalent_referencesI[where I=assoc])
    by (auto intro!: iso_reference_tensor_is_iso_reference simp: pair_o_tensor)
  also have \<open>equivalent_references \<dots> (F o (G; complement G);complement F)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) calculation disjoint_complement_right
        equivalent_references_sym equivalent_references_trans reference_comp_pair)
  also have \<open>equivalent_references \<dots> (F o id;complement F)\<close>
    apply (rule equivalent_references_pair_left, simp)
    apply (rule equivalent_references_comp, simp)
    by (metis assms(2) complement_is_complement complements_def equivalent_references_def iso_reference_def)
  also have \<open>equivalent_references \<dots> id\<close>
    by (metis assms(1) comp_id complement_is_complement complements_def equivalent_references_def iso_reference_def)
  finally show \<open>iso_reference (F \<circ> G;(complement F;F \<circ> complement G))\<close>
    using equivalent_references_sym iso_reference_equivalent_id by blast
qed

lemma complements_Fst_Snd[simp]: \<open>complements Fst Snd\<close>
  by (auto intro!: complementsI simp: pair_Fst_Snd)

lemma complements_Snd_Fst[simp]: \<open>complements Snd Fst\<close>
  by (auto intro!: complementsI simp flip: swap_def)

lemma disjoint_unit_reference[simp]: \<open>reference F \<Longrightarrow> disjoint F unit_reference\<close>
  using disjoint_sym unit_reference_disjoint unit_reference_is_unit_reference by blast

lemma complements_id_unit_reference[simp]: \<open>complements id unit_reference\<close>
  using complements_sym is_unit_reference_def unit_reference_is_unit_reference by blast

lemma complements_iso_unit_reference: \<open>iso_reference I \<Longrightarrow> is_unit_reference U \<Longrightarrow> complements I U\<close>
  using complements_sym equivalent_complements is_unit_reference_def iso_reference_equivalent_id by blast

lemma iso_reference_complement_is_unit_reference[simp]:
  assumes \<open>iso_reference F\<close>
  shows \<open>is_unit_reference (complement F)\<close>
  by (meson assms complement_is_complement complements_sym equivalent_complements equivalent_references_sym is_unit_reference_def iso_reference_equivalent_id iso_reference_is_reference)

text \<open>Adding support for \<^term>\<open>is_unit_reference F\<close> and \<^term>\<open>complements F G\<close> to the [@{attribute reference}] attribute\<close>
lemmas [reference_attribute_rule] = is_unit_reference_def[THEN iffD1] complements_def[THEN iffD1]
lemmas [reference_attribute_rule_immediate] = asm_rl[of \<open>is_unit_reference _\<close>]

no_notation comp_update (infixl "*\<^sub>u" 55)
no_notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

end
