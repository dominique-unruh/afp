section \<open>Generic laws about references\<close>

theory Laws
  imports Axioms
begin

text \<open>This notation is only used inside this file\<close>
notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)
notation reference_pair ("'(_;_')")

subsection \<open>Elementary facts\<close>

declare id_prereference[simp]
declare id_update_left[simp]
declare id_update_right[simp]
declare reference_prereference[simp]
declare reference_comp[simp]
declare reference_of_id[simp]
declare reference_tensor_left[simp]
declare reference_tensor_right[simp]
declare prereference_mult_right[simp]
declare prereference_mult_left[simp]
declare reference_id[simp]

subsection \<open>Prereferences\<close>

lemma prereference_tensor_left[simp]: \<open>prereference (\<lambda>b::'b::domain update. tensor_update a b)\<close>
  for a :: \<open>'a::domain update\<close>
proof -
  have \<open>prereference ((\<lambda>b1::('a\<times>'b) update. (a \<otimes>\<^sub>u id_update) *\<^sub>u b1) o (\<lambda>b. tensor_update id_update b))\<close>
    by (rule comp_prereference; simp)
  then show ?thesis
    by (simp add: o_def tensor_update_mult)
qed

lemma prereference_tensor_right[simp]: \<open>prereference (\<lambda>a::'a::domain update. tensor_update a b)\<close>  
  for b :: \<open>'b::domain update\<close>
proof -
  have \<open>prereference ((\<lambda>a1::('a\<times>'b) update. (id_update \<otimes>\<^sub>u b) *\<^sub>u a1) o (\<lambda>a. tensor_update a id_update))\<close>
    by (rule comp_prereference, simp_all)
  then show ?thesis
    by (simp add: o_def tensor_update_mult)
qed

subsection \<open>Registers\<close>

lemma id_update_tensor_reference[simp]:
  assumes \<open>reference F\<close>
  shows \<open>reference (\<lambda>a::'a::domain update. id_update \<otimes>\<^sub>u F a)\<close>
  using assms apply (rule reference_comp[unfolded o_def])
  by simp

lemma reference_tensor_id_update[simp]:
  assumes \<open>reference F\<close>
  shows \<open>reference (\<lambda>a::'a::domain update. F a \<otimes>\<^sub>u id_update)\<close>
  using assms apply (rule reference_comp[unfolded o_def])
  by simp

subsection \<open>Tensor product of references\<close>

definition reference_tensor  (infixr "\<otimes>\<^sub>r" 70) where
  "reference_tensor F G = reference_pair (\<lambda>a. tensor_update (F a) id_update) (\<lambda>b. tensor_update id_update (G b))"

lemma reference_tensor_is_reference: 
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  shows "reference F \<Longrightarrow> reference G \<Longrightarrow> reference (F \<otimes>\<^sub>r G)"
  unfolding reference_tensor_def
  apply (rule reference_pair_is_reference)
  by (simp_all add: tensor_update_mult)

lemma reference_tensor_apply[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  assumes \<open>reference F\<close> and \<open>reference G\<close>
  shows "(F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b) = F a \<otimes>\<^sub>u G b"
  unfolding reference_tensor_def
  apply (subst reference_pair_apply)
  unfolding reference_tensor_def 
  by (simp_all add: assms tensor_update_mult)

definition "separating (_::'b::domain itself) A \<longleftrightarrow> 
  (\<forall>F G :: 'a::domain update \<Rightarrow> 'b update. prereference F \<longrightarrow> prereference G \<longrightarrow> (\<forall>x\<in>A. F x = G x) \<longrightarrow> F = G)"

lemma separating_UNIV[simp]: \<open>separating TYPE(_) UNIV\<close>
  unfolding separating_def by auto

lemma separating_mono: \<open>A \<subseteq> B \<Longrightarrow> separating TYPE('a::domain) A \<Longrightarrow> separating TYPE('a) B\<close>
  unfolding separating_def by (meson in_mono) 

lemma reference_eqI: \<open>separating TYPE('b::domain) A \<Longrightarrow> prereference F \<Longrightarrow> prereference G \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> F x = G x) \<Longrightarrow> F = (G::_ \<Rightarrow> 'b update)\<close>
  unfolding separating_def by auto

lemma separating_tensor:
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes [simp]: \<open>separating TYPE('c::domain) A\<close>
  assumes [simp]: \<open>separating TYPE('c) B\<close>
  shows \<open>separating TYPE('c) {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
proof (unfold separating_def, intro allI impI)
  fix F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c update\<close>
  assume [simp]: \<open>prereference F\<close> \<open>prereference G\<close>
  have [simp]: \<open>prereference (\<lambda>x. F (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>prereference F\<close> apply (rule comp_prereference[unfolded o_def])
    by simp
  have [simp]: \<open>prereference (\<lambda>x. G (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>prereference G\<close> apply (rule comp_prereference[unfolded o_def])
    by simp
  have [simp]: \<open>prereference (\<lambda>x. F (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>prereference F\<close> apply (rule comp_prereference[unfolded o_def])
    by simp
  have [simp]: \<open>prereference (\<lambda>x. G (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>prereference G\<close> apply (rule comp_prereference[unfolded o_def])
    by simp

  assume \<open>\<forall>x\<in>{a \<otimes>\<^sub>u b |a b. a\<in>A \<and> b\<in>B}. F x = G x\<close>
  then have EQ: \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> and \<open>b \<in> B\<close> for a b
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> for a b
    apply (rule reference_eqI[where A=B, THEN fun_cong, where x=b, rotated -1])
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> for a b
    apply (rule reference_eqI[where A=A, THEN fun_cong, where x=a, rotated -1])
    by auto
  then show "F = G"
    apply (rule tensor_extensionality[rotated -1])
    by auto
qed

lemma reference_tensor_distrib:
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close> \<open>reference H\<close> \<open>reference L\<close>
  shows \<open>(F \<otimes>\<^sub>r G) o (H \<otimes>\<^sub>r L) = (F o H) \<otimes>\<^sub>r (G o L)\<close>
  apply (rule tensor_extensionality)
  by (auto intro!: reference_comp reference_prereference reference_tensor_is_reference)

text \<open>The following is easier to apply using the @{method rule}-method than @{thm [source] separating_tensor}\<close>
lemma separating_tensor':
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes \<open>separating TYPE('c::domain) A\<close>
  assumes \<open>separating TYPE('c) B\<close>
  assumes \<open>C = {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
  shows \<open>separating TYPE('c) C\<close>
  using assms
  by (simp add: separating_tensor)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close>
  assumes "\<And>f g h. F (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = G (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule reference_eqI[where A=\<open>{a\<otimes>\<^sub>ub\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>separating TYPE('d) {b \<otimes>\<^sub>u c |b c. True}\<close>
    apply (rule separating_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>separating TYPE('d) {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac separating_tensor'[where A=UNIV and B=\<open>{b\<otimes>\<^sub>uc| b c. True}\<close>])
    by auto
  show \<open>prereference F\<close> \<open>prereference G\<close> by auto
  show \<open>x \<in> {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed

lemma tensor_extensionality3': 
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>reference F\<close> \<open>reference G\<close>
  assumes "\<And>f g h. F ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = G ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule reference_eqI[where A=\<open>{(a\<otimes>\<^sub>ub)\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>separating TYPE('d) {a \<otimes>\<^sub>u b | a b. True}\<close>
    apply (rule separating_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>separating TYPE('d) {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac separating_tensor'[where B=UNIV and A=\<open>{a\<otimes>\<^sub>ub| a b. True}\<close>])
    by auto
  show \<open>prereference F\<close> \<open>prereference G\<close> by auto
  show \<open>x \<in> {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed

lemma reference_tensor_id[simp]: \<open>id \<otimes>\<^sub>r id = id\<close>
  apply (rule tensor_extensionality)
  by (auto simp add: reference_tensor_is_reference)

subsection \<open>Pairs and compatibility\<close>

definition disjoint :: \<open>('a::domain update \<Rightarrow> 'c::domain update)
                       \<Rightarrow> ('b::domain update \<Rightarrow> 'c update) \<Rightarrow> bool\<close> where
  \<open>disjoint F G \<longleftrightarrow> reference F \<and> reference G \<and> (\<forall>a b. F a *\<^sub>u G b = G b *\<^sub>u F a)\<close>

lemma disjointI:
  assumes "reference F" and "reference G"
  assumes \<open>\<And>a b. (F a) *\<^sub>u (G b) = (G b) *\<^sub>u (F a)\<close>
  shows "disjoint F G"
  using assms unfolding disjoint_def by simp

lemma swap_references:
  assumes "disjoint R S"
  shows "R a *\<^sub>u S b = S b *\<^sub>u R a"
  using assms unfolding disjoint_def by metis

lemma disjoint_sym: "disjoint x y \<Longrightarrow> disjoint y x"
  by (simp add: disjoint_def)

lemma pair_is_reference[simp]:
  assumes "disjoint F G"
  shows "reference (F; G)"
  by (metis assms disjoint_def reference_pair_is_reference)

lemma reference_pair_apply:
  assumes \<open>disjoint F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (F a) *\<^sub>u (G b)\<close>
  apply (rule reference_pair_apply)
  using assms unfolding disjoint_def by metis+

lemma reference_pair_apply':
  assumes \<open>disjoint F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (G b) *\<^sub>u (F a)\<close>
  apply (subst reference_pair_apply)
  using assms by (auto simp: disjoint_def intro: reference_prereference)



lemma disjoint_comp_left[simp]: "disjoint F G \<Longrightarrow> reference H \<Longrightarrow> disjoint (F \<circ> H) G"
  by (simp add: disjoint_def)

lemma disjoint_comp_right[simp]: "disjoint F G \<Longrightarrow> reference H \<Longrightarrow> disjoint F (G \<circ> H)"
  by (simp add: disjoint_def)

lemma disjoint_comp_inner[simp]: 
  "disjoint F G \<Longrightarrow> reference H \<Longrightarrow> disjoint (H \<circ> F) (H \<circ> G)"
  by (smt (verit, best) comp_apply disjoint_def reference_comp reference_mult)

lemma disjoint_reference1: \<open>disjoint F G \<Longrightarrow> reference F\<close>
  by (simp add: disjoint_def)
lemma disjoint_reference2: \<open>disjoint F G \<Longrightarrow> reference G\<close>
  by (simp add: disjoint_def)

lemma pair_o_tensor:
  assumes "disjoint A B" and [simp]: \<open>reference C\<close> and [simp]: \<open>reference D\<close>
  shows "(A; B) o (C \<otimes>\<^sub>r D) = (A o C; B o D)"
  apply (rule tensor_extensionality)
  using assms by (simp_all add: reference_tensor_is_reference reference_pair_apply comp_prereference)

lemma disjoint_tensor_id_update_left[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "disjoint F G"
  shows "disjoint (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  using assms apply (rule disjoint_comp_inner[unfolded o_def])
  by simp

lemma disjoint_tensor_id_update_right[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "disjoint F G"
  shows "disjoint (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  using assms apply (rule disjoint_comp_inner[unfolded o_def])
  by simp

lemma disjoint_tensor_id_update_rl[simp]:
  assumes "reference F" and "reference G"
  shows "disjoint (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  apply (rule disjointI)
  using assms by (auto simp: tensor_update_mult)

lemma disjoint_tensor_id_update_lr[simp]:
  assumes "reference F" and "reference G"
  shows "disjoint (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  apply (rule disjointI)
  using assms by (auto simp: tensor_update_mult)

lemma reference_comp_pair:
  assumes [simp]: \<open>reference F\<close> and [simp]: \<open>disjoint G H\<close>
  shows "(F o G; F o H) = F o (G; H)"
proof (rule tensor_extensionality)
  show \<open>prereference (F \<circ> G;F \<circ> H)\<close> and \<open>prereference (F \<circ> (G;H))\<close>
    by simp_all

  have [simp]: \<open>disjoint (F o G) (F o H)\<close>
    apply (rule disjoint_comp_inner, simp)
    by simp
  then have [simp]: \<open>reference (F \<circ> G)\<close> \<open>reference (F \<circ> H)\<close>
    unfolding disjoint_def by auto
  from assms have [simp]: \<open>reference G\<close> \<open>reference H\<close>
    unfolding disjoint_def by auto
  fix a b
  show \<open>(F \<circ> G;F \<circ> H) (a \<otimes>\<^sub>u b) = (F \<circ> (G;H)) (a \<otimes>\<^sub>u b)\<close>
    by (auto simp: reference_pair_apply reference_mult tensor_update_mult)
qed

lemma swap_references_left:
  assumes "disjoint R S"
  shows "R a *\<^sub>u S b *\<^sub>u c = S b *\<^sub>u R a *\<^sub>u c"
  using assms unfolding disjoint_def by metis

lemma swap_references_right:
  assumes "disjoint R S"
  shows "c *\<^sub>u R a *\<^sub>u S b = c *\<^sub>u S b *\<^sub>u R a"
  by (metis assms comp_update_assoc disjoint_def)

lemmas disjoint_ac_rules = swap_references comp_update_assoc[symmetric] swap_references_right

subsection \<open>Fst and Snd\<close>

(* TODO: specify types *)
definition Fst where \<open>Fst a = a \<otimes>\<^sub>u id_update\<close>
definition Snd where \<open>Snd a = id_update \<otimes>\<^sub>u a\<close>

lemma reference_Fst[simp]: \<open>reference Fst\<close>
  unfolding Fst_def by (rule reference_tensor_left)

lemma reference_Snd[simp]: \<open>reference Snd\<close>
  unfolding Snd_def by (rule reference_tensor_right)

lemma disjoint_Fst_Snd[simp]: \<open>disjoint Fst Snd\<close>
  apply (rule disjointI, simp, simp)
  by (simp add: Fst_def Snd_def tensor_update_mult)

lemmas disjoint_Snd_Fst[simp] = disjoint_Fst_Snd[THEN disjoint_sym]

definition \<open>swap = (Snd; Fst)\<close>

lemma swap_apply[simp]: "swap (a \<otimes>\<^sub>u b) = (b \<otimes>\<^sub>u a)"
  unfolding swap_def
  by (simp add: Axioms.reference_pair_apply Fst_def Snd_def tensor_update_mult) 

lemma swap_o_Fst: "swap o Fst = Snd"
  by (auto simp add: Fst_def Snd_def)
lemma swap_o_Snd: "swap o Snd = Fst"
  by (auto simp add: Fst_def Snd_def)

lemma reference_swap[simp]: \<open>reference swap\<close>
  by (simp add: swap_def)

lemma pair_Fst_Snd: \<open>(Fst; Snd) = id\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: reference_pair_apply Fst_def Snd_def tensor_update_mult)

lemma swap_o_swap[simp]: \<open>swap o swap = id\<close>
  by (metis swap_def disjoint_Snd_Fst pair_Fst_Snd reference_comp_pair reference_swap swap_o_Fst swap_o_Snd)

lemma swap_swap[simp]: \<open>swap (swap x) = x\<close>
  by (simp add: pointfree_idE)

lemma inv_swap[simp]: \<open>inv swap = swap\<close>
  by (meson inv_unique_comp swap_o_swap)

lemma reference_pair_Fst:
  assumes \<open>disjoint F G\<close>
  shows \<open>(F;G) o Fst = F\<close>
  using assms by (auto intro!: ext simp: Fst_def reference_pair_apply disjoint_reference2)

lemma reference_pair_Snd:
  assumes \<open>disjoint F G\<close>
  shows \<open>(F;G) o Snd = G\<close>
  using assms by (auto intro!: ext simp: Snd_def reference_pair_apply disjoint_reference1)

lemma reference_Fst_reference_Snd[simp]:
  assumes \<open>reference F\<close>
  shows \<open>(F o Fst; F o Snd) = F\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: reference_pair_apply Fst_def Snd_def reference_mult tensor_update_mult)

lemma reference_Snd_reference_Fst[simp]: 
  assumes \<open>reference F\<close>
  shows \<open>(F o Snd; F o Fst) = F o swap\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: reference_pair_apply Fst_def Snd_def reference_mult tensor_update_mult)


lemma disjoint3[simp]:
  assumes [simp]: "disjoint F G" and "disjoint G H" and "disjoint F H"
  shows "disjoint (F; G) H"
proof (rule disjointI)
  have [simp]: \<open>reference F\<close> \<open>reference G\<close> \<open>reference H\<close>
    using assms disjoint_def by auto
  then have [simp]: \<open>prereference F\<close> \<open>prereference G\<close> \<open>prereference H\<close>
    using reference_prereference by blast+
  have [simp]: \<open>prereference (\<lambda>a. (F;G) a *\<^sub>u z)\<close> for z
    apply (rule comp_prereference[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have [simp]: \<open>prereference (\<lambda>a. z *\<^sub>u (F;G) a)\<close> for z
    apply (rule comp_prereference[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have "(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u H h = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)" for f g h
  proof -
    have FH: "F f *\<^sub>u H h = H h *\<^sub>u F f"
      using assms disjoint_def by metis
    have GH: "G g *\<^sub>u H h = H h *\<^sub>u G g"
      using assms disjoint_def by metis
    have \<open>(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u (H h) = F f *\<^sub>u G g *\<^sub>u H h\<close>
      using \<open>disjoint F G\<close> by (subst reference_pair_apply, auto)
    also have \<open>\<dots> = H h *\<^sub>u F f *\<^sub>u G g\<close>
      using FH GH by (metis comp_update_assoc)
    also have \<open>\<dots> = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)\<close>
      using \<open>disjoint F G\<close> by (subst reference_pair_apply, auto simp: comp_update_assoc)
    finally show ?thesis
      by -
  qed
  then show "(F; G) fg *\<^sub>u (H h) = (H h) *\<^sub>u (F; G) fg" for fg h
    apply (rule_tac tensor_extensionality[THEN fun_cong])
    by auto
  show "reference H" and  "reference (F; G)"
    by simp_all
qed

lemma disjoint3'[simp]:
  assumes "disjoint F G" and "disjoint G H" and "disjoint F H"
  shows "disjoint F (G; H)"
  apply (rule disjoint_sym)
  apply (rule disjoint3)
  using assms by (auto simp: disjoint_sym)

lemma pair_o_swap[simp]:
  assumes [simp]: "disjoint A B"
  shows "(A; B) o swap = (B; A)"
proof (rule tensor_extensionality)
  have [simp]: "prereference A" "prereference B"
     apply (metis (no_types, opaque_lifting) assms disjoint_reference1 reference_prereference)
    by (metis (full_types) assms disjoint_reference2 reference_prereference)
  then show \<open>prereference ((A; B) \<circ> swap)\<close>
    by simp
  show \<open>prereference (B; A)\<close>
    by (metis (no_types, lifting) assms disjoint_sym reference_prereference pair_is_reference)
  show \<open>((A; B) \<circ> swap) (a \<otimes>\<^sub>u b) = (B; A) (a \<otimes>\<^sub>u b)\<close> for a b
    (* Without the "only:", we would not need the "apply subst",
       but that proof fails when instantiated in Classical.thy *)
    apply (simp only: o_def swap_apply)
    apply (subst reference_pair_apply, simp)
    apply (subst reference_pair_apply, simp add: disjoint_sym)
    by (metis (no_types, lifting) assms disjoint_def)
qed


subsection \<open>Compatibility of reference tensor products\<close>

lemma disjoint_reference_tensor:
  fixes F :: \<open>'a::domain update \<Rightarrow> 'e::domain update\<close> and G :: \<open>'b::domain update \<Rightarrow> 'f::domain update\<close>
    and F' :: \<open>'c::domain update \<Rightarrow> 'e update\<close> and G' :: \<open>'d::domain update \<Rightarrow> 'f update\<close>
  assumes [simp]: \<open>disjoint F F'\<close>
  assumes [simp]: \<open>disjoint G G'\<close>
  shows \<open>disjoint (F \<otimes>\<^sub>r G) (F' \<otimes>\<^sub>r G')\<close>
proof -
  note [intro!] = 
    comp_prereference[OF _ prereference_mult_right, unfolded o_def]
    comp_prereference[OF _ prereference_mult_left, unfolded o_def]
    comp_prereference
    reference_tensor_is_reference
  have [simp]: \<open>reference F\<close> \<open>reference G\<close> \<open>reference F'\<close> \<open>reference G'\<close>
    using assms disjoint_def by blast+
  have [simp]: \<open>reference (F \<otimes>\<^sub>r G)\<close> \<open>reference (F' \<otimes>\<^sub>r G')\<close>
    by (auto simp add: reference_tensor_def)
  have [simp]: \<open>reference (F;F')\<close> \<open>reference (G;G')\<close>
    by auto
  define reorder :: \<open>(('a\<times>'b) \<times> ('c\<times>'d)) update \<Rightarrow> (('a\<times>'c) \<times> ('b\<times>'d)) update\<close>
    where \<open>reorder = ((Fst o Fst; Snd o Fst); (Fst o Snd; Snd o Snd))\<close>
  have [simp]: \<open>prereference reorder\<close>
    by (auto simp: reorder_def)
  have [simp]: \<open>reorder ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d)) = ((a \<otimes>\<^sub>u c) \<otimes>\<^sub>u (b \<otimes>\<^sub>u d))\<close> for a b c d
    apply (simp add: reorder_def reference_pair_apply)
    by (simp add: Fst_def Snd_def tensor_update_mult)
  define \<Phi> where \<open>\<Phi> c d = ((F;F') \<otimes>\<^sub>r (G;G')) o reorder o (\<lambda>\<sigma>. \<sigma> \<otimes>\<^sub>u (c \<otimes>\<^sub>u d))\<close> for c d
  have [simp]: \<open>prereference (\<Phi> c d)\<close> for c d
    unfolding \<Phi>_def 
    by (auto intro: reference_prereference)
  have \<open>\<Phi> c d (a \<otimes>\<^sub>u b) = (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b) *\<^sub>u (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d)\<close> for a b c d
    unfolding \<Phi>_def by (auto simp: reference_pair_apply tensor_update_mult)
  then have \<Phi>1: \<open>\<Phi> c d \<sigma> = (F \<otimes>\<^sub>r G) \<sigma> *\<^sub>u (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d)\<close> for c d \<sigma>
    apply (rule_tac fun_cong[of _ _ \<sigma>])
    apply (rule tensor_extensionality)
    by auto
  have \<open>\<Phi> c d (a \<otimes>\<^sub>u b) = (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d) *\<^sub>u (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b)\<close> for a b c d
    unfolding \<Phi>_def apply (auto simp: reference_pair_apply)
    by (metis assms(1) assms(2) disjoint_def tensor_update_mult)
  then have \<Phi>2: \<open>\<Phi> c d \<sigma> = (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d) *\<^sub>u (F \<otimes>\<^sub>r G) \<sigma>\<close> for c d \<sigma>
    apply (rule_tac fun_cong[of _ _ \<sigma>])
    apply (rule tensor_extensionality)
    by auto
  from \<Phi>1 \<Phi>2 have \<open>(F \<otimes>\<^sub>r G) \<sigma> *\<^sub>u (F' \<otimes>\<^sub>r G') \<tau> = (F' \<otimes>\<^sub>r G') \<tau> *\<^sub>u (F \<otimes>\<^sub>r G) \<sigma>\<close> for \<tau> \<sigma>
    apply (rule_tac fun_cong[of _ _ \<tau>])
    apply (rule tensor_extensionality)
    by auto
  then show ?thesis
    apply (rule disjointI[rotated -1])
    by auto
qed

subsection \<open>Associativity of the tensor product\<close>

definition assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> ('a\<times>('b\<times>'c)) update\<close> where 
  \<open>assoc = ((Fst; Snd o Fst); Snd o Snd)\<close>

lemma assoc_is_hom[simp]: \<open>prereference assoc\<close>
  by (auto simp: assoc_def)

lemma assoc_apply[simp]: \<open>assoc ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c) = (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c))\<close>
  by (auto simp: assoc_def reference_pair_apply Fst_def Snd_def tensor_update_mult)

definition assoc' :: \<open>('a\<times>('b\<times>'c)) update \<Rightarrow> (('a::domain\<times>'b::domain)\<times>'c::domain) update\<close> where 
  \<open>assoc' = (Fst o Fst; (Fst o Snd; Snd))\<close>

lemma assoc'_is_hom[simp]: \<open>prereference assoc'\<close>
  by (auto simp: assoc'_def)

lemma assoc'_apply[simp]: \<open>assoc' (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c)) =  ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c)\<close>
  by (auto simp: assoc'_def reference_pair_apply Fst_def Snd_def tensor_update_mult)

lemma reference_assoc[simp]: \<open>reference assoc\<close>
  unfolding assoc_def
  by force

lemma reference_assoc'[simp]: \<open>reference assoc'\<close>
  unfolding assoc'_def 
  by force

lemma pair_o_assoc[simp]:
  assumes [simp]: \<open>disjoint F G\<close> \<open>disjoint G H\<close> \<open>disjoint F H\<close>
  shows \<open>(F; (G; H)) \<circ> assoc = ((F; G); H)\<close>
proof (rule tensor_extensionality3')
  show \<open>reference ((F; (G; H)) \<circ> assoc)\<close>
    by simp
  show \<open>reference ((F; G); H)\<close>
    by simp
  show \<open>((F; (G; H)) \<circ> assoc) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = ((F; G); H) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: reference_pair_apply assoc_apply comp_update_assoc)
qed

lemma pair_o_assoc'[simp]:
  assumes [simp]: \<open>disjoint F G\<close> \<open>disjoint G H\<close> \<open>disjoint F H\<close>
  shows \<open>((F; G); H) \<circ> assoc' = (F; (G; H))\<close>
proof (rule tensor_extensionality3)
  show \<open>reference (((F; G); H) \<circ> assoc')\<close>
    by simp
  show \<open>reference (F; (G; H))\<close>
    by simp
  show \<open>(((F; G); H) \<circ> assoc') (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = (F; (G; H)) (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: reference_pair_apply assoc'_apply comp_update_assoc)
qed

lemma assoc'_o_assoc[simp]: \<open>assoc' o assoc = id\<close>
  apply (rule tensor_extensionality3')
  by auto

lemma assoc'_assoc[simp]: \<open>assoc' (assoc x) = x\<close>
  by (simp add: pointfree_idE)

lemma assoc_o_assoc'[simp]: \<open>assoc o assoc' = id\<close>
  apply (rule tensor_extensionality3)
  by auto

lemma assoc_assoc'[simp]: \<open>assoc (assoc' x) = x\<close>
  by (simp add: pointfree_idE)

lemma inv_assoc[simp]: \<open>inv assoc = assoc'\<close>
  using assoc'_o_assoc assoc_o_assoc' inv_unique_comp by blast

lemma inv_assoc'[simp]: \<open>inv assoc' = assoc\<close>
  by (simp add: inv_equality)

lemma [simp]: \<open>bij assoc\<close>
  using assoc'_o_assoc assoc_o_assoc' o_bij by blast

lemma [simp]: \<open>bij assoc'\<close>
  using assoc'_o_assoc assoc_o_assoc' o_bij by blast

subsection \<open>Iso-references\<close>

definition \<open>iso_reference F \<longleftrightarrow> reference F \<and> (\<exists>G. reference G \<and> F o G = id \<and> G o F = id)\<close>
  for F :: \<open>_::domain update \<Rightarrow> _::domain update\<close>

lemma iso_referenceI:
  assumes \<open>reference F\<close> \<open>reference G\<close> \<open>F o G = id\<close> \<open>G o F = id\<close>
  shows \<open>iso_reference F\<close>
  using assms(1) assms(2) assms(3) assms(4) iso_reference_def by blast

lemma iso_reference_inv: \<open>iso_reference F \<Longrightarrow> iso_reference (inv F)\<close>
  by (metis inv_unique_comp iso_reference_def)

lemma iso_reference_inv_comp1: \<open>iso_reference F \<Longrightarrow> inv F o F = id\<close>
  using inv_unique_comp iso_reference_def by blast

lemma iso_reference_inv_comp2: \<open>iso_reference F \<Longrightarrow> F o inv F = id\<close>
  using inv_unique_comp iso_reference_def by blast


lemma iso_reference_id[simp]: \<open>iso_reference id\<close>
  by (simp add: iso_reference_def)

lemma iso_reference_is_reference: \<open>iso_reference F \<Longrightarrow> reference F\<close>
  using iso_reference_def by blast

lemma iso_reference_comp[simp]:
  assumes [simp]: \<open>iso_reference F\<close> \<open>iso_reference G\<close>
  shows \<open>iso_reference (F o G)\<close>
proof -
  from assms obtain F' G' where [simp]: \<open>reference F'\<close> \<open>reference G'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    by (meson iso_reference_def)
  show ?thesis
    apply (rule iso_referenceI[where G=\<open>G' o F'\<close>])
       apply (auto simp: reference_tensor_is_reference iso_reference_is_reference reference_tensor_distrib)
     apply (metis \<open>F \<circ> F' = id\<close> \<open>G \<circ> G' = id\<close> fcomp_assoc fcomp_comp id_fcomp)
    by (metis (no_types, lifting) \<open>F \<circ> F' = id\<close> \<open>F' \<circ> F = id\<close> \<open>G' \<circ> G = id\<close> fun.map_comp inj_iff inv_unique_comp o_inv_o_cancel)
qed


lemma iso_reference_tensor_is_iso_reference[simp]:
  assumes [simp]: \<open>iso_reference F\<close> \<open>iso_reference G\<close>
  shows \<open>iso_reference (F \<otimes>\<^sub>r G)\<close>
proof -
  from assms obtain F' G' where [simp]: \<open>reference F'\<close> \<open>reference G'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    by (meson iso_reference_def)
  show ?thesis
    apply (rule iso_referenceI[where G=\<open>F' \<otimes>\<^sub>r G'\<close>])
    by (auto simp: reference_tensor_is_reference iso_reference_is_reference reference_tensor_distrib)
qed

lemma iso_reference_bij: \<open>iso_reference F \<Longrightarrow> bij F\<close>
  using iso_reference_def o_bij by auto

lemma inv_reference_tensor[simp]: 
  assumes [simp]: \<open>iso_reference F\<close> \<open>iso_reference G\<close>
  shows \<open>inv (F \<otimes>\<^sub>r G) = inv F \<otimes>\<^sub>r inv G\<close>
  apply (auto intro!: inj_imp_inv_eq bij_is_inj iso_reference_bij 
              simp: reference_tensor_distrib[unfolded o_def, THEN fun_cong] iso_reference_is_reference
                    iso_reference_inv bij_is_surj iso_reference_bij surj_f_inv_f)
  by (metis eq_id_iff reference_tensor_id)

lemma iso_reference_swap[simp]: \<open>iso_reference swap\<close>
  apply (rule iso_referenceI[of _ swap])
  by auto

lemma iso_reference_assoc[simp]: \<open>iso_reference assoc\<close>
  apply (rule iso_referenceI[of _ assoc'])
  by auto

lemma iso_reference_assoc'[simp]: \<open>iso_reference assoc'\<close>
  apply (rule iso_referenceI[of _ assoc])
  by auto

definition \<open>equivalent_references F G \<longleftrightarrow> (reference F \<and> (\<exists>I. iso_reference I \<and> F o I = G))\<close>
  for F G :: \<open>_::domain update \<Rightarrow> _::domain update\<close>

lemma iso_reference_equivalent_id[simp]: \<open>equivalent_references id F \<longleftrightarrow> iso_reference F\<close>
  by (simp add: equivalent_references_def)

lemma equivalent_referencesI:
  assumes \<open>reference F\<close>
  assumes \<open>iso_reference I\<close>
  assumes \<open>F o I = G\<close>
  shows \<open>equivalent_references F G\<close>
  using assms unfolding equivalent_references_def by blast

lemma equivalent_references_refl: \<open>equivalent_references F F\<close> if \<open>reference F\<close>
  using that by (auto intro!: exI[of _ id] simp: equivalent_references_def)

lemma equivalent_references_reference_left: \<open>equivalent_references F G \<Longrightarrow> reference F\<close>
  using equivalent_references_def by auto

lemma equivalent_references_reference_right: \<open>reference G\<close> if \<open>equivalent_references F G\<close>
  by (metis equivalent_references_def iso_reference_def reference_comp that)

lemma equivalent_references_sym:
  assumes \<open>equivalent_references F G\<close>
  shows \<open>equivalent_references G F\<close>
  by (smt (verit) assms comp_id equivalent_references_def equivalent_references_reference_right fun.map_comp iso_reference_def)

lemma equivalent_references_trans[trans]: 
  assumes \<open>equivalent_references F G\<close> and \<open>equivalent_references G H\<close>
  shows \<open>equivalent_references F H\<close>
proof -
  from assms have [simp]: \<open>reference F\<close> \<open>reference G\<close>
    by (auto simp: equivalent_references_def)
  from assms(1) obtain I where [simp]: \<open>iso_reference I\<close> and \<open>F o I = G\<close>
    using equivalent_references_def by blast
  from assms(2) obtain J where [simp]: \<open>iso_reference J\<close> and \<open>G o J = H\<close>
    using equivalent_references_def by blast
  have \<open>reference F\<close>
    by (auto simp: equivalent_references_def)
  moreover have \<open>iso_reference (I o J)\<close>
    using \<open>iso_reference I\<close> \<open>iso_reference J\<close> iso_reference_comp by blast
  moreover have \<open>F o (I o J) = H\<close>
    by (simp add: \<open>F \<circ> I = G\<close> \<open>G \<circ> J = H\<close> o_assoc)
  ultimately show ?thesis
    by (rule equivalent_referencesI)
qed

lemma equivalent_references_assoc[simp]:
  assumes [simp]: \<open>disjoint F G\<close> \<open>disjoint F H\<close> \<open>disjoint G H\<close>
  shows \<open>equivalent_references (F;(G;H)) ((F;G);H)\<close>
  apply (rule equivalent_referencesI[where I=assoc])
  by auto

lemma equivalent_references_pair_right:
  assumes [simp]: \<open>disjoint F G\<close>
  assumes eq: \<open>equivalent_references G H\<close>
  shows \<open>equivalent_references (F;G) (F;H)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_reference I\<close> and \<open>G o I = H\<close>
    by (metis equivalent_references_def)
  then have *: \<open>(F;G) \<circ> (id \<otimes>\<^sub>r I) = (F;H)\<close>
    by (auto intro!: tensor_extensionality reference_comp reference_prereference reference_tensor_is_reference 
        simp:  reference_pair_apply iso_reference_is_reference)
  show ?thesis
    apply (rule equivalent_referencesI[where I=\<open>id \<otimes>\<^sub>r I\<close>])
    using * by (auto intro!: iso_reference_tensor_is_iso_reference)
qed

lemma equivalent_references_pair_left:
  assumes [simp]: \<open>disjoint F G\<close>
  assumes eq: \<open>equivalent_references F H\<close>
  shows \<open>equivalent_references (F;G) (H;G)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_reference I\<close> and \<open>F o I = H\<close>
    by (metis equivalent_references_def)
  then have *: \<open>(F;G) \<circ> (I \<otimes>\<^sub>r id) = (H;G)\<close>
    by (auto intro!: tensor_extensionality reference_comp reference_prereference reference_tensor_is_reference 
        simp:  reference_pair_apply iso_reference_is_reference)
  show ?thesis
    apply (rule equivalent_referencesI[where I=\<open>I \<otimes>\<^sub>r id\<close>])
    using * by (auto intro!: iso_reference_tensor_is_iso_reference)
qed

lemma equivalent_references_comp:
  assumes \<open>reference H\<close>
  assumes \<open>equivalent_references F G\<close>
  shows \<open>equivalent_references (H o F) (H o G)\<close>
  by (metis (no_types, lifting) assms(1) assms(2) comp_assoc equivalent_references_def reference_comp)

lemma equivalent_references_disjoint1:
  assumes \<open>disjoint F G\<close>
  assumes \<open>equivalent_references F F'\<close>
  shows \<open>disjoint F' G\<close>
  by (metis assms(1) assms(2) disjoint_comp_left equivalent_references_def iso_reference_is_reference)

lemma equivalent_references_disjoint2:
  assumes \<open>disjoint F G\<close>
  assumes \<open>equivalent_references G G'\<close>
  shows \<open>disjoint F G'\<close>
  by (metis assms(1) assms(2) disjoint_comp_right equivalent_references_def iso_reference_is_reference)

subsection \<open>Compatibility simplification\<close>

text \<open>The simproc \<open>disjointness_warn\<close> produces helpful warnings for subgoals of the form
   \<^term>\<open>disjoint x y\<close> that are probably unsolvable due to missing declarations of 
   variable compatibility facts. Same for subgoals of the form \<^term>\<open>reference x\<close>.\<close>
simproc_setup "disjointness_warn" ("disjoint x y" | "reference x") = \<open>
let val thy_string = Markup.markup (Theory.get_markup \<^theory>) (Context.theory_name \<^theory>)
in
fn m => fn ctxt => fn ct => let
  val (x,y) = case Thm.term_of ct of
                 Const(\<^const_name>\<open>disjoint\<close>,_ ) $ x $ y => (x, SOME y)
               | Const(\<^const_name>\<open>reference\<close>,_ ) $ x => (x, NONE)
  val str : string lazy = Lazy.lazy (fn () => Syntax.string_of_term ctxt (Thm.term_of ct))
  fun w msg = warning (msg ^ "\n(Disable these warnings with: using [[simproc del: "^thy_string^".disjointness_warn]])")
  val _ = case (x,y) of
        (Free(n,T), SOME (Free(n',T'))) => 
            if String.isPrefix ":" n orelse String.isPrefix ":" n' then 
                      w ("Simplification subgoal " ^ Lazy.force str ^ " contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else if n=n' then (if T=T' then () 
                          else w ("In simplification subgoal " ^ Lazy.force str ^ 
                               ", variables have same name and different types.\n" ^
                               "Probably something is wrong."))
                    else w ("Simplification subgoal " ^ Lazy.force str ^ 
                            " occurred but cannot be solved.\n" ^
                            "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ 
                            "\<close>  somewhere.")
      | (Free(n,T), NONE) => 
            if String.isPrefix ":" n then 
                      w ("Simplification subgoal '" ^ Lazy.force str ^ "' contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else w ("Simplification subgoal " ^ Lazy.force str ^ " occurred but cannot be solved.\n" ^
                    "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ "\<close>  somewhere.")
      | _ => ()
  in NONE end
end\<close>


named_theorems reference_attribute_rule_immediate
named_theorems reference_attribute_rule

lemmas [reference_attribute_rule] = conjunct1 conjunct2 iso_reference_is_reference iso_reference_is_reference[OF iso_reference_inv]
lemmas [reference_attribute_rule_immediate] = disjoint_sym disjoint_reference1 disjoint_reference2
  asm_rl[of \<open>disjoint _ _\<close>] asm_rl[of \<open>iso_reference _\<close>] asm_rl[of \<open>reference _\<close>] iso_reference_inv

text \<open>The following declares an attribute \<open>[reference]\<close>. When the attribute is applied to a fact
  of the form \<^term>\<open>reference F\<close>, \<^term>\<open>iso_reference F\<close>, \<^term>\<open>disjoint F G\<close> or a conjunction of these,
  then those facts are added to the simplifier together with some derived theorems
  (e.g., \<^term>\<open>disjoint F G\<close> also adds \<^term>\<open>reference F\<close>).

  In theory \<open>Laws_Complement\<close>, support for \<^term>\<open>is_unit_reference F\<close> and \<^term>\<open>complements F G\<close> is
  added to this attribute.\<close>

setup \<open>
let
fun add thm results = 
  Net.insert_term (K true) (Thm.concl_of thm, thm) results
  handle Net.INSERT => results
fun try_rule f thm rule state = case SOME (rule OF [thm]) handle THM _ => NONE  of
  NONE => state | SOME th => f th state
fun collect (rules,rules_immediate) thm results =
  results |> fold (try_rule add thm) rules_immediate |> fold (try_rule (collect (rules,rules_immediate)) thm) rules
fun declare thm context = let
  val ctxt = Context.proof_of context
  val rules = Named_Theorems.get ctxt @{named_theorems reference_attribute_rule}
  val rules_immediate = Named_Theorems.get ctxt @{named_theorems reference_attribute_rule_immediate}
  val thms = collect (rules,rules_immediate) thm Net.empty |> Net.entries
  (* val _ = \<^print> thms *)
  in Simplifier.map_ss (fn ctxt => ctxt addsimps thms) context end
in
Attrib.setup \<^binding>\<open>reference\<close>
 (Scan.succeed (Thm.declaration_attribute declare))
  "Add reference-related rules to the simplifier"
end
\<close>

subsection \<open>Notation\<close>

no_notation comp_update (infixl "*\<^sub>u" 55)
no_notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

bundle reference_notation begin
notation reference_tensor (infixr "\<otimes>\<^sub>r" 70)
notation reference_pair ("'(_;_')")
end

bundle no_reference_notation begin
no_notation reference_tensor (infixr "\<otimes>\<^sub>r" 70)
no_notation reference_pair ("'(_;_')")
end

end
