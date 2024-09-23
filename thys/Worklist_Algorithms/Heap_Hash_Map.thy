subsection \<open>Heap Hash Map\<close>

theory Heap_Hash_Map
  imports
    Separation_Logic_Imperative_HOL.Sep_Main Separation_Logic_Imperative_HOL.Sep_Examples
    Refine_Imperative_HOL.IICF
begin

no_notation Ref.update (\<open>_ := _\<close> 62)

definition big_star :: "assn multiset \<Rightarrow> assn" (\<open>\<And>* _\<close> [60] 90) where
  "big_star S \<equiv> fold_mset (*) emp S"

interpretation comp_fun_commute_mult:
  comp_fun_commute "(*) :: ('a :: ab_semigroup_mult \<Rightarrow> _ \<Rightarrow> _)"
  by standard (auto simp: ab_semigroup_mult_class.mult.left_commute)

lemma sep_big_star_insert [simp]: "\<And>* (add_mset x S) = (x * \<And>* S)"
  by (auto simp: big_star_def)

lemma sep_big_star_union [simp]: "\<And>* (S + T) = (\<And>* S) * (\<And>* T)"
  by (auto simp: big_star_def comp_fun_commute_mult.fold_mset_fun_left_comm)

lemma sep_big_star_empty [simp]: "\<And>* {#} = emp"
  by (simp add: big_star_def)

(* Unused *)
lemma big_star_entatilst_mono:
  "\<And>* T \<Longrightarrow>\<^sub>t \<And>* S" if "S \<subseteq># T"
  using that
proof (induction T arbitrary: S)
  case empty
  then show ?case
    by auto
next
  case (add x T)
  then show ?case
  proof (cases "x \<in># S")
    case True
    then obtain S' where "S' \<subseteq># T" "S = add_mset x S'"
      by (metis add.prems mset_add mset_subset_eq_add_mset_cancel)
    with add.IH[of S'] add.prems have "\<And>* T \<Longrightarrow>\<^sub>t \<And>* S'"
      by auto
    then show ?thesis
      unfolding \<open>S = _\<close> by (sep_auto intro: entt_star_mono)
  next
    case False
    with add.prems have "S \<subseteq># T"
      by (metis add_mset_remove_trivial diff_single_trivial mset_le_subtract)
    then have "\<And>* T \<Longrightarrow>\<^sub>t \<And>* S"
      by (rule add.IH)
    then show ?thesis
      using entt_fr_drop star_aci(2) by fastforce
  qed
qed

definition "map_assn V m mi \<equiv>
  \<up> (dom mi = dom m \<and> finite (dom m)) *
  (\<And>* {# V (the (m k)) (the (mi k)) . k \<in># mset_set (dom m)#})
"

lemma map_assn_empty_map[simp]:
  "map_assn A Map.empty Map.empty = emp"
  unfolding map_assn_def by auto

lemma in_mset_union_split:
  "mset_set S = mset_set (S - {k}) + {#k#}" if "k \<in> S" "finite S"
  using that by (auto simp: mset_set.remove)

lemma in_mset_dom_union_split:
  "mset_set (dom m) = mset_set (dom m - {k}) + {#k#}" if "m k = Some v" "finite (dom m)"
  apply (rule in_mset_union_split)
  using that by (auto)

lemma dom_remove_not_in_dom_simp[simp]:
  "dom m - {k} = dom m" if "m k = None"
  using that unfolding dom_def by auto

lemma map_assn_delete:
  "map_assn A m mh \<Longrightarrow>\<^sub>A
   map_assn A (m(k := None)) (mh(k := None)) * option_assn A (m k) (mh k)"
  unfolding map_assn_def
  apply sep_auto
  apply (sep_auto cong: multiset.map_cong_simp)
  apply (cases "m k"; cases "mh k"; simp)
     apply (solves auto)+
   by (subst in_mset_dom_union_split, assumption+, sep_auto)

lemma in_mset_set_iff_in_set[simp]:
  "z \<in># mset_set S \<longleftrightarrow> z \<in> S" if "finite S"
  using that by auto

lemma ent_refl':
  "a = b \<Longrightarrow> a \<Longrightarrow>\<^sub>A b"
  by auto

lemma map_assn_update_aux:
  "map_assn A m mh * A v vi \<Longrightarrow>\<^sub>A map_assn A (m(k \<mapsto> v)) (mh(k \<mapsto> vi))"
  if "k \<notin> dom m"
  unfolding map_assn_def
  apply (sep_auto simp: that cong: multiset.map_cong_simp)
  apply (subst mult.commute)
  apply (rule ent_star_mono)
   apply simp
  apply (rule ent_refl')
  apply (rule arg_cong[where f = "big_star"])
  apply (rule image_mset_cong)
  using that by auto

lemma map_assn_update:
  "map_assn A m mh * A v vi \<Longrightarrow>\<^sub>A
   map_assn A (m(k \<mapsto> v)) (mh(k \<mapsto> vi)) * true"
  apply (rule ent_frame_fwd[OF map_assn_delete[where k = k]], frame_inference)
  apply (rule ent_frame_fwd[OF map_assn_update_aux[where k = k and A = A], rotated], frame_inference)
  by sep_auto+

\<comment> \<open>This is a generic pattern to enhance a map-implementation to
  heap-based values, a la Chargueraud.\<close>
definition (in imp_map) "hms_assn A m mi \<equiv> \<exists>\<^sub>Amh. is_map mh mi * map_assn A m mh"

definition (in imp_map) "hms_assn' K A = hr_comp (hms_assn A) (\<langle>the_pure K, Id\<rangle>map_rel)"
declare (in imp_map) hms_assn'_def[symmetric, fcomp_norm_unfold]

definition (in imp_map_empty) [code_unfold]: "hms_empty \<equiv> empty"

lemma (in imp_map_empty) hms_empty_rule [sep_heap_rules]:
  "<emp> hms_empty <hms_assn A Map.empty>\<^sub>t"
  unfolding hms_empty_def hms_assn_def
  by (sep_auto eintros: exI[where x = Map.empty])

definition (in imp_map_update) [code_unfold]: "hms_update = update"

lemma (in imp_map_update) hms_update_rule [sep_heap_rules]:
  "<hms_assn A m mi * A v vi> hms_update k vi mi <hms_assn A (m(k \<mapsto> v))>\<^sub>t"
  unfolding hms_update_def hms_assn_def
  apply (sep_auto eintros del: exI)
  subgoal for mh mi
    apply (rule exI[where x = "mh(k \<mapsto> vi)"])
    apply (rule ent_frame_fwd[OF map_assn_update[where A = A]], frame_inference)
    by sep_auto
  done

lemma restrict_not_in_dom_simp[simp]:
  "m |` (- {k}) = m" if "m k = None"
  using that by (auto simp: restrict_map_def)

definition [code]:
  "hms_extract lookup delete k m =
    do {
      vo \<leftarrow> lookup k m;
      case vo of
        None \<Rightarrow> return (None, m) |
        Some v \<Rightarrow> do {
          m \<leftarrow> delete k m;
          return (Some v, m)
        }
    }
  "

definition [code]:
  "hms_lookup lookup copy k m =
    do {
      vo \<leftarrow> lookup k m;
      case vo of
        None \<Rightarrow> return None |
        Some v \<Rightarrow> do {
          v' \<leftarrow> copy v;
          return (Some v')
        }
    }
  "

locale imp_map_extract_derived = imp_map_delete + imp_map_lookup
begin

lemma map_assn_domain_simps[simp]:
  assumes "vassn_tag (map_assn A m mh)"
  shows "mh k = None \<longleftrightarrow> m k = None" "dom mh = dom m" "finite (dom m)"
  using assms unfolding map_assn_def vassn_tag_def by auto

lemma hms_extract_rule [sep_heap_rules]:
  "<hms_assn A m mi>
    hms_extract lookup delete k mi
  <\<lambda> (vi, mi'). option_assn A (m k) vi * hms_assn A (m(k := None)) mi'>\<^sub>t"
  unfolding hms_extract_def hms_assn_def
  apply (sep_auto eintros del: exI)
  subgoal
    unfolding map_assn_def by auto
  subgoal for mh
    apply (rule exI[where x = "mh(k := None)"])
    apply (rule fr_refl)
    apply (rule ent_star_mono, simp add: fun_upd_idem)
    apply (rule entails_preI, simp add: fun_upd_idem)
    done
  apply (sep_auto eintros del: exI)
  subgoal for mh
    apply (rule exI[where x = "mh(k := None)"])
    apply (rule ent_frame_fwd[OF map_assn_delete[where A = A]], frame_inference)
    by (sep_auto simp add: map_upd_eq_restrict)+
  done

lemma hms_lookup_rule [sep_heap_rules]:
  assumes
    "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  shows
 "<hms_assn A m mi>
    hms_lookup lookup copy k mi
  <\<lambda> vi. hms_assn A m mi * option_assn A (m k) vi>\<^sub>t"
proof -
  have 0: "
    <is_map mh mi * map_assn A (m(k := None)) (mh(k := None)) * option_assn A (m k) (mh k) * true>
      copy x'
    <\<lambda>r. \<exists>\<^sub>Ax.
    is_map mh mi * map_assn A (m(k := None)) (mh(k := None)) * option_assn A (m k) (mh k)
    * A x r * \<up>(m k = Some x)
    * true>
  " if "mh k = Some x'" for mh x'
    supply [sep_heap_rules] = assms[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
    by (sep_auto simp add: that option_assn_alt_def split: option.splits)
  have 1: "
    <is_map mh mi * map_assn A m mh * true>
      copy x'
    <\<lambda>r. \<exists>\<^sub>Ax. is_map mh mi * map_assn A m mh * A x r * \<up>(m k = Some x) * true>"
    if "mh k = Some x'" for mh x'
    apply (rule cons_rule[rotated 2], rule 0, rule that)
     apply (rule ent_frame_fwd[OF map_assn_delete[where A = A]], frame_inference, frame_inference)
    apply sep_auto
    apply (fr_rot 4)
    apply (fr_rot_rhs 3)
    apply (rule fr_refl)
    apply (fr_rot 1)
    apply (fr_rot_rhs 1)
    apply (rule fr_refl)
    apply (fr_rot 2)
    apply (fr_rot_rhs 1)
    unfolding option_assn_alt_def
    apply (sep_auto split: option.split)
    subgoal for x x'
      apply (subgoal_tac "m(k \<mapsto> x) = m")
       apply (subgoal_tac "mh(k \<mapsto> x') = mh")
      using map_assn_update[of A "m(k := None)" "mh(k := None)" x x' k]
      by (auto simp add: ent_true_drop(1))
    done
  show ?thesis
    unfolding hms_lookup_def hms_assn_def
    apply (sep_auto eintros del: exI)
    subgoal
      unfolding map_assn_def by auto
    subgoal for mh
      by (rule exI[where x = mh]) sep_auto
    by (sep_auto intro: 1)
qed

end

context imp_map_update
begin

lemma hms_update_hnr:
  "(uncurry2 hms_update, uncurry2 (RETURN ooo op_map_update)) \<in>
  id_assn\<^sup>k *\<^sub>a A\<^sup>d *\<^sub>a (hms_assn A)\<^sup>d \<rightarrow>\<^sub>a hms_assn A"
  by sepref_to_hoare sep_auto

sepref_decl_impl update: hms_update_hnr uses op_map_update.fref[where V = Id] .

end

context imp_map_empty
begin

lemma hms_empty_hnr:
  "(uncurry0 hms_empty, uncurry0 (RETURN op_map_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a hms_assn A"
  by sepref_to_hoare sep_auto

sepref_decl_impl (no_register) empty: hms_empty_hnr uses op_map_empty.fref[where V = Id] .

definition "op_hms_empty \<equiv> IICF_Map.op_map_empty"

sublocale hms: map_custom_empty op_hms_empty
  by unfold_locales (simp add: op_hms_empty_def)
(* lemmas [sepref_fr_rules] = hms_empty_hnr[folded op_hms_empty_def] *)

lemmas [sepref_fr_rules] = empty_hnr[folded op_hms_empty_def]

lemmas hms_fold_custom_empty = hms.fold_custom_empty

end

sepref_decl_op map_extract:
  "\<lambda>k m. (m k, m(k := None))" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>V\<rangle>option_rel \<times>\<^sub>r \<langle>K,V\<rangle>map_rel"
  where "single_valued K" "single_valued (K\<inverse>)"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
   apply (elim IntE)
   apply parametricity
  apply (elim IntE; rule IntI)
   apply parametricity
   apply (simp add: pres_eq_iff_svb; fail)
  by auto

context imp_map_extract_derived
begin

lemma hms_extract_hnr:
  "(uncurry (hms_extract lookup delete), uncurry (RETURN oo op_map_extract)) \<in>
  id_assn\<^sup>k *\<^sub>a (hms_assn A)\<^sup>d \<rightarrow>\<^sub>a prod_assn (option_assn A) (hms_assn A)"
  by sepref_to_hoare sep_auto

lemma hms_lookup_hnr:
  "(uncurry (hms_lookup lookup copy), uncurry (RETURN oo op_map_lookup)) \<in>
  id_assn\<^sup>k *\<^sub>a (hms_assn A)\<^sup>k \<rightarrow>\<^sub>a option_assn A" if "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  using that by sepref_to_hoare sep_auto

sepref_decl_impl "extract": hms_extract_hnr uses op_map_extract.fref[where V = Id] .

end

interpretation hms_hm: imp_map_extract_derived is_hashmap hm_delete hm_lookup by standard

end
