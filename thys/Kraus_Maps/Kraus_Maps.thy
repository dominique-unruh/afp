theory Kraus_Maps
  imports Kraus_Families
begin

definition kraus_map :: \<open>(('a::chilbert_space,'a) trace_class \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> bool\<close> where
  \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a,'b,unit) kraus_family. \<EE> = kf_apply EE)\<close>

lemma kraus_map_def': \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a::chilbert_space,'b::chilbert_space,'x) kraus_family. \<EE> = kf_apply EE)\<close>
proof (rule iffI)
  assume \<open>kraus_map \<EE>\<close>
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def by blast
  define EE' :: \<open>('a,'b,'x) kraus_family\<close> where \<open>EE' = kf_map (\<lambda>_. undefined) EE\<close>
  have \<open>kf_apply EE' = kf_apply EE\<close>
    by (simp add: EE'_def kf_apply_map)
  with EE show \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kf_apply EE\<close>
    by metis
next
  assume \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kf_apply EE\<close>
  then obtain EE :: \<open>('a,'b,'x) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def by blast
  define EE' :: \<open>('a,'b,unit) kraus_family\<close> where \<open>EE' = kf_map (\<lambda>_. ()) EE\<close>
  have \<open>kf_apply EE' = kf_apply EE\<close>
    by (simp add: EE'_def kf_apply_map)
  with EE show \<open>kraus_map \<EE>\<close>
    apply (simp add: kraus_map_def)
    by metis
qed

lemma kraus_mapI:
  assumes \<open>\<EE> = kf_apply EE\<close>
  shows \<open>kraus_map \<EE>\<close>
  using assms kraus_map_def' by blast

lemma kraus_map_kf_apply[iff]: \<open>kraus_map (kf_apply \<EE>)\<close>
  using kraus_map_def'
  by blast

lemma trace_is_kraus_map: \<open>kraus_map (one_dim_iso o trace_tc)\<close>
  by (auto intro!: ext kraus_mapI[of _ \<open>kf_trace some_chilbert_basis\<close>]
      simp: kf_trace_is_trace)

lemma id_is_kraus_map[iff]: \<open>kraus_map id\<close>
  by (auto intro!: ext kraus_mapI[of _ kf_id])

definition \<open>trace_preserving_map \<EE> \<longleftrightarrow> clinear \<EE> \<and> (\<forall>\<rho>. trace_tc (\<EE> \<rho>) = trace_tc \<rho>)\<close>

lemma trace_preserving_id[iff]: \<open>trace_preserving_map id\<close>
  by (simp add: trace_preserving_map_def complex_vector.linear_id)

lemma trace_preserving_trace_kraus_map[iff]: \<open>trace_preserving_map (one_dim_iso o trace_tc)\<close>
  by (auto intro!: clinear_compose simp add: trace_preserving_map_def bounded_clinear.clinear)



end
