section CTL

theory CTL
  imports Graphs
begin

lemmas [simp] = holds.simps

context Graph_Defs
begin

definition
  "Alw_ev \<phi> x \<equiv> \<forall> xs. run (x ## xs) \<longrightarrow> ev (holds \<phi>) (x ## xs)"

definition
  "Alw_alw \<phi> x \<equiv> \<forall> xs. run (x ## xs) \<longrightarrow> alw (holds \<phi>) (x ## xs)"

definition
  "Ex_ev \<phi> x \<equiv> \<exists> xs. run (x ## xs) \<and> ev (holds \<phi>) (x ## xs)"

definition
  "Ex_alw \<phi> x \<equiv> \<exists> xs. run (x ## xs) \<and> alw (holds \<phi>) (x ## xs)"

definition
  "leadsto \<phi> \<psi> x \<equiv> Alw_alw (\<lambda> x. \<phi> x \<longrightarrow> Alw_ev \<psi> x) x"

definition
  "deadlocked x \<equiv> \<not> (\<exists> y. x \<rightarrow> y)"

definition
  "deadlock x \<equiv> \<exists> y. reaches x y \<and> deadlocked y"

lemma no_deadlockD:
  "\<not> deadlocked y" if "\<not> deadlock x" "reaches x y"
  using that unfolding deadlock_def by auto

lemma not_deadlockedE:
  assumes "\<not> deadlocked x"
  obtains y where "x \<rightarrow> y"
  using assms unfolding deadlocked_def by auto

lemma holds_Not:
  "holds (Not \<circ> \<phi>) = (\<lambda> x. \<not> holds \<phi> x)"
  by auto

lemma Alw_alw_iff:
  "Alw_alw \<phi> x \<longleftrightarrow> \<not> Ex_ev (Not o \<phi>) x"
  unfolding Alw_alw_def Ex_ev_def holds_Not not_ev_not[symmetric] by simp

lemma Ex_alw_iff:
  "Ex_alw \<phi> x \<longleftrightarrow> \<not> Alw_ev (Not o \<phi>) x"
  unfolding Alw_ev_def Ex_alw_def holds_Not not_ev_not[symmetric] by simp

lemma leadsto_iff:
  "leadsto \<phi> \<psi> x \<longleftrightarrow> \<not> Ex_ev (\<lambda> x. \<phi> x \<and> \<not> Alw_ev \<psi> x) x"
  unfolding leadsto_def Alw_alw_iff by (simp add: comp_def)

lemma run_siterate_from:
  assumes "\<forall>y. x \<rightarrow>* y \<longrightarrow> (\<exists> z. y \<rightarrow> z)"
  shows "run (siterate (\<lambda> x. SOME y. x \<rightarrow> y) x)" (is "run (siterate ?f x)")
  using assms
proof (coinduction arbitrary: x)
  case (run x)
  let ?y = "SOME y. x \<rightarrow> y"
  from run have "x \<rightarrow> ?y"
    by (auto intro: someI)
  with run show ?case including graph_automation_aggressive by auto
qed

(* XXX Move *)
lemma extend_run':
  "run zs" if "steps xs" "run ys" "last xs = shd ys" "xs @- stl ys = zs"
  (* s/h *)
  by (metis
      Graph_Defs.run.cases Graph_Defs.steps_non_empty' extend_run
      stream.exhaust_sel stream.inject that)

lemma no_deadlock_run_extend:
  "\<exists> ys. run (x ## xs @- ys)" if "\<not> deadlock x" "steps (x # xs)"
proof -
  include graph_automation
  let ?x = "last (x # xs)" let ?f = "\<lambda> x. SOME y. x \<rightarrow> y" let ?ys = "siterate ?f ?x"
  have "\<exists>z. y \<rightarrow> z" if "?x \<rightarrow>* y" for y
  proof -
    from \<open>steps (x # xs)\<close> have "x \<rightarrow>* ?x"
    by auto
    from \<open>x \<rightarrow>* ?x\<close> \<open>?x \<rightarrow>* y\<close> have "x \<rightarrow>* y"
      by auto
    with \<open>\<not> deadlock x\<close> show ?thesis
      by (auto dest: no_deadlockD elim: not_deadlockedE)
  qed
  then have "run ?ys"
    by (blast intro: run_siterate_from)
  with \<open>steps (x # xs)\<close> show ?thesis
    by (fastforce intro: extend_run')
qed

lemma Ex_ev:
  "Ex_ev \<phi> x \<longleftrightarrow> (\<exists> y. x \<rightarrow>* y \<and> \<phi> y)" if "\<not> deadlock x"
  unfolding Ex_ev_def
proof safe
  fix xs assume prems: "run (x ## xs)" "ev (holds \<phi>) (x ## xs)"
  show "\<exists>y. x \<rightarrow>* y \<and> \<phi> y"
  proof (cases "\<phi> x")
    case True
    then show ?thesis
      by auto
  next
    case False
    with prems obtain y ys zs where
      "\<phi> y" "xs = ys @- y ## zs" "y \<notin> set ys"
      unfolding ev_holds_sset by (auto elim!:split_stream_first')
    with prems have "steps (x # ys @ [y])"
      by (auto intro: run_decomp[THEN conjunct1]) (* XXX *)
    with \<open>\<phi> y\<close> show ?thesis
      including graph_automation by (auto 4 3)
  qed
next
  fix y assume "x \<rightarrow>* y" "\<phi> y"
  then obtain xs where
    "\<phi> (last xs)" "x = hd xs" "steps xs" "y = last xs"
    by (auto dest: reaches_steps)
  then show "\<exists>xs. run (x ## xs) \<and> ev (holds \<phi>) (x ## xs)"
    by (cases xs)
       (auto split: if_split_asm simp: ev_holds_sset dest!: no_deadlock_run_extend[OF that])
qed

lemma Alw_ev:
  "Alw_ev \<phi> x \<longleftrightarrow> \<not> (\<exists> xs. run (x ## xs) \<and> alw (holds (Not o \<phi>)) (x ## xs))"
  unfolding Alw_ev_def
proof (safe, goal_cases)
  case prems: (1 xs)
  then have "ev (holds \<phi>) (x ## xs)" by auto
  then show ?case
    using prems(2,3) by induction (auto intro: run_stl)
next
  case prems: (2 xs)
  then have "\<not> alw (holds (Not \<circ> \<phi>)) (x ## xs)"
    by auto
  moreover have "(\<lambda> x. \<not> holds (Not \<circ> \<phi>) x) = holds \<phi>"
    by (rule ext) simp
  ultimately show ?case
    unfolding not_alw_iff by simp
qed

lemma leadsto_iff':
  "leadsto \<phi> \<psi> x \<longleftrightarrow> (\<nexists>y. x \<rightarrow>* y \<and> \<phi> y \<and> \<not> Alw_ev \<psi> y)" if "\<not> deadlock x"
  unfolding leadsto_iff Ex_ev[OF \<open>\<not> deadlock x\<close>] ..

end (* Graph Defs *)

context Bisimulation_Invariant
begin

context
  fixes \<phi> :: "'a \<Rightarrow> bool" and \<psi> :: "'b \<Rightarrow> bool"
  assumes compatible: "A_B.equiv' a b \<Longrightarrow> \<phi> a \<longleftrightarrow> \<psi> b"
begin

lemma ev_\<psi>_\<phi>:
  "ev (holds \<phi>) xs" if "stream_all2 B_A.equiv' ys xs" "ev (holds \<psi>) ys"
  using that
  apply -
  apply (drule stream_all2_rotate_1)
  apply (drule ev_imp_shift)
  apply clarify
  unfolding stream_all2_shift2
  apply (subst (asm) stream.rel_sel)
  apply (auto intro!: ev_shift dest!: compatible[symmetric])
  done

lemma ev_\<phi>_\<psi>:
  "ev (holds \<psi>) ys" if "stream_all2 A_B.equiv' xs ys" "ev (holds \<phi>) xs"
  using that
  apply -
  apply (subst (asm) stream.rel_flip[symmetric])
  apply (drule ev_imp_shift)
  apply clarify
  unfolding stream_all2_shift2
  apply (subst (asm) stream.rel_sel)
  apply (auto intro!: ev_shift dest!: compatible)
  done

lemma Ex_ev_iff:
  "A.Ex_ev \<phi> a \<longleftrightarrow> B.Ex_ev \<psi> b" if "A_B.equiv' a b"
  unfolding Graph_Defs.Ex_ev_def
  apply safe
  subgoal for xs
    apply (drule A_B.simulation_run[of a xs b])
    subgoal
      using that .
    apply clarify
    subgoal for ys
      apply (inst_existentials ys)
      using that
       apply (auto intro!: ev_\<phi>_\<psi> dest: stream_all2_rotate_1)
      done
    done
  subgoal for ys
    apply (drule B_A.simulation_run[of b ys a])
    subgoal
      using that by (rule equiv'_rotate_1)
    apply clarify
    subgoal for xs
      apply (inst_existentials xs)
      using that
       apply (auto intro!: ev_\<psi>_\<phi> dest: equiv'_rotate_1)
      done
    done
  done

lemma Alw_ev_iff:
  "A.Alw_ev \<phi> a \<longleftrightarrow> B.Alw_ev \<psi> b" if "A_B.equiv' a b"
  unfolding Graph_Defs.Alw_ev_def
  apply safe
  subgoal for ys
    apply (drule B_A.simulation_run[of b ys a])
    subgoal
      using that by (rule equiv'_rotate_1)
    apply safe
    subgoal for xs
      apply (inst_existentials xs)
        apply (elim allE impE, assumption)
      using that
        apply (auto intro!: ev_\<phi>_\<psi> dest: stream_all2_rotate_1)
      done
    done
  subgoal for xs
    apply (drule A_B.simulation_run[of a xs b])
    subgoal
      using that .
    apply safe
    subgoal for ys
      apply (inst_existentials ys)
      apply (elim allE impE, assumption)
      using that
      apply (auto intro!: ev_\<psi>_\<phi> elim!: equiv'_rotate_1 stream_all2_rotate_2)
      done
    done
  done  

end (* Compatiblity *)

context
  fixes \<phi> :: "'a \<Rightarrow> bool" and \<psi> :: "'b \<Rightarrow> bool"
  assumes compatible1: "A_B.equiv' a b \<Longrightarrow> \<phi> a \<longleftrightarrow> \<psi> b"
begin

lemma Alw_alw_iff_strong:
  "A.Alw_alw \<phi> a \<longleftrightarrow> B.Alw_alw \<psi> b" if "A_B.equiv' a b"
  unfolding Graph_Defs.Alw_alw_iff using that by (auto dest: compatible1 intro!: Ex_ev_iff)

lemma Ex_alw_iff:
  "A.Ex_alw \<phi> a \<longleftrightarrow> B.Ex_alw \<psi> b" if "A_B.equiv' a b"
  unfolding Graph_Defs.Ex_alw_iff using that by (auto dest: compatible1 intro!: Alw_ev_iff)

end (* Compatibility *)

context
  fixes \<phi> :: "'a \<Rightarrow> bool" and \<psi> :: "'b \<Rightarrow> bool"
    and \<phi>' :: "'a \<Rightarrow> bool" and \<psi>' :: "'b \<Rightarrow> bool"
  assumes compatible1: "A_B.equiv' a b \<Longrightarrow> \<phi> a \<longleftrightarrow> \<psi> b"
  assumes compatible2: "A_B.equiv' a b \<Longrightarrow> \<phi>' a \<longleftrightarrow> \<psi>' b"
begin

lemma Leadsto_iff:
  "A.leadsto \<phi> \<phi>' a \<longleftrightarrow> B.leadsto \<psi> \<psi>' b" if "A_B.equiv' a b"
  unfolding Graph_Defs.leadsto_def
  by (auto
        dest: Alw_ev_iff[of \<phi>' \<psi>', rotated] compatible1 compatible2 equiv'_D
        intro!: Alw_alw_iff_strong[OF _ that]
     )

end (* Compatibility *)

lemma deadlock_iff:
  "A.deadlock a \<longleftrightarrow> B.deadlock b" if "a \<sim> b" "PA a" "PB b"
  using that unfolding A.deadlock_def A.deadlocked_def B.deadlock_def B.deadlocked_def
  by (force dest: A_B_step B_A_step B_A.simulation_reaches A_B.simulation_reaches)

end

lemmas [simp del] = holds.simps

end (* Theory *)
