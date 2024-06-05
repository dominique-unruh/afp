(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory MultByAdd
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

(* Parse the input file. *)
install_C_file "mult_by_add.c"

(* Abstract the input file. *)
autocorres [ ts_force nondet = mult_by_add ] "mult_by_add.c"

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]
(*
 * Prove the function returns the correct result, and (simultaneously)
 * does not fail and terminates.
 *)
lemma (in ts_definition_mult_by_add) "mult_by_add' a b \<bullet> s\<lbrace> \<lambda>r s. r = Result (a * b) \<rbrace>"
  (* Unfold function definition. *)
  apply (clarsimp simp: mult_by_add'_def)
  apply runs_to_vcg
  apply (rule runs_to_whileLoop2
    [where I="\<lambda>(a', r) s. (a' * b) + r = (a * b)"
       and R="measure (\<lambda>((a', _), s). unat a')"])
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: split_def word_neq_0_conv[symmetric])
  (* Run "wp" weakest precondition tactic, and solve verification *
   * conditions generated by it. *)
  apply runs_to_vcg
     apply (simp add: field_simps)
  apply unat_arith
  done

(*
 * Equivalent partial-correctness proof using Simpl framework.
 *)
lemma (in mult_by_add_impl) "\<Gamma> \<turnstile> {s. s = t} \<acute>ret' :== CALL mult_by_add(\<acute>a, \<acute>b) \<lbrace> (\<acute>ret' = \<^bsup>t\<^esup>a * \<^bsup>t\<^esup>b) \<rbrace>"
  (* Unfold the body. *)
  apply vcg_step
   defer

   (* Annotate the while loop with an invariant and variant. *)
   apply (subst whileAnno_def)
   apply (subst whileAnno_def [symmetric,
     where I=" \<lbrace> (\<acute>a * \<acute>b + \<acute>result) = (\<^bsup>t\<^esup>a * \<^bsup>t\<^esup>b) \<rbrace>"
     and V="measure (\<lambda>s. unat (a_' s))"])

  (* Solve the remaining conditions. *)
   apply vcg
   apply (fastforce intro: unat_mono simp: gt0_iff_gem1 field_simps less_1_simp scast_id)+
  done

end
