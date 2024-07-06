(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Instance of bit ops for nat. Used by HaskellLib and AutoCorres.
 * Lemmas about this instance should also go here. *)
theory NatBitwise
imports
  More_Lib
begin

lemma lsb_nat_def:
  \<open>lsb n = lsb (int n)\<close>
  by (simp add: lsb_nat_def lsb_int_def bit_simps)

instantiation nat :: msb
begin

definition
  "msb x = msb (int x)"

instance ..

end

lemma not_msb_nat:
  \<open>\<not> msb n\<close> for n :: nat
  by (simp add: msb_nat_def msb_int_def)

instantiation nat :: set_bit
begin

definition
  "set_bit x y z = nat (set_bit (int x) y z)"

instance
  by intro_classes
     (metis (mono_tags) set_bit_nat_def bin_nth_sc_gen bin_sc_pos
                        bit_nat_iff exp_eq_0_imp_not_bit int_eq_iff)
end

lemma nat_2p_eq_shiftl:
  "(2::nat)^x = 1 << x"
  by simp


lemma shiftl_nat_def:
  "(x::nat) << y = nat (int x << y)"
  by (simp add: nat_int_mul push_bit_eq_mult shiftl_def)

lemma nat_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: nat) << n < y << m) = (x < y << (m - n))"
  apply (simp add: nat_int_comparison(2) shiftl_nat_def shiftl_def)
  by (metis int_shiftl_less_cancel shiftl_def)


lemma nat_shiftl_lt_2p_bits:
  "(x::nat) < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_nat_def zless_nat_eq_int_zless
                  dest!: le_Suc_ex)
  by (metis bit_take_bit_iff not_add_less1 take_bit_nat_eq_self_iff)

lemmas nat_eq_test_bit = bit_eq_iff
lemmas nat_eq_test_bitI = bit_eq_iff[THEN iffD2, rule_format]

end