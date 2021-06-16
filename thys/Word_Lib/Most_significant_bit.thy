(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Dedicated operation for the most significant bit\<close>

theory Most_significant_bit
  imports
    "HOL-Library.Word"
    Bits_Int
    More_Word
    More_Arithmetic
begin

class msb =
  fixes msb :: \<open>'a \<Rightarrow> bool\<close>

instantiation int :: msb
begin

definition \<open>msb x \<longleftrightarrow> x < 0\<close> for x :: int

instance ..

end

lemma msb_conv_bin_sign: "msb x \<longleftrightarrow> bin_sign x = -1"
by(simp add: bin_sign_def not_le msb_int_def)

lemma msb_bin_rest [simp]: "msb (x div 2) = msb x"
  for x :: int
  by (simp add: msb_int_def)

lemma int_msb_and [simp]: "msb ((x :: int) AND y) \<longleftrightarrow> msb x \<and> msb y"
by(simp add: msb_int_def)

lemma int_msb_or [simp]: "msb ((x :: int) OR y) \<longleftrightarrow> msb x \<or> msb y"
by(simp add: msb_int_def)

lemma int_msb_xor [simp]: "msb ((x :: int) XOR y) \<longleftrightarrow> msb x \<noteq> msb y"
by(simp add: msb_int_def)

lemma int_msb_not [simp]: "msb (NOT (x :: int)) \<longleftrightarrow> \<not> msb x"
by(simp add: msb_int_def not_less)

lemma msb_shiftl [simp]: "msb (push_bit n (x :: int)) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_shiftr [simp]: "msb (drop_bit r (x :: int)) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_bin_sc [simp]: "msb (bin_sc n b x) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign)

lemma msb_0 [simp]: "msb (0 :: int) = False"
by(simp add: msb_int_def)

lemma msb_1 [simp]: "msb (1 :: int) = False"
by(simp add: msb_int_def)

lemma msb_numeral [simp]:
  "msb (numeral n :: int) = False"
  "msb (- numeral n :: int) = True"
by(simp_all add: msb_int_def)

instantiation word :: (len) msb
begin

definition msb_word :: \<open>'a word \<Rightarrow> bool\<close>
  where \<open>msb a \<longleftrightarrow> bin_sign (signed_take_bit (LENGTH('a) - 1) (uint a)) = - 1\<close>

lemma msb_word_eq:
  \<open>msb w \<longleftrightarrow> bit w (LENGTH('a) - 1)\<close> for w :: \<open>'a::len word\<close>
  by (simp add: msb_word_def bin_sign_lem bit_uint_iff)

instance ..

end

lemma msb_word_iff_bit:
  \<open>msb w \<longleftrightarrow> bit w (LENGTH('a) - Suc 0)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: msb_word_def bin_sign_def bit_uint_iff)

lemma word_msb_def:
  "msb a \<longleftrightarrow> bin_sign (sint a) = - 1"
  by (simp add: msb_word_def sint_uint)

lemma word_msb_sint: "msb w \<longleftrightarrow> sint w < 0"
  by (simp add: msb_word_eq bit_last_iff)

lemma msb_word_iff_sless_0:
  \<open>msb w \<longleftrightarrow> w <s 0\<close>
  by (simp add: word_msb_sint word_sless_alt)

lemma msb_word_of_int: "msb (word_of_int x::'a::len word) = bit x (LENGTH('a) - 1)"
  by (simp add: word_msb_def bin_sign_lem)

lemma word_msb_numeral [simp]:
  "msb (numeral w::'a::len word) = bit (numeral w :: int) (LENGTH('a) - 1)"
  unfolding word_numeral_alt by (rule msb_word_of_int)

lemma word_msb_neg_numeral [simp]:
  "msb (- numeral w::'a::len word) = bit (- numeral w :: int) (LENGTH('a) - 1)"
  unfolding word_neg_numeral_alt by (rule msb_word_of_int)

lemma word_msb_0 [simp]: "\<not> msb (0::'a::len word)"
  by (simp add: word_msb_def bin_sign_def sint_uint sbintrunc_eq_take_bit)

lemma word_msb_1 [simp]: "msb (1::'a::len word) \<longleftrightarrow> LENGTH('a) = 1"
  unfolding word_1_wi msb_word_of_int eq_iff [where 'a=nat]
  by (simp add: Suc_le_eq)

lemma word_msb_nth: "msb w = bit (uint w) (LENGTH('a) - 1)"
  for w :: "'a::len word"
  by (simp add: word_msb_def sint_uint bin_sign_lem)

lemma msb_nth: "msb w = bit w (LENGTH('a) - 1)"
  for w :: "'a::len word"
  by (fact msb_word_eq)
  
lemma word_msb_n1 [simp]: "msb (-1::'a::len word)"
  by (simp add: msb_word_eq not_le)

lemma msb_shift: "msb w \<longleftrightarrow> drop_bit (LENGTH('a) - 1) w \<noteq> 0"
  for w :: "'a::len word"
  by (simp add: msb_word_eq bit_iff_odd_drop_bit drop_bit_eq_zero_iff_not_bit_last)

lemmas word_ops_msb = msb1 [unfolded msb_nth [symmetric, unfolded One_nat_def]]

lemma word_sint_msb_eq: "sint x = uint x - (if msb x then 2 ^ size x else 0)"
  apply (cases \<open>LENGTH('a)\<close>)
   apply (simp_all add: msb_word_def bin_sign_def bit_simps word_size)
  apply transfer
  apply (auto simp add: take_bit_Suc_from_most signed_take_bit_eq_if_positive signed_take_bit_eq_if_negative minus_exp_eq_not_mask ac_simps)
  apply (subst disjunctive_add)
   apply (simp_all add: bit_simps)
  done

lemma word_sle_msb_le: "x <=s y \<longleftrightarrow> (msb y \<longrightarrow> msb x) \<and> ((msb x \<and> \<not> msb y) \<or> x \<le> y)"
  apply (simp add: word_sle_eq word_sint_msb_eq word_size word_le_def)
  apply safe
   apply (rule order_trans[OF _ uint_ge_0])
   apply (simp add: order_less_imp_le)
  apply (erule notE[OF leD])
  apply (rule order_less_le_trans[OF _ uint_ge_0])
  apply simp
  done

lemma word_sless_msb_less: "x <s y \<longleftrightarrow> (msb y \<longrightarrow> msb x) \<and> ((msb x \<and> \<not> msb y) \<or> x < y)"
  by (auto simp add: word_sless_eq word_sle_msb_le)

lemma not_msb_from_less:
  "(v :: 'a word) < 2 ^ (LENGTH('a :: len) - 1) \<Longrightarrow> \<not> msb v"
  apply (clarsimp simp add: msb_nth)
  apply (drule less_mask_eq)
  apply (drule word_eqD, drule(1) iffD2)
  apply (simp add: bit_simps)
  done

lemma sint_eq_uint:
  "\<not> msb x \<Longrightarrow> sint x = uint x"
  apply (simp add: msb_word_eq)
  apply transfer
  apply auto
  apply (smt One_nat_def bintrunc_bintrunc_l bintrunc_sbintrunc' diff_le_self len_gt_0 signed_take_bit_eq_if_positive)
  done

lemma scast_eq_ucast:
  "\<not> msb x \<Longrightarrow> scast x = ucast x"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_signed_iff bit_unsigned_iff min_def msb_word_eq)
  apply (erule notE)
  apply (metis le_less_Suc_eq test_bit_bin)
  done

lemma msb_ucast_eq:
    "LENGTH('a) = LENGTH('b) \<Longrightarrow>
         msb (ucast x :: ('a::len) word) = msb (x :: ('b::len) word)"
  by (simp add: msb_word_eq bit_simps)

lemma msb_big:
  \<open>msb a \<longleftrightarrow> 2 ^ (LENGTH('a) - Suc 0) \<le> a\<close>
  for a :: \<open>'a::len word\<close>
  using bang_is_le [of a \<open>LENGTH('a) - Suc 0\<close>]
  apply (auto simp add: msb_nth word_le_not_less)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule ccontr)
    apply (clarsimp simp: not_less)
  apply (subgoal_tac "a = a AND mask (LENGTH('a) - Suc 0)")
   apply (cut_tac and_mask_less' [where w=a and n="LENGTH('a) - Suc 0"])
    apply clarsimp
  apply simp
  apply (simp flip: take_bit_eq_mask)
  apply (rule sym)
  apply (simp add: take_bit_eq_self_iff_drop_bit_eq_0 drop_bit_eq_zero_iff_not_bit_last)
  done

end
