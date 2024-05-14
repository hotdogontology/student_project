-- Problem Statement (IMO 1998 Ireland Problem 4)
-- Let a,b,c be non-negative real numbers such that a + b + c ≥ abc.
-- Prove that a^2 + b^2 + c^2 ≥ abc.

-- Solution
-- We may assume that a,b,c > 0.
-- Suppose by way of contradiction that a^2 + b^2 + c^2 < abc; then
-- abc > a^2 and so a < bc, and likewise b < ca, c < ab. Then
-- abc ≥ a^2 + b^2 + c^2 ≥ ab + bc + ca by AM-GM
-- and so abc ≥ ab + bc + ca ≥ a + b + c, contradiction.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Defs

namespace Real

open Classical

example {a b c : ℝ } (ha: a > 0) (hb : b > 0) ( hc : c > 0) (h : a + b + c ≥ a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥  a * b * c := by
-- Suppose by way of contradiction that a^2 + b^2 + c^2 < abc
by_contra! H

-- abc > a^2
have ha2 :=
  calc a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > a ^ 2 + 0 ^ 2 + 0 ^ 2 := by rel [hb, hc]
    _ = a ^ 2 := by ring

-- so a < bc
have ha3 : a < b * c := by
  calc
    a = a * 1 := by ring
    _ = a * (a / a) := by field_simp
    _ = (a * a) / a := by ring
    _ = (a ^ 2) / a := by ring
    _ < (a * b * c) / a := by rel [ha2]
    _ = (b * c * a) / a := by ring
    _ = b * c * (a / a) := by field_simp
    _ = b * c * 1 := by field_simp
    _ = b * c := by ring

-- abc > b^2
have hb2 :=
  calc a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + b ^ 2 + 0 ^ 2 := by rel [ha, hc]
    _ = b ^ 2 := by ring

-- so b < ac
have hb3 : b < a * c := by
  calc
    b = b * 1 := by ring
    _ = b * (b / b) := by field_simp
    _ = (b * b) / b := by ring
    _ = (b ^ 2) / b := by ring
    _ < (a * b * c) / b := by rel [hb2]
    _ = (a * c * b) / b := by ring
    _ = a * c * (b / b) := by field_simp
    _ = a * c * 1 := by field_simp
    _ = a * c := by ring

-- abc > c^2
have hc2 :=
  calc a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + 0 ^ 2 + c ^ 2 := by rel [ha, hb]
    _ = c ^ 2 := by ring

-- so c < ab
have hc3 : c < a * b := by
  calc
    c = c * 1 := by ring
    _ = c * (c / c) := by field_simp
    _ = (c * c) / c := by ring
    _ = (c ^ 2) / c := by ring
    _ < (a * b * c) / c := by rel [hc2]
    _ = a * b * (c / c) := by field_simp
    _ = a * b * 1 := by field_simp
    _ = a * b := by ring

-- abc ≥ a^2 + b^2 + c^2 ≥ ab + bc + ca by AM-GM

--a + b + c < ab + bc + ca
have h1 : a + b + c < a * b + b * c + a * c := by
  calc
    a + b + c = a + (b + c) := by ring
    _ < b * c + (b + c) := by rel [ha3]
    _ = (b * c + c) + b := by ring
    _ < (b * c + c) + a * c := by rel [hb3]
    _ = (a * c + b * c) + c := by ring
    _ < (a * c + b * c) + a * b := by rel [hc3]
    _ = a * b + b * c + a * c := by ring

--(a + b)/2 ≥ (ab).sqrt using amgm
--might not need this step now
--thank you martin from zulip
have ann : 0 ≤ a := le_of_lt ha
have bnn : 0 ≤ b := le_of_lt hb
have abnn : 0 ≤ a * b := Left.mul_nonneg ann bnn

have hab : (a + b) / 2 ≥ (a * b).sqrt := by
  have amgm := two_mul_le_add_sq a.sqrt b.sqrt
  rw [Real.sqrt_mul']
  rw [sq_sqrt ann, sq_sqrt bnn] at amgm
  linarith
  exact bnn

-- (b + c)/2 ≥ (bc).sqrt using amgm
have hbc : (b + c) / 2 ≥ (b * c) ^ (1/2) := by
  sorry

-- (a + c)/2 ≥ (ac).sqrt using amgm
have hac : (a + c) / 2 ≥ (a * c) ^ (1/2) := by
  sorry

-- (a^2 + 2ab + b^2) ≥ ab
have hab2 : a ^ 2 + b ^ 2 ≥ 2 * a * b := two_mul_le_add_sq a b

-- (b^2 + 2bc + c^2) ≥ bc
have hbc2 : b ^ 2 + c ^ 2 ≥ 2 * b * c := two_mul_le_add_sq b c

-- (a^2 + 2ac + c^2) ≥ ac
have hac2 : a ^ 2 + c ^ 2 ≥ 2 * a * c := two_mul_le_add_sq a c

-- the rest from previous ver

-- add three cases of AM-GM and divide by 2
-- (a^2 + b^2) + (b^2 + c^2) + (a^2 + c^2) ≥ 2ab + 2bc + 2ac
-- 2a^2 + 2b^2 + 2b^2 ≥ 2ab + 2bc + 2ac
-- a^2 + b^2 + c^2 > ab + bc + ca

have h2 : a * b + b * c + a * c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  calc
    a * b + b * c + a * c = 2 * (a * b + b * c + a * c) / 2 := by ring
    _ = (2 * a * b + 2 * b * c + 2 * a * c) / 2 := by ring
    _ ≤ ((a ^ 2 + b ^ 2) + (b ^ 2 + c ^ 2) + (a ^ 2 + c ^ 2)) / 2 := by rel [hab,hbc,hac]
    _ = (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^2) / 2 := by ring
    _ = 2 * (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by ring
    _ = a ^ 2 + b ^ 2 + c ^ 2 := by ring

-- chain inequalities together to get a contradiction
-- (h1) a + b + c < ab + bc + ac
-- (h2) ab + bc + ac < a^2 + b^2 + c^2
-- (H) a^2 + b^2 + c^2 < abc
-- so a + b + c < abc
have h' : a + b + c < a * b * c := by
  calc
    a + b + c < a * b + b * c + a * c := by rel [h1]
    _ ≤ a ^ 2 + b ^ 2 + c ^ 2 := by rel [h2]
    _ < a * b * c := by rel [H]

-- but this contradicts (h) a + b + c ≥ abc
