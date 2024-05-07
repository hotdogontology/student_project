-- Authors
-- Ni Yuan, GSSM Class of 2024
-- Teagan Mann, GSSM Class of 2025

-- Advisor
-- Taylor Belcher, GSSM Computer Science Instructor

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
import Mathlib.Analysis.MeanInequalitiesPow

--might need Real namespace instead?
namespace NNReal


--do we need an open statement here?
open Classical

example {a b c : ℝ } (ha: a > 0) (hb : b > 0) ( hc : c > 0) (h : a + b + c ≥ a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥  a * b * c := by
-- Suppose by way of contradiction that a^2 + b^2 + c^2 < abc
by_contra! H

-- abc > a^2
have ha2 : a * b * c > a ^ 2 := by
  calc
    a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > a ^ 2 + 0 ^ 2 + 0 ^ 2 := by rel [hb,hc]
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
have hb2 : a * b * c > b ^ 2 := by
  calc
    a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + b ^ 2 + 0 ^ 2 := by rel [ha,hc]
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
have hc2 : a * b * c > c ^ 2 := by
  calc
    a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + 0 ^ 2 + c ^ 2 := by rel [ha,hb]
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


-- plan: write lemma that takes in two real numbers and applies the AM-GM for 2 numbers to it
--https://github.com/leanprover-community/mathlib4/blob/03b471425ef6894a1385678605489d7ef289754b/Mathlib/Analysis/MeanInequalities.lean#L201-L205
-- def am_gm2 (x : ℝ) (y : ℝ) := add_rpow_le_rpow_add (Real.toNNreal x) (Real.toNNreal y)
-- justify that x ^ (1/2) ^ 2 = x : https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html#Real.rpow_inv_natCast_pow
-- connecting sqrt to fractional power also an issue
-- could probably streamline the proof if we had a lemma that took into two real numbers xy and returned xy_am_gm instead of repeating three times like we do

-- apply AM-GM to a,b
have ab_am_gm : (a + b) / 2 ≥ (a * b) ^ (1/2) := by sorry

-- a^2 + b^2 ≥ 2ab
have hab : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  calc
    a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * a * b := by ring
    _ = 4 * ((a + b) / 2) ^ 2 - 2 * a * b := by ring
    _ ≥ 4 * ((a * b) ^ (1/2)) ^ 2 - 2 * a * b := by rel [ab_am_gm]
    _ = 4 * a * b - 2 * a * b := by sorry
    _ = 2 * a * b := by ring


-- apply AM-GM to b,c
have bc_am_gm : (1/2) * b + (1/2) * c ≥ (b * c) ^ (1/2) := by sorry

-- b^2 + c^2 ≥ 2bc
have hbc : b ^ 2 + c ^ 2 ≥ 2 * b * c := by
  calc
    b ^ 2 + c ^ 2 = (b + c) ^ 2 - 2 * b * c := by ring
    _ = 4 * ((b + c) / 2) ^ 2 - 2 * b * c := by ring
    _ ≥ 4 * ((b * c) ^ (1/2)) ^ 2 - 2 * b * c := by rel [bc_am_gm]
    _ = 4 * b * c - 2 * b * c := by sorry
    _ = 2 * b * c := by ring

-- apply AM-GM to a,c
have ac_am_gm : (1/2) * a + (1/2) * c ≥ (a * c) ^ (1/2) := by sorry

-- a^2 + c^2 ≥ 2ac
have hac : a ^ 2 + c ^ 2 ≥ 2 * a * c := by
  calc
    a ^ 2 + c ^ 2 = (a + c) ^ 2 - 2 * a * c := by ring
    _ = 4 * ((a + c) / 2) ^ 2 - 2 * a * c := by ring
    _ ≥ 4 * ((a * c) ^ (1/2)) ^ 2 - 2 * a * c := by rel [ab_am_gm]
    _ = 4 * a * c - 2 * a * c := by sorry
    _ = 2 * a * c := by ring

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
