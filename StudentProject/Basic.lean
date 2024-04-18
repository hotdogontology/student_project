-- Problem Statement (IMO 1998 Ireland Problem 4)
-- Let a,b,c be non-negative real numbers such that a + b + c ≥ abc.
-- Prove that a^2 + b^2 + c ^2 ≥ abc.

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

example {a b c : ℝ } (ha: a > 0) (hb : b > 0) ( hc : c > 0) (h : a + b + c ≥ a * b * c) : ¬ (a ^ 2 + b ^ 2 + c ^ 2 < a * b * c) := by
-- Suppose by way of contradiction that a^2 + b^2 + c^2 < abc
intro H

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

sorry
