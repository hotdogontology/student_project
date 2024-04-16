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

-- abc > b^2
have hb2 : a * b * c > b ^ 2 := by
  calc
    a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + b ^ 2 + 0 ^ 2 := by rel [ha,hc]
    _ = b ^ 2 := by ring

-- so b < ac

-- abc > c^2
have hc2 : a * b * c > c ^ 2 := by
  calc
    a * b * c > a ^ 2 + b ^ 2 + c ^ 2 := by linarith [H]
    _ > 0 ^ 2 + 0 ^ 2 + c ^ 2 := by rel [ha,hc]
    _ = c ^ 2 := by ring

-- so c < ab
