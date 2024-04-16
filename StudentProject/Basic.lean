-- Problem Statement (IMO 1998 Ireland Problem 4)
-- Let a,b,c be non-negative real numbers such that a + b + c ≥ abc.
-- Prove that a^2 + b^2 + c ^2 ≥ abc.

-- Solution
-- We may assume that a,b,c > 0.
-- Suppose by way of contradiction that a^2 + b^2 +c^2; then
-- abc > a^2
import Mathlib.Data.Real.Basic
example {a b c : ℤ } (ha: a > 0) (hb : b > 0) ( hc : c > 0) (h : a + b + c ≥ a * b * c) : ¬ (a^2 + b^2 + c^2 < a * b * c) := by
intro h
have h' : a * b * c ≥ a^2
