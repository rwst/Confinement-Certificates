/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import ForMathlib.Data.Rat.NearestInt

@[expose] public section

/-- The distance from a real number to the nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

theorem distToNearestInt_nonneg (x : ℝ) : 0 ≤ distToNearestInt x := abs_nonneg _

/-- `round` is a nearest integer: the distance to any integer is at least
`distToNearestInt`. -/
theorem distToNearestInt_le_abs_sub_intCast (x : ℝ) (n : ℤ) :
    distToNearestInt x ≤ |x - n| :=
  round_le x n

/-- The `ℝ`-valued distance of a rational number to `ℤ` is the (computable) `ℚ`-valued
one (`Rat.distToNearestInt`) — the bridge between the two `NearestInt` files. -/
theorem distToNearestInt_ratCast (q : ℚ) :
    distToNearestInt (q : ℝ) = (q.distToNearestInt : ℝ) := by
  rw [distToNearestInt, Rat.distToNearestInt, Rat.round_cast]
  push_cast
  ring_nf

/-- An irrational number keeps positive distance from the integers. -/
theorem distToNearestInt_pos_of_irrational {x : ℝ} (hx : Irrational x) :
    0 < distToNearestInt x := by
  rw [distToNearestInt, abs_pos, sub_ne_zero]
  exact hx.ne_int (round x)

/-- The distance to `ℤ` is invariant under integer translation. -/
theorem distToNearestInt_add_intCast (x : ℝ) (m : ℤ) :
    distToNearestInt (x + m) = distToNearestInt x := by
  rw [distToNearestInt, distToNearestInt, round_add_intCast]
  push_cast
  ring_nf

/-- A point of `[0, 1]` is at distance at least `min y (1 - y)` from `ℤ`; together with
`distToNearestInt_le_abs_sub_intCast` this pins `distToNearestInt` on a fundamental domain.
(Outside `[0, 1]` the bound is vacuous, so no hypothesis is needed.) -/
theorem min_le_distToNearestInt (y : ℝ) :
    min y (1 - y) ≤ distToNearestInt y := by
  rw [distToNearestInt]
  rcases le_or_gt (round y : ℝ) 0 with hk | hk
  · refine le_trans (min_le_left _ _) ?_
    rw [le_abs]
    left; linarith
  · have hk1 : (1 : ℝ) ≤ (round y : ℝ) := by exact_mod_cast (by exact_mod_cast hk : (0:ℤ) < round y)
    refine le_trans (min_le_right _ _) ?_
    rw [le_abs]
    right; linarith

/-- If `x` sits in the middle part `[k + δ, k + 1 - δ]` of the gap between two consecutive
integers, then it is at distance at least `δ` from `ℤ`.  This is the workhorse behind the
"trap" conditions of Pollington's construction. -/
theorem le_distToNearestInt_of_mem_Icc {x δ : ℝ} {k : ℤ}
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) : δ ≤ distToNearestInt x := by
  have hshift : distToNearestInt x = distToNearestInt (x - k) := by
    have h := distToNearestInt_add_intCast (x - k) k
    simpa using h
  rw [hshift]
  refine le_trans ?_ (min_le_distToNearestInt (x - k))
  rw [le_min_iff]
  constructor <;> linarith
