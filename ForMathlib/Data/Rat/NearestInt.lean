/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Distance from a rational number to the nearest integer

`Rat.distToNearestInt x = |x - round x|` — the computable, `ℚ`-valued distance from a
rational number to the nearest integer (`round` breaks ties upward, which does not
affect the distance).  Rational companion of `distToNearestInt : ℝ → ℝ`
(`ForMathlib.Data.Real.NearestInt`).

Small API: nonnegativity, minimality over the integers
(`distToNearestInt_le_abs_sub_intCast`), vanishing exactly on the integers,
invariance under integer translation, subadditivity (`distToNearestInt_add_le`),
the integer-multiple bound
`(k·x).dist ≤ |k| · x.dist`, the dyadic repulsion floor
`one_le_two_pow_mul_distToNearestInt`: a rational whose `2^m`-fold is an *odd*
integer (`m ≥ 1`) keeps distance at least `2^{-m}` from `ℤ`, and the general
denominator floor `one_le_mul_distToNearestInt`: a non-integral rational whose
`D`-fold is an integer keeps distance at least `1/D` from `ℤ`.
-/

namespace Rat

/-- The distance from a rational number to the nearest integer. -/
def distToNearestInt (x : ℚ) : ℚ := |x - round x|

theorem distToNearestInt_nonneg (x : ℚ) : 0 ≤ x.distToNearestInt := abs_nonneg _

/-- `round` is a nearest integer: the distance to any integer is at least
`distToNearestInt`. -/
theorem distToNearestInt_le_abs_sub_intCast (x : ℚ) (n : ℤ) :
    x.distToNearestInt ≤ |x - n| :=
  round_le x n

/-- Special case `n = 0` of `distToNearestInt_le_abs_sub_intCast`. -/
theorem distToNearestInt_le_abs (x : ℚ) : x.distToNearestInt ≤ |x| := by
  simpa using distToNearestInt_le_abs_sub_intCast x 0

@[simp] theorem distToNearestInt_intCast (n : ℤ) : (n : ℚ).distToNearestInt = 0 := by
  simp [distToNearestInt]

/-- The distance to the nearest integer vanishes exactly on the integers. -/
theorem distToNearestInt_eq_zero_iff {x : ℚ} :
    x.distToNearestInt = 0 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    rw [distToNearestInt, abs_eq_zero, sub_eq_zero] at h
    exact ⟨round x, h⟩
  · rintro ⟨n, rfl⟩
    exact distToNearestInt_intCast n

/-- A rational with positive distance to `ℤ` is not an integer. -/
theorem not_exists_intCast_eq_of_distToNearestInt_pos {x : ℚ}
    (h : 0 < x.distToNearestInt) : ¬ ∃ n : ℤ, x = n := by
  intro hn
  rw [distToNearestInt_eq_zero_iff.mpr hn] at h
  exact lt_irrefl 0 h

/-- Integer translation invariance. -/
@[simp] theorem distToNearestInt_add_intCast (x : ℚ) (n : ℤ) :
    (x + n).distToNearestInt = x.distToNearestInt := by
  unfold distToNearestInt
  rw [round_add_intCast]
  congr 1
  push_cast
  ring

/-- **Subadditivity**: the distance to the nearest integer is subadditive, since
`round x + round y` is *an* integer near `x + y`. -/
theorem distToNearestInt_add_le (x y : ℚ) :
    (x + y).distToNearestInt ≤ x.distToNearestInt + y.distToNearestInt := by
  calc (x + y).distToNearestInt ≤ |x + y - ((round x + round y : ℤ) : ℚ)| :=
        distToNearestInt_le_abs_sub_intCast _ _
    _ = |(x - round x) + (y - round y)| := by
        congr 1
        push_cast
        ring
    _ ≤ |x - round x| + |y - round y| := abs_add_le _ _
    _ = x.distToNearestInt + y.distToNearestInt := rfl

/-- Integer multiples scale the distance to the nearest integer at most linearly. -/
theorem distToNearestInt_intCast_mul_le (k : ℤ) (x : ℚ) :
    ((k : ℚ) * x).distToNearestInt ≤ |(k : ℚ)| * x.distToNearestInt := by
  calc ((k : ℚ) * x).distToNearestInt ≤ |(k : ℚ) * x - ((k * round x : ℤ) : ℚ)| :=
        distToNearestInt_le_abs_sub_intCast _ _
    _ = |(k : ℚ) * (x - round x)| := by
        congr 1
        push_cast
        ring
    _ = |(k : ℚ)| * |x - round x| := abs_mul _ _
    _ = |(k : ℚ)| * x.distToNearestInt := rfl

/-- **Denominator repulsion floor**: if `D · x` is an integer for some `D > 0` and `x` is
not itself an integer (`0 < distToNearestInt x`), then `x` keeps distance at least `1/D`
from the integers, in the integer-certificate form `1 ≤ D · distToNearestInt x`. -/
theorem one_le_mul_distToNearestInt {x : ℚ} {D z : ℤ} (hD : 0 < D)
    (hzx : (z : ℚ) = D * x) (hpos : 0 < x.distToNearestInt) :
    1 ≤ (D : ℚ) * x.distToNearestInt := by
  set N : ℤ := z - D * round x with hN
  have hcast : (N : ℚ) = D * (x - round x) := by
    rw [hN]
    push_cast
    rw [hzx]
    ring
  have hNne : N ≠ 0 := by
    intro h0
    apply absurd hpos
    rw [h0] at hcast
    have hD0 : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hD.ne'
    have hx0 : x - round x = 0 := by
      rcases mul_eq_zero.mp hcast.symm with h | h
      · exact absurd h hD0
      · exact h
    simp [distToNearestInt, hx0]
  have h1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hNne
  calc (1 : ℚ) ≤ |(N : ℚ)| := by exact_mod_cast h1
    _ = |(D : ℚ) * (x - round x)| := by rw [hcast]
    _ = D * |x - round x| := by
        rw [abs_mul, abs_of_nonneg (by exact_mod_cast hD.le : (0 : ℚ) ≤ (D : ℚ))]
    _ = D * x.distToNearestInt := rfl

/-- **Dyadic repulsion floor**: if `2^m · x` is an *odd* integer with `m ≥ 1`, then
`x` keeps distance at least `2^{-m}` from the integers, in the integer-certificate
form `1 ≤ 2^m · distToNearestInt x`. -/
theorem one_le_two_pow_mul_distToNearestInt {x : ℚ} {m : ℕ} (hm : 1 ≤ m)
    {O : ℤ} (hO : O % 2 = 1) (hOx : (O : ℚ) = 2 ^ m * x) :
    1 ≤ 2 ^ m * x.distToNearestInt := by
  set N : ℤ := O - 2 ^ m * round x with hN
  have hNodd : N % 2 = 1 := by
    have h2 : ((2 : ℤ) ^ m * round x) % 2 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [show (2 : ℤ) ^ (j + 1) * round x = 2 * (2 ^ j * round x) by ring]
      exact Int.mul_emod_right 2 _
    omega
  have hNne : N ≠ 0 := by omega
  have h1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hNne
  have hcast : (N : ℚ) = 2 ^ m * (x - round x) := by
    rw [hN]
    push_cast
    rw [hOx]
    ring
  calc (1 : ℚ) ≤ |(N : ℚ)| := by exact_mod_cast h1
    _ = |(2 : ℚ) ^ m * (x - round x)| := by rw [hcast]
    _ = 2 ^ m * |x - round x| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ m)]
    _ = 2 ^ m * x.distToNearestInt := rfl

/-- Positivity form of the dyadic repulsion floor. -/
theorem distToNearestInt_pos_of_two_pow_mul_odd {x : ℚ} {m : ℕ} (hm : 1 ≤ m)
    {O : ℤ} (hO : O % 2 = 1) (hOx : (O : ℚ) = 2 ^ m * x) :
    0 < x.distToNearestInt := by
  have h := one_le_two_pow_mul_distToNearestInt hm hO hOx
  rcases (distToNearestInt_nonneg x).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, mul_zero] at h
    norm_num at h

end Rat
