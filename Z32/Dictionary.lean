/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The dictionary: floor residues are cells (plan-cert32 §1.2, milestone M1)

The confinement atlas for `{ξ(3/2)ⁿ}` rests on one translation, which this file proves once and
for all:

> **Dictionary.** For `m ≥ 1` and `0 ≤ r < m`,
> `⌊t⌋ ≡ r (mod m)` **iff** `{t/m} ∈ [r/m, (r+1)/m)`.

So every *residue* question about the integer part `⌊ξ(3/2)ⁿ⌋` is verbatim a *cell-confinement*
question about the fractional part of the rescaled orbit `η = ξ/m`, and the whole
Flatto–Lagarias–Pollington machinery of `FLP/` applies to it unchanged.  The computational core is
`Z32.fract_div_natCast`: dividing by `m` moves the residue of the integer part into the fractional
part, exactly,

`{t/m} = ((⌊t⌋ mod m) + {t}) / m`.

Two more pieces of glue live here: `Z32.ZSet_mono` (a `Z`-set only grows when its window grows)
and `Z32.mem_ZSet_of_eventually` (the **shift trick**: an orbit that is *eventually* confined
produces a genuine `Z`-number for the same window, namely `ξ(p/q)^N`).  Together they turn any
certified empty window into a statement about eventual behaviour, which is what the targets of
plan-cert32 are stated in.

## Contents

* `Z32.fract_div_natCast` — the exact split `{t/m} = ((⌊t⌋ mod m) + {t})/m`.
* `Z32.fract_div_mem_cell`, `Z32.floor_emod_of_fract_mem`, `Z32.floor_emod_iff_fract_mem` — the
  dictionary, both directions and as an `iff`.
* `Z32.ZSet_mono` — window monotonicity of `FLP.ZSet`.
* `Z32.mem_ZSet_of_eventually` — the shift trick.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arithmetica **70.2** (1995), 125–147.
* `plans/plan-cert32.html` §1.2 (the dictionary), §1.4 (statement classes), §9 (file plan).
-/

namespace Z32

open Set

/-! ## Division helpers

Kept elementary on purpose: only `ring`, `linarith`, `div_pos`, `div_nonneg`.  These four one-liners
replace the family of `div_le_div_*` lemmas whose names have churned across Mathlib versions. -/

private theorem div_le_div_right' {a b c : ℝ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  have h1 : 0 ≤ (b - a) / c := div_nonneg (by linarith) hc.le
  have h2 : b / c - a / c = (b - a) / c := by ring
  linarith

private theorem div_lt_div_right' {a b c : ℝ} (hc : 0 < c) (h : a < b) : a / c < b / c := by
  have h1 : 0 < (b - a) / c := div_pos (by linarith) hc
  have h2 : b / c - a / c = (b - a) / c := by ring
  linarith

private theorem le_of_div_le_div' {a b c : ℝ} (hc : 0 < c) (h : a / c ≤ b / c) : a ≤ b := by
  by_contra hcon
  rw [not_le] at hcon
  exact absurd h (not_le.mpr (div_lt_div_right' hc hcon))

private theorem lt_of_div_lt_div' {a b c : ℝ} (hc : 0 < c) (h : a / c < b / c) : a < b := by
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd h (not_lt.mpr (div_le_div_right' hc hcon))

/-! ## The dictionary -/

/-- **The dictionary, computational core.**  Dividing by `m` moves the residue of the integer part
into the fractional part, exactly: `{t/m} = ((⌊t⌋ mod m) + {t})/m`. -/
theorem fract_div_natCast {m : ℕ} (hm : 0 < m) (t : ℝ) :
    Int.fract (t / m) = (((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + Int.fract t) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm.ne'
  have hmzpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hu0 : (0 : ℤ) ≤ ⌊t⌋ % (m : ℤ) := Int.emod_nonneg _ hmz
  have hu1 : ⌊t⌋ % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ hmzpos
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have hu0' : (0 : ℝ) ≤ ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) := by exact_mod_cast hu0
  have hu1' : ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hu1
  have hθ0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
  have hθ1 : Int.fract t < 1 := Int.fract_lt_one t
  -- `t = m·(⌊t⌋ / m) + (⌊t⌋ mod m) + {t}` after casting
  have hdm : ⌊t⌋ % (m : ℤ) + (m : ℤ) * (⌊t⌋ / (m : ℤ)) = ⌊t⌋ := Int.emod_add_mul_ediv _ _
  have hdm' : ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + (m : ℝ) * ((⌊t⌋ / (m : ℤ) : ℤ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdm
  have hfl : ((⌊t⌋ : ℤ) : ℝ) + Int.fract t = t := Int.floor_add_fract t
  have hsplit : t / m
      = (((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + Int.fract t) / m + ((⌊t⌋ / (m : ℤ) : ℤ) : ℝ) := by
    field_simp
    linarith
  rw [hsplit, Int.fract_add_intCast]
  refine Int.fract_eq_self.mpr ⟨div_nonneg (by linarith) hm0.le, ?_⟩
  rw [div_lt_one hm0]
  linarith

/-- **The dictionary, forward direction.**  The fractional part of `t/m` lies in the cell indexed
by the residue of `⌊t⌋` modulo `m`. -/
theorem fract_div_mem_cell {m : ℕ} (hm : 0 < m) (t : ℝ) :
    Int.fract (t / m) ∈ Ico (((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) / m)
      ((((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + 1) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [fract_div_natCast hm t]
  exact ⟨div_le_div_right' hm0 (by linarith [Int.fract_nonneg t]),
    div_lt_div_right' hm0 (by linarith [Int.fract_lt_one t])⟩

/-- **The dictionary, backward direction.**  If `{t/m}` lies in the cell `[r/m, (r+1)/m)` for some
`0 ≤ r < m`, then `⌊t⌋ ≡ r (mod m)`. -/
theorem floor_emod_of_fract_mem {m : ℕ} (hm : 0 < m) {t : ℝ} {r : ℤ}
    (h : Int.fract (t / m) ∈ Ico ((r : ℝ) / m) (((r : ℝ) + 1) / m)) :
    ⌊t⌋ % (m : ℤ) = r := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
  have hθ1 : Int.fract t < 1 := Int.fract_lt_one t
  rw [fract_div_natCast hm t] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : (r : ℝ) ≤ ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + Int.fract t := le_of_div_le_div' hm0 h1
  have e2 : ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + Int.fract t < (r : ℝ) + 1 := lt_of_div_lt_div' hm0 h2
  have f1 : (r : ℝ) < ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + 1 := by linarith
  have f2 : ((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) < (r : ℝ) + 1 := by linarith
  have g1 : r < ⌊t⌋ % (m : ℤ) + 1 := by exact_mod_cast f1
  have g2 : ⌊t⌋ % (m : ℤ) < r + 1 := by exact_mod_cast f2
  omega

/-- **The dictionary** (plan-cert32 §1.2): for `0 ≤ r < m`, the integer part `⌊t⌋` has residue `r`
modulo `m` **iff** the rescaled fractional part `{t/m}` lies in the cell `[r/m, (r+1)/m)`.

Applied along an orbit this is the whole content of the transfer: `⌊ξ(3/2)ⁿ⌋ ≡ r (mod m)` for all
`n ≥ N` is exactly confinement of the orbit of `η = ξ/m` to a cell of length `1/m`. -/
theorem floor_emod_iff_fract_mem {m : ℕ} (hm : 0 < m) (t : ℝ) {r : ℤ} :
    ⌊t⌋ % (m : ℤ) = r ↔ Int.fract (t / m) ∈ Ico ((r : ℝ) / m) (((r : ℝ) + 1) / m) := by
  constructor
  · rintro rfl; exact fract_div_mem_cell hm t
  · exact floor_emod_of_fract_mem hm

/-! ## Glue for the `Z`-sets -/

/-- Window monotonicity: a wider window has a larger `Z`-set. -/
theorem ZSet_mono {p q : ℕ} {s t s' t' : ℝ} (h1 : s ≤ s') (h2 : s' + t' ≤ s + t) :
    FLP.ZSet p q s' t' ⊆ FLP.ZSet p q s t := by
  rintro ξ ⟨hξ, h⟩
  refine ⟨hξ, fun n => ?_⟩
  have := h n
  rw [mem_Ico] at this ⊢
  exact ⟨le_trans h1 this.1, lt_of_lt_of_le this.2 h2⟩

/-- **The shift trick** (used in `FLP/Capstone.lean`, isolated here): if the orbit of `ξ` is
*eventually* confined to `[s, s+t)`, then the shifted point `ξ(p/q)^N` is a genuine `Z`-number for
that window.  Hence a certified empty `Z`-set kills eventual confinement, not just confinement from
step `0`. -/
theorem mem_ZSet_of_eventually {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {s t ξ : ℝ} (hξ : 0 < ξ) {N : ℕ}
    (h : ∀ n, N ≤ n → Int.fract (ξ * ((p : ℝ) / q) ^ n) ∈ Ico s (s + t)) :
    ξ * ((p : ℝ) / q) ^ N ∈ FLP.ZSet p q s t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ : (0 : ℝ) < (p : ℝ) / q := div_pos hp0 hq0
  refine ⟨mul_pos hξ (pow_pos hβ N), fun n => ?_⟩
  have hval : ξ * ((p : ℝ) / q) ^ N * ((p : ℝ) / q) ^ n = ξ * ((p : ℝ) / q) ^ (N + n) := by
    rw [pow_add]; ring
  rw [hval]
  exact h _ (Nat.le_add_right _ _)

end Z32
