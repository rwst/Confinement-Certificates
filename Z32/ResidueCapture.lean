/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.EscapeCert

/-!
# Residue non-capture: `⌊ξ(3/2)ⁿ⌋ mod m` is never eventually constant (plan-cert32 T1, M1)

> **T1.** For every real `ξ > 0` and every modulus `m ≥ 3`, the sequence of residues
> `⌊ξ(3/2)ⁿ⌋ mod m` is **not** eventually constant.

Three ingredients, all already in place:

1. the **dictionary** (`Z32/Dictionary.lean`): `⌊t⌋ ≡ r (mod m)` iff `{t/m} ∈ [r/m, (r+1)/m)`, so
   eventual residue capture at `r` says the orbit of `η = ξ/m` is eventually confined to a cell of
   length `1/m ≤ 1/3`;
2. the **shift trick** (`Z32.mem_ZSet_of_eventually`): eventual confinement of `η` from step `N` is
   genuine confinement of `η(3/2)^N`, i.e. an element of `FLP.ZSet`;
3. the **five escape certificates** (`Z32/EscapeCert.lean`): `Z_{3/2}(s, s+⅓) = ∅` at
   `s ∈ {0, ⅙, ⅓, ½, ⅔}`.

The only genuinely new step is combinatorial: those five windows, of length `⅓` at spacing `⅙`,
**cover every cell** `[r/m, (r+1)/m)` with `m ≥ 3` (`Z32.exists_grid_window`: locate `6r` among the
multiples of `m`, with `m = 3, 4` checked cell by cell).  For `m = 3` the slack is zero and the cell
*is* the window (`r/3 ↦ s = r/3`); for `m ≥ 4` there is room to dodge.  Hence `Z32.ZSet_cell_empty`: no `ξ > 0` keeps `{ξ(3/2)ⁿ}` inside a cell of any
modulus `m ≥ 3`, and T1 follows.

## Claim level (gates G-5, G-6 of `plans/plan-cert32.html`)

T1 is stated nowhere in the twenty-eight papers read across the plan's six literature gates, but it
is **not** new mathematics: it is a one-line corollary of [Dub09AA] Theorem 1, which gives
`Z_{3/2}(s, s+⅓) = ∅` for *every* `s` — a strictly stronger input than the five positions used
here.  Claim level, fixed at G-5: **folklore-grade corollary, formalization-only.**  What is new is
the proof object: kernel-checked, `std3`-only, zero cited axioms, no `native_decide`.

`m = 2` is deliberately excluded and is not an oversight: the two cells `[0,½)` and `[½,1)` are
Mahler's `Z`-number problem and its parity twin (plan-cert32 §1.3, T8), both open.

## Contents

* `Z32.exists_grid_window` — the covering combinatorics: a window `k/6`, `k ≤ 4`, for every cell.
* `Z32.ZSet_cell_empty`, `Z32.ZSet_cell_empty_int` — `Z_{3/2}(r/m, (r+1)/m) = ∅` for `m ≥ 3`.
* `Z32.residue_not_eventually_constant` — **T1**.
* `Z32.exists_residue_change`, `Z32.residue_not_eventually_constant_one` — the i.o. form and the
  `ξ = 1` instance.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arithmetica **70.2** (1995), 125–147, Cor. 1.4a.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239, Thm 1 (the stronger all-positions statement; not used here).
* `plans/plan-cert32.html` §1.2, §2 (T1), §3.1, §3.5, §3.6, §11 (milestone M1).
-/

namespace Z32

open Set

/-! ## The covering combinatorics

The five certified windows are `[k/6, k/6 + 1/3)` for `k = 0, 1, 2, 3, 4`.  A cell
`[r/m, (r+1)/m)` fits into the window of index `k` exactly when `k·m ≤ 6r` (left endpoint) and
`6r + 6 ≤ (k+2)·m` (right endpoint).  Choosing `k` by the position of `6r` among the multiples of
`m` works for every `m ≥ 3`. -/

/-- **The covering lemma.**  For every modulus `m ≥ 3` and residue `r < m` there is a grid window
index `k ≤ 4` with `[r/m, (r+1)/m) ⊆ [k/6, k/6 + 1/3)`, stated as the two integer inequalities.

The tight cases are `m = 3` (equality on both sides — the cell *is* the window) and `m = 4` at
`r = 1, 3` (equality on the right). -/
theorem exists_grid_window {m r : ℕ} (hm : 3 ≤ m) (hr : r < m) :
    ∃ k : ℕ, k ≤ 4 ∧ k * m ≤ 6 * r ∧ 6 * r + 6 ≤ (k + 2) * m := by
  rcases lt_or_ge m 5 with hsmall | hbig
  · -- `m = 3, 4`: the seven cells checked one by one (both are tight cases)
    interval_cases m <;> interval_cases r <;>
      first
        | exact ⟨0, by omega, by omega, by omega⟩
        | exact ⟨1, by omega, by omega, by omega⟩
        | exact ⟨2, by omega, by omega, by omega⟩
        | exact ⟨3, by omega, by omega, by omega⟩
        | exact ⟨4, by omega, by omega, by omega⟩
  · -- `m ≥ 5`: locate `6r` among the multiples of `m`
    rcases lt_or_ge (6 * r) m with h | h
    · exact ⟨0, by omega, by omega, by omega⟩
    rcases lt_or_ge (6 * r) (2 * m) with h2 | h2
    · exact ⟨1, by omega, by omega, by omega⟩
    rcases lt_or_ge (6 * r) (3 * m) with h3 | h3
    · exact ⟨2, by omega, by omega, by omega⟩
    rcases lt_or_ge (6 * r) (4 * m) with h4 | h4
    · exact ⟨3, by omega, by omega, by omega⟩
    · exact ⟨4, by omega, by omega, by omega⟩

/-! ## Every cell of modulus `m ≥ 3` is empty -/

/-- **The cell atlas at `m ≥ 3`.**  For every modulus `m ≥ 3` and every residue `r < m`, no `ξ > 0`
keeps `{ξ(3/2)ⁿ}` inside the cell `[r/m, (r+1)/m)` for all `n`.

This is the FLP95 emptiness zone read through the dictionary: the cell has length `1/m ≤ 1/3`, so it
sits inside one of the five certified windows of `Z32.FLP_cor_one_four_a`. -/
theorem ZSet_cell_empty {m r : ℕ} (hm : 3 ≤ m) (hr : r < m) :
    FLP.ZSet 3 2 ((r : ℝ) / m) (1 / m) = ∅ := by
  obtain ⟨k, hk4, hk1, hk2⟩ := exists_grid_window hm hr
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have hk1R : (k : ℝ) * m ≤ 6 * r := by exact_mod_cast hk1
  have hk2R : 6 * (r : ℝ) + 6 ≤ ((k : ℝ) + 2) * m := by exact_mod_cast hk2
  -- the window `[k/6, k/6 + 1/3)` is certified empty
  have hwin : FLP.ZSet 3 2 ((k : ℝ) / 6) (1 / 3) = ∅ := by
    refine FLP_cor_one_four_a ?_
    simp only [mem_insert_iff, mem_singleton_iff]
    interval_cases k <;> norm_num
  -- and it contains the cell
  refine Set.eq_empty_of_subset_empty ?_
  rw [← hwin]
  refine ZSet_mono ?_ ?_
  · have key : (r : ℝ) / m - (k : ℝ) / 6 = (6 * (r : ℝ) - (k : ℝ) * m) / (6 * m) := by
      field_simp
      try ring
    have hnn : 0 ≤ (6 * (r : ℝ) - (k : ℝ) * m) / (6 * m) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  · have key : (k : ℝ) / 6 + 1 / 3 - ((r : ℝ) / m + 1 / m)
        = (((k : ℝ) + 2) * m - (6 * (r : ℝ) + 6)) / (6 * m) := by
      field_simp
      try ring
    have hnn : 0 ≤ (((k : ℝ) + 2) * m - (6 * (r : ℝ) + 6)) / (6 * m) :=
      div_nonneg (by linarith) (by positivity)
    linarith

/-- The cell atlas with an integer residue index — the form the dictionary hands over. -/
theorem ZSet_cell_empty_int {m : ℕ} {r : ℤ} (hm : 3 ≤ m) (hr0 : 0 ≤ r) (hr : r < (m : ℤ)) :
    FLP.ZSet 3 2 ((r : ℝ) / m) (1 / m) = ∅ := by
  lift r to ℕ using hr0 with r'
  have hr' : r' < m := by exact_mod_cast hr
  simpa using ZSet_cell_empty hm hr'

/-! ## T1 -/

/-- **T1 (plan-cert32 §2).**  For every `ξ > 0` and every modulus `m ≥ 3`, the residues
`⌊ξ(3/2)ⁿ⌋ mod m` are **not** eventually constant.

Claim level (gate G-5): a folklore-grade corollary — [Dub09AA] Thm 1 gives the stronger
all-positions emptiness at length `⅓`.  Formalization-only; the content here is the proof object. -/
theorem residue_not_eventually_constant {ξ : ℝ} (hξ : 0 < ξ) {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ (r : ℤ) (N : ℕ), ∀ n, N ≤ n → ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) = r := by
  rintro ⟨r, N, h⟩
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  have hmzpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm0
  -- the captured residue is a genuine residue
  have hr0 : 0 ≤ r := by rw [← h N le_rfl]; exact Int.emod_nonneg _ hmz
  have hrm : r < (m : ℤ) := by rw [← h N le_rfl]; exact Int.emod_lt_of_pos _ hmzpos
  -- the rescaled orbit is confined to the cell `[r/m, (r+1)/m)`
  have hηpos : 0 < ξ / m := div_pos hξ hmR
  have hcell : ∀ n, N ≤ n →
      Int.fract (ξ / m * (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ n)
        ∈ Ico ((r : ℝ) / m) ((r : ℝ) / m + 1 / m) := by
    intro n hn
    have hb : (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 3 / 2 := by norm_num
    have hval : ξ / m * (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ n = (ξ * (3 / 2 : ℝ) ^ n) / m := by
      rw [hb]; ring
    rw [hval]
    have hmem := fract_div_mem_cell hm0 (ξ * (3 / 2 : ℝ) ^ n)
    rw [h n hn] at hmem
    have hsplit : ((r : ℝ) + 1) / m = (r : ℝ) / m + 1 / m := by ring
    rwa [hsplit] at hmem
  -- the shift trick turns it into a `Z`-number of an empty cell
  have hmem := mem_ZSet_of_eventually (p := 3) (q := 2) (by norm_num) (by norm_num) hηpos hcell
  rw [ZSet_cell_empty_int hm hr0 hrm] at hmem
  exact hmem

/-- T1 in its infinitely-often form: past any index the residue still changes. -/
theorem exists_residue_change {ξ : ℝ} (hξ : 0 < ξ) {m : ℕ} (hm : 3 ≤ m) (N : ℕ) :
    ∃ n, N ≤ n ∧ ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ ⌊ξ * (3 / 2 : ℝ) ^ N⌋ % (m : ℤ) := by
  by_contra hc
  push Not at hc
  exact residue_not_eventually_constant hξ hm ⟨_, N, fun n hn => hc n hn⟩

/-- T1 at `ξ = 1`: the residues of `⌊(3/2)ⁿ⌋` modulo any `m ≥ 3` are not eventually constant
(plan-cert32 T7, the `ξ = 1` garnish). -/
theorem residue_not_eventually_constant_one {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ (r : ℤ) (N : ℕ), ∀ n, N ≤ n → ⌊(3 / 2 : ℝ) ^ n⌋ % (m : ℤ) = r := by
  have h := residue_not_eventually_constant (ξ := 1) one_pos hm
  simpa using h

/-! ## Sanity checks -/

/-- Sanity, the tight case `m = 3`: the middle cell `[⅓, ⅔)` is empty — the cell here *is* one of
the five certified windows. -/
example : FLP.ZSet 3 2 (1 / 3 : ℝ) (1 / 3) = ∅ := by
  simpa using ZSet_cell_empty (m := 3) (r := 1) (by norm_num) (by norm_num)

/-- Sanity: the last decimal digit of `⌊(3/2)ⁿ⌋` does not eventually stabilize. -/
example : ¬ ∃ (r : ℤ) (N : ℕ), ∀ n, N ≤ n → ⌊(3 / 2 : ℝ) ^ n⌋ % (10 : ℤ) = r := by
  simpa using residue_not_eventually_constant_one (m := 10) (by norm_num)

end Z32
