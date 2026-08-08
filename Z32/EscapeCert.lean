/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.Dictionary
import FLP.ParamDensity

/-!
# Per-position escape certificates at length ⅓ (plan-cert32 §3, milestone M1)

The `FLP/` chain reduces emptiness of `Z_{3/2}(s, s+⅓)` to a **finite** computation: by
`FLP.ZSet_eq_empty_of_survivors_finite` (their Thm 3.2) and `FLP.survivors_finite` (their Thm 3.4)
it suffices that the orbit of the origin under `f_{3/2,α}(x) = {3x/2 + α}`, `α = {(p−q)s} = {s}`,
escapes the interval `[0, 2/3)` at some finite time `N`.  This file runs that computation at the
five positions of **FLP95 Corollary 1.4a** and records the results as theorems:

| `s`   | orbit of `0` under `x ↦ {3x/2 + s}`            | escape time |
|-------|------------------------------------------------|-------------|
| `0`   | fixed at `0` — no escape                        | (endpoint argument, `FLP.ZSet_empty_zero`) |
| `1/6` | `0 ↦ 1/6 ↦ 5/12 ↦ 19/24`                        | `N = 3` |
| `1/3` | `0 ↦ 1/3 ↦ 5/6`                                 | `N = 2` |
| `1/2` | `0 ↦ 1/2 ↦ 1/4 ↦ 7/8`                           | `N = 3` |
| `2/3` | `0 ↦ 2/3`                                       | `N = 1` |

The witnesses `N = 3, 2, 3, 1` are exactly the ones FLP95 uses in its proof of Cor 1.4a (gate G-1,
`plans/plan-cert32.html` §3.1), so `Z32.FLP_cor_one_four_a` is the **X1 control** of the plan: a
kernel-checked replay of the paper's own certificates, with known answers.  Everything is exact
rational arithmetic through `FLP.lmo_of_lt` / `FLP.lmo_of_ge`; no `native_decide`, no cited axioms.

These five windows, of length `⅓` and at spacing `⅙`, are also all that milestone M1 needs: they
cover every cell `[r/m, (r+1)/m)` with `m ≥ 3` (see `Z32/ResidueCapture.lean`).

## Contents

* `Z32.alphaSym_three_two` — for `p/q = 3/2` the FLP offset is `{s}`.
* `Z32.ZSet_third_empty_of_escape` — the certificate scheme: an escape witness at `s` kills
  `Z_{3/2}(s, s+⅓)`.
* `Z32.escape_one_sixth`, `Z32.escape_one_third`, `Z32.escape_one_half`, `Z32.escape_two_thirds` —
  the four finite orbits.
* `Z32.FLP_cor_one_four_a` — FLP95 Cor 1.4a: `Z_{3/2}(s, s+⅓) = ∅` for `s ∈ {0, ⅙, ⅓, ½, ⅔}`.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arithmetica **70.2** (1995), 125–147, Cor. 1.4a (Thms 3.2, 3.4).
* `plans/plan-cert32.html` §3.1 (gate G-1: the witnesses confirmed against the paper), §9.
-/

namespace Z32

open Set

/-! ## The certificate scheme -/

/-- For `p/q = 3/2` the FLP offset `α = {(p−q)s}` is just `{s}`, and on `[0,1)` it is `s`. -/
theorem alphaSym_three_two {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : FLP.alphaSym 3 2 s = s := by
  have h1 : ((3 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) = 1 := by norm_num
  unfold FLP.alphaSym
  rw [h1, one_mul, Int.fract_eq_self.mpr ⟨hs0, hs1⟩]

/-- **The certificate scheme** (FLP95 Thms 3.4 + 3.2, specialized to `3/2`): if the origin's orbit
under `x ↦ {3x/2 + s}` reaches `[2/3, 1)` at some finite time `N`, then no `ξ > 0` has its whole
`(3/2)`-power orbit confined to the window `[s, s + ⅓)`. -/
theorem ZSet_third_empty_of_escape {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {N : ℕ}
    (hesc : (2 : ℝ) / 3 ≤ (FLP.lmo (3 / 2) s)^[N] 0) :
    FLP.ZSet 3 2 s (1 / 3) = ∅ := by
  have hthird : (1 : ℝ) / 3 = 1 / ((3 : ℕ) : ℝ) := by norm_num
  rw [hthird]
  refine FLP.ZSet_eq_empty_of_survivors_finite (p := 3) (q := 2) (by norm_num) (by norm_num)
    (by decide) hs0 ?_
  have hb : (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 3 / 2 := by norm_num
  rw [hb, alphaSym_three_two hs0 hs1]
  refine FLP.survivors_finite (by norm_num) hs0 hs1 (N := N) ?_
  have hthr : (1 : ℝ) / (3 / 2) = 2 / 3 := by norm_num
  rw [hthr]
  exact hesc

/-! ## The four finite orbits

Each step is one application of a branch of `f_{3/2,α}`: `lmo_step` for the lower branch
(`3x/2 + α ∈ [0,1)`), `lmo_step'` for the upper one (`3x/2 + α ∈ [1,2)`). -/

private theorem lmo_step {α x y : ℝ} (h0 : 0 ≤ (3 / 2 : ℝ) * x + α) (h1 : (3 / 2 : ℝ) * x + α < 1)
    (h : (3 / 2 : ℝ) * x + α = y) : FLP.lmo (3 / 2) α x = y := by
  rw [FLP.lmo_of_lt h0 h1, h]

private theorem lmo_step' {α x y : ℝ} (h0 : 1 ≤ (3 / 2 : ℝ) * x + α) (h1 : (3 / 2 : ℝ) * x + α < 2)
    (h : (3 / 2 : ℝ) * x + α - 1 = y) : FLP.lmo (3 / 2) α x = y := by
  rw [FLP.lmo_of_ge h0 h1, h]

/-- `s = ⅙`: `0 ↦ 1/6 ↦ 5/12 ↦ 19/24 ≥ 2/3` — escape at `N = 3` (FLP95's witness). -/
theorem escape_one_sixth : (2 : ℝ) / 3 ≤ (FLP.lmo (3 / 2) (1 / 6))^[3] 0 := by
  have h1 : (FLP.lmo (3 / 2) (1 / 6))^[1] 0 = 1 / 6 := by
    rw [Function.iterate_one]; exact FLP.lmo_zero (by norm_num) (by norm_num)
  have h2 : (FLP.lmo (3 / 2) (1 / 6))^[2] 0 = 5 / 12 := by
    rw [Function.iterate_succ_apply' (FLP.lmo (3 / 2) (1 / 6)) 1 0, h1]
    exact lmo_step (by norm_num) (by norm_num) (by norm_num)
  have h3 : (FLP.lmo (3 / 2) (1 / 6))^[3] 0 = 19 / 24 := by
    rw [Function.iterate_succ_apply' (FLP.lmo (3 / 2) (1 / 6)) 2 0, h2]
    exact lmo_step (by norm_num) (by norm_num) (by norm_num)
  rw [h3]; norm_num

/-- `s = ⅓`: `0 ↦ 1/3 ↦ 5/6 ≥ 2/3` — escape at `N = 2` (FLP95's witness). -/
theorem escape_one_third : (2 : ℝ) / 3 ≤ (FLP.lmo (3 / 2) (1 / 3))^[2] 0 := by
  have h1 : (FLP.lmo (3 / 2) (1 / 3))^[1] 0 = 1 / 3 := by
    rw [Function.iterate_one]; exact FLP.lmo_zero (by norm_num) (by norm_num)
  have h2 : (FLP.lmo (3 / 2) (1 / 3))^[2] 0 = 5 / 6 := by
    rw [Function.iterate_succ_apply' (FLP.lmo (3 / 2) (1 / 3)) 1 0, h1]
    exact lmo_step (by norm_num) (by norm_num) (by norm_num)
  rw [h2]; norm_num

/-- `s = ½`: `0 ↦ 1/2 ↦ 1/4 ↦ 7/8 ≥ 2/3` — escape at `N = 3` (FLP95's witness); the middle step
uses the *upper* branch (`3/4 + 1/2 = 5/4 ≥ 1`). -/
theorem escape_one_half : (2 : ℝ) / 3 ≤ (FLP.lmo (3 / 2) (1 / 2))^[3] 0 := by
  have h1 : (FLP.lmo (3 / 2) (1 / 2))^[1] 0 = 1 / 2 := by
    rw [Function.iterate_one]; exact FLP.lmo_zero (by norm_num) (by norm_num)
  have h2 : (FLP.lmo (3 / 2) (1 / 2))^[2] 0 = 1 / 4 := by
    rw [Function.iterate_succ_apply' (FLP.lmo (3 / 2) (1 / 2)) 1 0, h1]
    exact lmo_step' (by norm_num) (by norm_num) (by norm_num)
  have h3 : (FLP.lmo (3 / 2) (1 / 2))^[3] 0 = 7 / 8 := by
    rw [Function.iterate_succ_apply' (FLP.lmo (3 / 2) (1 / 2)) 2 0, h2]
    exact lmo_step (by norm_num) (by norm_num) (by norm_num)
  rw [h3]; norm_num

/-- `s = ⅔`: `0 ↦ 2/3 ≥ 2/3` — escape at `N = 1` (FLP95's witness). -/
theorem escape_two_thirds : (2 : ℝ) / 3 ≤ (FLP.lmo (3 / 2) (2 / 3))^[1] 0 := by
  have h1 : (FLP.lmo (3 / 2) (2 / 3))^[1] 0 = 2 / 3 := by
    rw [Function.iterate_one]; exact FLP.lmo_zero (by norm_num) (by norm_num)
  rw [h1]

/-! ## FLP95, Corollary 1.4a -/

/-- **FLP95, Corollary 1.4a**, regenerated as kernel-checked certificates (plan-cert32 experiment
X1, the control run): `Z_{3/2}(s, s+⅓) = ∅` for each of the five positions
`s ∈ {0, ⅙, ⅓, ½, ⅔}`.  For `s = 0` this is `FLP.ZSet_empty_zero` (the origin is a fixed point, so
there is no escape witness and the paper argues separately); the other four are the finite orbits
above. -/
theorem FLP_cor_one_four_a {s : ℝ} (hs : s ∈ ({0, 1 / 6, 1 / 3, 1 / 2, 2 / 3} : Set ℝ)) :
    FLP.ZSet 3 2 s (1 / 3) = ∅ := by
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have h : (1 : ℝ) / 3 = 1 / ((3 : ℕ) : ℝ) := by norm_num
    rw [h]
    exact FLP.ZSet_empty_zero (by decide) (by norm_num) (by norm_num)
  · exact ZSet_third_empty_of_escape (by norm_num) (by norm_num) escape_one_sixth
  · exact ZSet_third_empty_of_escape (by norm_num) (by norm_num) escape_one_third
  · exact ZSet_third_empty_of_escape (by norm_num) (by norm_num) escape_one_half
  · exact ZSet_third_empty_of_escape (by norm_num) (by norm_num) escape_two_thirds

end Z32
