/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.ParamDensity
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# The ⅓-spread theorem (FLP95, Theorem 1.4 — milestone M3)

The capstone.  For coprime `p > q ≥ 2` and **every** real `ξ > 0`, the fractional parts
`{ξ(p/q)ⁿ}` have range spread at least `1/p`:

> `1/p ≤ limsup {ξ(p/q)ⁿ} − liminf {ξ(p/q)ⁿ}`.

The `p/q = 3/2` case (`three_halves_spread`) is **milestone M3** of the `(3/2)ⁿ` equidistribution
ladder (report2-weyl §5): the orbit of `ξ(3/2)ⁿ` never gets trapped in an interval shorter than `1/3`.

## Proof (`plan-FLT.html` §4.3)

Suppose the spread were `< 1/p`.  Then, choosing `ε` small, the orbit is eventually trapped in an
interval `[s', L+ε)` of width `< 1/p` (from `eventually_lt_of_limsup_lt` /
`eventually_lt_of_lt_liminf`).  Shifting `ξ` to `ξ' = ξ(p/q)^K` traps the *whole* forward orbit, so
`ξ'` is a `Z`-number for a window of width `< 1/p`.  But the parameters with an empty `Z`-set are
dense (`FLP.ParamDensity.ZSet_empty_dense`) and include `s = 0` (`ZSet_empty_zero`), so there is an
`s*` with `[s', L+ε) ⊆ [s*, s*+1/p)` and `Z_{p/q}(s*, s*+1/p) = ∅` — yet `ξ' ∈ Z_{p/q}(s*, s*+1/p)`.
Contradiction.

`q ≥ 2` is essential: for integer `β = p` (i.e. `q = 1`), `ξ = 1/(p-1)` has `{ξpⁿ}` constant, spread
`0`.  The formal statement is the `Int.fract` version (not the centered/circle-arc variant, which is
genuinely not a corollary of FLP's interval machinery).

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Theorem 1.4.
* report2-weyl §5 (M-ladder), §9 (formalization recommendation).
-/

namespace FLP

open Set Filter

/-- **FLP95 Theorem 1.4:** for coprime `p > q ≥ 2` and every `ξ > 0`, the spread of `{ξ(p/q)ⁿ}` is
at least `1/p`. -/
theorem spread_lower_bound (p q : ℕ) (hcop : Nat.Coprime p q) (hq : 2 ≤ q) (hpq : q < p)
    (ξ : ℝ) (hξ : 0 < ξ) :
    (1 : ℝ) / p ≤ limsup (fun n : ℕ => Int.fract (ξ * ((p : ℝ) / q) ^ n)) atTop
                - liminf (fun n : ℕ => Int.fract (ξ * ((p : ℝ) / q) ^ n)) atTop := by
  set seq : ℕ → ℝ := fun n => Int.fract (ξ * ((p : ℝ) / q) ^ n) with hseqdef
  have hseq01 : ∀ n, 0 ≤ seq n ∧ seq n < 1 := fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hbddA : IsBoundedUnder (· ≤ ·) atTop seq :=
    ⟨1, eventually_map.mpr (Eventually.of_forall (fun n => (hseq01 n).2.le))⟩
  have hbddB : IsBoundedUnder (· ≥ ·) atTop seq :=
    ⟨0, eventually_map.mpr (Eventually.of_forall (fun n => (hseq01 n).1))⟩
  set L := limsup seq atTop with hL
  set ℓ := liminf seq atTop with hℓ
  by_contra hcon
  rw [not_le] at hcon
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpinv : (0 : ℝ) < 1 / p := by positivity
  set ε := (1 / (p : ℝ) - (L - ℓ)) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith [hcon]
  set s' := max 0 (ℓ - ε) with hs'
  have hs'0 : 0 ≤ s' := le_max_left _ _
  have hs'ge : ℓ - ε ≤ s' := le_max_right _ _
  have hwidth : L + ε - s' < 1 / p := by linarith [hs'ge]
  -- eventual trapping in [s', L+ε)
  have hev : ∀ᶠ n in atTop, seq n ∈ Ico s' (L + ε) := by
    filter_upwards [eventually_lt_of_lt_liminf (show ℓ - ε < ℓ by linarith [hεpos]) hbddB,
      eventually_lt_of_limsup_lt (show L < L + ε by linarith [hεpos]) hbddA] with n h1 h2
    rw [mem_Ico]
    exact ⟨max_le (hseq01 n).1 (le_of_lt h1), h2⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  set ξ' := ξ * ((p : ℝ) / q) ^ K with hξ'
  have hξ'pos : 0 < ξ' := by rw [hξ']; positivity
  -- the tail orbit is a Z-number for any window covering [s', L+ε)
  have hInZ : ∀ t : ℝ, t ≤ s' → L + ε ≤ t + 1 / p → ξ' ∈ ZSet p q t (1 / p) := by
    intro t ht1 ht2
    refine ⟨hξ'pos, fun m => ?_⟩
    have hval : Int.fract (ξ' * ((p : ℝ) / q) ^ m) = seq (K + m) := by
      simp only [hseqdef, hξ']; congr 1; rw [pow_add]; ring
    rw [hval]
    have htrap := hK (K + m) (by omega)
    rw [mem_Ico] at htrap ⊢
    exact ⟨le_trans ht1 htrap.1, lt_of_lt_of_le htrap.2 ht2⟩
  rcases eq_or_lt_of_le hs'0 with hs'eq | hs'pos
  · -- s' = 0: the s = 0 endpoint
    have hmem := hInZ 0 hs'0 (by linarith [hwidth])
    rw [ZSet_empty_zero hcop hq hpq] at hmem
    simp at hmem
  · -- s' > 0: density
    have hab : max 0 (L + ε - 1 / p) < s' := max_lt hs'pos (by linarith [hwidth])
    obtain ⟨t, ht1, ht2, htZ⟩ := ZSet_empty_dense hcop hq hpq (le_max_left _ _) hab
    have hmem := hInZ t (le_of_lt ht2)
      (by have := lt_of_le_of_lt (le_max_right 0 (L + ε - 1 / p)) ht1; linarith)
    rw [htZ] at hmem
    simp at hmem

/-- **Milestone M3** (report2-weyl §5): for every `ξ > 0`, the fractional parts of `ξ(3/2)ⁿ` have
spread at least `1/3` — no interval shorter than `1/3` eventually traps the orbit. -/
theorem three_halves_spread (ξ : ℝ) (hξ : 0 < ξ) :
    (1 : ℝ) / 3 ≤ limsup (fun n : ℕ => Int.fract (ξ * (3 / 2) ^ n)) atTop
                - liminf (fun n : ℕ => Int.fract (ξ * (3 / 2) ^ n)) atTop := by
  have h := spread_lower_bound 3 2 (by decide) (by norm_num) (by norm_num) ξ hξ
  norm_num at h
  exact h

/-- Milestone M3 at `ξ = 1`: the spread of `{(3/2)ⁿ}` is at least `1/3`. -/
theorem three_halves_spread_one :
    (1 : ℝ) / 3 ≤ limsup (fun n : ℕ => Int.fract ((3 / 2) ^ n)) atTop
                - liminf (fun n : ℕ => Int.fract ((3 / 2) ^ n)) atTop := by
  have h := three_halves_spread 1 one_pos
  simpa using h

end FLP
