/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.EscapeDense
import FLP.SurvivorFinite
import FLP.ZEmpty
import Mathlib.Tactic

/-!
# Density of the empty-`Z`-set parameters (FLP95, Theorems 3.3, 3.1)

Assembling the analytic inputs: from the escape-parameter density of `FLP.EscapeDense`
(`escape_dense`), the survivor-set finiteness of `FLP.SurvivorFinite` (`survivors_finite`), and the
`Z`-set emptiness of `FLP.ZEmpty` (`ZSet_eq_empty_of_survivors_finite`), we obtain:

> the parameters `s` with `Z_{p/q}(s, s + 1/p) = ∅` are **dense** (`ZSet_empty_dense`), and
> `s = 0` is one of them (`ZSet_empty_zero`).

The pullback `s ↦ {(p−q)s}` of `escape_dense` is made trivial by the observation that the linear
mod-one map depends on its offset only modulo `1`: `lmo β ({γ}) = lmo β γ` (`lmo_fract_offset`), so
an escaping *offset* `α` in the interval `((p−q)a, (p−q)b)` yields the escaping *parameter*
`s = α/(p−q)` in `(a, b)` — no interval-tiling of the `α`-line needed.

The `s = 0` endpoint is the one exceptional parameter (`f(0) = 0` never escapes, so `escape_dense`
does not reach it); there the survivor set is `{0}` directly (`survivors_zero_finite`): while an
orbit stays in `[0, 1/β)` under `x ↦ {βx}` it equals `βⁿx`, which for `x > 0` grows past `1/β`.

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Theorems 3.3, 3.1.
-/

namespace FLP

open Set

/-- The linear mod-one map depends on its offset only modulo `1`. -/
theorem lmo_fract_offset (β γ : ℝ) : lmo β (Int.fract γ) = lmo β γ := by
  funext x
  show Int.fract (β * x + Int.fract γ) = Int.fract (β * x + γ)
  have h1 : β * x + Int.fract γ = (β * x + γ) + (↑(-⌊γ⌋) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h1, Int.fract_add_intCast]

/-- Consequently the origin-orbit is unchanged by reducing the offset mod `1`. -/
theorem phi_fract_offset (β γ : ℝ) (N : ℕ) : phi β (Int.fract γ) N = phi β γ N := by
  unfold phi; rw [lmo_fract_offset]

/-- **The `s = 0` endpoint.** For `β > 1` the survivor set of `x ↦ {βx}` is finite (in fact `{0}`):
a trapped orbit equals `βⁿx`, which escapes `[0,1/β)` for `x > 0`. -/
theorem survivors_zero_finite {β : ℝ} (hβ : 1 < β) : (survivors β 0).Finite := by
  apply Set.Finite.subset (Set.finite_singleton (0 : ℝ))
  intro x hx
  simp only [Set.mem_singleton_iff]
  obtain ⟨hxJ, hxtrap⟩ := hx
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hxJ.1 (Ne.symm hne)
  have hb : (0 : ℝ) < β := by linarith
  have hiter : ∀ n, (lmo β 0)^[n] x = β ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, lmo]
        have hlt : β ^ k * x < 1 / β := by rw [← ih]; exact hxtrap k
        have h1 : β * (β ^ k * x) + 0 = β ^ (k + 1) * x := by rw [pow_succ]; ring
        rw [h1]
        apply Int.fract_eq_self.mpr
        refine ⟨by positivity, ?_⟩
        have := mul_lt_mul_of_pos_left hlt hb
        rw [mul_one_div, div_self (ne_of_gt hb)] at this
        rw [pow_succ]; nlinarith [this]
  have hbound : ∀ n, β ^ n * x < 1 / β := fun n => by rw [← hiter n]; exact hxtrap n
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / β / x) hβ
  have : 1 / β < β ^ n * x := by
    rw [div_lt_iff₀ hxpos] at hn; linarith [hn]
  exact absurd (hbound n) (not_lt.mpr (le_of_lt this))

private theorem one_lt_ratio {p q : ℕ} (hq2 : 2 ≤ q) (hpq : q < p) : 1 < (p : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqp : (q : ℝ) < p := by exact_mod_cast hpq
  rw [lt_div_iff₀ hq0]; linarith

/-- **The `s = 0` case, as an empty `Z`-set** (`Z_{p/q}(0, 1/p) = ∅`). -/
theorem ZSet_empty_zero {p q : ℕ} (hcop : Nat.Coprime p q) (hq2 : 2 ≤ q) (hpq : q < p) :
    ZSet p q 0 (1 / p) = ∅ := by
  apply ZSet_eq_empty_of_survivors_finite hq2 hpq hcop (le_refl 0)
  have h0 : alphaSym p q 0 = 0 := by unfold alphaSym; simp
  rw [h0]
  exact survivors_zero_finite (one_lt_ratio hq2 hpq)

/-- **FLP95 Theorems 3.3 + 3.1:** the parameters `s` with `Z_{p/q}(s, s+1/p) = ∅` are dense — every
interval `(a, b)` with `0 ≤ a < b` contains such an `s`.  (Via the `s ↦ {(p−q)s}` pullback of
`escape_dense`.) -/
theorem ZSet_empty_dense {p q : ℕ} (hcop : Nat.Coprime p q) (hq2 : 2 ≤ q) (hpq : q < p)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ s, a < s ∧ s < b ∧ ZSet p q s (1 / p) = ∅ := by
  have hpqR : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hpq
    linarith
  have hβ1 : 1 < (p : ℝ) / q := one_lt_ratio hq2 hpq
  -- escaping offset in the scaled interval
  obtain ⟨α, hα1, hα2, N, hesc⟩ :=
    escape_dense hβ1 (show ((p : ℝ) - q) * a < ((p : ℝ) - q) * b from by nlinarith [hpqR, hab])
  refine ⟨α / ((p : ℝ) - q), ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hpqR]; nlinarith [hα1]
  · rw [div_lt_iff₀ hpqR]; nlinarith [hα2]
  · set s := α / ((p : ℝ) - q) with hs
    have hprod : ((p : ℝ) - q) * s = α := by rw [hs]; field_simp
    have hs0 : 0 ≤ s := by
      rw [hs]; apply div_nonneg _ (le_of_lt hpqR)
      have : ((p : ℝ) - q) * a ≤ α := le_of_lt hα1
      nlinarith [mul_nonneg (le_of_lt hpqR) ha, this]
    apply ZSet_eq_empty_of_survivors_finite hq2 hpq hcop hs0
    apply survivors_finite hβ1 (by unfold alphaSym; exact Int.fract_nonneg _)
      (by unfold alphaSym; exact Int.fract_lt_one _)
    show 1 / ((p : ℝ) / q) ≤ (lmo ((p : ℝ) / q) (alphaSym p q s))^[N] 0
    have halpha : alphaSym p q s = Int.fract α := by unfold alphaSym; rw [hprod]
    rw [show (lmo ((p : ℝ) / q) (alphaSym p q s))^[N] 0 = phi ((p : ℝ) / q) (alphaSym p q s) N from rfl,
      halpha, phi_fract_offset]
    exact hesc

end FLP
