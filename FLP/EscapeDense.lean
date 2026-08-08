/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Mathlib.Tactic

/-!
# Escape-parameter density (FLP95, Theorem 3.5)

Flatto–Lagarias–Pollington's Theorem 3.5 states that the *escape parameters*
`{α ∈ [0,1) : ∃ N, f_{β,α}^N(0) ≥ 1/β}` are **dense** in `[0,1)` — the input that
`FLP.SurvivorFinite.survivors_finite` needs at a dense set of `α` (`plan-FLT.html` §4.1).

This file establishes the **load-bearing keystone** of that argument: the orbit of the origin,
as a function of the offset `α`, is *piecewise affine with slope `∑_{k<n} β^k`*, the pieces being
the cylinders on which the integer parts `⌊β·f^k(0) + α⌋` are fixed.  Concretely (`phi_affine`):

> if two offsets `α, α'` induce the **same** integer-part itinerary through step `n`, then
> `f_{β,α}^n(0) − f_{β,α'}^n(0) = (∑_{k<n} β^k)·(α − α')`.

Because `∑_{k<n} β^k → ∞`, cylinders shrink like `1/∑β^k`, and the density theorem
(`escape_dense`) follows by a clean **no-tiling** contradiction: were a nonempty open interval
entirely *trapped* (`φ_n < 1/β` forever), then at the first itinerary disagreement between two of
its points there is a "crossing" where `φ_{n+1}` jumps up to arbitrarily close to `1 ≥ 1/β` — an
escape — so a trapped interval carries a single constant itinerary, forcing all its points equal by
`phi_affine`, contradicting `u < v`.  (This sidesteps the measure/cylinder-count route, which fails
for `β < 2`, the `3/2` case included.)

## Contents

* `FLP.phi` — the orbit of the origin `f_{β,α}^n(0)` as a function of `α`; `phi_succ` its one-step
  recurrence `φ_{n+1} = βφ_n + α − ⌊βφ_n + α⌋`; `phi_nonneg`, `phi_lt_one` its range `[0,1)`.
* `FLP.phi_affine` — **the keystone**: equal integer-part itineraries ⟹ the orbit difference is
  `(∑_{k<n} β^k)·(α − α')`.
* `FLP.escape_dense` — **Theorem 3.5**: for `β > 1` the escape parameters are dense (every interval
  `u < v` contains an `α` with `1/β ≤ f_{β,α}^N(0)` for some `N`).

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, §3 (Lemmas 3.4–3.5,
  Theorem 3.5).
-/

namespace FLP

open Set

/-- The orbit of the origin, `φ_n(α) = f_{β,α}^n(0)`, viewed as a function of the offset `α`. -/
noncomputable def phi (β α : ℝ) (n : ℕ) : ℝ := (lmo β α)^[n] 0

/-- One-step recurrence: `φ_{n+1}(α) = βφ_n(α) + α − ⌊βφ_n(α) + α⌋`. -/
theorem phi_succ (β α : ℝ) (k : ℕ) :
    phi β α (k + 1) = β * phi β α k + α - ⌊β * phi β α k + α⌋ := by
  unfold phi
  rw [Function.iterate_succ_apply', lmo, Int.fract]

/-- **Keystone (FLP95, Lemma 3.4).** If two offsets `α, α'` induce the same integer-part itinerary
`⌊β·φ_k + ·⌋` through step `n`, then the orbits of the origin differ by exactly
`(∑_{k<n} β^k)·(α − α')` — the affine dependence of `φ_n` on `α` on a cylinder. -/
theorem phi_affine (β α α' : ℝ) :
    ∀ n, (∀ k < n, (⌊β * phi β α k + α⌋ : ℤ) = ⌊β * phi β α' k + α'⌋) →
      phi β α n - phi β α' n = (∑ k ∈ Finset.range n, β ^ k) * (α - α') := by
  intro n
  induction n with
  | zero => intro _; simp [phi]
  | succ m ih =>
      intro hagree
      have hC : (⌊β * phi β α m + α⌋ : ℤ) = ⌊β * phi β α' m + α'⌋ := hagree m (Nat.lt_succ_self m)
      have hd := ih (fun k hk => hagree k (Nat.lt_succ_of_lt hk))
      rw [phi_succ, phi_succ, hC, Finset.sum_range_succ]
      linear_combination β * hd + (α - α') * geom_sum_mul β m

/-- The orbit of the origin is nonnegative. -/
theorem phi_nonneg (β α : ℝ) (n : ℕ) : 0 ≤ phi β α n := by
  cases n with
  | zero => simp [phi]
  | succ k => unfold phi; rw [Function.iterate_succ_apply']; exact lmo_nonneg _ _ _

/-- The orbit of the origin is `< 1`. -/
theorem phi_lt_one (β α : ℝ) (n : ℕ) : phi β α n < 1 := by
  cases n with
  | zero => simp [phi]
  | succ k => unfold phi; rw [Function.iterate_succ_apply']; exact lmo_lt_one _ _ _

/-- **FLP95 Theorem 3.5**: for `β > 1` the escape parameters are **dense** — every interval
`u < v` contains an `α` whose origin-orbit escapes, `1/β ≤ f_{β,α}^N(0)` for some `N`.

Proof (no measure, no cylinder tiling): if `(u,v)` were entirely trapped, a "first-disagreement
crossing" would produce an escape (`φ_{n+1}` near `1`), so `(u,v)` carries one constant itinerary,
forcing all its points equal via `phi_affine` and `∑βᵏ → ∞` — impossible for `u < v`. -/
theorem escape_dense {β : ℝ} (hβ : 1 < β) {u v : ℝ} (huv : u < v) :
    ∃ α, u < α ∧ α < v ∧ ∃ N, 1 / β ≤ phi β α N := by
  by_contra hcon
  have htrap : ∀ α, u < α → α < v → ∀ N, phi β α N < 1 / β := by
    intro α ha hb N; by_contra h; exact hcon ⟨α, ha, hb, N, not_lt.mp h⟩
  have hβpos : 0 < β := by linarith
  set α₀ := u + (v - u) / 3 with hα₀
  set α₁ := u + 2 * (v - u) / 3 with hα₁
  have hα01 : α₀ < α₁ := by rw [hα₀, hα₁]; linarith
  have hmemuv : ∀ α, α₀ ≤ α → α ≤ α₁ → u < α ∧ α < v := by
    intro α h1 h2; rw [hα₀] at h1; rw [hα₁] at h2; constructor <;> linarith
  have agree : ∀ n, ∀ α, α₀ ≤ α → α ≤ α₁ →
      (⌊β * phi β α n + α⌋ : ℤ) = ⌊β * phi β α₀ n + α₀⌋ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hgα : ∀ α, α₀ ≤ α → α ≤ α₁ →
          β * phi β α n + α
            = (β * phi β α₀ n + α₀) + (∑ k ∈ Finset.range (n + 1), β ^ k) * (α - α₀) := by
        intro α h0 h1
        have hpa := phi_affine β α α₀ n (fun k hk => ih k hk α h0 h1)
        rw [geom_sum_succ]; linear_combination β * hpa
      set S := ∑ k ∈ Finset.range (n + 1), β ^ k with hS
      have hSpos : 0 < S := by
        rw [hS]; apply Finset.sum_pos (fun k _ => by positivity)
        exact ⟨0, Finset.mem_range.mpr (by omega)⟩
      have hSne : S ≠ 0 := ne_of_gt hSpos
      set g0 := β * phi β α₀ n + α₀ with hg0
      set j : ℤ := ⌊g0⌋ + 1 with hj
      have hg0lt : g0 < (j : ℝ) := by rw [hj]; push_cast; exact Int.lt_floor_add_one g0
      have hg0ge : ((⌊g0⌋ : ℤ) : ℝ) ≤ g0 := Int.floor_le g0
      -- g α₁ < j (else escape)
      have hg1 : β * phi β α₁ n + α₁ < (j : ℝ) := by
        by_contra hge
        push Not at hge
        rw [hgα α₁ (le_of_lt hα01) (le_refl _)] at hge
        set x := α₀ + ((j : ℝ) - g0) / S with hx
        have hxgt : α₀ < x := by
          rw [hx]; have h1 : 0 < (j : ℝ) - g0 := by linarith
          have := div_pos h1 hSpos; linarith
        have hxle : x ≤ α₁ := by
          have h2 : ((j : ℝ) - g0) / S ≤ α₁ - α₀ := by
            rw [div_le_iff₀ hSpos]; nlinarith [hge]
          rw [hx]; linarith
        have hgx : β * phi β x n + x = (j : ℝ) := by
          rw [hgα x (le_of_lt hxgt) hxle, hx]; field_simp; ring
        have hcpos : 0 < 1 - 1 / β := by
          have : 1 / β < 1 := by rw [div_lt_one hβpos]; linarith
          linarith
        set c := (1 - 1 / β) / 2 with hc
        have hc_pos : 0 < c := by rw [hc]; linarith
        have hc_lt : c < 1 := by rw [hc]; have : (0:ℝ) < 1 / β := by positivity
                                 linarith
        set δ := min (c / S) ((x - α₀) / 2) with hδ
        have hδpos : 0 < δ := lt_min (by positivity) (by linarith [hxgt])
        have hδ1 : δ ≤ c / S := min_le_left _ _
        have hδ2 : δ ≤ (x - α₀) / 2 := min_le_right _ _
        set αe := x - δ with hαe
        have hαegt : α₀ < αe := by rw [hαe]; nlinarith [hδ2, hxgt]
        have hαelt : αe < x := by rw [hαe]; linarith [hδpos]
        have hαele : αe ≤ α₁ := le_of_lt (lt_of_lt_of_le hαelt hxle)
        have hSδc : S * δ ≤ c := by
          calc S * δ ≤ S * (c / S) := mul_le_mul_of_nonneg_left hδ1 (le_of_lt hSpos)
            _ = c := by field_simp
        have hSδpos : 0 < S * δ := by positivity
        have hSδ1 : S * δ < 1 := by linarith [hSδc, hc_lt]
        have hge_esc : β * phi β αe n + αe = (j : ℝ) - S * δ := by
          rw [hgα αe (le_of_lt hαegt) hαele, hαe]
          have hxj : g0 + S * (x - α₀) = (j : ℝ) := by
            rw [← hgα x (le_of_lt hxgt) hxle]; exact hgx
          linear_combination hxj
        have hφe : phi β αe (n + 1) = 1 - S * δ := by
          rw [phi_succ, hge_esc]
          have hfloor : (⌊(j : ℝ) - S * δ⌋ : ℤ) = j - 1 := by
            rw [Int.floor_eq_iff]
            constructor <;> push_cast <;> [linarith [hSδ1]; linarith [hSδpos]]
          rw [hfloor]; push_cast; ring
        have hφe_ge : (1 : ℝ) / β ≤ phi β αe (n + 1) := by
          rw [hφe]
          have hβ1 : 1 / β ≤ 1 := by rw [div_le_one hβpos]; linarith
          rw [hc] at hSδc; linarith [hSδc, hβ1]
        obtain ⟨hu1, hu2⟩ := hmemuv αe (le_of_lt hαegt) hαele
        exact absurd hφe_ge (not_le.mpr (htrap αe hu1 hu2 (n + 1)))
      -- conclude agree n
      intro α hα0 hα1
      have heq := hgα α hα0 hα1
      have h1 : ((⌊g0⌋ : ℤ) : ℝ) ≤ β * phi β α n + α := by
        rw [heq]; have : (0 : ℝ) ≤ S * (α - α₀) := mul_nonneg (le_of_lt hSpos) (by linarith)
        linarith [hg0ge]
      have h2 : β * phi β α n + α < ((⌊g0⌋ : ℤ) : ℝ) + 1 := by
        have hle : g0 + S * (α - α₀) ≤ β * phi β α₁ n + α₁ := by
          rw [hgα α₁ (le_of_lt hα01) (le_refl _)]; nlinarith [hSpos, hα1]
        calc β * phi β α n + α = g0 + S * (α - α₀) := heq
          _ ≤ β * phi β α₁ n + α₁ := hle
          _ < (j : ℝ) := hg1
          _ = ((⌊g0⌋ : ℤ) : ℝ) + 1 := by rw [hj]; push_cast; ring
      exact Int.floor_eq_iff.mpr ⟨h1, h2⟩
  -- all levels agree ⟹ α₀ = α₁, contradiction
  have hbig : ∀ n, phi β α₁ n - phi β α₀ n = (∑ k ∈ Finset.range n, β ^ k) * (α₁ - α₀) :=
    fun n => phi_affine β α₁ α₀ n (fun k _ => agree k α₁ (le_of_lt hα01) (le_refl _))
  have hgeom_ge : ∀ n : ℕ, (n : ℝ) ≤ ∑ k ∈ Finset.range n, β ^ k := by
    intro n
    calc (n : ℝ) = ∑ _k ∈ Finset.range n, (1 : ℝ) := by simp
      _ ≤ ∑ k ∈ Finset.range n, β ^ k :=
          Finset.sum_le_sum (fun k _ => one_le_pow₀ (le_of_lt hβ))
  have hpos : 0 < α₁ - α₀ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / (α₁ - α₀))
  have hstep : (N : ℝ) * (α₁ - α₀) < 1 := by
    have h1 := hbig N
    have hlt : phi β α₁ N - phi β α₀ N < 1 := by
      have := phi_nonneg β α₀ N; have := phi_lt_one β α₁ N; linarith
    have hmul : (N : ℝ) * (α₁ - α₀) ≤ (∑ k ∈ Finset.range N, β ^ k) * (α₁ - α₀) :=
      mul_le_mul_of_nonneg_right (hgeom_ge N) (le_of_lt hpos)
    linarith [h1, hlt, hmul]
  rw [div_le_iff₀ hpos] at hN
  linarith [hN, hstep]

end FLP
