/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.BlockCert
import Z32.DepthKSchema
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The quantitative escape bound (plan z32-transform, milestone M2, target T4)

Every emptiness theorem in `Z32/` is proved by contradiction from
`Z32.not_isEventuallyPeriodic_carry`, so none of them says *when* an orbit leaves the window.
This file extracts the bound that is latent in that argument: from a certificate — a block
certificate `Z32.BlockCert.Cert` or a depth-`K` schema `Z32.SchemaCertifiedK` — and from a range
`L ≤ ξ ≤ X`, an explicit number of steps within which every such `ξ` must leave.

## The shape of the bound

`Z32.escapeSteps p q A X L = A + 1 + ⌈log_q (X·(p/q)^A + 1)⌉ + ⌈log_{p/q} (q/L)⌉`

is `A(c) + B(c)·log X + C(c)·log (1/L)`, with `A` the certificate's **combinatorial budget** — the
number of steps after which the carry word is forced to repeat.  Two logarithms, not one: the
escape time really does grow like `log (1/ξ)` as `ξ → 0`, because a `ξ` far below `1` needs
`log_{p/q}(1/ξ)` steps just to reach the scale at which the arithmetic argument has any content.
(The plan's T4 line asks for a bound in `X` alone; that is not available, and the counterexample is
an atlas entry: `Z32.BlockCert.escape_two_cell_fifth` certifies `[0, 1/5) ∪ [4/5, 1)` at `3/2`, and
for `0 < ξ < 1/5` the orbit `ξ(3/2)ⁿ` stays inside it for exactly `⌈log_{3/2}(1/(5ξ))⌉` steps —
unbounded as `ξ → 0`, with `⌊ξ⌋ = 0` throughout.)

## The argument, made effective

1. **Repetition.**  Confinement forces the carry word to be `P`-periodic from some `t` on, with
   `t + P ≤ A`.  For a depth-`K` schema, confinement on `[0, N]` gives `A = K + 2`
   (`Z32.exists_carry_period_of_certifiedK`): the rank rotation of `Z32/DepthKSchema.lean` takes
   `K + 1` values, so two of the first `K + 2` coincide.  For a block certificate the block graph
   replaces the rotation and `A = |H| = |blocks|`
   (`Z32.BlockCert.Cert.exists_carry_period_le`), but confinement is needed on `[0, N + K]` with
   `K = |levels|`, because the funnel condition looks **forward**: a point lies in a block only if
   the orbit stays in `U` for `K` further steps.  That surplus, not any delay before the period
   starts, is why `Cert.exists_escape_le` carries the offset `K` and the schema form does not.
2. **The ladder.**  `sₙ₊P = sₙ` gives `q·Mₙ₊₁ = p·Mₙ` for `Mₙ = x_{n+P} − xₙ`
   (`Z32.q_pow_mul_orbDiff`), hence `qᵐ ∣ M_t` by coprimality (`Z32.q_pow_dvd_orbDiff`).
3. **The dichotomy** (`Z32.escape_endgame`).  Either `M_t ≠ 0`, and then
   `q^{N−t−P} ≤ |ξ|(p/q)^{t+P} + 1` — an upper bound on `N` in terms of `X`; or `M_t = 0`, and
   then the integer part is exactly `P`-periodic, so `|ξ|(p/q)^{N−P}((p/q)−1) < 1` — an upper
   bound on `N` in terms of `1/L`.  Both are contradicted past `escapeSteps`.

## Main results

* `Z32.escape_endgame` — the dichotomy, for any orbit shift `ν` and any `ξ ≠ 0`.
* `Z32.exists_escape_le_of_certifiedK` — the depth-`K` schema, effective form.
* `Z32.BlockCert.Cert.exists_escape_le` — `Cert.escape_bound`, the plan's T4 deliverable.
* `Z32.BlockCert.exists_fract_notMem_le_of_cover` — the same, read off whatever set the
  certificate covers; eight of the nine functional atlas entries are one application each below,
  the ninth being `Z32.escape_union_7083` in `Z32/UnionRecord.lean`.

## Scope: the ranked certificates are not covered

`Z32.BlockCert.funcOk` asks for at most one outgoing edge **per rank**, and `Cert.not_confined`
uses that a non-increasing rank is eventually constant — a statement with no rate.  There is none
to be had from the certificate: a block may carry both an equal-rank edge and a lower-rank one, so
the model orbit can follow the equal-rank cycle for arbitrarily long and only then drop, and the
periodicity of step 1 is broken exactly when it drops.  The plan's §5.1 sketch ("the rank drops
`≤ R` times, so within `K + (R+1)|H|` steps the itinerary has entered a cycle") is wrong on that
point.  So the theorems here take `c.strata = []`, i.e. a genuinely functional block graph.  That
is nine of the ten atlas entries; the exception is `Z32.BlockCert.certDub08`, whose hold set has
transients feeding two cycles and which is the reason `funcOk` is stated by rank in the first
place.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — §2, equations (2)–(5), Proposition 2.3 and Lemma 2.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2.
* [Koh08] U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in
  Mathematics*, Springer 2008 — the metatheorems predicting that a bound of this shape, uniform
  in `ξ` through a majorant only, is extractable from the proof of `Cert.not_confined`.
-/

namespace Z32

open ForMathlib.SubwordComplexity

variable {p q : ℕ} {ξ ν : ℝ}

/-! ## A ceiling logarithm -/

/-- `x ≤ b ^ ⌈log_b x⌉` for `b > 1` and `x > 0`: the only property of the ceiling logarithm the
bounds below use. -/
theorem le_pow_natCeil_logb {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    x ≤ b ^ (⌈Real.logb b x⌉₊) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : b ≠ 1 := by linarith
  calc x = b ^ (Real.logb b x) := (Real.rpow_logb hb0 hb1 hx).symm
    _ ≤ b ^ ((⌈Real.logb b x⌉₊ : ℕ) : ℝ) :=
        (Real.rpow_le_rpow_left_iff hb).mpr (Nat.le_ceil _)
    _ = b ^ (⌈Real.logb b x⌉₊) := Real.rpow_natCast _ _

/-! ## The ladder of orbit differences -/

/-- `Mₙ = x_{n+P} − xₙ`, the integer part's increment over one period. -/
noncomputable def orbDiff (p q : ℕ) (ξ ν : ℝ) (P n : ℕ) : ℤ :=
  xInt p q ξ ν (n + P) - xInt p q ξ ν n

/-- **The ladder.**  A `P`-periodic carry word turns `M` into a geometric sequence:
`qᵐ·M_{t+m} = pᵐ·M_t`.  This is [Dub09AA]'s step "`q^ℓ ∣ M`" made quantitative — the exponent is
exactly the length of the range on which the periodicity is known. -/
theorem q_pow_mul_orbDiff {t P N : ℕ}
    (hper : ∀ n, t ≤ n → n + P + 1 ≤ N → carry p q ξ ν (n + P) = carry p q ξ ν n) :
    ∀ m : ℕ, t + m + P ≤ N →
      (q : ℤ) ^ m * orbDiff p q ξ ν P (t + m) = (p : ℤ) ^ m * orbDiff p q ξ ν P t := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hsucc : t + (m + 1) = t + m + 1 := by omega
    have hstep : (q : ℤ) * orbDiff p q ξ ν P (t + m + 1)
        = (p : ℤ) * orbDiff p q ξ ν P (t + m) := by
      have h := hper (t + m) (by omega) (by omega)
      have hidx : t + m + 1 + P = t + m + P + 1 := by omega
      simp only [orbDiff, hidx]
      simp only [carry] at h
      linear_combination h
    calc (q : ℤ) ^ (m + 1) * orbDiff p q ξ ν P (t + (m + 1))
        = (q : ℤ) ^ m * ((q : ℤ) * orbDiff p q ξ ν P (t + m + 1)) := by rw [hsucc]; ring
      _ = (q : ℤ) ^ m * ((p : ℤ) * orbDiff p q ξ ν P (t + m)) := by rw [hstep]
      _ = (p : ℤ) * ((q : ℤ) ^ m * orbDiff p q ξ ν P (t + m)) := by ring
      _ = (p : ℤ) * ((p : ℤ) ^ m * orbDiff p q ξ ν P t) := by rw [ih (by omega)]
      _ = (p : ℤ) ^ (m + 1) * orbDiff p q ξ ν P t := by ring

/-- **The divisibility.**  Coprimality turns the ladder into `qᵐ ∣ M_t`. -/
theorem q_pow_dvd_orbDiff (hcop : Nat.Coprime p q) {t P N : ℕ}
    (hper : ∀ n, t ≤ n → n + P + 1 ≤ N → carry p q ξ ν (n + P) = carry p q ξ ν n)
    {m : ℕ} (hm : t + m + P ≤ N) : (q : ℤ) ^ m ∣ orbDiff p q ξ ν P t := by
  have hlad := q_pow_mul_orbDiff (p := p) (q := q) (ξ := ξ) (ν := ν) hper m hm
  have hdvd : (q : ℤ) ^ m ∣ (p : ℤ) ^ m * orbDiff p q ξ ν P t := ⟨_, hlad.symm⟩
  have hco : IsCoprime ((q : ℤ) ^ m) ((p : ℤ) ^ m) := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow m m hcop.symm)
    push_cast at this
    exact this
  exact hco.dvd_of_dvd_mul_left hdvd

/-! ## The two branches of the endgame -/

/-- `M` in real terms: the growth of `ξ(p/q)ⁿ` minus a bounded fractional correction. -/
theorem orbDiff_cast (P n : ℕ) :
    (orbDiff p q ξ ν P n : ℝ)
      = ξ * ((p : ℝ) / q) ^ n * (((p : ℝ) / q) ^ P - 1)
        - (yFract p q ξ ν (n + P) - yFract p q ξ ν n) := by
  have h1 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := ν) n
  have h2 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := ν) (n + P)
  rw [pow_add] at h2
  simp only [orbDiff, Int.cast_sub]
  linear_combination h2 - h1

/-- The fractional correction is bounded by `1`. -/
private theorem abs_yFract_sub_lt (P n : ℕ) :
    |yFract p q ξ ν (n + P) - yFract p q ξ ν n| < 1 := by
  have h1 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := ν) (n + P)
  have h2 := yFract_lt_one (p := p) (q := q) (ξ := ξ) (ν := ν) (n + P)
  have h3 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := ν) n
  have h4 := yFract_lt_one (p := p) (q := q) (ξ := ξ) (ν := ν) n
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **The majorant.**  `|M_n| < |ξ|(p/q)^{n+P} + 1`: this is [Dub09AA] Proposition 2.3 in the form
the bound needs — the dependence on `ξ` is through `|ξ|` alone. -/
theorem abs_orbDiff_lt (hq : 0 < q) (hqp : q < p) (P n : ℕ) :
    |(orbDiff p q ξ ν P n : ℝ)| < |ξ| * ((p : ℝ) / q) ^ (n + P) + 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) ≤ (p : ℝ) / q := by rw [le_div_iff₀ hq0]; linarith
  have hb0 : (0 : ℝ) < (p : ℝ) / q := by linarith
  have hPn : (1 : ℝ) ≤ ((p : ℝ) / q) ^ P := one_le_pow₀ hb1
  have hbn : (0 : ℝ) ≤ ((p : ℝ) / q) ^ n := by positivity
  set A : ℝ := ξ * ((p : ℝ) / q) ^ n * (((p : ℝ) / q) ^ P - 1) with hA
  set Δ : ℝ := yFract p q ξ ν (n + P) - yFract p q ξ ν n with hΔ
  have hAbound : |A| ≤ |ξ| * ((p : ℝ) / q) ^ (n + P) := by
    rw [hA, abs_mul, abs_mul, abs_of_nonneg hbn, abs_of_nonneg (by linarith : (0:ℝ) ≤ ((p : ℝ) / q) ^ P - 1),
      pow_add]
    nlinarith [mul_nonneg (abs_nonneg ξ) hbn]
  have hΔbound : |Δ| < 1 := abs_yFract_sub_lt P n
  have hsplit : |A - Δ| ≤ |A| + |Δ| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le A (-Δ)
  rw [orbDiff_cast]
  calc |A - Δ| ≤ |A| + |Δ| := hsplit
    _ < |ξ| * ((p : ℝ) / q) ^ (n + P) + 1 := by linarith

/-- **The degenerate branch.**  `M_n = 0` says the integer part is exactly `P`-periodic at `n`,
which pins `ξ(p/q)ⁿ` to a bounded scale — the quantitative form of "`M = 0 ⟹ ξ = 0`". -/
theorem abs_mul_pow_lt_of_orbDiff_eq_zero (hq : 0 < q) (hqp : q < p) {P n : ℕ} (hP : 1 ≤ P)
    (h : orbDiff p q ξ ν P n = 0) :
    |ξ| * ((p : ℝ) / q) ^ n * ((p : ℝ) / q - 1) < 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) ≤ (p : ℝ) / q := by rw [le_div_iff₀ hq0]; linarith
  have hbn : (0 : ℝ) ≤ ((p : ℝ) / q) ^ n := by positivity
  have hPow : (p : ℝ) / q ≤ ((p : ℝ) / q) ^ P := by
    calc (p : ℝ) / q = ((p : ℝ) / q) ^ 1 := (pow_one _).symm
      _ ≤ ((p : ℝ) / q) ^ P := pow_le_pow_right₀ hb1 hP
  have hc := orbDiff_cast (p := p) (q := q) (ξ := ξ) (ν := ν) P n
  rw [h] at hc
  have hzero : ξ * ((p : ℝ) / q) ^ n * (((p : ℝ) / q) ^ P - 1)
      = yFract p q ξ ν (n + P) - yFract p q ξ ν n := by
    push_cast at hc; linarith
  have habs : |ξ * ((p : ℝ) / q) ^ n * (((p : ℝ) / q) ^ P - 1)| < 1 := by
    rw [hzero]; exact abs_yFract_sub_lt P n
  rw [abs_mul, abs_mul, abs_of_nonneg hbn,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ ((p : ℝ) / q) ^ P - 1)] at habs
  nlinarith [mul_nonneg (abs_nonneg ξ) hbn]

/-- **The endgame dichotomy.**  A carry word that is `P`-periodic on `[t, N]` forces one of two
explicit inequalities: an upper bound on the range in terms of `|ξ|`, or a bound on `|ξ|` itself
from below-scale.  Everything after this is arithmetic on the two bounds. -/
theorem escape_endgame (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {t P N : ℕ} (hP : 1 ≤ P) (hN : t + P ≤ N)
    (hper : ∀ n, t ≤ n → n + P + 1 ≤ N → carry p q ξ ν (n + P) = carry p q ξ ν n) :
    ((q : ℝ) ^ (N - t - P) ≤ |ξ| * ((p : ℝ) / q) ^ (t + P) + 1)
      ∨ (|ξ| * ((p : ℝ) / q) ^ (N - P) * ((p : ℝ) / q - 1) < 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set m : ℕ := N - t - P with hm
  have hmN : t + m + P = N := by omega
  have hdvd := q_pow_dvd_orbDiff (p := p) (q := q) (ξ := ξ) (ν := ν) hcop hper (m := m) (by omega)
  by_cases hz : orbDiff p q ξ ν P t = 0
  · right
    have hlad := q_pow_mul_orbDiff (p := p) (q := q) (ξ := ξ) (ν := ν) hper m (by omega)
    rw [hz, mul_zero] at hlad
    have hqm : ((q : ℤ)) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
    have hzero : orbDiff p q ξ ν P (t + m) = 0 := by
      rcases mul_eq_zero.mp hlad with h | h
      · exact absurd h hqm
      · exact h
    have hidx : t + m = N - P := by omega
    rw [hidx] at hzero
    exact abs_mul_pow_lt_of_orbDiff_eq_zero hq hqp hP hzero
  · left
    have hpos : (0 : ℤ) < |orbDiff p q ξ ν P t| := abs_pos.mpr hz
    have hle : (q : ℤ) ^ m ≤ |orbDiff p q ξ ν P t| :=
      Int.le_of_dvd hpos ((dvd_abs _ _).mpr hdvd)
    have hleR : (q : ℝ) ^ m ≤ |(orbDiff p q ξ ν P t : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr hle
      push_cast at this
      exact this
    exact le_of_lt (lt_of_le_of_lt hleR (abs_orbDiff_lt hq hqp P t))

/-! ## The budget -/

/-- **The escape budget.**  `A` combinatorial steps — the certificate's own contribution — then
`1 + ⌈log_q (X(p/q)^A + 1)⌉ + ⌈log_{p/q}(q/L)⌉` arithmetic ones. -/
noncomputable def escapeSteps (p q A : ℕ) (X L : ℝ) : ℕ :=
  A + 1 + ⌈Real.logb q (X * ((p : ℝ) / q) ^ A + 1)⌉₊
    + ⌈Real.logb ((p : ℝ) / q) ((q : ℝ) / L)⌉₊

/-- The ceiling logarithm is the least exponent that works. -/
theorem natCeil_logb_le {b x : ℝ} {n : ℕ} (hb : 1 < b) (hx : 0 < x) (h : x ≤ b ^ n) :
    ⌈Real.logb b x⌉₊ ≤ n := by
  refine Nat.ceil_le.mpr ((Real.logb_le_iff_le_rpow hb hx).mpr ?_)
  rwa [Real.rpow_natCast]

/-- `escapeSteps` is at most any pair of exponents that dominates the two bounds.  This is the
form every concrete instance uses: the two hypotheses are `norm_num` facts about numerals. -/
theorem escapeSteps_le {p q A : ℕ} {X Lo : ℝ} {α β : ℕ} (hq : 1 < q) (hqp : q < p) (hLo : 0 < Lo)
    (hX0 : 0 < X) (hα : X * ((p : ℝ) / q) ^ A + 1 ≤ (q : ℝ) ^ α)
    (hβ : (q : ℝ) / Lo ≤ ((p : ℝ) / q) ^ β) :
    escapeSteps p q A X Lo ≤ A + 1 + α + β := by
  have hq0R : (0 : ℝ) < q := by positivity
  have hq1R : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) < (p : ℝ) / q := by rw [lt_div_iff₀ hq0R]; linarith
  have h1 : ⌈Real.logb q (X * ((p : ℝ) / q) ^ A + 1)⌉₊ ≤ α :=
    natCeil_logb_le hq1R (by positivity) hα
  have h2 : ⌈Real.logb ((p : ℝ) / q) ((q : ℝ) / Lo)⌉₊ ≤ β :=
    natCeil_logb_le hb1 (by positivity) hβ
  simp only [escapeSteps]
  omega

/-- **No long period.**  A carry word cannot be periodic from `t` (with `t + P ≤ A`) all the way
to `M`, once `M` clears the budget, for any `ξ` with `L ≤ |ξ| ≤ X`.  This is the whole
quantitative content; the two front ends below only have to produce `t` and `P`. -/
theorem not_period_of_pow_le (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ |ξ|) (hξX : |ξ| ≤ X)
    {A t P M α β : ℕ} (hP : 1 ≤ P) (htP : t + P ≤ A)
    (hα : X * ((p : ℝ) / q) ^ A + 1 ≤ (q : ℝ) ^ α)
    (hβ : (q : ℝ) / Lo ≤ ((p : ℝ) / q) ^ β) (hM : A + 1 + α + β ≤ M)
    (hper : ∀ n, t ≤ n → n + P + 1 ≤ M → carry p q ξ ν (n + P) = carry p q ξ ν n) : False := by
  have hq0 : (0 : ℕ) < q := by omega
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) < (p : ℝ) / q := by rw [lt_div_iff₀ hq0R]; linarith
  have hb0 : (0 : ℝ) < (p : ℝ) / q := by linarith
  rcases escape_endgame (p := p) (q := q) (ξ := ξ) (ν := ν) hq0 hqp hcop hP (by omega) hper with
    hA | hB
  · -- the arithmetic branch: `q^{M−t−P}` overshoots the majorant
    have hmge : α + 1 ≤ M - t - P := by omega
    have h1 : (q : ℝ) ^ (α + 1) ≤ (q : ℝ) ^ (M - t - P) :=
      pow_le_pow_right₀ (le_of_lt hq1R) hmge
    have h2 : |ξ| * ((p : ℝ) / q) ^ (t + P) ≤ X * ((p : ℝ) / q) ^ A := by
      have hmono : ((p : ℝ) / q) ^ (t + P) ≤ ((p : ℝ) / q) ^ A :=
        pow_le_pow_right₀ (le_of_lt hb1) htP
      have hpos : (0 : ℝ) ≤ ((p : ℝ) / q) ^ (t + P) := by positivity
      nlinarith [abs_nonneg ξ, pow_nonneg hb0.le A]
    have h3 : (q : ℝ) ^ α < (q : ℝ) ^ (α + 1) := by
      have hpos : (0 : ℝ) < (q : ℝ) ^ α := by positivity
      rw [pow_succ]
      nlinarith
    linarith
  · -- the scale branch: `|ξ|(p/q)^{M−P}` is already past `q`
    have hmge : β ≤ M - P := by omega
    have h1 : ((p : ℝ) / q) ^ β ≤ ((p : ℝ) / q) ^ (M - P) :=
      pow_le_pow_right₀ (le_of_lt hb1) hmge
    have h2 : (q : ℝ) / Lo ≤ ((p : ℝ) / q) ^ (M - P) := le_trans hβ h1
    have h3 : (q : ℝ) ≤ |ξ| * ((p : ℝ) / q) ^ (M - P) := by
      have hmul : (q : ℝ) / Lo * Lo ≤ ((p : ℝ) / q) ^ (M - P) * |ξ| :=
        mul_le_mul h2 hLξ (le_of_lt hLo) (by positivity)
      have hcancel : (q : ℝ) / Lo * Lo = q := by field_simp
      rw [hcancel, mul_comm] at hmul
      linarith
    have hqp1 : (q : ℝ) + 1 ≤ (p : ℝ) := by
      have : q + 1 ≤ p := hqp
      exact_mod_cast this
    have h4 : (1 : ℝ) / q ≤ (p : ℝ) / q - 1 := by
      have hrw : (p : ℝ) / q - 1 = ((p : ℝ) - q) / q := by field_simp
      rw [hrw, div_le_div_iff_of_pos_right hq0R]
      linarith
    have h5 : (0 : ℝ) < |ξ| * ((p : ℝ) / q) ^ (M - P) := lt_of_lt_of_le hq0R h3
    have h6 : (q : ℝ) * (1 / q) ≤ |ξ| * ((p : ℝ) / q) ^ (M - P) * ((p : ℝ) / q - 1) :=
      mul_le_mul h3 h4 (by positivity) (le_of_lt h5)
    have h7 : (q : ℝ) * (1 / q) = 1 := by field_simp
    linarith

/-- **No long period, in closed form.**  `not_period_of_pow_le` with the two exponents taken to be
the ceiling logarithms, i.e. with `escapeSteps` itself. -/
theorem not_period_of_escapeSteps (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ |ξ|) (hξX : |ξ| ≤ X)
    {A t P M : ℕ} (hP : 1 ≤ P) (htP : t + P ≤ A) (hM : escapeSteps p q A X Lo ≤ M)
    (hper : ∀ n, t ≤ n → n + P + 1 ≤ M → carry p q ξ ν (n + P) = carry p q ξ ν n) : False := by
  have hq0R : (0 : ℝ) < q := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hq1R : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) < (p : ℝ) / q := by rw [lt_div_iff₀ hq0R]; linarith
  have hX0 : 0 < X := lt_of_lt_of_le hLo (le_trans hLξ hξX)
  refine not_period_of_pow_le (ν := ν) hq hqp hcop hLo hLξ hξX hP htP
    (le_pow_natCeil_logb hq1R (by positivity)) (le_pow_natCeil_logb hb1 (by positivity)) ?_ hper
  simpa [escapeSteps] using hM

/-! ## Front end 1: the depth-`K` schema

The rank rotation of `Z32/DepthKSchema.lean` is already a finite-state machine on `K+2` states, so
the repetition step needs nothing but a pigeonhole on `[0, K+2]`. -/

/-- **Repetition, depth-`K` schema.**  Confinement on `[0, N]` forces the carry word to be
`P`-periodic from `t` on, with `t + P ≤ K + 2`. -/
theorem exists_carry_period_of_certifiedK {K : ℕ} {s : ℝ} (hq : 0 < q) (hqp : q < p) {N : ℕ}
    (hy : ∀ n, n ≤ N → yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hcert : SchemaCertifiedK p q s K) :
    ∃ t P, 1 ≤ P ∧ t + P ≤ K + 2 ∧
      ∀ n, t ≤ n → n + P + 1 ≤ N → carry p q ξ (-s) (n + P) = carry p q ξ (-s) n := by
  obtain ⟨w, hw⟩ := hcert
  set e := schemaEps p q s with he
  have he0 : 0 ≤ e := schemaEps_nonneg p q s
  have hp : 0 < p := Nat.lt_of_lt_of_le hq hqp.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set v : ℕ → ℝ := fun n => (p : ℝ) * yFract p q ξ (-s) n with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n =>
    mul_nonneg hp0.le (yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n)
  have hv1 : ∀ n, n ≤ N → v n < 1 := by
    intro n hn
    have := mul_lt_mul_of_pos_left (hy n hn) hp0
    rwa [mul_one_div, div_self hp0.ne'] at this
  set r : ℕ → ℕ := fun n => blockRank w K (v n) with hr
  have hbranch : ∀ m, m + 1 ≤ N → ((p : ℝ) * (v m + e) < q) ∨ (1 ≤ v m + e) := by
    intro m hm
    obtain ⟨hbm, -⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp (hy m (by omega))
      (hy (m + 1) (by omega))
    rcases hbm with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  have hdet : ∀ m n, m + 1 ≤ N → n + 1 ≤ N → r m = r n → r (m + 1) = r (n + 1) := by
    intro m n hm hn hmn
    have hmn' : blockRank w K (v m) = blockRank w K (v n) := hmn
    obtain ⟨hbm, hrm⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp (hy m (by omega))
      (hy (m + 1) (by omega))
    obtain ⟨hbn, hrn⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp (hy n (by omega))
      (hy (n + 1) (by omega))
    have hm' := low_iff_blockRank_le hq hqp hw (hbranch m hm)
    have hn' := low_iff_blockRank_le hq hqp hw (hbranch n hn)
    by_cases hLm : (p : ℝ) * (v m + e) < q
    · have hLn : (p : ℝ) * (v n + e) < q := hn'.mpr (hmn' ▸ hm'.mp hLm)
      have hcm : carry p q ξ (-s) m = schemaBase p q s := by
        rcases hbm with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd hLm (not_low_of_one_le hqp h)
      have hcn : carry p q ξ (-s) n = schemaBase p q s := by
        rcases hbn with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd hLn (not_low_of_one_le hqp h)
      rw [ite_eq_left hcm, sub_zero] at hrm
      rw [ite_eq_left hcn, sub_zero] at hrn
      have hrm' : (q : ℝ) * v (m + 1) = (p : ℝ) * (v m + e) := hrm
      have hrn' : (q : ℝ) * v (n + 1) = (p : ℝ) * (v n + e) := hrn
      show blockRank w K (v (m + 1)) = blockRank w K (v (n + 1))
      rw [blockRank_step_low hq hqp he0 hw (hv0 m) hLm hrm',
        blockRank_step_low hq hqp he0 hw (hv0 n) hLn hrn', hmn']
    · have hLn : ¬ ((p : ℝ) * (v n + e) < q) := fun hc => hLm (hm'.mpr (hmn' ▸ hn'.mp hc))
      have hHm : 1 ≤ v m + e := by rcases hbranch m hm with h | h; exacts [absurd h hLm, h]
      have hHn : 1 ≤ v n + e := by rcases hbranch n hn with h | h; exacts [absurd h hLn, h]
      have hcm : carry p q ξ (-s) m ≠ schemaBase p q s := by
        rcases hbm with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h hLm
        · rw [h]; omega
      have hcn : carry p q ξ (-s) n ≠ schemaBase p q s := by
        rcases hbn with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h hLn
        · rw [h]; omega
      rw [ite_eq_right hcm] at hrm
      rw [ite_eq_right hcn] at hrn
      have hrm' : (q : ℝ) * v (m + 1) = (p : ℝ) * (v m + e - 1) := hrm
      have hrn' : (q : ℝ) * v (n + 1) = (p : ℝ) * (v n + e - 1) := hrn
      have em := blockRank_step_high hq hqp hw (hv1 m (by omega)) hHm hrm'
      have en := blockRank_step_high hq hqp hw (hv1 n (by omega)) hHn hrn'
      show blockRank w K (v (m + 1)) = blockRank w K (v (n + 1))
      omega
  have hcarry : ∀ m n, m + 1 ≤ N → n + 1 ≤ N → r m = r n →
      carry p q ξ (-s) m = carry p q ξ (-s) n := by
    intro m n hm hn hmn
    have hmn' : blockRank w K (v m) = blockRank w K (v n) := hmn
    obtain ⟨hbm, -⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp (hy m (by omega))
      (hy (m + 1) (by omega))
    obtain ⟨hbn, -⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp (hy n (by omega))
      (hy (n + 1) (by omega))
    have hm' := low_iff_blockRank_le hq hqp hw (hbranch m hm)
    have hn' := low_iff_blockRank_le hq hqp hw (hbranch n hn)
    by_cases hLm : (p : ℝ) * (v m + e) < q
    · have hLn : (p : ℝ) * (v n + e) < q := hn'.mpr (hmn' ▸ hm'.mp hLm)
      rcases hbm with ⟨-, h⟩ | ⟨h, -⟩
      · rcases hbn with ⟨-, h'⟩ | ⟨h', -⟩
        · rw [h, h']
        · exact absurd hLn (not_low_of_one_le hqp h')
      · exact absurd hLm (not_low_of_one_le hqp h)
    · have hLn : ¬ ((p : ℝ) * (v n + e) < q) := fun hc => hLm (hm'.mpr (hmn' ▸ hn'.mp hc))
      rcases hbm with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hLm
      · rcases hbn with ⟨h', -⟩ | ⟨-, h'⟩
        · exact absurd h' hLn
        · rw [h, h']
  have hrange : ∀ n, r n ∈ Finset.range (K + 2) := by
    intro n
    rw [Finset.mem_range, Nat.lt_succ_iff, hr]
    simp only [blockRank]
    calc (∑ i ∈ Finset.range (K + 1), if w i ≤ v n then (1 : ℕ) else 0)
        ≤ ∑ _i ∈ Finset.range (K + 1), (1 : ℕ) := Finset.sum_le_sum fun i _ => by split <;> simp
      _ = K + 1 := by simp
  have main : ∀ i j : ℕ, i < j → j ≤ K + 2 → r i = r j →
      ∃ t P, 1 ≤ P ∧ t + P ≤ K + 2 ∧
        ∀ n, t ≤ n → n + P + 1 ≤ N → carry p q ξ (-s) (n + P) = carry p q ξ (-s) n := by
    intro i j hij hjK heqr
    refine ⟨i, j - i, by omega, by omega, ?_⟩
    have hstep : ∀ k, j + k ≤ N → r (i + k) = r (j + k) := by
      intro k
      induction k with
      | zero => intro _; simpa only [Nat.add_zero] using heqr
      | succ k ih =>
        intro hk
        have hd := hdet (i + k) (j + k) (by omega) (by omega) (ih (by omega))
        have e1 : i + (k + 1) = i + k + 1 := by omega
        have e2 : j + (k + 1) = j + k + 1 := by omega
        rw [e1, e2]; exact hd
    intro n hn hnN
    have hri : r n = r (n + (j - i)) := by
      have hs := hstep (n - i) (by omega)
      rw [show i + (n - i) = n by omega, show j + (n - i) = n + (j - i) by omega] at hs
      exact hs
    exact (hcarry n (n + (j - i)) (by omega) (by omega) hri).symm
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (K + 3)) (t := Finset.range (K + 2))
      (by simp) (fun a _ => hrange a)
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rcases lt_or_gt_of_ne hne with h | h
  · exact main i j h (by omega) heq
  · exact main j i h (by omega) heq.symm

/-- **The escape bound for the depth-`K` schema.**  Every `ξ` with `L ≤ ξ ≤ X` leaves the window
`[s, s + 1/p)` within `escapeSteps p q (K+2) X L` steps. -/
theorem exists_escape_le_of_certifiedK {K : ℕ} {s : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hcert : SchemaCertifiedK p q s K)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ escapeSteps p q (K + 2) X Lo, 1 / (p : ℝ) ≤ yFract p q ξ (-s) n := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, P, hP, htP, hper⟩ :=
    exists_carry_period_of_certifiedK (p := p) (q := q) (ξ := ξ) (s := s) (K := K)
      (by omega) hqp (N := escapeSteps p q (K + 2) X Lo) hcon hcert
  have habs : |ξ| = ξ := abs_of_pos (lt_of_lt_of_le hLo hLξ)
  exact not_period_of_escapeSteps (ν := -s) hq hqp hcop hLo (by rw [habs]; exact hLξ)
    (by rw [habs]; exact hξX) hP htP le_rfl hper

/-- The `Z`-set form: an effective `Z32.ZSet_eq_empty_of_certifiedK`. -/
theorem exists_fract_notMem_le_of_certifiedK {K : ℕ} {s : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hcert : SchemaCertifiedK p q s K)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ escapeSteps p q (K + 2) X Lo,
      Int.fract (ξ * ((p : ℝ) / q) ^ n) ∉ Set.Ico s (s + 1 / (p : ℝ)) := by
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0R]; exact_mod_cast hp0
  obtain ⟨n, hn, hge⟩ := exists_escape_le_of_certifiedK hq hqp hcop hcert hLo hLξ hξX
  refine ⟨n, hn, fun hmem => ?_⟩
  rw [Set.mem_Ico] at hmem
  have hsplit : ξ * ((p : ℝ) / q) ^ n - s
      = (Int.fract (ξ * ((p : ℝ) / q) ^ n) - s) + (⌊ξ * ((p : ℝ) / q) ^ n⌋ : ℝ) := by
    have := Int.floor_add_fract (ξ * ((p : ℝ) / q) ^ n)
    linarith
  simp only [yFract, orb, ← sub_eq_add_neg] at hge
  rw [hsplit, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩] at hge
  linarith [hmem.2]

namespace BlockCert

/-! ## Front end 2: block certificates

For a certificate with a **functional** block graph (`c.strata = []`) the block itinerary is
deterministic outright, so the same pigeonhole applies to the `|H|` blocks.  See the scope note in
the module docstring for why the ranked case is excluded. -/

private theorem eq_of_mem_of_length_le_one' {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l with
  | [] => exact absurd ha (by simp)
  | [_] => rw [List.mem_singleton] at ha hb; rw [ha, hb]
  | _ :: _ :: _ => simp at h

/-- A sequence with values in a finite list repeats within `|L|` steps. -/
private theorem exists_lt_eq_le {α : Type*} [DecidableEq α] {L : List α} {B : ℕ → α} {N : ℕ}
    (hN : L.length ≤ N) (hB : ∀ n, n ≤ N → B n ∈ L) :
    ∃ i j, i < j ∧ j ≤ L.length ∧ B i = B j := by
  have hcard : L.toFinset.card < (Finset.range (L.length + 1)).card := by
    rw [Finset.card_range]
    exact Nat.lt_succ_of_le L.toFinset_card_le
  obtain ⟨x, hx, z, hz, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := B) fun a ha => List.mem_toFinset.mpr (hB a (by
        have := Finset.mem_range.mp ha; omega))
  have hx' := Finset.mem_range.mp hx
  have hz' := Finset.mem_range.mp hz
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨x, z, h, by omega, heq⟩
  · exact ⟨z, x, h, by omega, heq.symm⟩

/-- **Repetition, block certificate.**  Confinement to `U` on `[0, N + K]`, `K = |levels|`, forces
the carry word to be `P`-periodic from `t` on, with `t + P ≤ |H|`. -/
theorem Cert.exists_carry_period_le {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    {ξ : ℝ} {N : ℕ} (hLN : c.blocks.length ≤ N)
    (hmem : ∀ n, n ≤ N + c.levels.length →
      memL c.D c.closed c.U (yFract c.p c.q ξ 0 n)) :
    ∃ t P, 1 ≤ P ∧ t + P ≤ c.blocks.length ∧
      ∀ n, t ≤ n → n + P + 1 ≤ N → carry c.p c.q ξ 0 (n + P) = carry c.p c.q ξ 0 n := by
  obtain ⟨-, hq1, hqp, -, -, hfunc⟩ := Cert.parts hc
  have hq0' : 0 < c.q := by omega
  simp only [funcOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfunc
  have hone : ∀ I ∈ c.blocks, ((outEdges c.D c.p c.q c.closed c.blocks I).filter fun e =>
      decide (rank c.strata e.2 = rank c.strata I)).length ≤ 1 := fun I hI => (hfunc I hI).2
  have hrank : ∀ I : Ivl, rank c.strata I = 0 := by intro I; rw [hst]; rfl
  set y : ℕ → ℝ := yFract c.p c.q ξ 0 with hydef
  set w : ℕ → ℤ := carry c.p c.q ξ 0 with hwdef
  have hy0 : ∀ n, 0 ≤ y n := fun n => yFract_nonneg n
  have hy1 : ∀ n, y n < 1 := fun n => yFract_lt_one n
  have hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ) := by
    intro n
    have h := carry_eq (p := c.p) (q := c.q) (ξ := ξ) (ν := 0) hq0' n
    simp only [mul_zero, sub_zero] at h
    rw [hwdef, hydef]
    linarith
  have hchoice : ∀ n, ∃ I : Ivl, n ≤ N → (I ∈ c.blocks ∧ memI c.D c.closed I (y n)) := by
    intro n
    by_cases hn : n ≤ N
    · obtain ⟨I, hI, hIm⟩ :=
        Cert.memL_blocks_of_le hc hy0 hy1 hrec hmem (n := n) (by omega)
      exact ⟨I, fun _ => ⟨hI, hIm⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hn⟩
  choose Bl hBl using hchoice
  have hedge : ∀ n, n + 1 ≤ N →
      (w n, Bl (n + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (Bl n) := fun n hn =>
    Cert.mem_outEdges_of_memI hc hy0 hy1 hrec (hBl (n + 1) (by omega)).1
      (hBl n (by omega)).2 (hBl (n + 1) (by omega)).2
  have hdet : ∀ m n, m + 1 ≤ N → n + 1 ≤ N → Bl m = Bl n →
      w m = w n ∧ Bl (m + 1) = Bl (n + 1) := by
    intro m n hm hn hmn
    have key : ∀ k, k + 1 ≤ N →
        (w k, Bl (k + 1)) ∈ (outEdges c.D c.p c.q c.closed c.blocks (Bl k)).filter
          fun e => decide (rank c.strata e.2 = rank c.strata (Bl k)) := by
      intro k hk
      refine List.mem_filter.mpr ⟨hedge k hk, ?_⟩
      simp only [decide_eq_true_eq, hrank]
    have h1 := key m hm
    have h2 := key n hn
    rw [← hmn] at h2
    have := eq_of_mem_of_length_le_one' (hone (Bl m) (hBl m (by omega)).1) h1 h2
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨i, j, hij, hjL, hBij⟩ :=
    exists_lt_eq_le (L := c.blocks) (B := Bl) hLN fun n hn => (hBl n hn).1
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  have hstep : ∀ k, j + k ≤ N → Bl (i + k) = Bl (j + k) := by
    intro k
    induction k with
    | zero => intro _; simpa only [Nat.add_zero] using hBij
    | succ k ih =>
      intro hk
      have hd := hdet (i + k) (j + k) (by omega) (by omega) (ih (by omega))
      have e1 : i + (k + 1) = i + k + 1 := by omega
      have e2 : j + (k + 1) = j + k + 1 := by omega
      rw [e1, e2]; exact hd.2
  intro n hn hnN
  have hBn : Bl n = Bl (n + (j - i)) := by
    have hs := hstep (n - i) (by omega)
    rw [show i + (n - i) = n by omega, show j + (n - i) = n + (j - i) by omega] at hs
    exact hs
  exact ((hdet n (n + (j - i)) (by omega) (by omega) hBn).1).symm

/-- **`Cert.escape_bound` — target T4.**  A functional block certificate for `U` yields an
explicit escape time: every `ξ` with `L ≤ ξ ≤ X` has some `n ≤ K + escapeSteps p q |H| X L` with
`{ξ(p/q)ⁿ} ∉ U`. -/
theorem Cert.exists_escape_le {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    {ξ X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ c.levels.length + escapeSteps c.p c.q c.blocks.length X Lo,
      ¬ memL c.D c.closed c.U (yFract c.p c.q ξ 0 n) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hq1, hqp, hgcd, -, -⟩ := Cert.parts hc
  have hcop : Nat.Coprime c.p c.q := hgcd
  have hLN : c.blocks.length ≤ escapeSteps c.p c.q c.blocks.length X Lo := by
    simp only [escapeSteps]; omega
  obtain ⟨t, P, hP, htP, hper⟩ :=
    Cert.exists_carry_period_le hc hst (N := escapeSteps c.p c.q c.blocks.length X Lo) hLN
      (fun n hn => hcon n (by omega))
  have habs : |ξ| = ξ := abs_of_pos (lt_of_lt_of_le hLo hLξ)
  exact not_period_of_escapeSteps (ν := 0) hq1 hqp hcop hLo (by rw [habs]; exact hLξ)
    (by rw [habs]; exact hξX) hP htP le_rfl hper

/-- **The readable form.**  Whatever set `S` the certificate covers, an orbit leaves it inside the
budget.  Each atlas entry below supplies its own covering, exactly as its qualitative counterpart
in `Z32/BlockCert.lean` does. -/
theorem exists_fract_notMem_le_of_cover {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    (b : ℝ) (hb : (c.p : ℝ) / c.q = b) {S : Set ℝ}
    (hU : ∀ y ∈ S, memL c.D c.closed c.U y)
    {ξ X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ c.levels.length + escapeSteps c.p c.q c.blocks.length X Lo,
      Int.fract (ξ * b ^ n) ∉ S := by
  obtain ⟨n, hn, hne⟩ := Cert.exists_escape_le hc hst hLo hLξ hξX
  refine ⟨n, hn, fun hmem => hne ?_⟩
  rw [yFract_shift_zero, hb]
  exact hU _ hmem

/-- **The per-entry packaging.**  The budget with the two logarithms replaced by any exponents that
dominate them, and the certificate's two lengths by numerals: every entry below is one
application. -/
theorem exists_fract_notMem_le_of_cover_pow {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    (b : ℝ) (hb : (c.p : ℝ) / c.q = b) {Q : ℕ} (hQ : c.q = Q) {K L : ℕ}
    (hK : c.levels.length = K)
    (hL : c.blocks.length = L) {S : Set ℝ} (hU : ∀ y ∈ S, memL c.D c.closed c.U y)
    {ξ X : ℝ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X) {α β : ℕ}
    (hα : X * b ^ L + 1 ≤ (Q : ℝ) ^ α) (hβ : (Q : ℝ) ≤ b ^ β) :
    ∃ n ≤ K + L + 1 + α + β, Int.fract (ξ * b ^ n) ∉ S := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover hc hst b hb hU (Lo := 1) (X := X) one_pos h1 hX
  refine ⟨n, ?_, hne⟩
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos (le_trans h1 hX)
  have hbound : escapeSteps c.p c.q c.blocks.length X 1 ≤ c.blocks.length + 1 + α + β := by
    refine escapeSteps_le hq1 hqp one_pos hX0 ?_ ?_
    · rw [hb, hL, hQ]; exact hα
    · rw [hb, hQ]; simpa using hβ
  omega

/-! ### The atlas, made effective

Nine of the ten atlas entries of `Z32/BlockCert.lean` have a functional block graph; each becomes
one effective theorem below, in the shape the plan's T4 line asks for: an explicit
`A(c) + α` with `α` any exponent past `log_q(X·(p/q)^{|H|} + 1)`.  The tenth,
`Z32.BlockCert.dubickas_2008_cor_1_2`, is the ranked certificate `certDub08` and is out of scope —
see the module docstring. -/

/-- **Effective `Z32.ZSet_three_two_sixth_3_8`.**  Every `ξ ∈ [1, X]` has some
`n ≤ 14 + α` with `{ξ(3/2)ⁿ} ∉ [1/6, 13/24)`, where `2^α ≥ X(3/2)³ + 1`. -/
theorem escape_sixth_3_8 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 3 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 14 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 6 : ℝ) (13 / 24) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 8) (L := 3) (β := 2)
      (S := Set.Ico (1 / 6 : ℝ) (13 / 24)) certWindow38_ok rfl (3 / 2)
      (by norm_num [certWindow38]) rfl rfl rfl
      (fun y hy => by
        obtain ⟨ha, hb⟩ := hy
        refine ⟨(26244, 85293), by simp [certWindow38], ?_, ?_⟩ <;>
          simp only [certWindow38, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **A numeral instance.**  Every `ξ ∈ [1, 10⁶]` leaves `[1/6, 13/24)` within `36` steps. -/
theorem escape_sixth_3_8_million {ξ : ℝ} (h1 : 1 ≤ ξ) (hX : ξ ≤ 10 ^ 6) :
    ∃ n ≤ 36, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 6 : ℝ) (13 / 24) := by
  obtain ⟨n, hn, hne⟩ := escape_sixth_3_8 (α := 22) h1 hX (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.ZSet_three_two_frontier`**, the longest single certified window: every
`ξ ∈ [1, X]` leaves `[961/3600, 2427/3600)` within `18 + α` steps, `2^α ≥ X(3/2)² + 1`. -/
theorem escape_frontier {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 2 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 18 + α,
      Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (961 / 3600 : ℝ) (2427 / 3600) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 13) (L := 2) (β := 2)
      (S := Set.Ico (961 / 3600 : ℝ) (2427 / 3600)) certFrontier_ok rfl (3 / 2)
      (by norm_num [certFrontier]) rfl rfl rfl
      (fun y hy => by
        obtain ⟨ha, hb⟩ := hy
        refine ⟨(1532144403, 3869421921), by simp [certFrontier], ?_, ?_⟩ <;>
          simp only [certFrontier, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.BlockCert.union_seven_twelfths_empty`**: total length `7/12`, left within
`11 + α` steps. -/
theorem escape_union_712 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 1 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 11 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 6) ∪ Set.Ico (1 / 4 : ℝ) (1 / 3) ∪ Set.Ico (5 / 12 : ℝ) (2 / 3) ∪
        Set.Ico (3 / 4 : ℝ) (5 / 6) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 7) (L := 1) (β := 2)
      (S := Set.Ico (0 : ℝ) (1 / 6) ∪ Set.Ico (1 / 4 : ℝ) (1 / 3) ∪
        Set.Ico (5 / 12 : ℝ) (2 / 3) ∪ Set.Ico (3 / 4 : ℝ) (5 / 6)) certUnion712_ok rfl (3 / 2)
      (by norm_num [certUnion712]) rfl rfl rfl
      (fun y hy => by
        rcases hy with ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
        · refine ⟨(0, 4374), by simp [certUnion712], ?_, ?_⟩ <;>
            simp only [certUnion712, rleR] <;> push_cast <;> linarith
        · refine ⟨(6561, 8748), by simp [certUnion712], ?_, ?_⟩ <;>
            simp only [certUnion712, rleR] <;> push_cast <;> linarith
        · refine ⟨(10935, 17496), by simp [certUnion712], ?_, ?_⟩ <;>
            simp only [certUnion712, rleR] <;> push_cast <;> linarith
        · refine ⟨(19683, 21870), by simp [certUnion712], ?_, ?_⟩ <;>
            simp only [certUnion712, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.BlockCert.union_two_thirds_empty`**: total length `2/3`, left within
`24 + α` steps. -/
theorem escape_union_23 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 12 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 24 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 9) ∪ Set.Ico (1 / 6 : ℝ) (4 / 9) ∪ Set.Ico (1 / 2 : ℝ) (5 / 9) ∪
        Set.Ico (11 / 18 : ℝ) (7 / 9) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 9) (L := 12) (β := 2)
      (S := Set.Ico (0 : ℝ) (1 / 9) ∪ Set.Ico (1 / 6 : ℝ) (4 / 9) ∪
        Set.Ico (1 / 2 : ℝ) (5 / 9) ∪ Set.Ico (11 / 18 : ℝ) (7 / 9) ∪
        Set.Ico (5 / 6 : ℝ) (8 / 9)) certUnion23_ok rfl (3 / 2)
      (by norm_num [certUnion23]) rfl rfl rfl
      (fun y hy => by
        rcases hy with (((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
        · refine ⟨(0, 39366), by simp [certUnion23], ?_, ?_⟩ <;>
            simp only [certUnion23, rleR] <;> push_cast <;> linarith
        · refine ⟨(59049, 157464), by simp [certUnion23], ?_, ?_⟩ <;>
            simp only [certUnion23, rleR] <;> push_cast <;> linarith
        · refine ⟨(177147, 196830), by simp [certUnion23], ?_, ?_⟩ <;>
            simp only [certUnion23, rleR] <;> push_cast <;> linarith
        · refine ⟨(216513, 275562), by simp [certUnion23], ?_, ?_⟩ <;>
            simp only [certUnion23, rleR] <;> push_cast <;> linarith
        · refine ⟨(295245, 314928), by simp [certUnion23], ?_, ?_⟩ <;>
            simp only [certUnion23, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.BlockCert.union_record_empty`**, the union-largeness record `25/36`: left
within `31 + α` steps. -/
theorem escape_union_2536 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 17 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 31 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 12) ∪ Set.Ico (1 / 9 : ℝ) (11 / 36) ∪ Set.Ico (4 / 9 : ℝ) (2 / 3) ∪
        Set.Ico (25 / 36 : ℝ) (3 / 4) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) ∪
        Set.Ico (11 / 12 : ℝ) 1 := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 11) (L := 17) (β := 2)
      (S := Set.Ico (0 : ℝ) (1 / 12) ∪ Set.Ico (1 / 9 : ℝ) (11 / 36) ∪
        Set.Ico (4 / 9 : ℝ) (2 / 3) ∪ Set.Ico (25 / 36 : ℝ) (3 / 4) ∪
        Set.Ico (5 / 6 : ℝ) (8 / 9) ∪ Set.Ico (11 / 12 : ℝ) 1) certUnion2536_ok rfl (3 / 2)
      (by norm_num [certUnion2536]) rfl rfl rfl
      (fun y hy => by
        rcases hy with ((((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
        · refine ⟨(0, 531441), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith
        · refine ⟨(708588, 1948617), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith
        · refine ⟨(2834352, 4251528), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith
        · refine ⟨(4428675, 4782969), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith
        · refine ⟨(5314410, 5668704), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith
        · refine ⟨(5845851, 6377292), by simp [certUnion2536], ?_, ?_⟩ <;>
            simp only [certUnion2536, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.BlockCert.two_cell_fifth_empty`**, the nearest-integer entry: no `ξ ∈ [1, X]`
keeps `‖ξ(3/2)ⁿ‖ < 1/5` beyond step `6 + α`. -/
theorem escape_two_cell_fifth {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 2 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 6 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1 := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 1) (L := 2) (β := 2)
      (S := Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1) certTwoCellFifth_ok rfl (3 / 2)
      (by norm_num [certTwoCellFifth]) rfl rfl rfl
      (fun y hy => by
        rcases hy with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · refine ⟨(0, 3), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
            simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith
        · refine ⟨(12, 15), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
            simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.ZSet_four_three_beyond_line`**, at the base `4/3`: `[1/3, 5/8)` is left
within `12 + α` steps, `3^α ≥ X(4/3)² + 1`. -/
theorem escape_four_three {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((4 : ℝ) / 3) ^ 2 + 1 ≤ 3 ^ α) :
    ∃ n ≤ 12 + α, Int.fract (ξ * ((4 : ℝ) / 3) ^ n) ∉ Set.Ico (1 / 3 : ℝ) (5 / 8) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 3) (K := 5) (L := 2) (β := 4)
      (S := Set.Ico (1 / 3 : ℝ) (5 / 8)) certFourThree_ok rfl (4 / 3)
      (by norm_num [certFourThree]) rfl rfl rfl
      (fun y hy => by
        obtain ⟨ha, hb⟩ := hy
        refine ⟨(8192, 15360), by simp [certFourThree], ?_, ?_⟩ <;>
          simp only [certFourThree, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

/-- **Effective `Z32.ZSet_five_two_fifth`**, in the regime `p > q²`: `[1/5, 2/5)` is left within
`4 + α` steps. -/
theorem escape_five_two_fifth {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((5 : ℝ) / 2) ^ 1 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 4 + α, Int.fract (ξ * ((5 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 5 : ℝ) (2 / 5) := by
  obtain ⟨n, hn, hne⟩ :=
    exists_fract_notMem_le_of_cover_pow (Q := 2) (K := 1) (L := 1) (β := 1)
      (S := Set.Ico (1 / 5 : ℝ) (2 / 5)) certFiveTwo_ok rfl (5 / 2)
      (by norm_num [certFiveTwo]) rfl rfl rfl
      (fun y hy => by
        obtain ⟨ha, hb⟩ := hy
        refine ⟨(5, 10), by simp [certFiveTwo], ?_, ?_⟩ <;>
          simp only [certFiveTwo, rleR] <;> push_cast <;> linarith)
      h1 hX (by push_cast; exact hα) (by norm_num)
  exact ⟨n, by omega, hne⟩

end BlockCert

end Z32
