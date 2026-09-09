/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DubickasWord
import FLP.Basic

/-!
# The depth-one certificate schema, in closed form (plan z32-transform, milestone M1)

Gate G-1 of `plans/plan-z32-transform.html` asked whether the thirty kernel-checked block
certificates of [Ste26] Table 3 — six positions at each of five bases with `p > q²` — collapse
into finitely many symbolic schemas.  They collapse into **one**, and it does not need the
certificate machinery at all: this file is the anti-unified statement, proved directly.

## The schema

Fix coprime `p > q > 1` and a real position `s`, and let the window be `[s, s + 1/p)`.  Put

* `θ = (p − q)s`, `k = ⌊θ⌋`, `ε = {θ}` (`Z32.schemaTheta`, `Z32.schemaBase`, `Z32.schemaEps`).

In the coordinate `uₙ = {ξ(p/q)ⁿ − s}` the dynamics is `q·u_{n+1} = p·uₙ + θ − sₙ`, so confinement
`0 ≤ uₙ < 1/p` squeezes each carry into `(θ − q/p, θ + 1)`, an interval of length `1 + q/p < 2`:
`sₙ ∈ {k, k+1}` (`Z32.carry_eq_base_or_succ` — the alphabet lemma of [Dub09AA] Thm. 3, restated
around `⌊θ⌋` instead of `⌈θ − q/p⌉`).  The two letters are then confined to two blocks

* `sₙ = k` forces `uₙ ∈ B_low = [0, (q − pε)/p²)` (`Z32.base_block`),
* `sₙ = k+1` forces `uₙ ∈ B_high = [(1 − ε)/p, 1/p)` (`Z32.succ_block`),

and each block maps *onto* an end of the window, the two images meeting at the single point `ε/q`.
Everything therefore turns on where that one point sits relative to the hole between the blocks:

* `ε = 0` kills `B_high`, so the carry word is constantly `k`;
* `q ≤ pε` kills `B_low`, so it is constantly `k+1`;
* `q² ≤ p(p+q)ε` and `(p+q)ε ≤ q` make each letter forbid its own repetition, so the word
  alternates.

In all three cases the carry word is eventually periodic, which [DN05] Lemma 2
(`Z32.not_isEventuallyPeriodic_carry`) forbids for `ξ ≠ 0`.  That is the whole proof: no interval
arithmetic, no certificate structure, and nothing for the kernel to evaluate.  (`decide` does
appear below, but only to discharge `Nat.Coprime p q` at numeral bases — never on certificate
data.)

## Main results

* `Z32.SchemaCertified` — the hypothesis on `ε`, the union of the three cases above.
* `Z32.not_confined_of_certified` — the core: a certified window traps no orbit.
* `Z32.exists_fract_ge_of_certified` — the [Dub09AA]-style "infinitely often" form.
* `Z32.ZSet_eq_empty_of_certified` — `Z_{p/q}(s, s + 1/p) = ∅`, for every **real** certified `s`
  and with no assumption on the arithmetic nature of `ξ`.
* `Z32.ZSet_zero_eq_empty` — target T1: the plan's schema `𝒮₀`, at every coprime base.
* `Z32.ZSet_half_eq_empty` — the gate's own test position `s = 1/2`.
* `Z32.ZSet_five_two`, `Z32.ZSet_seven_two`, `Z32.ZSet_nine_two`, `Z32.ZSet_ten_three`,
  `Z32.ZSet_eleven_three` — target T2: [Ste26] Theorem `thm:pastsquare`, six positions at each of
  five bases, now a corollary of one symbolic statement instead of thirty kernel checks.
* `Z32.ZSet_five_two_interval`, `Z32.ZSet_five_two_upper` — target T3 grade 1: emptiness for a
  continuum of real positions at a base with `p > q²`.

## Scope, honestly

For `p < q²` the emptiness itself is [Dub09AA] Theorem 1, already in the corpus as
`Z32.ZSet_eq_empty_of_lt_sq`; what is new there is only which windows are *depth one*.  For
`p > q²` [Dub19] Theorem 1.1 settles every position for **algebraic** `ξ`, so the statements here
are new only for transcendental `ξ` — and every use must say "with no assumption on the arithmetic
nature of `ξ`".  The residual positions, where this file says nothing, are exactly two `ε`-bands of
total measure `2q²/(p(p+q))`; see `plans/note-z32transform-G1.html` §5.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — Theorem 3 (the two-letter alphabet) and §4 (the `p > q²`
  question this file addresses on a subset of positions).
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2, the aperiodicity of the carry word.
* [Dub19] A. Dubickas, *Fractional parts of powers of large rational numbers*, Discrete Math.
  **342** (2019), 1949–1955 — Theorem 1.1, the algebraic-`ξ` half of the `p > q²` regime.
* [Ste26] R. Stephan, *Confinement certificates for powers of rational numbers modulo one*,
  preprint 2026, `doi:10.13140/RG.2.2.36190.19520` —
  `publ/10.13140_RG.2.2.36190.19520/paper-cert32.tex`; Theorem `thm:pastsquare` with its Table 3
  is the thirty-certificate grid this file replaces.
* `plans/note-z32transform-G1.html` — the derivation, its validation against the corpus engines,
  and the map back to the plan's targets.
-/

namespace Z32

open ForMathlib.SubwordComplexity

variable {p q : ℕ} {ξ s : ℝ}

/-! ## The three parameters of the schema -/

/-- `θ = (p − q)s`, the only way the position enters. -/
noncomputable def schemaTheta (p q : ℕ) (s : ℝ) : ℝ := ((p : ℝ) - q) * s

/-- `k = ⌊(p − q)s⌋`, the lower of the two surviving carries. -/
noncomputable def schemaBase (p q : ℕ) (s : ℝ) : ℤ := ⌊schemaTheta p q s⌋

/-- `ε = {(p − q)s}`, the single number the depth-one layer depends on. -/
noncomputable def schemaEps (p q : ℕ) (s : ℝ) : ℝ := Int.fract (schemaTheta p q s)

theorem schema_theta_eq (p q : ℕ) (s : ℝ) :
    (schemaBase p q s : ℝ) + schemaEps p q s = schemaTheta p q s := Int.floor_add_fract _

theorem schemaEps_nonneg (p q : ℕ) (s : ℝ) : 0 ≤ schemaEps p q s := Int.fract_nonneg _

theorem schemaEps_lt_one (p q : ℕ) (s : ℝ) : schemaEps p q s < 1 := Int.fract_lt_one _

/-- `ε` read off an explicit decomposition `(p − q)s = m + e` with `0 ≤ e < 1`.  This is how every
concrete instance below discharges its hypothesis. -/
theorem schemaEps_eq_of_decomp {p q : ℕ} {s e : ℝ} {m : ℤ}
    (hm : ((p : ℝ) - q) * s = m + e) (he0 : 0 ≤ e) (he1 : e < 1) : schemaEps p q s = e := by
  have hfloor : ⌊schemaTheta p q s⌋ = m := by
    rw [Int.floor_eq_iff]
    constructor
    · simp only [schemaTheta, hm]; linarith
    · simp only [schemaTheta, hm]; linarith
  have hval : schemaTheta p q s = (m : ℝ) + e := by simp only [schemaTheta]; exact hm
  simp only [schemaEps, Int.fract]
  rw [hfloor, hval]
  ring

/-- **The certified positions.**  Written with denominators cleared: `ε = 0`, or `q/p ≤ ε`, or
`ε` in the band `[q²/(p(p+q)), q/(p+q)]`. -/
def SchemaCertified (p q : ℕ) (s : ℝ) : Prop :=
  schemaEps p q s = 0 ∨ (q : ℝ) ≤ p * schemaEps p q s ∨
    ((q : ℝ) ^ 2 ≤ (p : ℝ) * ((p : ℝ) + q) * schemaEps p q s ∧
      ((p : ℝ) + q) * schemaEps p q s ≤ q)

/-! ## Confinement forces a two-letter alphabet, and each letter its own block -/

/-- The recursion in the window coordinate: `q·y_{n+1} = p·yₙ + θ − sₙ`.  This is [Dub09AA] (3)
with `ν = −s`, rearranged. -/
theorem q_mul_yFract_succ (hq : 0 < q) (n : ℕ) :
    (q : ℝ) * yFract p q ξ (-s) (n + 1)
      = p * yFract p q ξ (-s) n + schemaTheta p q s - carry p q ξ (-s) n := by
  have h := carry_eq (p := p) (q := q) (ξ := ξ) (ν := -s) hq n
  simp only [schemaTheta]
  linarith [h]

/-- **The alphabet, pointwise.**  Only two consecutive window memberships are used, which is what
the quantitative form of `Z32/EscapeBound.lean` needs. -/
theorem carry_eq_base_or_succ_at (hq : 0 < q) (hpq : q < p) {n : ℕ}
    (hyn : yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hyn1 : yFract p q ξ (-s) (n + 1) < 1 / (p : ℝ)) :
    carry p q ξ (-s) n = schemaBase p q s ∨ carry p q ξ (-s) n = schemaBase p q s + 1 := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqp : (q : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact_mod_cast hpq
  have hrec := q_mul_yFract_succ (p := p) (q := q) (ξ := ξ) (s := s) hq n
  have h0 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n
  have h2 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) (n + 1)
  have hth := schema_theta_eq p q s
  have he0 := schemaEps_nonneg p q s
  have he1 := schemaEps_lt_one p q s
  have hpy : (p : ℝ) * yFract p q ξ (-s) n < 1 := by
    have := mul_lt_mul_of_pos_left hyn hp0
    rwa [mul_one_div, div_self hp0.ne'] at this
  have hqy : (q : ℝ) * yFract p q ξ (-s) (n + 1) < (q : ℝ) / p := by
    have := mul_lt_mul_of_pos_left hyn1 hq0
    rwa [mul_one_div] at this
  have hlow : ((schemaBase p q s : ℝ) - 1) < (carry p q ξ (-s) n : ℝ) := by nlinarith
  have hhigh : (carry p q ξ (-s) n : ℝ) < (schemaBase p q s : ℝ) + 2 := by nlinarith
  have hlow' : schemaBase p q s - 1 < carry p q ξ (-s) n := by exact_mod_cast hlow
  have hhigh' : carry p q ξ (-s) n < schemaBase p q s + 2 := by exact_mod_cast hhigh
  omega

/-- **The alphabet.**  A confined orbit has every carry in `{k, k+1}`, `k = ⌊(p−q)s⌋`.  This is
[Dub09AA] Theorem 3's first half (`Z32.carry_mem_alphabet`) restated around `⌊θ⌋`, which is the
form the block analysis below needs; the half-open window makes both bounds strict. -/
theorem carry_eq_base_or_succ (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (n : ℕ) :
    carry p q ξ (-s) n = schemaBase p q s ∨ carry p q ξ (-s) n = schemaBase p q s + 1 :=
  carry_eq_base_or_succ_at hq hpq (hy n) (hy (n + 1))

/-- Branch `sₙ = k`: `q·y_{n+1} = p·yₙ + ε`. -/
theorem branch_base (hq : 0 < q) {n : ℕ} (h : carry p q ξ (-s) n = schemaBase p q s) :
    (q : ℝ) * yFract p q ξ (-s) (n + 1) = p * yFract p q ξ (-s) n + schemaEps p q s := by
  have hrec := q_mul_yFract_succ (p := p) (q := q) (ξ := ξ) (s := s) hq n
  have hth := schema_theta_eq p q s
  rw [h] at hrec
  linarith

/-- Branch `sₙ = k+1`: `q·y_{n+1} = p·yₙ + ε − 1`. -/
theorem branch_succ (hq : 0 < q) {n : ℕ} (h : carry p q ξ (-s) n = schemaBase p q s + 1) :
    (q : ℝ) * yFract p q ξ (-s) (n + 1) = p * yFract p q ξ (-s) n + schemaEps p q s - 1 := by
  have hrec := q_mul_yFract_succ (p := p) (q := q) (ξ := ξ) (s := s) hq n
  have hth := schema_theta_eq p q s
  rw [h] at hrec
  push_cast at hrec
  linarith

/-- **The low block.**  The letter `k` occurs only on `B_low = [0, (q − pε)/p²)`. -/
theorem base_block (hq : 0 < q) (hp : 0 < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) {n : ℕ}
    (h : carry p q ξ (-s) n = schemaBase p q s) :
    (p : ℝ) * ((p : ℝ) * yFract p q ξ (-s) n) + p * schemaEps p q s < q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := branch_base hq h
  have hqy : (q : ℝ) * yFract p q ξ (-s) (n + 1) < (q : ℝ) / p := by
    have := mul_lt_mul_of_pos_left (hy (n + 1)) hq0
    rwa [mul_one_div] at this
  rw [hb] at hqy
  have h2 := mul_lt_mul_of_pos_left hqy hp0
  rw [show (p : ℝ) * ((q : ℝ) / p) = q by field_simp] at h2
  linarith

/-- **The high block.**  The letter `k+1` occurs only on `B_high = [(1 − ε)/p, 1/p)`. -/
theorem succ_block (hq : 0 < q) {n : ℕ}
    (h : carry p q ξ (-s) n = schemaBase p q s + 1) :
    1 - schemaEps p q s ≤ (p : ℝ) * yFract p q ξ (-s) n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := branch_succ hq h
  have h2 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) (n + 1)
  nlinarith [hb, h2]

/-! ## The three cases -/

/-- Case `ε = 0`: `B_high` is empty, so the carry word is constantly `k`. -/
theorem carry_const_base (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (heps : schemaEps p q s = 0) (n : ℕ) :
    carry p q ξ (-s) n = schemaBase p q s := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rcases carry_eq_base_or_succ hq hpq hy n with h | h
  · exact h
  · exfalso
    have hlo := succ_block hq h
    have hpy : (p : ℝ) * yFract p q ξ (-s) n < 1 := by
      have := mul_lt_mul_of_pos_left (hy n) hp0
      rwa [mul_one_div, div_self hp0.ne'] at this
    rw [heps] at hlo
    linarith

/-- Case `q ≤ pε`: `B_low` is empty, so the carry word is constantly `k+1`. -/
theorem carry_const_succ (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hbig : (q : ℝ) ≤ p * schemaEps p q s) (n : ℕ) :
    carry p q ξ (-s) n = schemaBase p q s + 1 := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rcases carry_eq_base_or_succ hq hpq hy n with h | h
  · exfalso
    have hhi := base_block hq hp hy h
    have h0 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n
    have hnn : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) * yFract p q ξ (-s) n) := by positivity
    linarith
  · exact h

/-- Case band, first half: the letter `k` cannot repeat, because the image of `B_low` starts at
`ε/q`, which the band hypothesis `q² ≤ p(p+q)ε` puts at or past `B_low`'s right end. -/
theorem carry_succ_of_base (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hband : (q : ℝ) ^ 2 ≤ (p : ℝ) * ((p : ℝ) + q) * schemaEps p q s) {n : ℕ}
    (h : carry p q ξ (-s) n = schemaBase p q s) :
    carry p q ξ (-s) (n + 1) = schemaBase p q s + 1 := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rcases carry_eq_base_or_succ hq hpq hy (n + 1) with h' | h'
  · exfalso
    -- `q·y_{n+1} ≥ ε` from `y_n ≥ 0`, against `p²·y_{n+1} + pε < q` from the block bound
    have h1 : schemaEps p q s ≤ (q : ℝ) * yFract p q ξ (-s) (n + 1) := by
      have hb := branch_base hq h
      have h0 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n
      nlinarith
    have h2 := base_block hq hp hy h'
    have e1 := mul_lt_mul_of_pos_left h2 hq0
    have e2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (p : ℝ) * p)
    nlinarith [e1, e2, hband]
  · exact h'

/-- Case band, second half: the letter `k+1` cannot repeat, because the image of `B_high` ends at
`ε/q`, which the band hypothesis `(p+q)ε ≤ q` puts at or before `B_high`'s left end. -/
theorem carry_base_of_succ (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hband : ((p : ℝ) + q) * schemaEps p q s ≤ q) {n : ℕ}
    (h : carry p q ξ (-s) n = schemaBase p q s + 1) :
    carry p q ξ (-s) (n + 1) = schemaBase p q s := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rcases carry_eq_base_or_succ hq hpq hy (n + 1) with h' | h'
  · exact h'
  · exfalso
    -- `q·y_{n+1} < ε` from `p·y_n < 1`, against `1 − ε ≤ p·y_{n+1}` from the block bound
    have h1 : (q : ℝ) * yFract p q ξ (-s) (n + 1) < schemaEps p q s := by
      have hb := branch_succ hq h
      have hpy : (p : ℝ) * yFract p q ξ (-s) n < 1 := by
        have := mul_lt_mul_of_pos_left (hy n) hp0
        rwa [mul_one_div, div_self hp0.ne'] at this
      linarith
    have h2 := succ_block hq h'
    have e1 := mul_le_mul_of_nonneg_left h2 hq0.le
    have e2 := mul_lt_mul_of_pos_left h1 hp0
    nlinarith [e1, e2, hband]

/-! ## Eventual periodicity, and the theorem -/

/-- A certified window forces an eventually periodic carry word: period `1` in the two degenerate
cases, period `2` in the band. -/
theorem isEventuallyPeriodic_carry_of_certified (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (hcert : SchemaCertified p q s) :
    IsEventuallyPeriodic (carry p q ξ (-s)) := by
  rcases hcert with heps | hbig | ⟨hb1, hb2⟩
  · exact ⟨0, 1, one_pos, fun n _ => by
      rw [carry_const_base hq hpq hy heps, carry_const_base hq hpq hy heps]⟩
  · exact ⟨0, 1, one_pos, fun n _ => by
      rw [carry_const_succ hq hpq hy hbig, carry_const_succ hq hpq hy hbig]⟩
  · refine ⟨0, 2, two_pos, fun n _ => ?_⟩
    have hstep : carry p q ξ (-s) (n + 2) = carry p q ξ (-s) n := by
      rcases carry_eq_base_or_succ hq hpq hy n with h | h
      · have h1 := carry_succ_of_base hq hpq hy hb1 h
        have h2 := carry_base_of_succ hq hpq hy hb2 h1
        rw [show n + 1 + 1 = n + 2 from rfl] at h2
        rw [h2, h]
      · have h1 := carry_base_of_succ hq hpq hy hb2 h
        have h2 := carry_succ_of_base hq hpq hy hb1 h1
        rw [show n + 1 + 1 = n + 2 from rfl] at h2
        rw [h2, h]
    exact hstep

/-- **The schema theorem, core form.**  For coprime `p > q > 1`, any `ξ ≠ 0` and any real `s`
whose `ε = {(p−q)s}` is certified, the orbit `{ξ(p/q)ⁿ − s}` leaves `[0, 1/p)`. -/
theorem not_confined_of_certified (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) (hcert : SchemaCertified p q s) :
    ∃ n : ℕ, 1 / (p : ℝ) ≤ yFract p q ξ (-s) n := by
  by_contra hcon
  push Not at hcon
  exact not_isEventuallyPeriodic_carry hq hpq hcop hξ
    (isEventuallyPeriodic_carry_of_certified (by omega) hpq hcon hcert)

/-- **The schema theorem, [Dub09AA] form.**  The fractional parts leave the window infinitely
often. -/
theorem exists_fract_ge_of_certified (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) (hcert : SchemaCertified p q s) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 / (p : ℝ) ≤ Int.fract (ξ * ((p : ℝ) / q) ^ n - s) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq0' : (0 : ℝ) < q := hq0
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hqne : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    positivity
  have hβ0 : (0 : ℝ) < (p : ℝ) / q := div_pos hp0 (by positivity)
  obtain ⟨m, hm⟩ := not_confined_of_certified (ξ := ξ * ((p : ℝ) / q) ^ N) (s := s) hq hpq hcop
    (mul_ne_zero hξ (pow_ne_zero _ hβ0.ne')) hcert
  refine ⟨N + m, Nat.le_add_right _ _, ?_⟩
  have hrw : yFract p q (ξ * ((p : ℝ) / q) ^ N) (-s) m
      = Int.fract (ξ * ((p : ℝ) / q) ^ (N + m) - s) := by
    simp only [yFract, orb, pow_add]
    ring_nf
  rwa [hrw] at hm

/-- **Target T1/T2/T3 in one statement.**  `Z_{p/q}(s, s + 1/p) = ∅` for every real position `s`
whose `ε = {(p−q)s}` is certified — at *every* coprime base `p > q > 1`, and with no assumption on
the arithmetic nature of `ξ`.

This is the anti-unification of the thirty depth-one certificates of [Ste26] Table 3, and it
covers a set of positions of measure `1 − 2q²/(p(p+q))` at each base. -/
theorem ZSet_eq_empty_of_certified (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hcert : SchemaCertified p q s) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := by
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0R]; exact_mod_cast hp0
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hξ0, hmem⟩
  obtain ⟨n, -, hn⟩ := exists_fract_ge_of_certified hq hpq hcop hξ0.ne' hcert 0
  have h := hmem n
  rw [Set.mem_Ico] at h
  have hsplit : ξ * ((p : ℝ) / q) ^ n - s
      = (Int.fract (ξ * ((p : ℝ) / q) ^ n) - s) + (⌊ξ * ((p : ℝ) / q) ^ n⌋ : ℝ) := by
    have := Int.floor_add_fract (ξ * ((p : ℝ) / q) ^ n)
    linarith
  rw [hsplit, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith [h.1], by linarith [h.2]⟩] at hn
  linarith [h.2]

/-- The certification hypothesis in the form every concrete instance uses: an explicit
decomposition `(p − q)s = m + e`. -/
theorem ZSet_eq_empty_of_decomp (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {m : ℤ} {e : ℝ} (hm : ((p : ℝ) - q) * s = m + e) (he0 : 0 ≤ e) (he1 : e < 1)
    (hcert : e = 0 ∨ (q : ℝ) ≤ p * e ∨
      ((q : ℝ) ^ 2 ≤ (p : ℝ) * ((p : ℝ) + q) * e ∧ ((p : ℝ) + q) * e ≤ q)) :
    FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := by
  refine ZSet_eq_empty_of_certified hq hpq hcop ?_
  rw [SchemaCertified, schemaEps_eq_of_decomp hm he0 he1]
  exact hcert

/-! ## T1 — the plan's schema `𝒮₀`, at every base -/

/-- **Target T1.**  `Z_{p/q}(0, 1/p) = ∅` at every coprime base `p > q > 1`: the `ε = 0` case, and
the plan's worked seed `𝒮₀` (`plans/plan-z32-transform.html` §3.2) without its certificate. -/
theorem ZSet_zero_eq_empty (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) :
    FLP.ZSet p q 0 (1 / (p : ℝ)) = ∅ :=
  ZSet_eq_empty_of_decomp hq hpq hcop (m := 0) (e := 0) (by ring) le_rfl one_pos (Or.inl rfl)

/-- More generally every position with `(p − q)s ∈ ℤ` is certified — at `p/q = 3/2` these are the
halves, at `10/3` the sevenths, and so on. -/
theorem ZSet_eq_empty_of_theta_int (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {m : ℤ} (hs : ((p : ℝ) - q) * s = m) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ :=
  ZSet_eq_empty_of_decomp hq hpq hcop (m := m) (e := 0) (by rw [hs]; ring) le_rfl one_pos
    (Or.inl rfl)

/-! ## The gate's test position `s = 1/2` -/

/-- **The `s = 1/2` schema.**  `Z_{p/q}(1/2, 1/2 + 1/p) = ∅` whenever `p − q` is even (then
`ε = 0`) or `2q ≤ p` (then `ε = 1/2 ≥ q/p`).  Gate G-1 asked for exactly this position, and the
depth-one attempt fails precisely in the remaining case `p − q` odd with `p < 2q` — of which
`(4,3)`, the corpus's funnel-depth-26 window, is the smallest instance. -/
theorem ZSet_half_eq_empty (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (h : (p - q) % 2 = 0 ∨ 2 * q ≤ p) :
    FLP.ZSet p q (1 / 2) (1 / (p : ℝ)) = ∅ := by
  have hcast : ((p : ℝ) - q) = ((p - q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpq.le]
  rcases h with heven | hbig
  · obtain ⟨t, ht⟩ : ∃ t, p - q = 2 * t := ⟨(p - q) / 2, by omega⟩
    refine ZSet_eq_empty_of_decomp hq hpq hcop (m := (t : ℤ)) (e := 0) ?_ le_rfl one_pos
      (Or.inl rfl)
    rw [hcast, ht]
    push_cast
    ring
  · obtain ⟨t, ht⟩ : ∃ t, p - q = 2 * t ∨ p - q = 2 * t + 1 := ⟨(p - q) / 2, by omega⟩
    have hq0 : (0 : ℝ) < q := by
      have : 0 < q := by omega
      positivity
    have hbig' : 2 * (q : ℝ) ≤ p := by exact_mod_cast hbig
    rcases ht with ht | ht
    · refine ZSet_eq_empty_of_decomp hq hpq hcop (m := (t : ℤ)) (e := 0) ?_ le_rfl one_pos
        (Or.inl rfl)
      rw [hcast, ht]; push_cast; ring
    · refine ZSet_eq_empty_of_decomp hq hpq hcop (m := (t : ℤ)) (e := 1 / 2) ?_ (by norm_num)
        (by norm_num) (Or.inr (Or.inl ?_))
      · rw [hcast, ht]; push_cast; ring
      · linarith

/-! ## T2 — [Ste26] Theorem `thm:pastsquare`, the thirty grid entries -/

section PastSquare

/-- The six positions of Table 3 at the base `5/2`. -/
theorem ZSet_five_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 5 2 ((j : ℝ) / 6) (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  interval_cases j
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))

/-- The six positions of Table 3 at the base `7/2`.  The entry at `s = 5/6` is one of the three
two-block certificates of the table: `ε = 1/6` sits in the band `[4/63, 2/9]`. -/
theorem ZSet_seven_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 7 2 ((j : ℝ) / 6) (1 / ((7 : ℕ) : ℝ)) = ∅ := by
  interval_cases j
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 5 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 3) (e := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 4) (e := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inr ⟨by norm_num, by norm_num⟩))

/-- The six positions of Table 3 at the base `9/2`.  The entry at `s = 1/6` is a two-block
certificate: `ε = 1/6` sits in the band `[4/99, 2/11]`. -/
theorem ZSet_nine_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 9 2 ((j : ℝ) / 6) (1 / ((9 : ℕ) : ℝ)) = ∅ := by
  interval_cases j
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inr ⟨by norm_num, by norm_num⟩))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 3) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 4) (e := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 5) (e := 5 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))

/-- The six positions of Table 3 at the base `10/3`.  The entry at `s = 1/6` is a two-block
certificate: `ε = 1/6` sits in the band `[9/130, 3/13]`. -/
theorem ZSet_ten_three (j : ℕ) (hj : j < 6) :
    FLP.ZSet 10 3 ((j : ℝ) / 6) (1 / ((10 : ℕ) : ℝ)) = ∅ := by
  interval_cases j
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inr ⟨by norm_num, by norm_num⟩))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 3) (e := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 4) (e := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 5) (e := 5 / 6)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))

/-- The six positions of Table 3 at the base `11/3`.  Here `p − q = 8` is even, so `s = 1/2` lands
in the `ε = 0` case. -/
theorem ZSet_eleven_three (j : ℕ) (hj : j < 6) :
    FLP.ZSet 11 3 ((j : ℝ) / 6) (1 / ((11 : ℕ) : ℝ)) = ∅ := by
  interval_cases j
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 1) (e := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 2) (e := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 4) (e := 0)
      (by norm_num) le_rfl one_pos (Or.inl rfl)
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 5) (e := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  · exact ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 6) (e := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))

/-- The `(5,2)` entry the paper checks by hand ([Ste26] Example `ex:fivetwo`), read off the
schema instead: `ε = {3·(1/5)} = 3/5 ≥ q/p = 2/5`, one carry, one block. -/
example : FLP.ZSet 5 2 (1 / 5) (1 / 5 : ℝ) = ∅ :=
  ZSet_eq_empty_of_decomp (by norm_num) (by norm_num) (by decide) (m := 0) (e := 3 / 5)
    (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))

/-- Table 3 with the numerals spelled out: the `s = 1/6` window at `9/2`, one of the three
two-block entries. -/
example : FLP.ZSet 9 2 (1 / 6) (1 / 9 : ℝ) = ∅ := by
  simpa using ZSet_nine_two 1 (by norm_num)

/-- And the `s = 1/2` window at `11/3`, where `p − q = 8` is even. -/
example : FLP.ZSet 11 3 (1 / 2) (1 / 11 : ℝ) = ∅ := by
  simpa using ZSet_half_eq_empty (p := 11) (q := 3) (by norm_num) (by norm_num) (by decide)
    (Or.inl (by norm_num))

end PastSquare

/-! ## T3 grade 1 — a continuum of real positions at a base with `p > q²` -/

/-- **Target T3, grade 1, upper cell.**  At the base `5/2`, *every real* `s` with
`{3s} ≥ 2/5` has `Z_{5/2}(s, s + 1/5) = ∅`.  Rational or not, algebraic or not: the interval
`[2/5, 1)` in `ε` is one of the two arcs of note G-1 §5, and pulls back to three intervals of
positions per unit. -/
theorem ZSet_five_two_upper {s : ℝ} (h : (2 : ℝ) / 5 ≤ Int.fract (3 * s)) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  refine ZSet_eq_empty_of_certified (by norm_num) (by norm_num) (by decide) ?_
  refine Or.inr (Or.inl ?_)
  have : schemaEps 5 2 s = Int.fract (3 * s) := by
    simp only [schemaEps, schemaTheta]
    norm_num
  rw [this]
  push_cast
  linarith

/-- **Target T3, grade 1, band cell.**  At the base `5/2`, every real `s` with
`{3s} ∈ [4/35, 2/7]` has `Z_{5/2}(s, s + 1/5) = ∅` — the two-block arc, where the carry word is
forced to alternate. -/
theorem ZSet_five_two_band {s : ℝ} (h1 : (4 : ℝ) / 35 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 2 / 7) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  refine ZSet_eq_empty_of_certified (by norm_num) (by norm_num) (by decide) ?_
  have heps : schemaEps 5 2 s = Int.fract (3 * s) := by
    simp only [schemaEps, schemaTheta]
    norm_num
  refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> rw [heps] <;> push_cast <;> linarith

/-- A concrete interval of positions, stated without `Int.fract`: on `[4/105, 2/21]` we have
`3s ∈ [4/35, 2/7] ⊂ [0,1)`, so the band applies verbatim.  This is the shape of statement the plan
calls a T3 grade-1 theorem: emptiness for *all real* `s` in an interval, at a base where
[Dub09AA] §4 is open and [Dub19] needs `ξ` algebraic. -/
theorem ZSet_five_two_interval {s : ℝ} (h1 : (4 : ℝ) / 105 ≤ s) (h2 : s ≤ 2 / 21) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  have hfr : Int.fract (3 * s) = 3 * s := by
    rw [Int.fract_eq_self]
    constructor <;> linarith
  exact ZSet_five_two_band (by rw [hfr]; linarith) (by rw [hfr]; linarith)

end Z32
