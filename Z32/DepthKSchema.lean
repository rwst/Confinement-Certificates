/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.SymbolicCert

/-!
# The depth-`K` certificate schema, in closed form (plan z32-transform, milestone M3)

`Z32/SymbolicCert.lean` (milestone M1) certifies the window `[s, s + 1/p)` whenever
`ε = {(p−q)s}` avoids two open bands.  Experiment X-P decomposed those two bands exactly and found
the decomposition to be the **same at every base** — the sign that the depth-`K` layer, like the
depth-one layer, is one closed-form schema rather than a table.  This file is that schema, and
this is a **formalization of known mathematics**: see "Provenance" below.

## The marked orbit

Rescale the window coordinate to `v = p·u ∈ [0,1)`, `u = {ξ(p/q)ⁿ − s}`.  The two surviving
carries `k`, `k+1` become the two branches

* **low**  `p(v + ε) < q`, and then `q·v' = p(v + ε)`;
* **high** `1 ≤ v + ε`,  and then `q·v' = p(v + ε − 1)`;

between them sits the *hole* `q/p − ε ≤ v < 1 − ε`, from which no step is possible.  Run this map
from the window's own left endpoint `v = 0`:

`w 0 = 0`,  `w (i+1) = ` the branch image of `w i`.

`Z32.Escape p q ε K w` says that orbit is defined for `K` steps and that `w K` lands in the hole
(`Z32.Escape.hit_lo`, `Z32.Escape.hit_hi`, with the right end taken closed, which folds in the
case where the orbit returns to `0`).  That single condition is the whole schema:

* `K = 0` is `q ≤ pε` — the second clause of `Z32.SchemaCertified`;
* `K = 1` is `q² ≤ p(p+q)ε ∧ (p+q)ε ≤ q` — the band, the third clause;
* `K ≥ 2` is what the two residual bands of M1 are made of.

`Z32.certifiedK_of_certified` records that containment.

## Why it certifies

The `K+1` marked points cut `[0,1)` into `K+1` arcs, and the *rank* `r(x) = #{i ≤ K : w i ≤ x}`
(`Z32.blockRank`) names the arc of `x`.  (`ν` is the orbit shift throughout the corpus, so the
rank is written `r` here and in the paper.)  The branch map is increasing on each branch and its two
images tile `[0,1)`, so it acts on the ranks as a **cyclic rotation**: with `N_L` marked points on
the low branch and `N_R` on the high one (`Z32.lowCount`, `Z32.highCount`, `N_L + N_R = K`),

`r(v') = r(v) + N_R + 1` on the low branch, and `r(v') + N_L = r(v)` on the high one

(`Z32.blockRank_step_low`, `Z32.blockRank_step_high`), while `r` also *decides* the branch
(`Z32.low_iff_blockRank_le`).  So along a confined orbit the rank sequence is deterministic with
values in `{1, …, K+1}`; it repeats, and the carry word — a function of the rank — is eventually
periodic, which `Z32.not_isEventuallyPeriodic_carry` ([DN05] Lemma 2) forbids.

No certificate data reaches the kernel: the proof is uniform in `p`, `q`, `s` and `K`.  (The two
`decide`s in the file check `Nat.Coprime 5 2` in the numeral instances at the end, nothing else.)

## The closed-form family

Taking the low branch `K` times (`Z32.lowOrbit`) gives an explicit interval of `ε` for every `K`,

`q^{K+1}(p−q) ≤ p·ε·(p^{K+1} − q^{K+1})`  and  `ε·(p^{K+1} − q^{K+1}) ≤ q^K(p−q)`

(`Z32.LowBand`, `Z32.ZSet_eq_empty_of_lowBand`), of length `q^K(p−q)²/(p(p^{K+1}−q^{K+1}))`.  At
`K = 1` it *is* the M1 band; at `K ≥ 2` it is a new band inside the old residual one — at `(5,2)`,
`K = 2` gives `[8/195, 4/39]` (`Z32.ZSet_five_two_depth_two`), which is 54% of the residual band by
itself, and the family covers about 87% of it.  In the notation of [Bug04] Lemma 3 this family is
`J_{K+1}^1(q/p)`; the other words give the intervals `J_b^a(q/p)` for the remaining rationals
`a/b`, which is why X-P found the cell decomposition to be base-independent — the cells are indexed
by rotation numbers, not by the base.

## Provenance, and what is new here

The mathematics is not new, and the corpus should not claim it is.

* [FLP95] Theorem 3.4 already gives the criterion, and the rotation with it: if `N` is least with
  `f^N(0) ≥ 1/β` then the survivor set is finite, with exactly `N` elements, *cyclically permuted*
  by the map.  `Z32.Escape` is that condition in the corpus's coordinates, and the rank rotation
  proved here is that cyclic permutation.
* [Bug04] Lemma 1 adds the returning case `f^N(0) = 0`, Lemma 2 makes the two together an
  *iff*, and Lemma 3 (from [Bug93], [BC99]) lists the resulting parameter intervals `J_b^a(γ)`
  explicitly, with the attractor a `b`-cycle carrying the dynamics of the rotation by `a/b` — the
  rank rotation proved here.
* [Bug04] Theorem 1 is the resulting statement `Z_{p/q}(s, s+1/p) = ∅` for a set of `s` of **full
  Lebesgue measure**, and [Bug04] Theorem 3 says the exceptional set is null, uncountable and not
  closed.  That is the plan's target T3 grade 2, in print since 2004.

What this file adds is a machine-checked form of the criterion and of the closed-form family,
uniform in `p`, `q`, `s`, `K`, with no data for the kernel to evaluate — and the identification of
`Z32.Escape` with the *depth* of the corpus's block certificates, which is what lets the
certificate engine and this theory talk to each other.

## Scope, honestly

As in `Z32/SymbolicCert.lean`: for `p < q²` the emptiness is [Dub09AA] Theorem 1, and for `p > q²`
and *algebraic* `ξ` it is [Dub19] Theorem 1.1; the statements here hold with no assumption on the
arithmetic nature of `ξ`.  Two sets of `ε` are not covered: `ε = 0` (already
`Z32.ZSet_zero_eq_empty`), and those whose marked orbit never escapes — by [Bug04] Theorem 1 these
are exactly the numbers `((p−q)/p)·Σ ε_{−k}(τ)(q/p)^k` for irrational `τ`, a null uncountable set
whose elements are transcendental by [BKLN21].  Their emptiness is open ([Bug04] §2: "we have not
been able to determine whether `Z_{p/q}(s, s+1/p)` is empty for all values of `s`"), which is the
plan's T3 grade 3.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **70** (1995), 125–147 — Theorems 3.4, 3.5.
  `papers/FlattoLagariasPollington.pdf`.
* [Bug04] Y. Bugeaud, *Linear mod one transformations and the distribution of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **114** (2004), 301–311 — Theorem 1, Theorem 3, Lemmas 1–3.
  `papers/Bugeaud2004.pdf`.
* [Bug93] Y. Bugeaud, *Dynamique de certaines applications contractantes linéaires par morceaux
  sur `[0,1[`*, C. R. Acad. Sci. Paris **317** (1993), 575–578; [BC99] Y. Bugeaud, J.-P. Conze,
  *Calcul de la dynamique de transformations linéaires contractantes mod 1 et arbre de Farey*,
  Acta Arith. **88** (1999), 201–218.
* [BKLN21] Y. Bugeaud, D. H. Kim, M. Laurent, A. Nogueira, *On the Diophantine nature of the
  elements of Cantor sets arising in the dynamics of contracted rotations*, Ann. Sc. Norm. Super.
  Pisa (2021).
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2.
* [Dub19] A. Dubickas, *Fractional parts of powers of large rational numbers*, Discrete Math.
  **342** (2019), 1949–1955.
* `plans/note-z32transform-M3.html` — the derivation, the identification with [Bug04], and the
  validation against the engines of `Z32/xp.py`.
-/

namespace Z32

open ForMathlib.SubwordComplexity

variable {p q K : ℕ} {e s ξ : ℝ} {w : ℕ → ℝ}

/-! ## The marked orbit and its rank function -/

/-- **The escape data.**  The orbit of the window's left endpoint `w 0 = 0` under the two-branch
map, defined for `K` steps and landing in the hole at step `K`. -/
structure Escape (p q : ℕ) (e : ℝ) (K : ℕ) (w : ℕ → ℝ) : Prop where
  /-- the orbit starts at the window's left endpoint -/
  zero : w 0 = 0
  /-- every point of the orbit is in the window -/
  nonneg : ∀ i, i ≤ K → 0 ≤ w i
  /-- every point before the escape is in the window -/
  lt_one : ∀ i, i < K → w i < 1
  /-- each step takes the low or the high branch -/
  step : ∀ i, i < K → ((p : ℝ) * (w i + e) < q ∧ (q : ℝ) * w (i + 1) = p * (w i + e)) ∨
    (1 ≤ w i + e ∧ (q : ℝ) * w (i + 1) = p * (w i + e - 1))
  /-- at step `K` the low branch is unavailable -/
  hit_lo : (q : ℝ) ≤ p * (w K + e)
  /-- at step `K` the high branch is unavailable (its left end taken closed) -/
  hit_hi : w K + e ≤ 1

/-- `ν(x)`: the number of marked points at or below `x`, i.e. the index of the arc holding `x`. -/
noncomputable def blockRank (w : ℕ → ℝ) (K : ℕ) (x : ℝ) : ℕ :=
  ∑ i ∈ Finset.range (K + 1), if w i ≤ x then 1 else 0

/-- `N_L`: how many of `w 0, …, w (K−1)` sit on the low branch. -/
noncomputable def lowCount (p q : ℕ) (e : ℝ) (w : ℕ → ℝ) (K : ℕ) : ℕ :=
  ∑ i ∈ Finset.range K, if (p : ℝ) * (w i + e) < q then 1 else 0

/-- `N_R`: how many of `w 0, …, w (K−1)` sit on the high branch. -/
noncomputable def highCount (p q : ℕ) (e : ℝ) (w : ℕ → ℝ) (K : ℕ) : ℕ :=
  ∑ i ∈ Finset.range K, if (p : ℝ) * (w i + e) < q then 0 else 1

theorem lowCount_add_highCount (p q : ℕ) (e : ℝ) (w : ℕ → ℝ) (K : ℕ) :
    lowCount p q e w K + highCount p q e w K = K := by
  have hpt : ∀ i ∈ Finset.range K,
      ((if (p : ℝ) * (w i + e) < q then (1 : ℕ) else 0)
        + (if (p : ℝ) * (w i + e) < q then 0 else 1)) = 1 := by
    intro i _
    by_cases h : (p : ℝ) * (w i + e) < q <;> simp [h]
  rw [lowCount, highCount, ← Finset.sum_add_distrib, Finset.sum_congr rfl hpt]
  simp

/-- The two branches exclude each other once `q < p`. -/
theorem not_low_of_one_le (hqp : q < p) {x : ℝ} (h : 1 ≤ x + e) :
    ¬ ((p : ℝ) * (x + e) < q) := by
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg q) hqpR
  nlinarith

/-- The low branch, unpacked. -/
theorem Escape.step_low (hw : Escape p q e K w) (hqp : q < p) {i : ℕ} (hi : i < K)
    (hlow : (p : ℝ) * (w i + e) < q) : (q : ℝ) * w (i + 1) = p * (w i + e) := by
  rcases hw.step i hi with ⟨-, h⟩ | ⟨h1, -⟩
  · exact h
  · exact absurd hlow (not_low_of_one_le hqp h1)

/-- The high branch, unpacked. -/
theorem Escape.step_high (hw : Escape p q e K w) {i : ℕ} (hi : i < K)
    (hhigh : ¬ ((p : ℝ) * (w i + e) < q)) :
    1 ≤ w i + e ∧ (q : ℝ) * w (i + 1) = p * (w i + e - 1) := by
  rcases hw.step i hi with ⟨h1, -⟩ | h
  · exact absurd h1 hhigh
  · exact h

/-! ## The rank is a rotation -/

/-- On the low branch the rank goes up by `N_R + 1`. -/
theorem blockRank_step_low (hq : 0 < q) (hqp : q < p) (he : 0 ≤ e) (hw : Escape p q e K w)
    {v v' : ℝ} (hv0 : 0 ≤ v) (hlow : (p : ℝ) * (v + e) < q) (hrec : (q : ℝ) * v' = p * (v + e)) :
    blockRank w K v' = blockRank w K v + highCount p q e w K + 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hv'0 : 0 ≤ v' := by nlinarith
  -- the `i = 0` term, and a reindexing of the rest
  have e1 : blockRank w K v'
      = (∑ i ∈ Finset.range K, if w (i + 1) ≤ v' then (1 : ℕ) else 0) + 1 := by
    rw [blockRank, Finset.sum_range_succ']
    congr 1
    rw [hw.zero, ite_eq_left hv'0]
  have e2 : ∀ i ∈ Finset.range K, (if w (i + 1) ≤ v' then (1 : ℕ) else 0)
      = (if (p : ℝ) * (w i + e) < q then (if w i ≤ v then 1 else 0) else 0)
        + (if (p : ℝ) * (w i + e) < q then 0 else 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hL : (p : ℝ) * (w i + e) < q
    · have hrw := hw.step_low hqp hi hL
      have key : w (i + 1) ≤ v' ↔ w i ≤ v := by
        constructor
        · intro h
          have h2 := mul_le_mul_of_nonneg_left h hq0.le
          rw [hrw, hrec] at h2
          nlinarith
        · intro h
          have h2 : (q : ℝ) * w (i + 1) ≤ (q : ℝ) * v' := by
            rw [hrw, hrec]; nlinarith
          nlinarith
      rw [ite_eq_left hL, ite_eq_left hL, add_zero]
      by_cases h : w i ≤ v
      · rw [ite_eq_left (key.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hc => h (key.mp hc)), ite_eq_right h]
    · obtain ⟨h1, hrw⟩ := hw.step_high hi hL
      have hle : w (i + 1) ≤ v' := by
        have hlt : w i - 1 < v := by linarith [hw.lt_one i hi]
        have h2 : (q : ℝ) * w (i + 1) < (q : ℝ) * v' := by rw [hrw, hrec]; nlinarith
        nlinarith
      rw [ite_eq_right hL, ite_eq_right hL, ite_eq_left hle, zero_add]
  have e3 : blockRank w K v
      = ∑ i ∈ Finset.range K,
          (if (p : ℝ) * (w i + e) < q then (if w i ≤ v then (1 : ℕ) else 0) else 0) := by
    rw [blockRank, Finset.sum_range_succ]
    have hK : ¬ (w K ≤ v) := by nlinarith [hw.hit_lo]
    rw [ite_eq_right hK, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hL : (p : ℝ) * (w i + e) < q
    · rw [ite_eq_left hL]
    · rw [ite_eq_right hL, ite_eq_right (show ¬ (w i ≤ v) by nlinarith)]
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib, ← e3, highCount]

/-- On the high branch the rank goes down by `N_L`. -/
theorem blockRank_step_high (hq : 0 < q) (hqp : q < p) (hw : Escape p q e K w)
    {v v' : ℝ} (hv1 : v < 1) (hhigh : 1 ≤ v + e)
    (hrec : (q : ℝ) * v' = p * (v + e - 1)) :
    blockRank w K v' + lowCount p q e w K = blockRank w K v := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hv'0 : 0 ≤ v' := by nlinarith
  have e1 : blockRank w K v'
      = (∑ i ∈ Finset.range K, if w (i + 1) ≤ v' then (1 : ℕ) else 0) + 1 := by
    rw [blockRank, Finset.sum_range_succ']
    congr 1
    rw [hw.zero, ite_eq_left hv'0]
  have e2 : ∀ i ∈ Finset.range K, (if w (i + 1) ≤ v' then (1 : ℕ) else 0)
      = (if (p : ℝ) * (w i + e) < q then 0 else (if w i ≤ v then 1 else 0)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hL : (p : ℝ) * (w i + e) < q
    · have hrw := hw.step_low hqp hi hL
      have hnot : ¬ (w (i + 1) ≤ v') := by
        have h2 : (q : ℝ) * v' < (q : ℝ) * w (i + 1) := by
          rw [hrw, hrec]; nlinarith [hw.nonneg i hi.le]
        nlinarith
      rw [ite_eq_right hnot, ite_eq_left hL]
    · obtain ⟨h1, hrw⟩ := hw.step_high hi hL
      have key : w (i + 1) ≤ v' ↔ w i ≤ v := by
        constructor
        · intro h
          have h2 := mul_le_mul_of_nonneg_left h hq0.le
          rw [hrw, hrec] at h2
          nlinarith
        · intro h
          have h2 : (q : ℝ) * w (i + 1) ≤ (q : ℝ) * v' := by
            rw [hrw, hrec]; nlinarith
          nlinarith
      rw [ite_eq_right hL]
      by_cases h : w i ≤ v
      · rw [ite_eq_left (key.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hc => h (key.mp hc)), ite_eq_right h]
  have e3 : blockRank w K v
      = lowCount p q e w K
        + ((∑ i ∈ Finset.range K,
            (if (p : ℝ) * (w i + e) < q then (0 : ℕ) else (if w i ≤ v then 1 else 0))) + 1) := by
    have hK : w K ≤ v := by linarith [hw.hit_hi]
    have hpt : ∀ i ∈ Finset.range K, (if w i ≤ v then (1 : ℕ) else 0)
        = (if (p : ℝ) * (w i + e) < q then (1 : ℕ) else 0)
          + (if (p : ℝ) * (w i + e) < q then (0 : ℕ) else (if w i ≤ v then 1 else 0)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hL : (p : ℝ) * (w i + e) < q
      · rw [ite_eq_left hL, ite_eq_left hL, ite_eq_left (show w i ≤ v by nlinarith), add_zero]
      · rw [ite_eq_right hL, ite_eq_right hL, zero_add]
    rw [blockRank, Finset.sum_range_succ, ite_eq_left hK, Finset.sum_congr rfl hpt,
      Finset.sum_add_distrib, lowCount]
    ring
  rw [e1, Finset.sum_congr rfl e2, e3]
  omega

/-! ## The rank decides the branch -/

/-- A low point has rank at most `N_L`. -/
theorem blockRank_le_of_low (hq : 0 < q) (hqp : q < p) (hw : Escape p q e K w) {v : ℝ}
    (hlow : (p : ℝ) * (v + e) < q) : blockRank w K v ≤ lowCount p q e w K := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  rw [blockRank, Finset.sum_range_succ, ite_eq_right (show ¬ (w K ≤ v) by nlinarith [hw.hit_lo]),
    add_zero, lowCount]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases hL : (p : ℝ) * (w i + e) < q
  · rw [ite_eq_left hL]
    split <;> simp
  · rw [ite_eq_right hL, ite_eq_right (show ¬ (w i ≤ v) by nlinarith)]

/-- A high point has rank greater than `N_L`. -/
theorem lowCount_lt_blockRank (hq : 0 < q) (hqp : q < p) (hw : Escape p q e K w) {v : ℝ}
    (hhigh : 1 ≤ v + e) : lowCount p q e w K < blockRank w K v := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hK : w K ≤ v := by linarith [hw.hit_hi]
  rw [blockRank, Finset.sum_range_succ, ite_eq_left hK, lowCount]
  have : ∑ i ∈ Finset.range K, (if (p : ℝ) * (w i + e) < q then (1 : ℕ) else 0)
      ≤ ∑ i ∈ Finset.range K, (if w i ≤ v then (1 : ℕ) else 0) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hL : (p : ℝ) * (w i + e) < q
    · rw [ite_eq_left hL, ite_eq_left (show w i ≤ v by nlinarith)]
    · rw [ite_eq_right hL]; split <;> simp
  omega

/-- **The rank decides the branch.**  Two points of the same rank take the same branch, so the
rank sequence of a confined orbit is deterministic. -/
theorem low_iff_blockRank_le (hq : 0 < q) (hqp : q < p) (hw : Escape p q e K w) {v : ℝ}
    (hstep : ((p : ℝ) * (v + e) < q) ∨ (1 ≤ v + e)) :
    (p : ℝ) * (v + e) < q ↔ blockRank w K v ≤ lowCount p q e w K := by
  refine ⟨blockRank_le_of_low hq hqp hw, fun h => ?_⟩
  rcases hstep with hL | hH
  · exact hL
  · exact absurd h (Nat.not_le.mpr (lowCount_lt_blockRank hq hqp hw hH))

/-! ## Soundness: the schema forbids confinement -/

/-- **The certified positions at depth `K`.** -/
def SchemaCertifiedK (p q : ℕ) (s : ℝ) (K : ℕ) : Prop :=
  ∃ w : ℕ → ℝ, Escape p q (schemaEps p q s) K w

/-- The rescaled orbit `v = p·u` of a confined point takes one of the two branches at every
step, and the branch is the carry.  Pointwise version: only the two window memberships at `n` and
`n+1` are used, which is what `Z32/EscapeBound.lean` needs on a finite range. -/
theorem step_of_confined_at (hq : 0 < q) (hqp : q < p) {n : ℕ}
    (hyn : yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hyn1 : yFract p q ξ (-s) (n + 1) < 1 / (p : ℝ)) :
    (((p : ℝ) * ((p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s) < q ∧
        carry p q ξ (-s) n = schemaBase p q s) ∨
      (1 ≤ (p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s ∧
        carry p q ξ (-s) n = schemaBase p q s + 1)) ∧
    (q : ℝ) * ((p : ℝ) * yFract p q ξ (-s) (n + 1))
      = p * ((p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s
        - (if carry p q ξ (-s) n = schemaBase p q s then 0 else 1)) := by
  have hp : 0 < p := Nat.lt_of_lt_of_le hq hqp.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h0 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n
  have h1 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) (n + 1)
  have hlt1 : (p : ℝ) * yFract p q ξ (-s) (n + 1) < 1 := by
    have h := mul_lt_mul_of_pos_left hyn1 hp0
    rwa [mul_one_div, div_self hp0.ne'] at h
  rcases carry_eq_base_or_succ_at hq hqp hyn hyn1 with hc | hc
  · have hb := branch_base (p := p) (q := q) (ξ := ξ) (s := s) hq hc
    constructor
    · left
      refine ⟨?_, hc⟩
      nlinarith
    · rw [ite_eq_left hc]; nlinarith
  · have hb := branch_succ (p := p) (q := q) (ξ := ξ) (s := s) hq hc
    have hne : ¬ (carry p q ξ (-s) n = schemaBase p q s) := by rw [hc]; omega
    constructor
    · right
      refine ⟨?_, hc⟩
      nlinarith
    · rw [ite_eq_right hne]; nlinarith

/-- The rescaled orbit `v = p·u` of a confined point takes one of the two branches at every
step, and the branch is the carry. -/
theorem step_of_confined (hq : 0 < q) (hqp : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (n : ℕ) :
    (((p : ℝ) * ((p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s) < q ∧
        carry p q ξ (-s) n = schemaBase p q s) ∨
      (1 ≤ (p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s ∧
        carry p q ξ (-s) n = schemaBase p q s + 1)) ∧
    (q : ℝ) * ((p : ℝ) * yFract p q ξ (-s) (n + 1))
      = p * ((p : ℝ) * yFract p q ξ (-s) n + schemaEps p q s
        - (if carry p q ξ (-s) n = schemaBase p q s then 0 else 1)) :=
  step_of_confined_at hq hqp (hy n) (hy (n + 1))

/-- **The depth-`K` schema forces an eventually periodic carry word.** -/
theorem isEventuallyPeriodic_carry_of_certifiedK (hq : 0 < q) (hqp : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (hcert : SchemaCertifiedK p q s K) :
    IsEventuallyPeriodic (carry p q ξ (-s)) := by
  obtain ⟨w, hw⟩ := hcert
  set e := schemaEps p q s with he
  have he0 : 0 ≤ e := schemaEps_nonneg p q s
  have hp : 0 < p := Nat.lt_of_lt_of_le hq hqp.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set v : ℕ → ℝ := fun n => (p : ℝ) * yFract p q ξ (-s) n with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n =>
    mul_nonneg hp0.le (yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n)
  have hv1 : ∀ n, v n < 1 := by
    intro n
    have := mul_lt_mul_of_pos_left (hy n) hp0
    rwa [mul_one_div, div_self hp0.ne'] at this
  -- the rank sequence is deterministic
  set r : ℕ → ℕ := fun n => blockRank w K (v n) with hr
  have hdet : ∀ m n, r m = r n → r (m + 1) = r (n + 1) := by
    intro m n hmn
    have hmn' : blockRank w K (v m) = blockRank w K (v n) := hmn
    obtain ⟨hbm, hrm⟩ := step_of_confined (ξ := ξ) (s := s) hq hqp hy m
    obtain ⟨hbn, hrn⟩ := step_of_confined (ξ := ξ) (s := s) hq hqp hy n
    have hstepm : ((p : ℝ) * (v m + e) < q) ∨ (1 ≤ v m + e) := by
      rcases hbm with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
    have hstepn : ((p : ℝ) * (v n + e) < q) ∨ (1 ≤ v n + e) := by
      rcases hbn with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
    have hm := low_iff_blockRank_le hq hqp hw hstepm
    have hn := low_iff_blockRank_le hq hqp hw hstepn
    by_cases hLm : (p : ℝ) * (v m + e) < q
    · have hLn : (p : ℝ) * (v n + e) < q := hn.mpr (hmn' ▸ hm.mp hLm)
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
    · have hLn : ¬ ((p : ℝ) * (v n + e) < q) := fun hc => hLm (hm.mpr (hmn' ▸ hn.mp hc))
      have hHm : 1 ≤ v m + e := by rcases hstepm with h | h; exacts [absurd h hLm, h]
      have hHn : 1 ≤ v n + e := by rcases hstepn with h | h; exacts [absurd h hLn, h]
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
      have em := blockRank_step_high hq hqp hw (hv1 m) hHm hrm'
      have en := blockRank_step_high hq hqp hw (hv1 n) hHn hrn'
      show blockRank w K (v (m + 1)) = blockRank w K (v (n + 1))
      omega
  -- the carry is a function of the rank
  have hcarry : ∀ m n, r m = r n → carry p q ξ (-s) m = carry p q ξ (-s) n := by
    intro m n hmn
    have hmn' : blockRank w K (v m) = blockRank w K (v n) := hmn
    obtain ⟨hbm, -⟩ := step_of_confined (ξ := ξ) (s := s) hq hqp hy m
    obtain ⟨hbn, -⟩ := step_of_confined (ξ := ξ) (s := s) hq hqp hy n
    have hstepm : ((p : ℝ) * (v m + e) < q) ∨ (1 ≤ v m + e) := by
      rcases hbm with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
    have hstepn : ((p : ℝ) * (v n + e) < q) ∨ (1 ≤ v n + e) := by
      rcases hbn with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
    have hm := low_iff_blockRank_le hq hqp hw hstepm
    have hn := low_iff_blockRank_le hq hqp hw hstepn
    by_cases hLm : (p : ℝ) * (v m + e) < q
    · have hLn : (p : ℝ) * (v n + e) < q := hn.mpr (hmn' ▸ hm.mp hLm)
      rcases hbm with ⟨-, h⟩ | ⟨h, -⟩
      · rcases hbn with ⟨-, h'⟩ | ⟨h', -⟩
        · rw [h, h']
        · exact absurd hLn (not_low_of_one_le hqp h')
      · exact absurd hLm (not_low_of_one_le hqp h)
    · have hLn : ¬ ((p : ℝ) * (v n + e) < q) := fun hc => hLm (hm.mpr (hmn' ▸ hn.mp hc))
      rcases hbm with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hLm
      · rcases hbn with ⟨h', -⟩ | ⟨-, h'⟩
        · exact absurd h' hLn
        · rw [h, h']
  -- pigeonhole on the finitely many ranks
  have hrange : ∀ n, r n ∈ Finset.range (K + 2) := by
    intro n
    rw [Finset.mem_range, Nat.lt_succ_iff, hr]
    simp only [blockRank]
    calc (∑ i ∈ Finset.range (K + 1), if w i ≤ v n then (1 : ℕ) else 0)
        ≤ ∑ _i ∈ Finset.range (K + 1), (1 : ℕ) := Finset.sum_le_sum fun i _ => by split <;> simp
      _ = K + 1 := by simp
  obtain ⟨i, -, j, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (K + 3)) (t := Finset.range (K + 2))
      (by simp) (fun a _ => hrange a)
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact ⟨i, j - i, by omega, fun k hk => by
      have hstep : ∀ m, r (i + m) = r (j + m) := by
        intro m
        induction m with
        | zero => simpa only [Nat.add_zero] using heq
        | succ n ih => exact hdet _ _ ih
      have := hcarry (k + (j - i)) k
      refine this ?_
      have hk' : k = i + (k - i) := by omega
      rw [hk']
      have : i + (k - i) + (j - i) = j + (k - i) := by omega
      rw [this]
      exact (hstep (k - i)).symm⟩
  · exact ⟨j, i - j, by omega, fun k hk => by
      have hstep : ∀ m, r (j + m) = r (i + m) := by
        intro m
        induction m with
        | zero => simpa only [Nat.add_zero] using heq.symm
        | succ n ih => exact hdet _ _ ih
      have := hcarry (k + (i - j)) k
      refine this ?_
      have hk' : k = j + (k - j) := by omega
      rw [hk']
      have : j + (k - j) + (i - j) = i + (k - j) := by omega
      rw [this]
      exact (hstep (k - j)).symm⟩

/-- **The depth-`K` schema theorem, core form.** -/
theorem not_confined_of_certifiedK (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) (hcert : SchemaCertifiedK p q s K) :
    ∃ n : ℕ, 1 / (p : ℝ) ≤ yFract p q ξ (-s) n := by
  by_contra hcon
  push Not at hcon
  exact not_isEventuallyPeriodic_carry hq hqp hcop hξ
    (isEventuallyPeriodic_carry_of_certifiedK (by omega) hqp hcon hcert)

/-- **The depth-`K` schema theorem.**  `Z_{p/q}(s, s + 1/p) = ∅` for every real position `s`
whose marked orbit escapes, at every coprime base `p > q > 1`, with no assumption on the
arithmetic nature of `ξ`. -/
theorem ZSet_eq_empty_of_certifiedK (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hcert : SchemaCertifiedK p q s K) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := by
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0R]; exact_mod_cast hp0
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hξ0, hmem⟩
  obtain ⟨n, hn⟩ := not_confined_of_certifiedK hq hqp hcop hξ0.ne' hcert
  have h := hmem n
  rw [Set.mem_Ico] at h
  have hsplit : ξ * ((p : ℝ) / q) ^ n - s
      = (Int.fract (ξ * ((p : ℝ) / q) ^ n) - s) + (⌊ξ * ((p : ℝ) / q) ^ n⌋ : ℝ) := by
    have := Int.floor_add_fract (ξ * ((p : ℝ) / q) ^ n)
    linarith
  simp only [yFract, orb, ← sub_eq_add_neg] at hn
  rw [hsplit, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith [h.1], by linarith [h.2]⟩] at hn
  linarith [h.2]

/-! ## The closed-form family: taking the low branch `K` times -/

/-- The marked orbit of the all-low word: `w 0 = 0`, `w (i+1) = p(w i + ε)/q`. -/
noncomputable def lowOrbit (p q : ℕ) (e : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => (p : ℝ) * (lowOrbit p q e i + e) / q

/-- The closed form of the all-low orbit: `w i + ε = ε(p^{i+1} − q^{i+1})/(q^i(p − q))`. -/
theorem lowOrbit_add_eq (hq : 0 < q) (hqp : q < p) (e : ℝ) (i : ℕ) :
    lowOrbit p q e i + e
      = e * ((p : ℝ) ^ (i + 1) - (q : ℝ) ^ (i + 1)) / ((q : ℝ) ^ i * ((p : ℝ) - q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hd0 : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  induction i with
  | zero => simp only [lowOrbit, pow_zero, pow_one, zero_add, one_mul]; field_simp
  | succ i ih =>
    have hstep : lowOrbit p q e (i + 1) + e = (p : ℝ) * (lowOrbit p q e i + e) / q + e := rfl
    rw [hstep, ih]
    have hqi : ((q : ℝ) ^ i) ≠ 0 := by positivity
    field_simp
    ring

/-- **The closed-form band at depth `K`**: the `ε` whose all-low marked orbit escapes at step `K`.
At `K = 0` this is `q ≤ pε` and at `K = 1` the band `q² ≤ p(p+q)ε ≤ q(p+q)` — the second and third
clauses of `Z32.SchemaCertified`.  For `K ≥ 2` it is new. -/
def LowBand (p q : ℕ) (e : ℝ) (K : ℕ) : Prop :=
  (q : ℝ) ^ (K + 1) * ((p : ℝ) - q) ≤ p * e * ((p : ℝ) ^ (K + 1) - (q : ℝ) ^ (K + 1)) ∧
    e * ((p : ℝ) ^ (K + 1) - (q : ℝ) ^ (K + 1)) ≤ (q : ℝ) ^ K * ((p : ℝ) - q)

/-- The right-hand end of the band at depth `K` keeps every earlier step on the low branch. -/
theorem lowBand_step (hq : 0 < q) (hqp : q < p) (i d : ℕ)
    (h : e * ((p : ℝ) ^ (i + 1 + d + 1) - (q : ℝ) ^ (i + 1 + d + 1))
      ≤ (q : ℝ) ^ (i + 1 + d) * ((p : ℝ) - q)) :
    (p : ℝ) * e * ((p : ℝ) ^ (i + 1) - (q : ℝ) ^ (i + 1)) < (q : ℝ) ^ (i + 1) * ((p : ℝ) - q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  set A : ℝ := (p : ℝ) ^ (i + 1) with hA
  set B : ℝ := (q : ℝ) ^ (i + 1) with hB
  set C : ℝ := (p : ℝ) ^ d with hC
  set D : ℝ := (q : ℝ) ^ d with hD
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  have hC0 : 0 < C := by positivity
  have hD0 : 0 < D := by positivity
  have hAB : B ≤ A := by
    rw [hA, hB]; exact pow_le_pow_left₀ hq0.le hqpR.le _
  have hCD : D ≤ C := by
    rw [hC, hD]; exact pow_le_pow_left₀ hq0.le hqpR.le d
  have hrw1 : (p : ℝ) ^ (i + 1 + d + 1) = A * C * p := by
    rw [hA, hC, ← pow_add, ← pow_succ]
  have hrw2 : (q : ℝ) ^ (i + 1 + d + 1) = B * D * q := by
    rw [hB, hD, ← pow_add, ← pow_succ]
  have hrw3 : (q : ℝ) ^ (i + 1 + d) = B * D := by rw [hB, hD, ← pow_add]
  rw [hrw1, hrw2, hrw3] at h
  have hBDAC : B * D ≤ A * C := mul_le_mul hAB hCD hD0.le hA0.le
  have hpos : 0 < A * C * p - B * D * q := by
    nlinarith [mul_le_mul_of_nonneg_right hBDAC hp0.le, mul_pos hB0 hD0]
  -- `B·(ACp − BDq) − p·BD·(A−B) = ABp(C−D) + B²D(p−q) > 0`
  have hexp : B * ((p : ℝ) - q) * (A * C * p - B * D * q)
        - (p : ℝ) * (A - B) * (B * D * ((p : ℝ) - q))
      = ((p : ℝ) - q) * (A * B * p * (C - D) + B * B * D * ((p : ℝ) - q)) := by ring
  have hdq : (0 : ℝ) < (p : ℝ) - q := by linarith
  have hinner : 0 < A * B * p * (C - D) + B * B * D * ((p : ℝ) - q) := by
    have h1 : 0 ≤ A * B * p * (C - D) := mul_nonneg (by positivity) (by linarith)
    nlinarith [mul_pos (mul_pos (mul_pos hB0 hB0) hD0) hdq]
  have hgap : (p : ℝ) * (A - B) * (B * D * ((p : ℝ) - q))
      < B * ((p : ℝ) - q) * (A * C * p - B * D * q) := by
    have h2 := mul_pos hdq hinner
    linarith [hexp]
  have hmul : (p : ℝ) * e * (A - B) * (A * C * p - B * D * q)
      ≤ (p : ℝ) * (A - B) * (B * D * ((p : ℝ) - q)) := by
    have hc : (0 : ℝ) ≤ (p : ℝ) * (A - B) := mul_nonneg hp0.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h hc]
  refine lt_of_mul_lt_mul_right (a := A * C * p - B * D * q) ?_ hpos.le
  nlinarith

/-- **The closed-form schema.**  Every `ε` in the depth-`K` band escapes. -/
theorem escape_lowOrbit (hq : 0 < q) (hqp : q < p) (he : 0 ≤ e) (hb : LowBand p q e K) :
    Escape p q e K (lowOrbit p q e) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hd0 : (0 : ℝ) < (p : ℝ) - q := by linarith
  have hnn : ∀ i, 0 ≤ lowOrbit p q e i := by
    intro i
    induction i with
    | zero => exact le_of_eq rfl
    | succ i ih =>
      have : lowOrbit p q e (i + 1) = (p : ℝ) * (lowOrbit p q e i + e) / q := rfl
      rw [this]
      positivity
  have hlow : ∀ i, i < K → (p : ℝ) * (lowOrbit p q e i + e) < q := by
    intro i hi
    obtain ⟨d, rfl⟩ : ∃ d, K = i + 1 + d := ⟨K - (i + 1), by omega⟩
    have hstep := lowBand_step (p := p) (q := q) (e := e) hq hqp i d hb.2
    rw [lowOrbit_add_eq hq hqp e i, ← mul_div_assoc,
      div_lt_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ i * ((p : ℝ) - q))]
    have hg1 : (p : ℝ) * (e * ((p : ℝ) ^ (i + 1) - (q : ℝ) ^ (i + 1)))
        = (p : ℝ) * e * ((p : ℝ) ^ (i + 1) - (q : ℝ) ^ (i + 1)) := by ring
    have hg2 : (q : ℝ) * ((q : ℝ) ^ i * ((p : ℝ) - q))
        = (q : ℝ) ^ (i + 1) * ((p : ℝ) - q) := by rw [pow_succ]; ring
    rw [hg1, hg2]
    exact hstep
  refine ⟨rfl, fun i _ => hnn i, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := hlow i hi
    nlinarith [hnn i, he, hp0]
  · intro i hi
    refine Or.inl ⟨hlow i hi, ?_⟩
    have : lowOrbit p q e (i + 1) = (p : ℝ) * (lowOrbit p q e i + e) / q := rfl
    rw [this]
    field_simp
  · rw [lowOrbit_add_eq hq hqp e K, ← mul_div_assoc,
      le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ K * ((p : ℝ) - q))]
    have hg2 : (q : ℝ) * ((q : ℝ) ^ K * ((p : ℝ) - q))
        = (q : ℝ) ^ (K + 1) * ((p : ℝ) - q) := by rw [pow_succ]; ring
    nlinarith [hb.1, hg2]
  · rw [lowOrbit_add_eq hq hqp e K, div_le_one (by positivity)]
    exact hb.2

/-- **The depth-`K` schema, closed form.**  `Z_{p/q}(s, s + 1/p) = ∅` whenever `ε = {(p−q)s}`
lies in the depth-`K` band, at every coprime base and for every `K`. -/
theorem ZSet_eq_empty_of_lowBand (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hb : LowBand p q (schemaEps p q s) K) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ :=
  ZSet_eq_empty_of_certifiedK (K := K) hq hqp hcop
    ⟨lowOrbit p q (schemaEps p q s),
      escape_lowOrbit (by omega) hqp (schemaEps_nonneg p q s) hb⟩

/-- The depth-one schema of `Z32/SymbolicCert.lean` is the `K ≤ 1` part of this one: apart from
the degenerate `ε = 0`, every position it certifies has an escaping marked orbit. -/
theorem certifiedK_of_certified (hq : 0 < q) (hqp : q < p) (hcert : SchemaCertified p q s) :
    schemaEps p q s = 0 ∨ ∃ K, SchemaCertifiedK p q s K := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have he0 := schemaEps_nonneg p q s
  have he1 := schemaEps_lt_one p q s
  rcases hcert with h0 | hbig | ⟨hb1, hb2⟩
  · exact Or.inl h0
  · refine Or.inr ⟨0, lowOrbit p q (schemaEps p q s), escape_lowOrbit hq hqp he0 ?_⟩
    constructor
    · norm_num
      nlinarith
    · norm_num
      nlinarith
  · refine Or.inr ⟨1, lowOrbit p q (schemaEps p q s), escape_lowOrbit hq hqp he0 ?_⟩
    constructor
    · norm_num
      nlinarith [mul_le_mul_of_nonneg_right hb1 (show (0:ℝ) ≤ (p:ℝ) - q by linarith)]
    · norm_num
      nlinarith [mul_le_mul_of_nonneg_right hb2 (show (0:ℝ) ≤ (p:ℝ) - q by linarith)]

/-! ## Instances: new certified positions inside the residual bands of M1 -/

/-- **Target T3, grade 2, at `(5,2)`, depth two.**  Every real `s` with `{3s} ∈ [8/195, 4/39]` has
`Z_{5/2}(s, s + 1/5) = ∅`.  That interval sits strictly inside the LOW band `(0, 4/35)` on which
the depth-one schema of `Z32/SymbolicCert.lean` says nothing, and it is 54% of it. -/
theorem ZSet_five_two_depth_two {s : ℝ} (h1 : (8 : ℝ) / 195 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 4 / 39) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  refine ZSet_eq_empty_of_lowBand (K := 2) (by norm_num) (by norm_num) (by decide) ?_
  have heps : schemaEps 5 2 s = Int.fract (3 * s) := by
    simp only [schemaEps, schemaTheta]
    norm_num
  refine ⟨?_, ?_⟩ <;> rw [heps] <;> norm_num <;> linarith

/-- **Depth three at `(5,2)`**: `{3s} ∈ [16/1015, 8/203]`, the next band down.  Its endpoints are
two of the accumulation points experiment X-P located inside the LOW band. -/
theorem ZSet_five_two_depth_three {s : ℝ} (h1 : (16 : ℝ) / 1015 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 8 / 203) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  refine ZSet_eq_empty_of_lowBand (K := 3) (by norm_num) (by norm_num) (by decide) ?_
  have heps : schemaEps 5 2 s = Int.fract (3 * s) := by
    simp only [schemaEps, schemaTheta]
    norm_num
  refine ⟨?_, ?_⟩ <;> rw [heps] <;> norm_num <;> linarith

/-- A concrete interval of positions, stated without `Int.fract`: on `[8/585, 4/117]` we have
`3s ∈ [8/195, 4/39] ⊂ [0,1)`.  This is a T3 grade-2 statement — emptiness for *all real* `s` in an
interval of positions that M1 could not reach. -/
theorem ZSet_five_two_depth_two_interval {s : ℝ} (h1 : (8 : ℝ) / 585 ≤ s) (h2 : s ≤ 4 / 117) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := by
  have hfr : Int.fract (3 * s) = 3 * s := by
    rw [Int.fract_eq_self]
    constructor <;> linarith
  exact ZSet_five_two_depth_two (by rw [hfr]; linarith) (by rw [hfr]; linarith)

end Z32
