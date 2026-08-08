/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.Dictionary
import Z32.DubickasWord
import ForMathlib.Combinatorics.Sturmian

/-!
# Powers of a rational number modulo 1 cannot lie in a small interval (M1-bis)

**[Dub09AA] Theorem 1.**  *Let `p, q` be coprime integers with `1 < q < p < q²`, and let `I` be a
closed subinterval of `ℝ/ℤ` of length `1/p`.  Then for every real `ξ ≠ 0` the fractional parts
`{ξ(p/q)ⁿ}` lie outside `I` for infinitely many `n`.*

At `(p,q) = (3,2)` — legitimate, since `3 < 4 = q²` — this says `Z_{3/2}(s, s+⅓) = ∅` for **every**
`s`, which is the all-`s` emptiness that milestone M1 could only reach at the five [FLP95]
positions and on the rational grid.  It is the sharp baseline for targets T1 and T2(a) of
`plans/plan-cert32.html`, fixed at gate G-5 and confirmed on the primary source at G-6.

## The proof, in three moves

1. **Confinement forces a two-letter carry word** (`Z32.carry_mem_alphabet`).  With `ν = −s` the
   hypothesis reads `0 ≤ yₙ ≤ 1/p`, and `sₙ = p·yₙ − q·y_{n+1} + (p−q)s` then ranges over an
   interval of length `1 + q/p < 2`: at most two consecutive integers `k`, `k+1`.
2. **The word is Sturmian** (`Z32.isSturmian_carryBit` = [Dub09AA] Theorem 3).  It is aperiodic by
   `Z32.not_isEventuallyPeriodic_carry`, and it has no bispecial pair: if `k·u·k` and
   `(k+1)·u·(k+1)` both occurred, the summation identity (4) applied at the two occurrences would
   give `((p/q)^{M−1} + 1)/q ≤ ((p/q)^M + 1)/p`, i.e. `p ≤ q`.  The bispecial criterion
   (`ForMathlib.SubwordComplexity.isSturmian_of_not_hasBispecialPair`) concludes.
3. **Complexity `m + 1` collides with `p < q²`** (`Z32.no_confinement`).  Among the `m + 2` factors
   of length `m` read at positions `0, …, m+1`, two coincide; identity (4) then gives
   `x_{m+j} − x_{m+i} = (p/q)^m (x_j − x_i)`, so `q^m` divides the nonzero integer `x_j − x_i`,
   which is `O((p/q)^{m+1})`.  Hence `(q²/p)^m = O(1)`, and `p ≤ q² − 1` makes this false for large
   `m` by Bernoulli's inequality.

## Main results

* `Z32.no_confinement` — the core: no `ξ ≠ 0` has its whole orbit in a closed length-`1/p` window.
* `Z32.dubickas_theorem_1` — the source statement, in "infinitely many escapes" form.
* `Z32.ZSet_eq_empty_of_lt_sq` — `FLP.ZSet p q s (1/p) = ∅` for all `s`, all `1 < q < p < q²`.
* `Z32.ZSet_three_two_third_empty` — the `(3,2)` headline: `Z_{3/2}(s, s+⅓) = ∅` for **every** real
  `s`.  Compare `Z32.FLP_cor_one_four_a` (M1), which certifies the five [FLP95] positions with an
  axiom-free proof, and `Z32.ZSet_cell_empty` (M1), which certifies every cell of every modulus
  `m ≥ 3`.

## Trust ledger

Everything here is `std3`: no cited axioms, no `sorry`, no `native_decide`.  The word-combinatorics
input — the Sturmian bispecial criterion attributed to [Lot02] — is **proved** in
`ForMathlib.Combinatorics.Sturmian`, and [Dub09AA]'s other external ingredient, the aperiodicity
Lemma 2 of [DN05], is proved in `Z32.DubickasWord`.  Milestone M1 is likewise axiom-free.

## Claim level

Formalization only.  [Dub09AA] is a published 2009 theorem; §4 of that paper leaves open whether
the hypothesis `p < q²` can be relaxed to `p < q^{I_S}` with `I_S > 2`, and the case `p > q²` is
wholly open.  Nothing here claims either.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.  Local copy: `papers/dubickas2009AA.pdf`.
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **70.2** (1995), 125–147 — Corollary 1.4a, the five positions.
* [Bug04] Y. Bugeaud, *Linear mod one transformations and the distribution of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **114** (2004), 301–311 — the almost-every-`s` predecessor.
* [Lot02] M. Lothaire, *Algebraic Combinatorics on Words*, Encyclopedia of Mathematics and its
  Applications **90**, Cambridge Univ. Press, 2002 — Proposition 2.1.3 and Theorem 2.1.5, the
  bispecial criterion; proved in `ForMathlib/Combinatorics/Sturmian.lean` rather than cited.
* `plans/plan-cert32.html` §3.5, §3.6 (the gate findings), §11 (milestone M1-bis).
-/

namespace Z32

open ForMathlib.SubwordComplexity

variable {p q : ℕ} {ξ s : ℝ}

/-! ## Step 1: confinement forces a two-letter alphabet -/

/-- The lower letter `k = ⌈(p−q)s − q/p⌉` of [Dub09AA] Theorem 3. -/
noncomputable def letterBase (p q : ℕ) (s : ℝ) : ℤ := ⌈((p : ℝ) - q) * s - (q : ℝ) / p⌉

/-- The two-letter recoding of the carry word: `true` marks the larger letter `k + 1`. -/
noncomputable def carryBit (p q : ℕ) (ξ ν : ℝ) (k : ℤ) (n : ℕ) : Bool :=
  decide (carry p q ξ ν n = k + 1)

/-- `orb p q ξ (−s) n = ξ(p/q)ⁿ − s`. -/
theorem orb_neg (n : ℕ) : orb p q ξ (-s) n = ξ * ((p : ℝ) / q) ^ n - s := by
  rw [orb, sub_eq_add_neg]

/-- Lower bound for the carry: `sₙ ≥ (p−q)s − q/p`. -/
theorem carry_ge (hq : 0 < q) (hp : 0 < p) (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) (n : ℕ) :
    ((p : ℝ) - q) * s - (q : ℝ) / p ≤ (carry p q ξ (-s) n : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc := carry_eq (p := p) (q := q) (ξ := ξ) (ν := -s) hq n
  have h1 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n
  have h2 := hy (n + 1)
  have h3 : (q : ℝ) * yFract p q ξ (-s) (n + 1) ≤ (q : ℝ) / p := by
    rw [div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_left h2 hq0.le
  nlinarith [hc, h1, h3]

/-- Upper bound for the carry: `sₙ ≤ (p−q)s + 1`. -/
theorem carry_le (hq : 0 < q) (hp : 0 < p) (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) (n : ℕ) :
    (carry p q ξ (-s) n : ℝ) ≤ ((p : ℝ) - q) * s + 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc := carry_eq (p := p) (q := q) (ξ := ξ) (ν := -s) hq n
  have h1 := hy n
  have h2 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) (n + 1)
  have h3 : (p : ℝ) * yFract p q ξ (-s) n ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hp0.le
    rwa [mul_one_div, div_self hp0.ne'] at this
  nlinarith [hc, h2, h3]

/-- **[Dub09AA] Theorem 3, first half.**  A confined orbit has a carry word on the two-letter
alphabet `{k, k+1}`, `k = ⌈(p−q)s − q/p⌉`: the range of `sₙ` is an interval of length
`1 + q/p < 2`. -/
theorem carry_mem_alphabet (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) (n : ℕ) :
    carry p q ξ (-s) n = letterBase p q s ∨ carry p q ξ (-s) n = letterBase p q s + 1 := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hqp : (q : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact_mod_cast hpq
  have hlow : letterBase p q s ≤ carry p q ξ (-s) n :=
    Int.ceil_le.mpr (carry_ge hq hp hy n)
  have hceil : ((p : ℝ) - q) * s - (q : ℝ) / p ≤ (letterBase p q s : ℝ) := Int.le_ceil _
  have hhigh : (carry p q ξ (-s) n : ℝ) < (letterBase p q s : ℝ) + 2 := by
    have := carry_le hq hp hy n
    linarith
  have hhigh' : carry p q ξ (-s) n < letterBase p q s + 2 := by exact_mod_cast hhigh
  omega

/-- Under confinement every carry lies in `[0, p]`, hence `|sₙ| ≤ p`.  ([Dub09AA] states the
weaker `|sₙ| < 2p`.)  This uses `0 ≤ s < 1`, exactly as the source does. -/
theorem abs_carry_le (hq : 0 < q) (hpq : q < p) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) (n : ℕ) :
    |(carry p q ξ (-s) n : ℝ)| ≤ (p : ℝ) := by
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  have hqp : (q : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact hpq'
  have hlow := carry_ge hq hp hy n
  have hhigh := carry_le hq hp hy n
  have h1 : (-1 : ℝ) < (carry p q ξ (-s) n : ℝ) := by nlinarith
  have h2 : (carry p q ξ (-s) n : ℝ) < p + 1 := by nlinarith
  have h1' : (-1 : ℤ) < carry p q ξ (-s) n := by exact_mod_cast h1
  have h2' : carry p q ξ (-s) n < (p : ℤ) + 1 := by exact_mod_cast h2
  have h3 : (0 : ℤ) ≤ carry p q ξ (-s) n := by omega
  have h4 : carry p q ξ (-s) n ≤ (p : ℤ) := by omega
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ (carry p q ξ (-s) n : ℝ) := by exact_mod_cast h3
    linarith
  · exact_mod_cast h4

/-! ## Step 2: the carry word is Sturmian ([Dub09AA] Theorem 3) -/

/-- Reading a `true` bit. -/
theorem carry_of_bit_true {k : ℤ} {n : ℕ} (h : carryBit p q ξ (-s) k n = true) :
    carry p q ξ (-s) n = k + 1 := of_decide_eq_true h

/-- Reading a `false` bit, using that the alphabet has only two letters. -/
theorem carry_of_bit_false (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) {n : ℕ}
    (h : carryBit p q ξ (-s) (letterBase p q s) n = false) :
    carry p q ξ (-s) n = letterBase p q s := by
  have hne : carry p q ξ (-s) n ≠ letterBase p q s + 1 := of_decide_eq_false h
  rcases carry_mem_alphabet hq hpq hy n with h' | h'
  · exact h'
  · exact absurd h' hne

/-- **No bispecial pair.**  This is the arithmetic heart of [Dub09AA] Theorem 3: if the blocks
`k·u·k` and `(k+1)·u·(k+1)` both occurred in the carry word, identity (4) at their two starting
positions would force `p ≤ q`. -/
theorem not_hasBispecialPair (hq : 0 < q) (hpq : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) :
    ¬ HasBispecialPair (carryBit p q ξ (-s) (letterBase p q s)) := by
  rintro ⟨m, i, j, hi, him, hj, hjm, hu⟩
  have hp : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  set β : ℝ := (p : ℝ) / q with hβdef
  have hβ0 : (0 : ℝ) < β := div_pos hp0 hq0
  -- the letters at the four marked positions
  have hci : carry p q ξ (-s) i = letterBase p q s := carry_of_bit_false hq hpq hy hi
  have hcim : carry p q ξ (-s) (i + 1 + m) = letterBase p q s := carry_of_bit_false hq hpq hy him
  have hcj : carry p q ξ (-s) j = letterBase p q s + 1 := carry_of_bit_true hj
  have hcjm : carry p q ξ (-s) (j + 1 + m) = letterBase p q s + 1 := carry_of_bit_true hjm
  -- the difference word: `1` at the two ends, `0` in between
  set d : ℕ → ℝ :=
    fun r => (carry p q ξ (-s) (j + r) : ℝ) - (carry p q ξ (-s) (i + r) : ℝ) with hddef
  have hd0 : d 0 = 1 := by simp only [hddef, Nat.add_zero, hci, hcj]; push_cast; ring
  have hdz : ∀ r, 1 ≤ r → r ≤ m → d r = 0 := by
    intro r h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    have ht : t < m := by omega
    have hij : carry p q ξ (-s) (i + (t + 1)) = carry p q ξ (-s) (j + (t + 1)) := by
      have h := hu t ht
      have e1 : i + 1 + t = i + (t + 1) := by omega
      have e2 : j + 1 + t = j + (t + 1) := by omega
      rw [e1, e2] at h
      by_cases hb : carryBit p q ξ (-s) (letterBase p q s) (i + (t + 1)) = true
      · rw [carry_of_bit_true hb, carry_of_bit_true (h ▸ hb)]
      · rw [Bool.not_eq_true] at hb
        rw [carry_of_bit_false hq hpq hy hb, carry_of_bit_false hq hpq hy (h ▸ hb)]
    simp only [hddef, hij]; ring
  have hdlast : d (m + 1) = 1 := by
    have e1 : i + (m + 1) = i + 1 + m := by omega
    have e2 : j + (m + 1) = j + 1 + m := by omega
    simp only [hddef, e1, e2, hcim, hcjm]; push_cast; ring
  -- the accumulated difference over the two blocks is `β^{m+1} + 1`
  have hacc : geomAcc β (fun r => (carry p q ξ (-s) (j + r) : ℝ)) (m + 2)
      - geomAcc β (fun r => (carry p q ξ (-s) (i + r) : ℝ)) (m + 2) = β ^ (m + 1) + 1 := by
    rw [← geomAcc_sub β _ _ (m + 2)]
    have h1 : geomAcc β d (m + 1) = β ^ m * 1 := geomAcc_spike hd0 hdz
    have h2 : geomAcc β d (m + 2) = β * geomAcc β d (m + 1) + d (m + 1) := geomAcc_succ β d (m + 1)
    rw [show (fun r => (carry p q ξ (-s) (j + r) : ℝ) - (carry p q ξ (-s) (i + r) : ℝ)) = d from
      hddef.symm, h2, h1, hdlast, pow_succ]
    ring
  -- the fractional-part form of identity (4), with the `ν`-terms cancelling
  have hyM : ∀ n : ℕ, yFract p q ξ (-s) (n + (m + 2))
      = -s + β ^ (m + 2) * s + β ^ (m + 2) * yFract p q ξ (-s) n
        - geomAcc β (fun r => (carry p q ξ (-s) (n + r) : ℝ)) (m + 2) / q := by
    intro n
    have hx := xInt_add (p := p) (q := q) (ξ := ξ) (ν := -s) hq n (m + 2)
    have hy1 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := -s) n
    have hy2 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := -s) (n + (m + 2))
    rw [← hβdef] at hx hy1 hy2
    linear_combination hy2 - hx - β ^ (m + 2) * hy1
  have hkey : yFract p q ξ (-s) (j + (m + 2)) - yFract p q ξ (-s) (i + (m + 2))
      = β ^ (m + 2) * (yFract p q ξ (-s) j - yFract p q ξ (-s) i) - (β ^ (m + 1) + 1) / q := by
    rw [hyM i, hyM j]
    have hq' : (q : ℝ) ≠ 0 := hq0.ne'
    field_simp
    linarith [hacc]
  -- and the bounds `0 ≤ y ≤ 1/p` turn it into `p ≤ q`
  have b1 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) i
  have b2 := hy j
  have b3 := hy (i + (m + 2))
  have b4 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) (j + (m + 2))
  have hβpow : (0 : ℝ) ≤ β ^ (m + 2) := (pow_pos hβ0 _).le
  have hmono : β ^ (m + 2) * (yFract p q ξ (-s) j - yFract p q ξ (-s) i)
      ≤ β ^ (m + 2) * (1 / (p : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hβpow
    linarith
  have hineq : (β ^ (m + 1) + 1) / q ≤ (β ^ (m + 2) + 1) / (p : ℝ) := by
    have e1 : (β ^ (m + 2) + 1) / (p : ℝ) = β ^ (m + 2) * (1 / (p : ℝ)) + 1 / (p : ℝ) := by ring
    rw [e1]
    linarith [hkey, hmono, b3, b4]
  have hcross : (β ^ (m + 1) + 1) * p ≤ (β ^ (m + 2) + 1) * q := by
    rw [div_le_div_iff₀ hq0 hp0] at hineq
    linarith
  have hpow : β ^ (m + 2) = β ^ (m + 1) * β := pow_succ _ _
  have hqβ : β * q = p := by rw [hβdef]; field_simp
  rw [hpow] at hcross
  nlinarith [hcross, hqβ, pow_pos hβ0 (m + 1)]

/-- **[Dub09AA] Theorem 3.**  If the orbit of `ξ ≠ 0` stays in the closed window `[s, s+1/p]`
mod 1, its carry word is a Sturmian word on the two-letter alphabet `{k, k+1}`. -/
theorem isSturmian_carryBit (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0)
    (hy : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ)) :
    IsSturmian (carryBit p q ξ (-s) (letterBase p q s)) := by
  refine isSturmian_of_not_hasBispecialPair ?_ (not_hasBispecialPair (by omega) hpq hy)
  -- aperiodicity transfers from the integer carry word to its two-letter recoding
  rintro ⟨N, P, hP, hper⟩
  refine not_isEventuallyPeriodic_carry (ν := -s) hq hpq hcop hξ ⟨N, P, hP, ?_⟩
  intro n hn
  have h := hper n hn
  by_cases hb : carryBit p q ξ (-s) (letterBase p q s) (n + P) = true
  · rw [carry_of_bit_true hb, carry_of_bit_true (h ▸ hb : _ = true)]
  · rw [Bool.not_eq_true] at hb
    rw [carry_of_bit_false (by omega) hpq hy hb,
      carry_of_bit_false (by omega) hpq hy (h ▸ hb : _ = false)]

/-! ## Step 3: `p < q²` kills the Sturmian word -/

private theorem lt_of_step {f : ℕ → ℤ} {m₀ : ℕ} (h : ∀ n, m₀ ≤ n → f n < f (n + 1)) :
    ∀ a b, m₀ ≤ a → a < b → f a < f b := by
  intro a b ha hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h1 | h1
    · exact lt_trans (ih h1) (h b (by omega))
    · subst h1; exact h a ha

private theorem gt_of_step {f : ℕ → ℤ} {m₀ : ℕ} (h : ∀ n, m₀ ≤ n → f (n + 1) < f n) :
    ∀ a b, m₀ ≤ a → a < b → f b < f a := by
  intro a b ha hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h1 | h1
    · exact lt_trans (h b (by omega)) (ih h1)
    · subst h1; exact h a ha

/-- **Eventual injectivity of the integer parts.**  For `ξ ≠ 0` the sequence `xₙ` is eventually
strictly monotone (increasing if `ξ > 0`, decreasing if `ξ < 0`), because consecutive orbit points
eventually differ by more than `1`. -/
theorem exists_xInt_injective (hq : 0 < q) (hpq : q < p) {ν : ℝ} (hξ : ξ ≠ 0) :
    ∃ m₀ : ℕ, ∀ a b : ℕ, m₀ ≤ a → a < b → xInt p q ξ ν a ≠ xInt p q ξ ν b := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  have hβ1 : 1 < (p : ℝ) / q := by rw [lt_div_iff₀ hq0]; linarith
  have hβ0 : (0 : ℝ) < (p : ℝ) / q := by linarith
  have habs : 0 < |ξ| := abs_pos.mpr hξ
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (1 / (|ξ| * ((p : ℝ) / q - 1))) hβ1
  refine ⟨m₀, ?_⟩
  have hgap : ∀ n, m₀ ≤ n → 1 ≤ |ξ| * ((p : ℝ) / q) ^ n * ((p : ℝ) / q - 1) := by
    intro n hn
    have h1 : ((p : ℝ) / q) ^ m₀ ≤ ((p : ℝ) / q) ^ n := pow_le_pow_right₀ hβ1.le hn
    have h2 : 1 / (|ξ| * ((p : ℝ) / q - 1)) < ((p : ℝ) / q) ^ n := lt_of_lt_of_le hm₀ h1
    rw [div_lt_iff₀ (by positivity)] at h2
    nlinarith [h2]
  -- the orbit step, whose sign is the sign of `ξ`
  have hstep : ∀ n, orb p q ξ ν (n + 1) - orb p q ξ ν n = ξ * ((p : ℝ) / q) ^ n * ((p:ℝ)/q - 1) := by
    intro n
    simp only [orb, pow_succ]
    ring
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · -- `ξ < 0`: the integer parts strictly decrease
    have hdec : ∀ n, m₀ ≤ n → xInt p q ξ ν (n + 1) < xInt p q ξ ν n := by
      intro n hn
      have h1 := hgap n hn
      have h2 := hstep n
      rw [abs_of_neg hneg] at h1
      have h3 : orb p q ξ ν (n + 1) + 1 ≤ orb p q ξ ν n := by nlinarith [h1, h2]
      have h5 : ⌊orb p q ξ ν (n + 1) + 1⌋ ≤ ⌊orb p q ξ ν n⌋ := Int.floor_le_floor h3
      rw [Int.floor_add_one] at h5
      have h6 : ⌊orb p q ξ ν (n + 1)⌋ + 1 ≤ ⌊orb p q ξ ν n⌋ := h5
      show ⌊orb p q ξ ν (n + 1)⌋ < ⌊orb p q ξ ν n⌋
      omega
    exact fun a b ha hab => (gt_of_step hdec a b ha hab).ne'
  · -- `ξ > 0`: the integer parts strictly increase
    have hinc : ∀ n, m₀ ≤ n → xInt p q ξ ν n < xInt p q ξ ν (n + 1) := by
      intro n hn
      have h1 := hgap n hn
      have h2 := hstep n
      rw [abs_of_pos hpos] at h1
      have h3 : orb p q ξ ν n + 1 ≤ orb p q ξ ν (n + 1) := by nlinarith [h1, h2]
      have h5 : ⌊orb p q ξ ν n + 1⌋ ≤ ⌊orb p q ξ ν (n + 1)⌋ := Int.floor_le_floor h3
      rw [Int.floor_add_one] at h5
      show ⌊orb p q ξ ν n⌋ < ⌊orb p q ξ ν (n + 1)⌋
      omega
    exact fun a b ha hab => (lt_of_step hinc a b ha hab).ne

/-- **The core of [Dub09AA] Theorem 1.**  For coprime `1 < q < p < q²` no `ξ ≠ 0` has its entire
`(p/q)`-orbit inside a closed window of length `1/p`. -/
theorem no_confinement (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy : ∀ n : ℕ, Int.fract (ξ * ((p : ℝ) / q) ^ n - s) ≤ 1 / (p : ℝ)) : False := by
  have hq0' : 0 < q := by omega
  have hp : 0 < p := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq0'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  have hy' : ∀ n, yFract p q ξ (-s) n ≤ 1 / (p : ℝ) := by
    intro n; rw [yFract, orb_neg]; exact hy n
  set β : ℝ := (p : ℝ) / q with hβdef
  have hβ1 : 1 < β := by rw [hβdef, lt_div_iff₀ hq0]; linarith
  have hβ0 : (0 : ℝ) < β := by linarith
  -- the Sturmian carry word
  have hSt := isSturmian_carryBit hq hpq hcop hξ hy'
  -- the growth constant and the eventual-injectivity threshold
  have hcar := abs_carry_le hq0' hpq hs0 hs1 hy'
  set c : ℝ := |(xInt p q ξ (-s) 0 : ℝ)| + p with hcdef
  have hc0 : 0 < c := by
    have : (0 : ℝ) ≤ |(xInt p q ξ (-s) 0 : ℝ)| := abs_nonneg _
    rw [hcdef]; linarith
  have hgrow : ∀ n, |(xInt p q ξ (-s) n : ℝ)| ≤ c * β ^ n := by
    intro n
    have h := abs_xInt_le (p := p) (q := q) (ξ := ξ) (ν := -s) hq0' hpq hp0.le hcar n
    rw [← hβdef, ← hcdef] at h
    linarith [hp0]
  obtain ⟨m₀, hm₀⟩ := exists_xInt_injective (ν := -s) hq0' hpq hξ
  -- Bernoulli: `(q²/(q²−1))^m ≥ 1 + m/(q²−1)` beats the constant `c·p`
  set B : ℝ := (q : ℝ) * (q : ℝ) - 1 with hBdef
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hB0 : 0 < B := by rw [hBdef]; nlinarith
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, m₀ ≤ m ∧ c * p * B < m := by
    refine ⟨max m₀ (⌈c * p * B⌉₊ + 1), le_max_left _ _, ?_⟩
    have h1 : (⌈c * (p : ℝ) * B⌉₊ : ℝ) ≥ c * p * B := Nat.le_ceil _
    have h2 : ⌈c * (p : ℝ) * B⌉₊ + 1 ≤ max m₀ (⌈c * (p : ℝ) * B⌉₊ + 1) := le_max_right _ _
    have h3 : ((⌈c * (p : ℝ) * B⌉₊ : ℕ) : ℝ) + 1
        ≤ ((max m₀ (⌈c * (p : ℝ) * B⌉₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  -- pigeonhole on the Sturmian word: a factor repeats within the first `m + 2` positions
  obtain ⟨i, j, hij, hjm, hfac⟩ := exists_factor_eq_of_isSturmian hSt m
  have hcarry : ∀ t, t < m → carry p q ξ (-s) (i + t) = carry p q ξ (-s) (j + t) := by
    intro t ht
    have h := hfac t ht
    by_cases hb : carryBit p q ξ (-s) (letterBase p q s) (i + t) = true
    · rw [carry_of_bit_true hb, carry_of_bit_true (h ▸ hb : _ = true)]
    · rw [Bool.not_eq_true] at hb
      rw [carry_of_bit_false hq0' hpq hy' hb, carry_of_bit_false hq0' hpq hy' (h ▸ hb : _ = false)]
  have hacc : geomAcc β (fun r => (carry p q ξ (-s) (i + r) : ℝ)) m
      = geomAcc β (fun r => (carry p q ξ (-s) (j + r) : ℝ)) m :=
    geomAcc_congr fun r hr => by rw [hcarry r hr]
  -- identity (4): `x_{j+m} − x_{i+m} = β^m (x_j − x_i)`
  have hxi := xInt_add (p := p) (q := q) (ξ := ξ) (ν := -s) hq0' i m
  have hxj := xInt_add (p := p) (q := q) (ξ := ξ) (ν := -s) hq0' j m
  rw [← hβdef] at hxi hxj
  have hdiff : (xInt p q ξ (-s) (j + m) : ℝ) - (xInt p q ξ (-s) (i + m) : ℝ)
      = β ^ m * ((xInt p q ξ (-s) j : ℝ) - (xInt p q ξ (-s) i : ℝ)) := by
    rw [hxi, hxj, hacc]; ring
  -- clear denominators: `q^m ∣ p^m (x_j − x_i)`
  have hZ : (q : ℤ) ^ m * (xInt p q ξ (-s) (j + m) - xInt p q ξ (-s) (i + m))
      = (p : ℤ) ^ m * (xInt p q ξ (-s) j - xInt p q ξ (-s) i) := by
    have hR : (q : ℝ) ^ m * ((xInt p q ξ (-s) (j + m) : ℝ) - (xInt p q ξ (-s) (i + m) : ℝ))
        = (p : ℝ) ^ m * ((xInt p q ξ (-s) j : ℝ) - (xInt p q ξ (-s) i : ℝ)) := by
      rw [hdiff, hβdef, div_pow]
      field_simp
    exact_mod_cast hR
  -- the two integer parts at `i + m`, `j + m` are distinct, hence so are those at `i`, `j`
  have hne : xInt p q ξ (-s) (i + m) ≠ xInt p q ξ (-s) (j + m) :=
    hm₀ (i + m) (j + m) (by omega) (by omega)
  have hne0 : xInt p q ξ (-s) j - xInt p q ξ (-s) i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hZ
    have hqm : (q : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0'.ne')
    rcases mul_eq_zero.mp hZ with h | h
    · exact hqm h
    · exact hne (by omega)
  -- divisibility
  have hdvd : (q : ℤ) ^ m ∣ xInt p q ξ (-s) j - xInt p q ξ (-s) i := by
    have hdd : (q : ℤ) ^ m ∣ (p : ℤ) ^ m * (xInt p q ξ (-s) j - xInt p q ξ (-s) i) :=
      ⟨xInt p q ξ (-s) (j + m) - xInt p q ξ (-s) (i + m), hZ.symm⟩
    exact ((Nat.isCoprime_iff_coprime.mpr hcop.symm).pow).dvd_of_dvd_mul_left hdd
  have hqle : (q : ℤ) ^ m ≤ |xInt p q ξ (-s) j - xInt p q ξ (-s) i| :=
    Int.le_of_dvd (abs_pos.mpr hne0) ((dvd_abs _ _).mpr hdvd)
  have hqleR : (q : ℝ) ^ m
      ≤ |(xInt p q ξ (-s) j : ℝ)| + |(xInt p q ξ (-s) i : ℝ)| := by
    have h3 : |xInt p q ξ (-s) j - xInt p q ξ (-s) i|
        ≤ |xInt p q ξ (-s) j| + |xInt p q ξ (-s) i| := abs_sub _ _
    have h4 : (q : ℤ) ^ m ≤ |xInt p q ξ (-s) j| + |xInt p q ξ (-s) i| := le_trans hqle h3
    exact_mod_cast h4
  -- the size estimate `q^m ≤ c·p·β^m`
  have hβi : β ^ i ≤ β ^ (m + 1) := pow_le_pow_right₀ hβ1.le (by omega)
  have hβj : β ^ j ≤ β ^ (m + 1) := pow_le_pow_right₀ hβ1.le (by omega)
  have h2β : (2 : ℝ) * β ≤ p := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hβq : β * q = p := by rw [hβdef]; field_simp
    nlinarith [hβq, mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ (q : ℝ) - 2)]
  have hsize : (q : ℝ) ^ m ≤ c * p * β ^ m := by
    have h1 : |(xInt p q ξ (-s) i : ℝ)| ≤ c * β ^ (m + 1) :=
      le_trans (hgrow i) (by nlinarith [hβi, hc0])
    have h2 : |(xInt p q ξ (-s) j : ℝ)| ≤ c * β ^ (m + 1) :=
      le_trans (hgrow j) (by nlinarith [hβj, hc0])
    have h7 : (q : ℝ) ^ m ≤ 2 * (c * β ^ (m + 1)) := by linarith
    rw [pow_succ] at h7
    nlinarith [h7, h2β, pow_pos hβ0 m, hc0,
      mul_nonneg (mul_nonneg hc0.le (pow_pos hβ0 m).le) (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2 * β)]
  -- `q^{2m} ≤ c·p·B^m` with `B = q² − 1 ≥ p`
  have hpB : (p : ℝ) ≤ B := by
    have h1 : (p : ℤ) < (q : ℤ) * (q : ℤ) := by exact_mod_cast hpq2
    have h2 : (p : ℤ) ≤ (q : ℤ) * (q : ℤ) - 1 := by omega
    have h3 : (p : ℝ) ≤ (q : ℝ) * (q : ℝ) - 1 := by exact_mod_cast h2
    rw [hBdef]; linarith
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := pow_pos hq0 m
  have hqsq : (q : ℝ) ^ m * (q : ℝ) ^ m ≤ c * p * B ^ m := by
    have hβm : β ^ m = (p : ℝ) ^ m / (q : ℝ) ^ m := by rw [hβdef, div_pow]
    have h2 : (q : ℝ) ^ m * (q : ℝ) ^ m ≤ c * p * (p : ℝ) ^ m := by
      have h5 := mul_le_mul_of_nonneg_right hsize hqm.le
      have h6 : c * (p : ℝ) * β ^ m * (q : ℝ) ^ m = c * p * (p : ℝ) ^ m := by
        rw [hβm]; field_simp
      linarith [h5, h6]
    have h4 : (p : ℝ) ^ m ≤ B ^ m := pow_le_pow_left₀ hp0.le hpB m
    calc (q : ℝ) ^ m * (q : ℝ) ^ m ≤ c * p * (p : ℝ) ^ m := h2
      _ ≤ c * p * B ^ m := mul_le_mul_of_nonneg_left h4 (mul_nonneg hc0.le hp0.le)
  -- Bernoulli finishes it
  have hBern : 1 + (m : ℝ) * (1 / B) ≤ (1 + 1 / B) ^ m := by
    apply one_add_mul_le_pow
    have : (0 : ℝ) < 1 / B := by positivity
    linarith
  have hBm : (0 : ℝ) < B ^ m := pow_pos hB0 m
  have hfinal : (1 + 1 / B) ^ m ≤ c * p := by
    have hBne : B ≠ 0 := hB0.ne'
    have h1 : (1 : ℝ) + 1 / B = (q : ℝ) * (q : ℝ) / B := by
      field_simp
      linarith [hBdef]
    rw [h1, div_pow, div_le_iff₀ hBm, mul_pow]
    linarith [hqsq]
  have hle : 1 + (m : ℝ) * (1 / B) ≤ c * p := le_trans hBern hfinal
  have h2 : (1 + (m : ℝ) * (1 / B)) * B ≤ c * (p : ℝ) * B :=
    mul_le_mul_of_nonneg_right hle hB0.le
  have h3 : (1 + (m : ℝ) * (1 / B)) * B = B + m := by field_simp
  rw [h3] at h2
  linarith [h2, hm2, hB0]

/-! ## The source statement and its corollaries -/

/-- **[Dub09AA] Theorem 1.**  Let `p, q` be coprime with `1 < q < p < q²` and let
`I = [s, s + 1/p]` be a closed interval of length `1/p` in `ℝ/ℤ`.  Then for every real `ξ ≠ 0`,
`{ξ(p/q)ⁿ} ∉ I` for infinitely many `n`. -/
theorem dubickas_theorem_1 (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q)
    (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0) (s : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / q) ^ n - s) := by
  by_contra hcon
  push Not at hcon
  have hq0 : 0 < q := by omega
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hβ0 : (0 : ℝ) < (p : ℝ) / q := div_pos hp0R hq0R
  -- the shift trick: pass to `ξ(p/q)^N`, which is confined from step `0` on
  refine no_confinement (ξ := ξ * ((p : ℝ) / q) ^ N) (s := Int.fract s) hq hpq hpq2 hcop
    (mul_ne_zero hξ (pow_ne_zero _ hβ0.ne')) (Int.fract_nonneg s) (Int.fract_lt_one s) ?_
  intro n
  have h1 : ξ * ((p : ℝ) / q) ^ N * ((p : ℝ) / q) ^ n = ξ * ((p : ℝ) / q) ^ (N + n) := by
    rw [pow_add]; ring
  have hsf : Int.fract s = s - (⌊s⌋ : ℝ) := rfl
  have h2 : ξ * ((p : ℝ) / q) ^ (N + n) - Int.fract s
      = (ξ * ((p : ℝ) / q) ^ (N + n) - s) + (⌊s⌋ : ℝ) := by rw [hsf]; ring
  rw [h1, h2, Int.fract_add_intCast]
  exact hcon (N + n) (by omega)

/-- **[Dub09AA] Theorem 1, `Z`-set form.**  For coprime `1 < q < p < q²` the set
`Z_{p/q}(s, s + 1/p)` is empty for **every** real `s` — the all-`s` strengthening of [FLP95]
Corollary 1.4a and of [Bug04] Corollary 1. -/
theorem ZSet_eq_empty_of_lt_sq (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q)
    (hcop : Nat.Coprime p q) (s : ℝ) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := by
  have hp0 : 0 < p := by omega
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0R]; exact_mod_cast hp0
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hξ0, hmem⟩
  obtain ⟨n, -, hn⟩ := dubickas_theorem_1 hq hpq hpq2 hcop hξ0.ne' s 0
  have h := hmem n
  rw [Set.mem_Ico] at h
  have hsplit : ξ * ((p : ℝ) / q) ^ n - s
      = (Int.fract (ξ * ((p : ℝ) / q) ^ n) - s) + (⌊ξ * ((p : ℝ) / q) ^ n⌋ : ℝ) := by
    have := Int.floor_add_fract (ξ * ((p : ℝ) / q) ^ n)
    linarith
  rw [hsplit, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith [h.1], by linarith [h.2]⟩] at hn
  linarith [h.2]

/-- **The `(3,2)` headline.**  `Z_{3/2}(s, s + ⅓) = ∅` for **every** real `s` (legitimate because
`3 < 4 = 2²`).

Milestone M1 reached this only at the five [FLP95] positions (`Z32.FLP_cor_one_four_a`) and on the
rational cells `[r/m, (r+1)/m)`, `m ≥ 3` (`Z32.ZSet_cell_empty`).  This statement covers every
position, including irrational ones, and is likewise free of cited axioms. -/
theorem ZSet_three_two_third_empty (s : ℝ) : FLP.ZSet 3 2 s (1 / 3) = ∅ := by
  have h := ZSet_eq_empty_of_lt_sq (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    (by decide) s
  norm_num at h
  exact h

/-- The five [FLP95] Corollary 1.4a positions are an instance — a cross-check of M1 against
M1-bis (the M1 proof `Z32.FLP_cor_one_four_a` is independent and axiom-free). -/
example : FLP.ZSet 3 2 (1 / 6) (1 / 3) = ∅ := ZSet_three_two_third_empty _

/-- Positions off every rational grid are covered too — the genuinely new reach of M1-bis over
M1's covering argument. -/
example (s : ℝ) : FLP.ZSet 3 2 s (1 / 3) = ∅ := ZSet_three_two_third_empty s

end Z32
