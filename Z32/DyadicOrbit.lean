/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.VisitDensity

/-!
# The exact 2-adic shape of the orbit `{(3/2)ⁿ}` (plan-A6+, WP0, correction C10a)

At `ξ = 1` the orbit is not merely a sequence of reals: it is a sequence of *dyadic rationals of
exactly known level*,

`xₙ = {(3/2)ⁿ} = rₙ / 2ⁿ`,  `rₙ = 3ⁿ mod 2ⁿ` **odd** (`n ≥ 1`),

so date `n` and 2-adic level `n` are the same thing.  Everything the M6 program does on Front D
(`plans/plan-A6+.html` §3.1) rests on the three consequences proved here: the orbit points are
pairwise distinct, their mutual separation is *exactly* `2^{-max(m,n)}` at best, and — the lemma
the sojourn dichotomy C7 runs on — the orbit stays a definite distance away from every rational
with **odd** denominator:

`|xₙ - c/D| ≥ 1/(D·2ⁿ)`  for every odd `D > 0`.

The cycle points of the map `×3/2` are exactly such rationals (odd denominator dividing `3^p-2^p`,
the [L90] shape), so this is the quantitative floor under any shadowing argument: an orbit that
follows a `p`-periodic carry word for `L` steps at date `n` is trapped within `(2/3)^L` of a cycle
point, and the floor forces `L ≤ (log 2 / log(3/2))·n + C_p` — the same constant as
`RB.dubickasConst`.  WP2 assembles that; this file supplies the floor.

## The annealed baseline

The last section proves the *negative* companion (report2-weyl §5, plan-A6+ C9): the **low** bits
of `rₙ` carry no information.  `3` has multiplicative order exactly `2^{k-2}` modulo `2ᵏ`
(`Z32.three_pow_period`, `Z32.three_pow_not_period`), so `n ↦ rₙ mod 2ᵏ` is purely periodic with
period `2^{k-2}` for `n ≥ k` (`Z32.oddNum_low_periodic`) — a statistic dominated by low bits is
trivially uniform and measures nothing about M6.  Every census statistic of WP6 is to be compared
against this baseline before it is believed.

## Contents

* `Z32.oddNum`, `Z32.x` — the numerator `rₙ` and the orbit point `xₙ`.
* `Z32.x_eq`, `Z32.oddNum_odd`, `Z32.oddNum_lt` — the dictionary and the exact level.
* `Z32.x_ne` — the orbit points are pairwise distinct (`n ≥ 1`).
* `Z32.separation` — `|xₘ - xₙ| ≥ 2^{-max(m,n)}`.
* `Z32.dist_odd_denom` — **the 2-adic floor**, `|xₙ - c/D| ≥ 1/(D 2ⁿ)` for odd `D`.
* `Z32.three_pow_two_pow`, `Z32.three_pow_period`, `Z32.three_pow_not_period`,
  `Z32.oddNum_low_periodic` — the annealed baseline.
* `Z32.M5_ap`, `Z32.visitsIO_along_ap` — the AP specialization (C10b): every arithmetic
  progression of dates escapes every closed arc of length `3^{-k}` infinitely often.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`.  The AP section quotes `Z32.M5_one_sub_inv`, itself proved from
`Z32.dubickas_theorem_1` ([Dub09AA] Theorem 1, proved in `Z32/SmallInterval.lean`).

## Claim level

Formalization only.  The 2-adic shape is folklore (it is the reason the whole `{(3/2)ⁿ}` literature
speaks of `3ⁿ mod 2ⁿ`); the order of `3` modulo `2ᵏ` is classical; the AP specialization is a pure
instantiation of [Dub09AA] Theorem 1 at `(p,q) = (3ᵏ,2ᵏ)`, which satisfies `p < q²` for every `k`.

## References

* `plans/plan-A6+.html` C7 (the sojourn dichotomy), C9 (the annealed baseline), C10a/C10b.
* `plans/report2-weyl.html` §5 (the annealed low-bit model, `ord_{2ᵏ}3 = 2^{k-2}`).
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [L90] J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56**
  (1990) — the odd-denominator shape of the cycle points (corpus root `L90/`).
-/

namespace Z32

open Filter Topology

/-! ## The numerator and the orbit point -/

/-- `rₙ = 3ⁿ mod 2ⁿ`, the numerator of `{(3/2)ⁿ}` over `2ⁿ`. -/
def oddNum (n : ℕ) : ℕ := 3 ^ n % 2 ^ n

/-- `xₙ = {(3/2)ⁿ}`, the orbit point at date `n` for `ξ = 1`. -/
noncomputable def x (n : ℕ) : ℝ := Int.fract ((3 / 2 : ℝ) ^ n)

theorem oddNum_lt (n : ℕ) : oddNum n < 2 ^ n :=
  Nat.mod_lt _ (pow_pos (by norm_num) n)

/-- **The dictionary at `ξ = 1`**: the orbit point is the residue over the power. -/
theorem x_eq (n : ℕ) : x n = (oddNum n : ℝ) / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hdm : (2 : ℕ) ^ n * (3 ^ n / 2 ^ n) + 3 ^ n % 2 ^ n = 3 ^ n := Nat.div_add_mod _ _
  have hcast : (2 : ℝ) ^ n * ((3 ^ n / 2 ^ n : ℕ) : ℝ) + (oddNum n : ℝ) = 3 ^ n := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdm
    push_cast at this
    simpa [oddNum] using this
  have key : ((3 : ℝ) / 2) ^ n = ((3 ^ n / 2 ^ n : ℕ) : ℝ) + (oddNum n : ℝ) / 2 ^ n := by
    rw [div_pow]
    field_simp
    linarith
  rw [x, key, add_comm, Int.fract_add_natCast]
  refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
  rw [div_lt_one h2]
  exact_mod_cast oddNum_lt n

/-- **The numerator is odd**, so `xₙ` is a dyadic rational of *exact* level `n`. -/
theorem oddNum_odd {n : ℕ} (hn : 1 ≤ n) : Odd (oddNum n) := by
  have hdvd : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h : oddNum n % 2 = 3 ^ n % 2 := Nat.mod_mod_of_dvd _ hdvd
  have h3 : 3 ^ n % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  exact Nat.odd_iff.mpr (by rw [h, h3])

theorem oddNum_pos {n : ℕ} (hn : 1 ≤ n) : 0 < oddNum n := by
  rcases Nat.eq_zero_or_pos (oddNum n) with h | h
  · exact absurd (h ▸ oddNum_odd hn) (by decide)
  · exact h

theorem x_pos {n : ℕ} (hn : 1 ≤ n) : 0 < x n := by
  rw [x_eq]
  have := oddNum_pos hn
  positivity

theorem x_lt_one (n : ℕ) : x n < 1 := Int.fract_lt_one _

/-! ## Distinctness and separation

The orbit meets each dyadic level exactly once, so no two dates carry the same point and the
mutual separation is bounded below by the *finer* of the two levels.  Both statements fail for a
general `ξ`; they are the first place where `ξ = 1` is consumed (GR1). -/

/-- The core computation: at `m < n`, `xₘ - xₙ` has denominator `2ⁿ` and an **odd** numerator. -/
private theorem sub_num {m n : ℕ} (hm : 1 ≤ m) (hlt : m < n) :
    ∃ A : ℤ, Odd A ∧ x m - x n = (A : ℝ) / 2 ^ n := by
  refine ⟨(oddNum m : ℤ) * 2 ^ (n - m) - (oddNum n : ℤ), ?_, ?_⟩
  · refine Even.sub_odd ?_ ?_
    · refine (Int.even_mul).mpr (Or.inr ?_)
      exact (Int.even_pow' (by omega)).mpr (by decide)
    · exact_mod_cast oddNum_odd (by omega)
  · have hpow : (2 : ℝ) ^ n = 2 ^ m * 2 ^ (n - m) := by
      rw [← pow_add]
      congr 1
      omega
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have h2j : (0 : ℝ) < 2 ^ (n - m) := by positivity
    rw [x_eq, x_eq, hpow]
    push_cast
    field_simp

/-- **Separation.**  Distinct dates carry points at distance at least `2^{-max(m,n)}`; the bound is
sharp, since `xₘ - xₙ` is an odd multiple of `2^{-max(m,n)}`. -/
theorem separation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    1 / (2 : ℝ) ^ max m n ≤ |x m - x n| := by
  have key : ∀ i j : ℕ, 1 ≤ i → i < j → 1 / (2 : ℝ) ^ j ≤ |x i - x j| := by
    intro i j hi hij
    obtain ⟨A, hodd, hA⟩ := sub_num hi hij
    have hA0 : A ≠ 0 := by
      have := Int.odd_iff.mp hodd
      omega
    have h1 : (1 : ℝ) ≤ |(A : ℝ)| := by
      have : (1 : ℤ) ≤ |A| := Int.one_le_abs hA0
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|A| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(A : ℝ)| := by rw [Int.cast_abs]
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [hA, abs_div, abs_of_pos h2]
    gcongr
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [max_eq_right h.le]
    exact key m n hm h
  · rw [max_eq_left h.le, abs_sub_comm]
    exact key n m hn h

/-- The orbit points are pairwise distinct from date `1` on. -/
theorem x_ne {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) : x m ≠ x n := by
  intro h
  have := separation hm hn hmn
  rw [h, sub_self, abs_zero] at this
  have : (0 : ℝ) < 1 / 2 ^ max m n := by positivity
  linarith

/-- **The 2-adic floor.**  The orbit never comes closer than `1/(D·2ⁿ)` to a rational with odd
denominator `D` — in particular to any cycle point of `×3/2`, whose denominator divides
`3^p - 2^p` and is odd.  This is the quantitative content of C7. -/
theorem dist_odd_denom {n : ℕ} (hn : 1 ≤ n) {D : ℕ} (hD : Odd D) (c : ℤ) :
    1 / ((D : ℝ) * 2 ^ n) ≤ |x n - (c : ℝ) / D| := by
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exact absurd (h ▸ hD) (by decide)
    · exact h
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  set B : ℤ := (oddNum n : ℤ) * D - c * 2 ^ n with hB
  have hB0 : B ≠ 0 := by
    intro h0
    have heq : (oddNum n : ℤ) * D = c * 2 ^ n := by
      rw [hB] at h0; omega
    have hdvd : ((2 : ℕ) ^ n : ℤ) ∣ ((oddNum n * D : ℕ) : ℤ) := by
      push_cast
      exact ⟨c, by linarith [heq]⟩
    have hdvdN : (2 : ℕ) ^ n ∣ oddNum n * D := by exact_mod_cast hdvd
    have hcop : Nat.Coprime (2 ^ n) D := by
      refine Nat.Coprime.pow_left n ?_
      refine (Nat.prime_two.coprime_iff_not_dvd).mpr ?_
      obtain ⟨s, hs⟩ := hD
      rintro ⟨u, hu⟩
      omega
    have : (2 : ℕ) ^ n ∣ oddNum n := hcop.dvd_of_dvd_mul_right hdvdN
    have hle := Nat.le_of_dvd (oddNum_pos hn) this
    exact absurd (oddNum_lt n) (by omega)
  have hkey : x n - (c : ℝ) / D = (B : ℝ) / ((D : ℝ) * 2 ^ n) := by
    rw [x_eq, hB]
    push_cast
    field_simp
  have h1 : (1 : ℝ) ≤ |(B : ℝ)| := by
    have : (1 : ℤ) ≤ |B| := Int.one_le_abs hB0
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|B| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(B : ℝ)| := by rw [Int.cast_abs]
  rw [hkey, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (D : ℝ) * 2 ^ n)]
  gcongr

/-! ## The annealed baseline: the low bits are periodic

`3^{2^j} = 1 + 2^{j+2} + c·2^{j+3}` (`j ≥ 1`) is the 2-adic lifting-the-exponent step, proved here
by a bare induction.  It gives both halves of `ord_{2ᵏ}(3) = 2^{k-2}`. -/

/-- **The lifting step.**  `3^{2^{j+1}} = 1 + 2^{j+3} + c·2^{j+4}` for some `c`. -/
theorem three_pow_two_pow (j : ℕ) :
    ∃ c : ℕ, 3 ^ 2 ^ (j + 1) = 1 + 2 ^ (j + 3) + c * 2 ^ (j + 4) := by
  induction j with
  | zero => exact ⟨0, by norm_num⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 2 ^ (j + 1) * (1 + 2 * c) ^ 2, ?_⟩
    have hsplit : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) * 2 := by ring
    calc 3 ^ 2 ^ (j + 1 + 1) = (3 ^ 2 ^ (j + 1)) ^ 2 := by rw [hsplit, pow_mul]
      _ = (1 + 2 ^ (j + 3) + c * 2 ^ (j + 4)) ^ 2 := by rw [hc]
      _ = 1 + 2 ^ (j + 1 + 3) + (c + 2 ^ (j + 1) * (1 + 2 * c) ^ 2) * 2 ^ (j + 1 + 4) := by
          simp only [pow_add]
          ring

/-- `3^{2^{k-2}} ≡ 1 (mod 2ᵏ)`: the order divides `2^{k-2}`. -/
theorem three_pow_order (k : ℕ) (hk : 3 ≤ k) : 3 ^ 2 ^ (k - 2) ≡ 1 [MOD 2 ^ k] := by
  obtain ⟨c, hc⟩ := three_pow_two_pow (k - 3)
  have h1 : k - 3 + 1 = k - 2 := by omega
  have h3 : k - 3 + 3 = k := by omega
  have h4 : k - 3 + 4 = k + 1 := by omega
  rw [h1, h3, h4] at hc
  have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
  have : 3 ^ 2 ^ (k - 2) = 1 + 2 ^ k * (1 + c * 2) := by rw [hc, hpow]; ring
  rw [Nat.ModEq, this, Nat.add_mul_mod_self_left]

/-- **The annealed period.**  `n ↦ 3ⁿ mod 2ᵏ` is periodic with period `2^{k-2}`. -/
theorem three_pow_period (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    3 ^ (n + 2 ^ (k - 2)) ≡ 3 ^ n [MOD 2 ^ k] := by
  have h := (three_pow_order k hk).mul_left (3 ^ n)
  rw [← pow_add] at h
  simpa using h

/-- **The period is exact**: `3^{2^{k-3}} ≢ 1 (mod 2ᵏ)`, so `ord_{2ᵏ}(3) = 2^{k-2}` — the
`2^{k-2}` of report2-weyl §5. -/
theorem three_pow_not_period (k : ℕ) (hk : 3 ≤ k) : ¬ (3 ^ 2 ^ (k - 3) ≡ 1 [MOD 2 ^ k]) := by
  rcases eq_or_lt_of_le hk with h3 | h4
  · rw [← h3]
    decide
  · obtain ⟨c, hc⟩ := three_pow_two_pow (k - 4)
    have h1 : k - 4 + 1 = k - 3 := by omega
    have h3 : k - 4 + 3 = k - 1 := by omega
    have h4 : k - 4 + 4 = k := by omega
    rw [h1, h3, h4] at hc
    have hval : 3 ^ 2 ^ (k - 3) % 2 ^ k = 1 + 2 ^ (k - 1) := by
      rw [hc, Nat.add_mul_mod_self_right]
      refine Nat.mod_eq_of_lt ?_
      have : (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k := by
        rw [← pow_succ]
        congr 1
        omega
      have hpos : 0 < (2 : ℕ) ^ (k - 1) := pow_pos (by norm_num) _
      have h1lt : (1 : ℕ) < 2 ^ (k - 1) := by
        have : (2 : ℕ) ^ 1 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    intro hcon
    rw [Nat.ModEq, hval] at hcon
    have h1lt : (1 : ℕ) < 2 ^ k := by
      have : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.mod_eq_of_lt h1lt] at hcon
    have hpos : 0 < (2 : ℕ) ^ (k - 1) := pow_pos (by norm_num) _
    omega

/-- **The low bits of the numerator are periodic**: for `n ≥ k`, `rₙ mod 2ᵏ` repeats with period
`2^{k-2}`.  Any statistic of the orbit that is a function of the low `k` bits is therefore exactly
periodic — the annealed baseline every census statistic must be compared against (C9). -/
theorem oddNum_low_periodic {k n : ℕ} (hk : 3 ≤ k) (hn : k ≤ n) :
    oddNum (n + 2 ^ (k - 2)) % 2 ^ k = oddNum n % 2 ^ k := by
  have hd1 : (2 : ℕ) ^ k ∣ 2 ^ n := pow_dvd_pow 2 hn
  have hd2 : (2 : ℕ) ^ k ∣ 2 ^ (n + 2 ^ (k - 2)) := pow_dvd_pow 2 (Nat.le_trans hn (Nat.le_add_right n _))
  rw [oddNum, oddNum, Nat.mod_mod_of_dvd _ hd1, Nat.mod_mod_of_dvd _ hd2]
  exact three_pow_period k hk n

/-! ## The AP specialization (C10b)

`(p,q) = (3ᵏ,2ᵏ)` satisfies `1 < q < p < q²` for every `k ≥ 1`, so [Dub09AA] Theorem 1 —
`Z32.dubickas_theorem_1`, proved in `Z32/SmallInterval.lean` — applies at every base `(3/2)ᵏ`.
Reading it along the dates `n ≡ r (mod k)` with `ξ_r = (3/2)^r` gives a rung *for every arithmetic
progression of dates*, at no cost. -/

/-- **The uniform rung at base `(3/2)ᵏ`**: every arc of length `1 - 3^{-k}` is visited infinitely
often by the orbit of every `ξ ≠ 0`. -/
theorem M5_ap {k : ℕ} (hk : 1 ≤ k) : M5 (((3 : ℝ) / 2) ^ k) (1 - 1 / 3 ^ k) := by
  have hq : 1 < 2 ^ k := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hpq : (2 : ℕ) ^ k < 3 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hpq2 : (3 : ℕ) ^ k < 2 ^ k * 2 ^ k := by
    rw [← mul_pow]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hcop : Nat.Coprime (3 ^ k) (2 ^ k) := Nat.Coprime.pow k k (by norm_num)
  have h := M5_one_sub_inv hq hpq hpq2 hcop
  have hbase : (((3 : ℕ) ^ k : ℕ) : ℝ) / (((2 : ℕ) ^ k : ℕ) : ℝ) = ((3 : ℝ) / 2) ^ k := by
    push_cast
    rw [div_pow]
  have hlen : 1 - 1 / (((3 : ℕ) ^ k : ℕ) : ℝ) = 1 - 1 / 3 ^ k := by push_cast; ring
  rwa [hbase, hlen] at h

/-- **The AP rung (C10b).**  For every modulus `k ≥ 1` and every residue `r`, the dates
`n ≡ r (mod k)` alone already visit every arc of length `1 - 3^{-k}` infinitely often. -/
theorem visitsIO_along_ap {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (s : ℝ) :
    ∃ᶠ m : ℕ in atTop, inArc s (1 - 1 / 3 ^ k) (((3 : ℝ) / 2) ^ (r + k * m)) := by
  have hξ : ((3 : ℝ) / 2) ^ r ≠ 0 := by positivity
  have h := M5_ap hk (((3 : ℝ) / 2) ^ r) hξ s
  refine Filter.Frequently.mono h fun m hm => ?_
  have hrw : ((3 : ℝ) / 2) ^ (r + k * m) = ((3 : ℝ) / 2) ^ r * (((3 : ℝ) / 2) ^ k) ^ m := by
    rw [pow_add, pow_mul]
  rwa [hrw]

/-! ## Sanity checks -/

theorem oddNum_examples : oddNum 1 = 1 ∧ oddNum 2 = 1 ∧ oddNum 3 = 3 ∧ oddNum 4 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem x_one : x 1 = 1 / 2 := by
  rw [x_eq]
  norm_num [oddNum]

end Z32
