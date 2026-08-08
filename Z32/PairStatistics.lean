/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DyadicOrbit
import ForMathlib.Data.Real.NearestInt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Pair statistics, window energies, and the Weyl collapse (plan-A6+, WP0)

The statistics of the rebuilt angle A6′ (`plans/plan-A6+.html` §1, §5 WP0), stated once so that
every later work package quotes them rather than re-deriving them:

* **the lag identity** — `x_{m+d} - x_m ≡ ((3/2)^d - 1)(3/2)^m (mod 1)`, so a pair event at lag `d`
  is a *single-orbit* event for the multiplier `(3/2)^d - 1` (`Z32.fract_lag`);
* **the lag decomposition** — `P_N(s) = Σ_d C_N(s,d)` (`Z32.pairCount_eq_sum_lagCount`), finite
  bookkeeping, the report's Defect 1 made explicit;
* **the window energy** `E_N(w) = Σ_b A_N(w,b)²` with the exact L² defect identity and the cost of
  an empty window (`Z32.energy_defect`, `Z32.energy_ge_of_empty`): a window missed for `N` steps
  costs `N²/4ʷ` of energy — the quantitative form of "M6 fails here";
* **the Weyl collapse** — `|S_N(2h) - S_N(3h)| ≤ 2` for *every* `h` (`Z32.weylSum_collapse`,
  correction C8): an exact consequence of `2·(3/2)^{n+1} = 3·(3/2)^n`, so the whole Weyl family is
  constant along the lines `{2^a 3^b m : a + b = c}` and only the skeleton `gcd(m,6) = 1` carries
  independent information;
* **the Fourier energy** `𝓔_N(H) = Σ_{|h|≤H} |S_N(h)|²` and its exact pair expansion
  (`Z32.fourierEnergy_eq_pair_sum`).

Two boundary warnings recorded in C8 and *not* formalized here because they are no-gos rather than
theorems: the family is van-der-Corput-closed (differencing maps it into itself, so vdC iteration
alone can never produce a saving), and a 3-smooth-spectrum minorant of a short interval does not
exist for sparsity reasons.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`.  Nothing here is conditional on anything.

## Claim level

Formalization only.  Every statement is an identity or an elementary inequality; the mathematical
content of the plan sits in what these statistics are *used for* (WP2–WP5), not in the statistics.

## References

* `plans/plan-A6+.html` §1 (the statistics `A_N`, `E_N`, `C_N(s,d)`, `𝓔_N(H)`), C4 (why linear
  forms in logarithms cannot bound `C_N(s,d)` below the trivial separation), C8 (the collapse),
  C10a (the lag decomposition).
* `plans/report2-weyl.html` §6.4 (the van-der-Corput self-map at `ξ = 1`).
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, Acta Arith. **70.2** (1995), 125–147 — the
  decoupling identity behind the collapse (`FLP/Decoupling.lean`).
-/

namespace Z32

open Filter Topology

/-! ## The lag identity

A pair event `‖x_{m+d} - x_m‖ ≤ ε` is not a two-point condition: it is the one-point condition
`‖((3/2)^d - 1)(3/2)^m‖ ≤ ε` for a *fixed* multiplier.  This is what makes the lag-stratified
statistic `C_N(s,d)` the right object, and it is also where C4's no-go lives: the free integer in
that inequality has height `≍ m`. -/

/-- **The lag identity.**  Mod one, the gap at lag `d` is the orbit of the multiplier `βᵈ - 1`. -/
theorem fract_lag (β ξ : ℝ) (m d : ℕ) :
    Int.fract (ξ * β ^ (m + d) - ξ * β ^ m) = Int.fract ((β ^ d - 1) * (ξ * β ^ m)) := by
  congr 1
  rw [pow_add]
  ring

/-- The same identity for the distance to the nearest integer, the gauge the pair statistics use. -/
theorem dist_lag (β ξ : ℝ) (m d : ℕ) :
    distToNearestInt (ξ * β ^ (m + d) - ξ * β ^ m)
      = distToNearestInt ((β ^ d - 1) * (ξ * β ^ m)) := by
  congr 1
  rw [pow_add]
  ring

/-- Fractional parts see only the difference: `{x} - {y} ≡ x - y (mod 1)`. -/
theorem fract_sub_fract (a b : ℝ) :
    Int.fract (Int.fract a - Int.fract b) = Int.fract (a - b) := by
  have h : Int.fract a - Int.fract b = a - b + ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) := by
    rw [Int.fract, Int.fract]
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

/-! ## Pair counts and the lag decomposition -/

open scoped Classical in
/-- `C_N(s,d)` — the dates `m` with `m + d < N` whose gap at lag `d` is at most `s/N`. -/
noncomputable def lagCount (β ξ s : ℝ) (N d : ℕ) : ℕ :=
  ((Finset.range (N - d)).filter fun m =>
    distToNearestInt ((β ^ d - 1) * (ξ * β ^ m)) ≤ s / N).card

open scoped Classical in
/-- `P_N(s)` — the ordered pairs `m < n < N` whose gap is at most `s/N`. -/
noncomputable def pairCount (β ξ s : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N ×ˢ Finset.range N).filter fun p =>
    p.1 < p.2 ∧ distToNearestInt (ξ * β ^ p.2 - ξ * β ^ p.1) ≤ s / N).card

/-- **The lag decomposition.**  Every pair contributes to exactly one lag. -/
theorem pairCount_eq_sum_lagCount (β ξ s : ℝ) (N : ℕ) :
    pairCount β ξ s N = ∑ d ∈ Finset.Ico 1 N, lagCount β ξ s N d := by
  classical
  set P : Finset (ℕ × ℕ) := (Finset.range N ×ˢ Finset.range N).filter fun p =>
    p.1 < p.2 ∧ distToNearestInt (ξ * β ^ p.2 - ξ * β ^ p.1) ≤ s / N with hP
  have hmem : ∀ p : ℕ × ℕ, p ∈ P ↔
      (p.1 < N ∧ p.2 < N ∧ p.1 < p.2 ∧
        distToNearestInt (ξ * β ^ p.2 - ξ * β ^ p.1) ≤ s / N) := by
    intro p
    simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) (Finset.Ico 1 N) := by
    intro p hp
    obtain ⟨h1, h2, h3, -⟩ := (hmem p).mp (Finset.mem_coe.mp hp)
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  rw [pairCount, ← hP, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, hd2⟩ := Finset.mem_Ico.mp hd
  rw [lagCount]
  refine Finset.card_bij' (fun p _ => p.1) (fun m _ => (m, m + d)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := (hmem p).mp hpP
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have hsplit : p.1 + d = p.2 := by omega
    have := h4
    rwa [← hsplit, dist_lag] at this
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    have hm1' : m < N - d := Finset.mem_range.mp hm1
    refine Finset.mem_filter.mpr ⟨(hmem _).mpr ⟨by omega, by omega, by omega, ?_⟩, by simp⟩
    rw [dist_lag]
    exact hm2
  · intro p hp
    obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := (hmem p).mp hpP
    have : p.1 + d = p.2 := by omega
    simp [this]
  · intro m _
    rfl

/-! ## Dyadic cells, window counts, and the energy

The level-`w` cells partition the circle, so the window counts `A_N(w,b)` sum to `N`; the energy
`E_N(w) = Σ_b A_N(w,b)²` therefore obeys an exact L² defect identity.  The consequence the M6
program uses: a window that receives *no* visit in `N` steps costs `N²/4ʷ` of energy. -/

/-- The level-`w` cell index of a real number: `⌊2ʷ {y}⌋`. -/
noncomputable def cell (w : ℕ) (y : ℝ) : ℕ := ⌊(2 : ℝ) ^ w * Int.fract y⌋₊

theorem cell_lt (w : ℕ) (y : ℝ) : cell w y < 2 ^ w := by
  have hne : (2 : ℕ) ^ w ≠ 0 := by positivity
  rw [cell, Nat.floor_lt' hne]
  have h1 : Int.fract y < 1 := Int.fract_lt_one y
  have h2 : (0 : ℝ) < 2 ^ w := by positivity
  have : (2 : ℝ) ^ w * Int.fract y < 2 ^ w * 1 := by
    exact mul_lt_mul_of_pos_left h1 h2
  push_cast
  linarith

/-- **The cell dictionary.**  For `b < 2ʷ`, membership in the dyadic window `[b/2ʷ, (b+1)/2ʷ)` is
the statement that the cell index is `b`.  (No wrap-around: the window sits inside `[0,1)`.) -/
theorem inArc_dyadic_iff {w b : ℕ} (hb : b < 2 ^ w) (y : ℝ) :
    inArc ((b : ℝ) / 2 ^ w) (1 / 2 ^ w) y ↔ cell w y = b := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  set P : ℝ := (2 : ℝ) ^ w with hPdef
  set f : ℝ := Int.fract y with hfdef
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hbP : (b : ℝ) + 1 ≤ P := by
    have h : b + 1 ≤ 2 ^ w := hb
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / P := by positivity
  have hb1 : (b : ℝ) / P < 1 := (div_lt_one h2).mpr (by linarith)
  have hbq : (b : ℝ) / P + 1 / P = ((b : ℝ) + 1) / P := by ring
  have hshift : Int.fract (y - (b : ℝ) / P) = Int.fract (f - (b : ℝ) / P) := by
    have h : f - (b : ℝ) / P = y - (b : ℝ) / P + ((-⌊y⌋ : ℤ) : ℝ) := by
      rw [hfdef, Int.fract]
      push_cast
      ring
    rw [h, Int.fract_add_intCast]
  have hcelliff : cell w y = b ↔ (b : ℝ) ≤ f * P ∧ f * P < (b : ℝ) + 1 := by
    rw [cell, ← hfdef, ← hPdef, mul_comm]
    exact Nat.floor_eq_iff (by positivity)
  rw [hcelliff]
  constructor
  · intro hmem
    have hmem' : Int.fract (f - (b : ℝ) / P) < 1 / P := by rw [← hshift]; exact hmem
    rcases le_or_gt ((b : ℝ) / P) f with hge | hlt
    · have heq : Int.fract (f - (b : ℝ) / P) = f - (b : ℝ) / P :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [heq] at hmem'
      refine ⟨(div_le_iff₀ h2).mp hge, ?_⟩
      have hup : f < ((b : ℝ) + 1) / P := by linarith [hbq]
      exact (lt_div_iff₀ h2).mp hup
    · exfalso
      have hneg : f - (b : ℝ) / P < 0 := by linarith
      have heq : Int.fract (f - (b : ℝ) / P) = f - (b : ℝ) / P + 1 := by
        have h1 : f - (b : ℝ) / P + ((1 : ℤ) : ℝ) = f - (b : ℝ) / P + 1 := by push_cast; ring
        rw [← Int.fract_add_intCast (f - (b : ℝ) / P) 1, h1]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [heq] at hmem'
      have hone : ((b : ℝ) + 1) / P ≤ 1 := (div_le_one h2).mpr hbP
      linarith [hbq]
  · rintro ⟨hle, hlt⟩
    have hge : (b : ℝ) / P ≤ f := (div_le_iff₀ h2).mpr hle
    have hup : f < ((b : ℝ) + 1) / P := (lt_div_iff₀ h2).mpr hlt
    have heq : Int.fract (f - (b : ℝ) / P) = f - (b : ℝ) / P :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    show Int.fract (y - (b : ℝ) / P) < 1 / P
    rw [hshift, heq]
    linarith [hbq]

/-- `A_N(w,b)` — the number of visits to the level-`w` dyadic window `b` before time `N`. -/
noncomputable def winCount (β ξ : ℝ) (w b N : ℕ) : ℕ :=
  visitCount β ξ ((b : ℝ) / 2 ^ w) (1 / 2 ^ w) N

/-- The level-`w` windows partition the dates: `Σ_b A_N(w,b) = N`. -/
theorem sum_winCount (β ξ : ℝ) (w N : ℕ) :
    ∑ b ∈ Finset.range (2 ^ w), winCount β ξ w b N = N := by
  classical
  have hmaps : Set.MapsTo (fun n => cell w (ξ * β ^ n)) (Finset.range N : Set ℕ)
      (Finset.range (2 ^ w)) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact cell_lt w _
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_range] at hcard
  have hfib : ∀ b ∈ Finset.range (2 ^ w), winCount β ξ w b N
      = ((Finset.range N).filter fun n => cell w (ξ * β ^ n) = b).card := by
    intro b hb
    have hb' : b < 2 ^ w := Finset.mem_range.mp hb
    rw [winCount, visitCount, visits]
    exact congrArg Finset.card (Finset.filter_congr fun n _ => inArc_dyadic_iff hb' (ξ * β ^ n))
  rw [Finset.sum_congr rfl hfib, ← hcard]

/-- `E_N(w) = Σ_b A_N(w,b)²`, the level-`w` window energy. -/
noncomputable def energy (β ξ : ℝ) (w N : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (2 ^ w), (winCount β ξ w b N) ^ 2

/-- **The L² defect identity.**  The energy exceeds its equidistributed value `N²/2ʷ` by exactly
the squared deviation of the window counts. -/
theorem energy_defect (β ξ : ℝ) (w N : ℕ) :
    ∑ b ∈ Finset.range (2 ^ w), ((winCount β ξ w b N : ℝ) - (N : ℝ) / 2 ^ w) ^ 2
      = (energy β ξ w N : ℝ) - (N : ℝ) ^ 2 / 2 ^ w := by
  have h2 : (0 : ℝ) < 2 ^ w := by positivity
  have hsum : ∑ b ∈ Finset.range (2 ^ w), (winCount β ξ w b N : ℝ) = (N : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (sum_winCount β ξ w N)
  have hcard : ((Finset.range (2 ^ w)).card : ℝ) = 2 ^ w := by
    rw [Finset.card_range]
    push_cast
    ring
  have hexp : ∀ b : ℕ, ((winCount β ξ w b N : ℝ) - (N : ℝ) / 2 ^ w) ^ 2
      = (winCount β ξ w b N : ℝ) ^ 2 - 2 * ((N : ℝ) / 2 ^ w) * (winCount β ξ w b N : ℝ)
        + ((N : ℝ) / 2 ^ w) ^ 2 := by
    intro b; ring
  rw [Finset.sum_congr rfl fun b _ => hexp b]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, hsum, hcard]
  have henergy : ∑ b ∈ Finset.range (2 ^ w), (winCount β ξ w b N : ℝ) ^ 2
      = (energy β ξ w N : ℝ) := by
    rw [energy]
    push_cast
    ring
  rw [henergy]
  field_simp
  ring

/-- Cauchy–Schwarz, free from the defect identity: the energy is never below `N²/2ʷ`. -/
theorem energy_ge (β ξ : ℝ) (w N : ℕ) : (N : ℝ) ^ 2 / 2 ^ w ≤ (energy β ξ w N : ℝ) := by
  have h := energy_defect β ξ w N
  have hnn : 0 ≤ ∑ b ∈ Finset.range (2 ^ w), ((winCount β ξ w b N : ℝ) - (N : ℝ) / 2 ^ w) ^ 2 :=
    Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith

/-- **The cost of an empty window.**  A level-`w` window that receives no visit before time `N`
forces `N²/4ʷ` of excess energy.  This is the statistic M6 is about: M6 fails at a window exactly
when this excess persists with positive density. -/
theorem energy_ge_of_empty {β ξ : ℝ} {w b N : ℕ} (hb : b < 2 ^ w) (h : winCount β ξ w b N = 0) :
    (N : ℝ) ^ 2 / 2 ^ w + (N : ℝ) ^ 2 / 4 ^ w ≤ (energy β ξ w N : ℝ) := by
  have hdef := energy_defect β ξ w N
  have hmem : b ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr hb
  have hterm : ((N : ℝ) ^ 2 / 4 ^ w)
      ≤ ∑ b' ∈ Finset.range (2 ^ w), ((winCount β ξ w b' N : ℝ) - (N : ℝ) / 2 ^ w) ^ 2 := by
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun b' => ((winCount β ξ w b' N : ℝ) - (N : ℝ) / 2 ^ w) ^ 2)
        (fun b' _ => sq_nonneg _) hmem)
    have hpow : ((2 : ℝ) ^ w) ^ 2 = 4 ^ w := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h]
    push_cast
    rw [zero_sub, neg_sq, div_pow, hpow]
  linarith

/-! ## Weyl sums and the collapse

`2·(3/2)^{n+1} = 3·(3/2)^n` holds **exactly**, so the summand of `S_N(2h)` at date `n+1` is the
summand of `S_N(3h)` at date `n`: the two sums differ by their two boundary terms, whatever `h`,
whatever `ξ`.  Testing frequencies is therefore only informative on the skeleton `gcd(m,6) = 1`
(C8). -/

/-- `e(y) = exp(2πiy)`. -/
noncomputable def ex (y : ℝ) : ℂ := Complex.exp ((2 * Real.pi * y : ℝ) * Complex.I)

theorem norm_ex (y : ℝ) : ‖ex y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem ex_add (a b : ℝ) : ex a * ex b = ex (a + b) := by
  rw [ex, ex, ex, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_ex (y : ℝ) : (starRingEnd ℂ) (ex y) = ex (-y) := by
  rw [ex, ex, ← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- `S_N(h) = Σ_{n<N} e(h·ξβⁿ)`. -/
noncomputable def weylSum (β ξ : ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ex ((h : ℝ) * (ξ * β ^ n))

theorem norm_weylSum_le (β ξ : ℝ) (h : ℤ) (N : ℕ) : ‖weylSum β ξ h N‖ ≤ N := by
  refine le_trans (norm_sum_le _ _) ?_
  simp [norm_ex]

/-- **The exact shift.**  At base `3/2` the summand of `S(2h)` at date `n+1` *is* the summand of
`S(3h)` at date `n`. -/
theorem ex_shift (ξ : ℝ) (h : ℤ) (n : ℕ) :
    ex (((2 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ (n + 1)))
      = ex (((3 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ n)) := by
  congr 1
  rw [pow_succ]
  push_cast
  ring

/-- **The Weyl collapse (C8).**  `|S_N(2h) - S_N(3h)| ≤ 2` for every `h`, every `ξ`, every `N`. -/
theorem weylSum_collapse (ξ : ℝ) (h : ℤ) (N : ℕ) :
    ‖weylSum ((3 : ℝ) / 2) ξ (2 * h) N - weylSum ((3 : ℝ) / 2) ξ (3 * h) N‖ ≤ 2 := by
  have hsucc : weylSum ((3 : ℝ) / 2) ξ (2 * h) (N + 1)
      = weylSum ((3 : ℝ) / 2) ξ (2 * h) N + ex (((2 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ N)) :=
    Finset.sum_range_succ _ N
  have hsucc' : weylSum ((3 : ℝ) / 2) ξ (2 * h) (N + 1)
      = weylSum ((3 : ℝ) / 2) ξ (3 * h) N + ex (((2 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ 0)) := by
    simp only [weylSum]
    rw [Finset.sum_range_succ']
    congr 1
    exact Finset.sum_congr rfl fun n _ => ex_shift ξ h n
  have hdiff : weylSum ((3 : ℝ) / 2) ξ (2 * h) N - weylSum ((3 : ℝ) / 2) ξ (3 * h) N
      = ex (((2 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ 0))
        - ex (((2 * h : ℤ) : ℝ) * (ξ * ((3 : ℝ) / 2) ^ N)) := by
    rw [hsucc] at hsucc'
    linear_combination hsucc'
  rw [hdiff]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_ex, norm_ex]
  norm_num

/-! ## The Fourier energy -/

/-- `𝓔_N(H) = Σ_{|h| ≤ H} |S_N(h)|²`. -/
noncomputable def fourierEnergy (β ξ : ℝ) (H N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), ‖weylSum β ξ h N‖ ^ 2

/-- **The pair expansion.**  `|S_N(h)|²` is the pair sum of `e(h(x_m - x_n))`. -/
theorem normSq_weylSum_eq (β ξ : ℝ) (h : ℤ) (N : ℕ) :
    ((‖weylSum β ξ h N‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ex ((h : ℝ) * (ξ * β ^ m - ξ * β ^ n)) := by
  have hconj : ((‖weylSum β ξ h N‖ ^ 2 : ℝ) : ℂ)
      = weylSum β ξ h N * (starRingEnd ℂ) (weylSum β ξ h N) := by
    rw [Complex.mul_conj]
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Complex.sq_norm (weylSum β ξ h N))
  rw [hconj, weylSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [conj_ex, ex_add]
  congr 1
  ring

/-- The Fourier energy is the double sum of the Dirichlet kernel along the pairs. -/
theorem fourierEnergy_eq_pair_sum (β ξ : ℝ) (H N : ℕ) :
    ((fourierEnergy β ξ H N : ℝ) : ℂ)
      = ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ex ((h : ℝ) * (ξ * β ^ m - ξ * β ^ n)) := by
  rw [fourierEnergy, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun h _ => normSq_weylSum_eq β ξ h N

/-- The trivial floor: the zero frequency alone contributes `N²`. -/
theorem sq_le_fourierEnergy (β ξ : ℝ) (H N : ℕ) : (N : ℝ) ^ 2 ≤ fourierEnergy β ξ H N := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hzero : ‖weylSum β ξ 0 N‖ ^ 2 = (N : ℝ) ^ 2 := by
    have : weylSum β ξ 0 N = (N : ℂ) := by
      rw [weylSum]
      simp [ex]
    rw [this]
    simp
  rw [fourierEnergy, ← hzero]
  exact Finset.single_le_sum (f := fun h => ‖weylSum β ξ h N‖ ^ 2) (fun h _ => sq_nonneg _) hmem

end Z32
