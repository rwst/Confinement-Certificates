/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.PairStatistics
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

/-!
# Balance vectors: the finite-resolution form of the M6 enemy (plan-A6+, WP1)

`plans/plan-A6+.html` C6 asks for the two-front architecture in a form Lean can hold *today*:
instead of weak-\* limits of empirical measures on the solenoid (risk R-G, unsurveyed at the time),
work at finite resolution with **level-`w` frequency vectors** and the **flow-conservation
equations** of the level-`w` carry graph.  This file is that layer.  See "The measure formulation"
below for the current status of that deferral — the gap has since half closed, and it does not
change what is proved here.

## The objects

* `Z32.edgeOk w b b'` — the **level-`w` carry graph**.  At `ξ = 1` consecutive orbit points obey
  `2x_{n+1} = 3xₙ - sₙ` with an integer carry `sₙ ∈ {-1,0,1,2}` (`Z32.exists_carry`); the edge test
  asks whether *some* point of the window `b` is carried into the window `b'` by one branch.  After
  scaling by `2ʷ` this is an intersection of two integer intervals, so `edgeOk` is a `Bool` the
  kernel evaluates (`Z32.edgeOk_complete_two`).
* `Z32.freqVec`, `Z32.flowVec` — the empirical frequency vector `A_N(w,b)/N` and the empirical edge
  flow `#{n < N : cellₙ = b, cell_{n+1} = b'}/N`.
* `Z32.BalanceVec w` — a **balance vector**: a probability vector `μ` on the level-`w` cells and a
  nonnegative flow `ν` on the edges with `Σ_{b'} ν(b,b') = μ(b) = Σ_{b'} ν(b',b)` (conservation)
  and `ν` supported on the graph.  Pure finite linear algebra: no measure theory anywhere.

## The results

* `Z32.exists_balanceVec` — **the balance lemma**.  Along any sequence of horizons `N k → ∞` the
  empirical flow vectors have a limit point, and every limit point *is* a balance vector whose mass
  vector is the limit of the empirical frequency vectors.  (Bolzano–Weierstrass on `[0,1]^{E}`; the
  out-marginal is exact, the in-marginal costs the two boundary dates, `≤ 1/N`.)
* `Z32.exists_balanceVec_zero_of_not_V4` — **the enemy statement (C6)**.  If the window `(w,b)`
  fails M6 — no positive lower density — then the level-`w` carry graph carries a stationary vector
  with **zero mass at `b`**.  Its support is a `Z32.IsTrap`: a nonempty set of cells closed under
  taking some successor and some predecessor, i.e. a subgraph carrying a cycle that avoids `b`.
* `Z32.V4_of_forall_trap_mem` — the criterion in contrapositive form: if *every* trap of the
  level-`w` graph contains `b`, then the window `(w,b)` has positive lower density.
* `Z32.exists_trap_not_mem` — and the criterion's hypothesis is never satisfiable (`w ≥ 2`).
* `Z32.exists_balanceVec_zero` — **and the criterion is vacuous at every level.**  For every
  `w ≥ 2` and every window `b` there is a balance vector with zero mass at `b`: the fixed point `0`
  gives a self-loop at the cell of `0`, and the rational 2-cycle `{2/5, 3/5}` (denominator
  `5 = 3² - 2²`, the [L90] shape) gives a cycle avoiding it.  So no level-`w` balance argument can
  prove M6 at any window, at any resolution — the flow layer alone never excludes the *atomic*
  (cycle) enemies.  This is C6's "the stationary vectors supported on proper subgraphs are exactly
  the cycle enemies", proved rather than asserted, and it is why Front D of the plan is Diophantine
  and not dynamical.
* `Z32.cycle_point_eq`, `Z32.dist_cycle_point` — **the cycle-point classification** promised by
  WP1: a `p`-periodic point of the carry relation is `A/(3^p - 2^p)` with `3^p - 2^p` **odd** (the
  [L90] rational-cycle shape), so `Z32.dist_odd_denom` applies to it and the `ξ = 1` orbit stays
  `≥ 1/((3^p-2^p)2ⁿ)` away from every `p`-cycle — the quantitative floor C7/WP2 runs on.

## The measure formulation (status of risk R-G; hygiene item H3, 2026-08-01)

The deferral above was recorded as risk R-G — "the weak-\* machinery is unsurveyed, attacking WP1
through `ProbabilityMeasure` sinks it".  **Its compactness half has closed upstream.**
`Mathlib.MeasureTheory.Measure.Prokhorov` now supplies
`instCompactSpaceProbabilityMeasure : CompactSpace E → CompactSpace (ProbabilityMeasure E)` together
with the tightness variants (`isCompact_closure_of_isTightMeasureSet` and friends), and
`Measure.Tight`, `Measure.LevyProkhorovMetric`, `Measure.Portmanteau` sit beside it — so limit
measures of empirical measures on a compact metrizable solenoid exist by *instance search*, not by
hand.  The measure-theoretic form of this file is therefore **scheduled rather than blocked**:
`TH/Solenoid/LimitMeasures.lean` (`plans/plan-A1+.html` L4–L5, work package W4) is where
`empirical`, `limitMeasures`, invariance under the doubling map, and `u.d. ⟺ {Haar}` go, on
`Σ₆ = (ℝ × ℚ₂ × ℚ₃)/ℤ[1/6]`.  What is still genuinely absent (probe `plan-A1+` §3.3, re-checked
2026-08-01) is the *solenoid type* itself — none upstream, none repo-wide — and **measure-theoretic
(Kolmogorov–Sinai) entropy**, which `ForMathlib` must supply; Mathlib has only
`Dynamics.TopologicalEntropy`.

**None of this weakens the theorems below, and the vacuity result is not an artifact of finite
resolution.**  `exists_balanceVec_zero` holds at *every* level `w ≥ 2`, and its two witnesses are
genuine points of the orbit closure — the fixed point `0` and the rational 2-cycle `{2/5, 3/5}` —
whose Dirac and cycle-averaged measures are invariant measures upstairs as well.  A solenoid version
inherits exactly the same atomic enemies.  Passing to measures buys resolution, not the missing
hypothesis: that stays Front D (Diophantine, atomic exclusion), which is C6's point and claim-ledger
entry L-24.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`.

## Claim level

Formalization only.  Flow conservation for empirical vectors is standard (it is the finite form of
"empirical limits are invariant"); the cycle-denominator computation is [L90] arithmetic.  What is
new here is only the *bookkeeping*: the level-`w` carry graph as a kernel-checkable `Bool`, and the
vacuity theorem `Z32.exists_balanceVec_zero`, which records once and for all what this layer cannot
do (L-23 discipline: the objects are new, the mathematics is not).

## References

* `plans/plan-A6+.html` C6 (the two-front architecture and the balance-vector formulation),
  §5 WP1 (this file), §7 R-G (the deferral of the measure formulation; fired and mitigated
  2026-07-31), §6 L-24 (the ledger entry this file's vacuity theorem backs).
* `plans/plan-A1+.html` §3.3 (the Mathlib probe that closed R-G's compactness half), L4–L5/W4
  (`TH/Solenoid/LimitMeasures.lean`, the successor file), §6.3 H3 (this note).
* [L90] J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56**
  (1990) — the odd denominator `3^p - 2^p` (corpus root `L90/`).
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, Acta Arith. **70.2** (1995), 125–147 — the
  decoupling identity behind the carry step (`FLP/Decoupling.lean`).
-/

namespace Z32

open Filter Topology

/-! ## The carry step at `ξ = 1`

`2·(3/2)^{n+1} = 3·(3/2)^n` holds exactly, so subtracting integer parts gives an integer carry.
Its range is forced by `xₙ, x_{n+1} ∈ [0,1)`: the alphabet is `{-1,0,1,2}`, the four letters of
`Z32.BlockCert.carries 3 2`. -/

/-- **The carry step.**  `2x_{n+1} = 3xₙ - sₙ` with `sₙ` an integer in `{-1,0,1,2}`. -/
theorem exists_carry (n : ℕ) :
    ∃ s : ℤ, 2 * x (n + 1) = 3 * x n - (s : ℝ) ∧ -1 ≤ s ∧ s ≤ 2 := by
  refine ⟨2 * ⌊((3 : ℝ) / 2) ^ (n + 1)⌋ - 3 * ⌊((3 : ℝ) / 2) ^ n⌋, ?_, ?_, ?_⟩
  · have hpow : ((3 : ℝ) / 2) ^ (n + 1) = (3 / 2) * (3 / 2) ^ n := by ring
    simp only [x, Int.fract]
    push_cast
    rw [hpow]
    ring
  all_goals {
    have heq : ((2 * ⌊((3 : ℝ) / 2) ^ (n + 1)⌋ - 3 * ⌊((3 : ℝ) / 2) ^ n⌋ : ℤ) : ℝ)
        = 3 * x n - 2 * x (n + 1) := by
      have hpow : ((3 : ℝ) / 2) ^ (n + 1) = (3 / 2) * (3 / 2) ^ n := by ring
      simp only [x, Int.fract]
      push_cast
      rw [hpow]
      ring
    have h0 : (0 : ℝ) ≤ x n := Int.fract_nonneg _
    have h0' : (0 : ℝ) ≤ x (n + 1) := Int.fract_nonneg _
    have h1 : x n < 1 := x_lt_one n
    have h1' : x (n + 1) < 1 := x_lt_one (n + 1)
    first
      | (have : ((-1 : ℤ) : ℝ) < ((2 * ⌊((3 : ℝ) / 2) ^ (n + 1)⌋
              - 3 * ⌊((3 : ℝ) / 2) ^ n⌋ : ℤ) : ℝ) + 1 := by rw [heq]; push_cast; linarith
         exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this))
      | (have : ((2 * ⌊((3 : ℝ) / 2) ^ (n + 1)⌋ - 3 * ⌊((3 : ℝ) / 2) ^ n⌋ : ℤ) : ℝ)
              < ((3 : ℤ) : ℝ) := by rw [heq]; push_cast; linarith
         exact Int.lt_add_one_iff.mp (by exact_mod_cast this)) }

/-! ## The level-`w` carry graph

An edge `b → b'` records that *some* point of the window `b` is carried into the window `b'`.  This
is weaker than any invariance statement — deliberately so: it is the largest graph the orbit is
guaranteed to walk in, and the whole point of the vacuity theorem below is that this is too weak to
exclude cycles.  Scaled by `2ʷ`, the branch-`s` condition is the meeting of `[3b, 3b+3) - s·2ʷ`
with `[2b', 2b'+2)`, an integer test. -/

/-- The carry alphabet at base `3/2`: the four letters of `Z32.BlockCert.carries 3 2`. -/
def carryAlphabet : List ℤ := [-1, 0, 1, 2]

/-- The branch-`s` edge test at level `w`, scaled by `2ʷ`. -/
def edgeVia (w b b' : ℕ) (s : ℤ) : Bool :=
  decide (max (3 * (b : ℤ) - s * 2 ^ w) (2 * (b' : ℤ))
    < min (3 * (b : ℤ) + 3 - s * 2 ^ w) (2 * (b' : ℤ) + 2))

/-- **The level-`w` carry graph.**  `edgeOk w b b'` iff some point of the level-`w` window `b` is
carried into the window `b'` by one branch `2y' = 3y - s` of the carry relation. -/
def edgeOk (w b b' : ℕ) : Bool := carryAlphabet.any (edgeVia w b b')

theorem edgeOk_of_edgeVia {w b b' : ℕ} {s : ℤ} (hs : s ∈ carryAlphabet)
    (h : edgeVia w b b' s = true) : edgeOk w b b' = true :=
  List.any_eq_true.mpr ⟨s, hs, h⟩

/-- **Realized transitions are edges.**  Any two points of `[0,1)` linked by a branch of the carry
relation give an edge between their level-`w` cells. -/
theorem edgeOk_of_step {w : ℕ} {y y' : ℝ} {s : ℤ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hy'0 : 0 ≤ y') (hy'1 : y' < 1) (h : 2 * y' = 3 * y - (s : ℝ)) :
    edgeOk w (cell w y) (cell w y') = true := by
  have hfy : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, hy1⟩
  have hfy' : Int.fract y' = y' := Int.fract_eq_self.mpr ⟨hy'0, hy'1⟩
  have h2 : (0 : ℝ) < 2 ^ w := by positivity
  set b : ℕ := cell w y with hb
  set b' : ℕ := cell w y' with hb'
  have hb1 : (b : ℝ) ≤ 2 ^ w * Int.fract y :=
    Nat.floor_le (mul_nonneg (by positivity) (Int.fract_nonneg y))
  have hb2 : (2 : ℝ) ^ w * Int.fract y < b + 1 := Nat.lt_floor_add_one _
  have hb1' : (b' : ℝ) ≤ 2 ^ w * Int.fract y' :=
    Nat.floor_le (mul_nonneg (by positivity) (Int.fract_nonneg y'))
  have hb2' : (2 : ℝ) ^ w * Int.fract y' < b' + 1 := Nat.lt_floor_add_one _
  rw [hfy] at hb1 hb2
  rw [hfy'] at hb1' hb2'
  -- the alphabet bound
  have hsR : (s : ℝ) = 3 * y - 2 * y' := by linarith
  have hs1 : (-1 : ℤ) ≤ s := by
    have : ((-2 : ℤ) : ℝ) < (s : ℝ) := by push_cast; rw [hsR]; linarith
    have : (-2 : ℤ) < s := by exact_mod_cast this
    omega
  have hs2 : s ≤ 2 := by
    have : (s : ℝ) < ((3 : ℤ) : ℝ) := by push_cast; rw [hsR]; linarith
    have : s < 3 := by exact_mod_cast this
    omega
  have hsmem : s ∈ carryAlphabet := by
    have : s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2 := by omega
    rcases this with h | h | h | h <;> simp [carryAlphabet, h]
  refine edgeOk_of_edgeVia hsmem ?_
  -- the four interval inequalities, transported from `ℝ`
  have hv : (2 : ℝ) * (2 ^ w * y') = 3 * (2 ^ w * y) - (s : ℝ) * 2 ^ w := by
    have : (2 : ℝ) ^ w * (2 * y') = 2 ^ w * (3 * y - (s : ℝ)) := by rw [h]
    nlinarith [this]
  have e1 : ((3 * (b : ℤ) - s * 2 ^ w : ℤ) : ℝ) ≤ 2 * (2 ^ w * y') := by
    push_cast
    linarith
  have e2 : (2 : ℝ) * (2 ^ w * y') < ((3 * (b : ℤ) + 3 - s * 2 ^ w : ℤ) : ℝ) := by
    push_cast
    linarith
  have e3 : ((2 * (b' : ℤ) : ℤ) : ℝ) ≤ 2 * (2 ^ w * y') := by push_cast; linarith
  have e4 : (2 : ℝ) * (2 ^ w * y') < ((2 * (b' : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
  have f1 : (3 * (b : ℤ) - s * 2 ^ w) < 3 * (b : ℤ) + 3 - s * 2 ^ w := by omega
  have f2 : (3 * (b : ℤ) - s * 2 ^ w) < 2 * (b' : ℤ) + 2 := by
    have : ((3 * (b : ℤ) - s * 2 ^ w : ℤ) : ℝ) < ((2 * (b' : ℤ) + 2 : ℤ) : ℝ) := lt_of_le_of_lt e1 e4
    exact_mod_cast this
  have f3 : (2 * (b' : ℤ)) < 3 * (b : ℤ) + 3 - s * 2 ^ w := by
    have : ((2 * (b' : ℤ) : ℤ) : ℝ) < ((3 * (b : ℤ) + 3 - s * 2 ^ w : ℤ) : ℝ) :=
      lt_of_le_of_lt e3 e2
    exact_mod_cast this
  have f4 : (2 * (b' : ℤ)) < 2 * (b' : ℤ) + 2 := by omega
  simp only [edgeVia, decide_eq_true_eq]
  exact max_lt (lt_min f1 f2) (lt_min f3 f4)

/-- Cells depend only on the fractional part. -/
theorem cell_fract (w : ℕ) (y : ℝ) : cell w (Int.fract y) = cell w y := by
  rw [cell, cell, Int.fract_fract]

/-- **The orbit walks in the graph.**  Consecutive cells of the `ξ = 1` orbit are joined by an
edge of the level-`w` carry graph. -/
theorem edgeOk_orbit (w n : ℕ) :
    edgeOk w (cell w (1 * ((3 : ℝ) / 2) ^ n)) (cell w (1 * ((3 : ℝ) / 2) ^ (n + 1))) = true := by
  obtain ⟨s, hs, -, -⟩ := exists_carry n
  have h1 : cell w (1 * ((3 : ℝ) / 2) ^ n) = cell w (x n) := by
    rw [x, cell_fract, one_mul]
  have h2 : cell w (1 * ((3 : ℝ) / 2) ^ (n + 1)) = cell w (x (n + 1)) := by
    rw [x, cell_fract, one_mul]
  rw [h1, h2]
  exact edgeOk_of_step (Int.fract_nonneg _) (x_lt_one n) (Int.fract_nonneg _)
    (x_lt_one (n + 1)) hs

/-! ## Empirical frequency and flow vectors

`freqVec` is the level-`w` histogram of the first `N` dates, `flowVec` the histogram of the first
`N` *transitions*.  The out-marginal of `flowVec` is `freqVec` **exactly**; the in-marginal misses
by at most the two boundary dates. -/

/-- The level-`w` window count as a `Finset.card` of dates — the form every marginal argument
uses. -/
theorem winCount_eq_card (β ξ : ℝ) {w b : ℕ} (hb : b < 2 ^ w) (N : ℕ) :
    winCount β ξ w b N
      = ((Finset.range N).filter fun n => cell w (ξ * β ^ n) = b).card := by
  classical
  rw [winCount, visitCount, visits]
  exact congrArg Finset.card (Finset.filter_congr fun n _ => inArc_dyadic_iff hb (ξ * β ^ n))

open scoped Classical in
/-- The dates `n < N` whose cell is `b` and whose successor's cell is `b'`. -/
noncomputable def edgeCount (β ξ : ℝ) (w b b' N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n =>
    cell w (ξ * β ^ n) = b ∧ cell w (ξ * β ^ (n + 1)) = b').card

/-- The empirical level-`w` frequency vector `φ_N(b) = A_N(w,b)/N`. -/
noncomputable def freqVec (β ξ : ℝ) (w N b : ℕ) : ℝ := (winCount β ξ w b N : ℝ) / N

/-- The empirical level-`w` flow vector on edges. -/
noncomputable def flowVec (β ξ : ℝ) (w N b b' : ℕ) : ℝ := (edgeCount β ξ w b b' N : ℝ) / N

theorem freqVec_eq_visitRatio (β ξ : ℝ) (w N b : ℕ) :
    freqVec β ξ w N b = visitRatio β ξ ((b : ℝ) / 2 ^ w) (1 / 2 ^ w) N := rfl

theorem edgeCount_le (β ξ : ℝ) (w b b' N : ℕ) : edgeCount β ξ w b b' N ≤ N := by
  classical
  have := Finset.card_le_card (Finset.filter_subset
    (fun n => cell w (ξ * β ^ n) = b ∧ cell w (ξ * β ^ (n + 1)) = b') (Finset.range N))
  rwa [Finset.card_range] at this

/-- A nonzero transition count exhibits a date realizing the transition. -/
theorem exists_of_edgeCount_ne_zero {β ξ : ℝ} {w b b' N : ℕ} (h : edgeCount β ξ w b b' N ≠ 0) :
    ∃ n, cell w (ξ * β ^ n) = b ∧ cell w (ξ * β ^ (n + 1)) = b' := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  rw [edgeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n - ⟨h1, h2⟩
  exact hcon n h1 h2

theorem flowVec_nonneg (β ξ : ℝ) (w N b b' : ℕ) : 0 ≤ flowVec β ξ w N b b' :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem flowVec_le_one (β ξ : ℝ) (w N b b' : ℕ) : flowVec β ξ w N b b' ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [flowVec, hN]
  · rw [flowVec, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast edgeCount_le β ξ w b b' N

/-- **The out-marginal is exact**: every date has exactly one successor cell. -/
theorem sum_edgeCount_out (β ξ : ℝ) {w b : ℕ} (hb : b < 2 ^ w) (N : ℕ) :
    ∑ b' ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N = winCount β ξ w b N := by
  classical
  set S : Finset ℕ := (Finset.range N).filter fun n => cell w (ξ * β ^ n) = b with hS
  have hmaps : Set.MapsTo (fun n => cell w (ξ * β ^ (n + 1))) (S : Set ℕ)
      (Finset.range (2 ^ w)) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact cell_lt w _
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  rw [winCount_eq_card β ξ hb N, ← hS, hcard]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [edgeCount, hS, Finset.filter_filter]

/-- **The in-marginal**, exactly: the dates whose *successor* lies in the window `b'`. -/
theorem sum_edgeCount_in (β ξ : ℝ) (w b' N : ℕ) :
    ∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N
      = ((Finset.range N).filter fun n => cell w (ξ * β ^ (n + 1)) = b').card := by
  classical
  set S : Finset ℕ := (Finset.range N).filter fun n => cell w (ξ * β ^ (n + 1)) = b' with hS
  have hmaps : Set.MapsTo (fun n => cell w (ξ * β ^ n)) (S : Set ℕ)
      (Finset.range (2 ^ w)) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact cell_lt w _
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hcard]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [edgeCount, hS, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun n _ => by tauto)

/-- One more date, one more term. -/
private theorem card_filter_range_succ (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    ((Finset.range (N + 1)).filter Q).card
      = ((Finset.range N).filter Q).card + (if Q N then 1 else 0) := by
  classical
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : Q N
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, add_zero]

/-- The shift by one date costs exactly the first term. -/
private theorem card_filter_shift (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    ((Finset.range N).filter fun n => Q (n + 1)).card + (if Q 0 then 1 else 0)
      = ((Finset.range (N + 1)).filter Q).card := by
  classical
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.zero_add,
      Finset.range_one, Finset.filter_singleton]
    split <;> simp
  | succ N ih =>
    rw [card_filter_range_succ (fun n => Q (n + 1)) N, card_filter_range_succ Q (N + 1)]
    omega

/-- **The in-marginal is exact up to the boundary**: `|Σ_b ν_N(b,b') - φ_N(b')| ≤ 1/N`. -/
theorem abs_sum_edgeCount_in_sub (β ξ : ℝ) {w b' : ℕ} (hb' : b' < 2 ^ w) (N : ℕ) :
    |((∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N : ℕ) : ℝ)
      - (winCount β ξ w b' N : ℝ)| ≤ 1 := by
  classical
  set Q : ℕ → Prop := fun n => cell w (ξ * β ^ n) = b' with hQ
  have h1 : (∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N)
      + (if Q 0 then 1 else 0) = ((Finset.range (N + 1)).filter Q).card := by
    rw [sum_edgeCount_in β ξ w b' N]
    exact card_filter_shift Q N
  have h2 : ((Finset.range (N + 1)).filter Q).card
      = winCount β ξ w b' N + (if Q N then 1 else 0) := by
    rw [card_filter_range_succ Q N, winCount_eq_card β ξ hb' N]
  have key : (∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N)
      + (if Q 0 then 1 else 0) = winCount β ξ w b' N + (if Q N then 1 else 0) := by
    rw [h1, h2]
  have hz : -1 ≤ ((∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N : ℕ) : ℤ)
        - ((winCount β ξ w b' N : ℕ) : ℤ) ∧
      ((∑ b ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N : ℕ) : ℤ)
        - ((winCount β ξ w b' N : ℕ) : ℤ) ≤ 1 := by
    by_cases h0 : Q 0 <;> by_cases hN : Q N <;>
      simp only [if_pos, h0, hN, if_false] at key <;> omega
  rw [abs_le]
  exact ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2⟩

/-- The transitions partition the dates: `Σ_{b,b'} ν_N(b,b') = 1` for `N ≥ 1`. -/
theorem sum_edgeCount_all (β ξ : ℝ) (w N : ℕ) :
    ∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w), edgeCount β ξ w b b' N = N := by
  rw [Finset.sum_congr rfl fun b hb =>
    sum_edgeCount_out β ξ (Finset.mem_range.mp hb) N]
  exact sum_winCount β ξ w N

/-- The out-marginal of the empirical flow is the empirical frequency, exactly. -/
theorem sum_flowVec_out (β ξ : ℝ) {w b : ℕ} (hb : b < 2 ^ w) (N : ℕ) :
    ∑ b' ∈ Finset.range (2 ^ w), flowVec β ξ w N b b' = freqVec β ξ w N b := by
  simp only [flowVec, freqVec, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_edgeCount_out β ξ hb N]

/-- The in-marginal of the empirical flow is the empirical frequency up to `1/N`. -/
theorem abs_sum_flowVec_in_sub (β ξ : ℝ) {w b' : ℕ} (hb' : b' < 2 ^ w) (N : ℕ) :
    |(∑ b ∈ Finset.range (2 ^ w), flowVec β ξ w N b b') - freqVec β ξ w N b'| ≤ 1 / N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [flowVec, freqVec, hN]
  · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [flowVec, freqVec, ← Finset.sum_div]
    rw [← Nat.cast_sum, div_sub_div_same, abs_div, abs_of_pos hNR]
    gcongr
    exact abs_sum_edgeCount_in_sub β ξ hb' N

/-- The whole flow has mass `1`. -/
theorem sum_flowVec_all (β ξ : ℝ) (w : ℕ) {N : ℕ} (hN : 0 < N) :
    ∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w), flowVec β ξ w N b b' = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by positivity
  simp only [flowVec, ← Finset.sum_div]
  have hcast : ∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w),
      (edgeCount β ξ w b b' N : ℝ)
      = ((∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w),
          edgeCount β ξ w b b' N : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, sum_edgeCount_all β ξ w N, div_self hNR]

/-! ## Balance vectors

The finite-resolution replacement for a `×3/2`-invariant limit measure (C6).  Everything is a
finite sum of reals: `μ` is a probability vector on the `2ʷ` cells, `ν` a nonnegative flow on the
edges, and the two marginals of `ν` are both `μ` — flow conservation.  The last field is the only
place the dynamics enters: the flow lives on the level-`w` carry graph. -/

/-- A **balance vector** at level `w`: a probability vector `μ` on the level-`w` cells and a
nonnegative flow `ν` on the level-`w` carry graph whose two marginals are both `μ`. -/
structure BalanceVec (w : ℕ) where
  /-- The mass of each level-`w` cell. -/
  μ : ℕ → ℝ
  /-- The flow along each edge of the level-`w` carry graph. -/
  ν : ℕ → ℕ → ℝ
  /-- Flows are nonnegative. -/
  ν_nonneg : ∀ b b', 0 ≤ ν b b'
  /-- The masses sum to one. -/
  sum_μ : ∑ b ∈ Finset.range (2 ^ w), μ b = 1
  /-- Conservation, outgoing. -/
  out : ∀ b < 2 ^ w, ∑ b' ∈ Finset.range (2 ^ w), ν b b' = μ b
  /-- Conservation, incoming. -/
  inn : ∀ b' < 2 ^ w, ∑ b ∈ Finset.range (2 ^ w), ν b b' = μ b'
  /-- The flow lives on the graph. -/
  adm : ∀ b b', 0 < ν b b' → edgeOk w b b' = true

namespace BalanceVec

variable {w : ℕ} (B : BalanceVec w)

theorem μ_nonneg {b : ℕ} (hb : b < 2 ^ w) : 0 ≤ B.μ b := by
  rw [← B.out b hb]
  exact Finset.sum_nonneg fun _ _ => B.ν_nonneg _ _

/-- The **support** of a balance vector: the cells carrying positive mass. -/
noncomputable def supp : Finset ℕ := (Finset.range (2 ^ w)).filter fun b => 0 < B.μ b

theorem mem_supp {b : ℕ} : b ∈ B.supp ↔ b < 2 ^ w ∧ 0 < B.μ b := by
  classical
  simp [supp, Finset.mem_filter, Finset.mem_range]

theorem supp_nonempty : B.supp.Nonempty := by
  classical
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty, supp, Finset.filter_eq_empty_iff] at hcon
  have hz : ∀ b ∈ Finset.range (2 ^ w), B.μ b = 0 := fun b hb =>
    le_antisymm (not_lt.mp (hcon hb)) (B.μ_nonneg (Finset.mem_range.mp hb))
  have h1 := B.sum_μ
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero] at h1
  exact absurd h1 (by norm_num)

/-- Every cell of the support sends flow into the support. -/
theorem exists_succ_mem_supp {b : ℕ} (hb : b ∈ B.supp) :
    ∃ b' ∈ B.supp, edgeOk w b b' = true := by
  classical
  obtain ⟨hblt, hbpos⟩ := B.mem_supp.mp hb
  rw [← B.out b hblt] at hbpos
  obtain ⟨b', hb'mem, hb'pos⟩ :
      ∃ b' ∈ Finset.range (2 ^ w), 0 < B.ν b b' := by
    by_contra hcon
    push Not at hcon
    have : ∑ b' ∈ Finset.range (2 ^ w), B.ν b b' ≤ 0 :=
      Finset.sum_nonpos fun b' hb' => hcon b' hb'
    linarith
  refine ⟨b', B.mem_supp.mpr ⟨Finset.mem_range.mp hb'mem, ?_⟩, B.adm b b' hb'pos⟩
  rw [← B.inn b' (Finset.mem_range.mp hb'mem)]
  refine lt_of_lt_of_le hb'pos (Finset.single_le_sum (f := fun c => B.ν c b')
    (fun c _ => B.ν_nonneg c b') (Finset.mem_range.mpr hblt))

/-- Every cell of the support receives flow from the support. -/
theorem exists_pred_mem_supp {b' : ℕ} (hb' : b' ∈ B.supp) :
    ∃ b ∈ B.supp, edgeOk w b b' = true := by
  classical
  obtain ⟨hb'lt, hb'pos⟩ := B.mem_supp.mp hb'
  rw [← B.inn b' hb'lt] at hb'pos
  obtain ⟨b, hbmem, hbpos⟩ : ∃ b ∈ Finset.range (2 ^ w), 0 < B.ν b b' := by
    by_contra hcon
    push Not at hcon
    have : ∑ b ∈ Finset.range (2 ^ w), B.ν b b' ≤ 0 :=
      Finset.sum_nonpos fun b hb => hcon b hb
    linarith
  refine ⟨b, B.mem_supp.mpr ⟨Finset.mem_range.mp hbmem, ?_⟩, B.adm b b' hbpos⟩
  rw [← B.out b (Finset.mem_range.mp hbmem)]
  refine lt_of_lt_of_le hbpos (Finset.single_le_sum (f := fun c => B.ν b c)
    (fun c _ => B.ν_nonneg b c) (Finset.mem_range.mpr hb'lt))

end BalanceVec

/-- A **trap** of the level-`w` carry graph: a nonempty set of cells in which every cell has a
successor and a predecessor.  By finiteness a trap contains a directed cycle; it is exactly the
shape of the support of a balance vector, and hence of an M6 enemy. -/
def IsTrap (w : ℕ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ b ∈ S, ∃ b' ∈ S, edgeOk w b b' = true) ∧
    (∀ b' ∈ S, ∃ b ∈ S, edgeOk w b b' = true)

/-- The support of a balance vector is a trap. -/
theorem BalanceVec.isTrap_supp {w : ℕ} (B : BalanceVec w) : IsTrap w B.supp :=
  ⟨B.supp_nonempty, fun _ hb => B.exists_succ_mem_supp hb, fun _ hb => B.exists_pred_mem_supp hb⟩

/-! ## The balance lemma

Bolzano–Weierstrass on `[0,1]^{cells × cells}` — a finite product, so the compactness is
`isCompact_univ_pi` and nothing measure-theoretic is involved.  The out-marginal identity is exact,
so the frequency vectors converge along the *same* subsequence; the in-marginal identity costs the
two boundary dates, i.e. `1/N`, which vanishes. -/

private theorem sum_range_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ b ∈ Finset.range n, f b = ∑ q : Fin n, f q := (Fin.sum_univ_eq_sum_range f n).symm

/-- **The balance lemma (WP1).**  Along any sequence of horizons tending to infinity, the empirical
flow vectors have a convergent subsequence, and the limit is a balance vector whose mass vector is
the limit of the empirical frequency vectors. -/
theorem exists_balanceVec (β ξ : ℝ) (w : ℕ)
    (hadm : ∀ n, edgeOk w (cell w (ξ * β ^ n)) (cell w (ξ * β ^ (n + 1))) = true)
    (Nseq : ℕ → ℕ) (hNseq : Tendsto Nseq atTop atTop) :
    ∃ (B : BalanceVec w) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ b < 2 ^ w, Tendsto (fun k => freqVec β ξ w (Nseq (φ k)) b) atTop (𝓝 (B.μ b)) := by
  classical
  -- Bolzano–Weierstrass on the finite cube of flows
  have hcpt : IsCompact (Set.univ.pi fun _ : Fin (2 ^ w) × Fin (2 ^ w) => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq
    (x := fun k (q : Fin (2 ^ w) × Fin (2 ^ w)) => flowVec β ξ w (Nseq k) q.1 q.2)
    (fun k => Set.mem_univ_pi.mpr fun q =>
      ⟨flowVec_nonneg β ξ w (Nseq k) q.1 q.2, flowVec_le_one β ξ w (Nseq k) q.1 q.2⟩)
  set M : ℕ → ℕ := fun k => Nseq (φ k) with hMdef
  have hMtop : Tendsto M atTop atTop := hNseq.comp hφ.tendsto_atTop
  have hcoord : ∀ q : Fin (2 ^ w) × Fin (2 ^ w),
      Tendsto (fun k => flowVec β ξ w (M k) q.1 q.2) atTop (𝓝 (a q)) := fun q =>
    (tendsto_pi_nhds.mp hlim) q
  -- the limit flow, as a function on `ℕ × ℕ`
  set ν : ℕ → ℕ → ℝ := fun b b' =>
    if h : b < 2 ^ w then if h' : b' < 2 ^ w then a (⟨b, h⟩, ⟨b', h'⟩) else 0 else 0 with hνdef
  have hν : ∀ {b b' : ℕ} (h : b < 2 ^ w) (h' : b' < 2 ^ w),
      ν b b' = a (⟨b, h⟩, ⟨b', h'⟩) := by
    intro b b' h h'
    rw [hνdef]
    simp only [dif_pos h, dif_pos h']
  have hνtend : ∀ b b' : ℕ, b < 2 ^ w → b' < 2 ^ w →
      Tendsto (fun k => flowVec β ξ w (M k) b b') atTop (𝓝 (ν b b')) := by
    intro b b' hb hb'
    rw [hν hb hb']
    exact hcoord (⟨b, hb⟩, ⟨b', hb'⟩)
  have hνnonneg : ∀ b b', 0 ≤ ν b b' := by
    intro b b'
    by_cases hb : b < 2 ^ w
    · by_cases hb' : b' < 2 ^ w
      · exact ge_of_tendsto' (hνtend b b' hb hb') fun k => flowVec_nonneg β ξ w (M k) b b'
      · rw [hνdef]; simp [dif_neg hb']
    · rw [hνdef]; simp [dif_neg hb]
  -- the limit mass vector is the out-marginal
  set μ : ℕ → ℝ := fun b => ∑ b' ∈ Finset.range (2 ^ w), ν b b' with hμdef
  have hμtend : ∀ b < 2 ^ w, Tendsto (fun k => freqVec β ξ w (M k) b) atTop (𝓝 (μ b)) := by
    intro b hb
    have h1 : Tendsto (fun k => ∑ b' ∈ Finset.range (2 ^ w), flowVec β ξ w (M k) b b')
        atTop (𝓝 (μ b)) :=
      tendsto_finsetSum _ fun b' hb' => hνtend b b' hb (Finset.mem_range.mp hb')
    exact h1.congr fun k => sum_flowVec_out β ξ hb (M k)
  -- conservation, incoming
  have hzero : Tendsto (fun k => 1 / (M k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hMtop
  have hinn : ∀ b' < 2 ^ w, ∑ b ∈ Finset.range (2 ^ w), ν b b' = μ b' := by
    intro b' hb'
    have h1 : Tendsto (fun k => ∑ b ∈ Finset.range (2 ^ w), flowVec β ξ w (M k) b b')
        atTop (𝓝 (∑ b ∈ Finset.range (2 ^ w), ν b b')) :=
      tendsto_finsetSum _ fun b hb => hνtend b b' (Finset.mem_range.mp hb) hb'
    have hdiff : Tendsto (fun k => (∑ b ∈ Finset.range (2 ^ w), flowVec β ξ w (M k) b b')
        - freqVec β ξ w (M k) b') atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) hzero
      simpa using abs_sum_flowVec_in_sub β ξ hb' (M k)
    have h2 : Tendsto (fun k => ∑ b ∈ Finset.range (2 ^ w), flowVec β ξ w (M k) b b')
        atTop (𝓝 (μ b' + 0)) := by
      have := (hμtend b' hb').add hdiff
      exact this.congr fun k => by ring
    rw [add_zero] at h2
    exact tendsto_nhds_unique h1 h2
  -- total mass
  have hsum : ∑ b ∈ Finset.range (2 ^ w), μ b = 1 := by
    have h1 : Tendsto
        (fun k => ∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w),
          flowVec β ξ w (M k) b b') atTop (𝓝 (∑ b ∈ Finset.range (2 ^ w), μ b)) :=
      tendsto_finsetSum _ fun b hb =>
        tendsto_finsetSum _ fun b' hb' =>
          hνtend b b' (Finset.mem_range.mp hb) (Finset.mem_range.mp hb')
    have h2 : Tendsto
        (fun k => ∑ b ∈ Finset.range (2 ^ w), ∑ b' ∈ Finset.range (2 ^ w),
          flowVec β ξ w (M k) b b') atTop (𝓝 1) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hMtop.eventually_ge_atTop 1] with k hk
      exact (sum_flowVec_all β ξ w hk).symm
    exact tendsto_nhds_unique h1 h2
  -- admissibility of the limit flow
  have hadmν : ∀ b b', 0 < ν b b' → edgeOk w b b' = true := by
    intro b b' hpos
    by_cases hb : b < 2 ^ w
    · by_cases hb' : b' < 2 ^ w
      · obtain ⟨k, hk⟩ := ((hνtend b b' hb hb').eventually (lt_mem_nhds hpos)).exists
        have hcard : edgeCount β ξ w b b' (M k) ≠ 0 := by
          intro h0
          rw [flowVec, h0] at hk
          simp at hk
        obtain ⟨n, h1, h2⟩ := exists_of_edgeCount_ne_zero hcard
        have := hadm n
        rw [h1, h2] at this
        exact this
      · rw [hνdef] at hpos; simp [dif_neg hb'] at hpos
    · rw [hνdef] at hpos; simp [dif_neg hb] at hpos
  exact ⟨BalanceVec.mk μ ν hνnonneg hsum (fun _ _ => rfl) hinn hadmν, φ, hφ, hμtend⟩

/-! ## The enemy statement, and the criterion it yields

M6 at a dyadic window is exactly `V4` there.  Failure produces a horizon sequence along which the
window's frequency tends to `0`; the balance lemma turns it into a stationary vector with zero mass
at that window, whose support is a trap avoiding it. -/

/-- **The enemy statement (C6).**  If the level-`w` window `b` has zero lower density of visits at
`ξ = 1`, the level-`w` carry graph carries a balance vector with **zero mass at `b`**. -/
theorem exists_balanceVec_zero_of_not_V4 {w b : ℕ} (hb : b < 2 ^ w)
    (h : ¬ V4 ((3 : ℝ) / 2) 1 ((b : ℝ) / 2 ^ w) (1 / 2 ^ w)) :
    ∃ B : BalanceVec w, B.μ b = 0 := by
  classical
  set s : ℝ := (b : ℝ) / 2 ^ w with hs
  set t : ℝ := 1 / 2 ^ w with ht
  have hlow : lowerDensity ((3 : ℝ) / 2) 1 s t = 0 :=
    le_antisymm (not_lt.mp h) (lowerDensity_nonneg _ _ _ _)
  -- horizons along which the window's frequency vanishes
  have hex : ∀ k : ℕ, ∃ N : ℕ, k ≤ N ∧
      visitRatio ((3 : ℝ) / 2) 1 s t N < 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : liminf (visitRatio ((3 : ℝ) / 2) 1 s t) atTop < 1 / ((k : ℝ) + 1) := by
      have h0 : liminf (visitRatio ((3 : ℝ) / 2) 1 s t) atTop = 0 := hlow
      rw [h0]
      positivity
    have hfreq := frequently_lt_of_liminf_lt
      (isCoboundedUnder_ge_visitRatio ((3 : ℝ) / 2) 1 s t) hlt
    obtain ⟨N, hN1, hN2⟩ := (hfreq.and_eventually (eventually_ge_atTop k)).exists
    exact ⟨N, hN2, hN1⟩
  choose Nseq hNge hNlt using hex
  have hNtop : Tendsto Nseq atTop atTop := tendsto_atTop_mono hNge tendsto_id
  have hfreq0 : Tendsto (fun k => freqVec ((3 : ℝ) / 2) 1 w (Nseq k) b) atTop (𝓝 0) :=
    squeeze_zero (fun k => visitRatio_nonneg _ _ _ _ _) (fun k => (hNlt k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨B, φ, hφ, hconv⟩ :=
    exists_balanceVec ((3 : ℝ) / 2) 1 w (edgeOk_orbit w) Nseq hNtop
  exact ⟨B, tendsto_nhds_unique (hconv b hb) (hfreq0.comp hφ.tendsto_atTop)⟩

/-- **The enemy is a trap.**  M6 failure at the level-`w` window `b` produces a nonempty set of
cells, avoiding `b`, in which every cell has a successor and a predecessor along the level-`w`
carry graph — a subgraph carrying a cycle that never visits `b`. -/
theorem exists_trap_of_not_V4 {w b : ℕ} (hb : b < 2 ^ w)
    (h : ¬ V4 ((3 : ℝ) / 2) 1 ((b : ℝ) / 2 ^ w) (1 / 2 ^ w)) :
    ∃ S : Finset ℕ, IsTrap w S ∧ b ∉ S := by
  obtain ⟨B, hB⟩ := exists_balanceVec_zero_of_not_V4 hb h
  refine ⟨B.supp, B.isTrap_supp, fun hmem => ?_⟩
  have hpos := (B.mem_supp.mp hmem).2
  rw [hB] at hpos
  exact lt_irrefl 0 hpos

/-- **The criterion.**  If every trap of the level-`w` carry graph contains `b`, the window `(w,b)`
has positive lower density of visits.  (The next section shows the hypothesis is never met.) -/
theorem V4_of_forall_trap_mem {w b : ℕ} (hb : b < 2 ^ w)
    (h : ∀ S : Finset ℕ, IsTrap w S → b ∈ S) :
    V4 ((3 : ℝ) / 2) 1 ((b : ℝ) / 2 ^ w) (1 / 2 ^ w) := by
  by_contra hcon
  obtain ⟨S, hS, hbS⟩ := exists_trap_of_not_V4 hb hcon
  exact hbS (h S hS)

/-! ## The cycle enemies, and the vacuity of the criterion

The carry relation has the fixed point `0` and the rational 2-cycle `{2/5, 3/5}` (denominator
`5 = 3² - 2²`, the [L90] shape).  Their cells give traps at *every* level, and one of the two
always avoids any prescribed window.  So the criterion above never fires: the flow layer cannot
exclude the atomic enemies, which is precisely why C6 sends them to Front D. -/

theorem cell_zero (w : ℕ) : cell w 0 = 0 := by simp [cell]

/-- Points at distance `≥ 2^{-w}` from `0` do not sit in the zero cell. -/
theorem cell_ne_zero {w : ℕ} {y : ℝ} (h0 : 1 / (2 : ℝ) ^ w ≤ y) (h1 : y < 1) : cell w y ≠ 0 := by
  have h2 : (0 : ℝ) < 2 ^ w := by positivity
  have hy0 : (0 : ℝ) ≤ y := le_trans (by positivity) h0
  have hfy : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, h1⟩
  have hge : (1 : ℝ) ≤ 2 ^ w * y := by
    rw [div_le_iff₀ h2] at h0
    linarith
  have : 1 ≤ cell w y := by
    rw [cell, hfy]
    exact Nat.le_floor (by push_cast; linarith)
  omega

/-- The fixed point `0` of the carry relation gives a self-loop at the zero cell. -/
theorem edgeOk_zero (w : ℕ) : edgeOk w 0 0 = true := by
  have h := edgeOk_of_step (w := w) (y := 0) (y' := 0) (s := 0) le_rfl (by norm_num) le_rfl
    (by norm_num) (by norm_num)
  rwa [cell_zero] at h

/-- The 2-cycle `{2/5, 3/5}`, first edge: `2·(3/5) = 3·(2/5) - 0`. -/
theorem edgeOk_two_fifths (w : ℕ) : edgeOk w (cell w (2 / 5)) (cell w (3 / 5)) = true :=
  edgeOk_of_step (s := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The 2-cycle `{2/5, 3/5}`, second edge: `2·(2/5) = 3·(3/5) - 1`. -/
theorem edgeOk_three_fifths (w : ℕ) : edgeOk w (cell w (3 / 5)) (cell w (2 / 5)) = true :=
  edgeOk_of_step (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The stationary vector of a self-loop: all the mass at one cell. -/
noncomputable def loopVec (w c : ℕ) (hc : c < 2 ^ w) (h : edgeOk w c c = true) : BalanceVec w where
  μ := fun b => if b = c then 1 else 0
  ν := fun b b' => if b = c then (if b' = c then 1 else 0) else 0
  ν_nonneg := by
    intro b b'
    split <;> [split; skip] <;> norm_num
  sum_μ := by
    classical
    simp [Finset.sum_ite_eq', Finset.mem_range, hc]
  out := by
    intro b _
    classical
    by_cases hbc : b = c
    · simp [hbc, Finset.sum_ite_eq', Finset.mem_range, hc]
    · simp [hbc]
  inn := by
    intro b' _
    classical
    by_cases hb'c : b' = c
    · simp [hb'c, Finset.sum_ite_eq', Finset.mem_range, hc]
    · simp [hb'c]
  adm := by
    intro b b' hpos
    by_cases hbc : b = c
    · by_cases hb'c : b' = c
      · rw [hbc, hb'c]; exact h
      · simp [hbc, hb'c] at hpos
    · simp [hbc] at hpos

/-- The stationary vector of a 2-cycle: half the mass at each of two distinct cells. -/
noncomputable def twoCycleVec (w c d : ℕ) (hc : c < 2 ^ w) (hd : d < 2 ^ w) (hcd : c ≠ d)
    (h1 : edgeOk w c d = true) (h2 : edgeOk w d c = true) : BalanceVec w where
  μ := fun b => (if b = c then 1 / 2 else 0) + (if b = d then 1 / 2 else 0)
  ν := fun b b' => (if b = c then (if b' = d then 1 / 2 else 0) else 0)
    + (if b = d then (if b' = c then 1 / 2 else 0) else 0)
  ν_nonneg := by
    intro b b'
    have h₁ : (0 : ℝ) ≤ if b = c then (if b' = d then 1 / 2 else 0) else 0 := by
      split <;> [split; skip] <;> norm_num
    have h₂ : (0 : ℝ) ≤ if b = d then (if b' = c then 1 / 2 else 0) else 0 := by
      split <;> [split; skip] <;> norm_num
    linarith
  sum_μ := by
    classical
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq', Finset.mem_range, hc, hd]
    norm_num
  out := by
    intro b _
    classical
    rw [Finset.sum_add_distrib]
    by_cases hbc : b = c
    · have hbd : ¬ b = d := by rw [hbc]; exact hcd
      simp [hbc, hcd, Finset.sum_ite_eq', Finset.mem_range, hd]
    · by_cases hbd : b = d
      · simp [hbd, Ne.symm hcd, Finset.sum_ite_eq', Finset.mem_range, hc]
      · simp [hbc, hbd]
  inn := by
    intro b' _
    classical
    rw [Finset.sum_add_distrib]
    by_cases hb'c : b' = c
    · have hb'd : ¬ b' = d := by rw [hb'c]; exact hcd
      simp [hb'c, hcd, Finset.sum_ite_eq', Finset.mem_range, hd]
    · by_cases hb'd : b' = d
      · simp [hb'd, Ne.symm hcd, Finset.sum_ite_eq', Finset.mem_range, hc]
      · simp [hb'c, hb'd]
  adm := by
    intro b b' hpos
    by_cases hbc : b = c
    · by_cases hb'd : b' = d
      · rw [hbc, hb'd]; exact h1
      · by_cases hbd : b = d
        · by_cases hb'c : b' = c
          · rw [hbd, hb'c]; exact h2
          · simp [hbc, hb'd, hcd] at hpos
        · simp [hbc, hb'd, hcd] at hpos
    · by_cases hbd : b = d
      · by_cases hb'c : b' = c
        · rw [hbd, hb'c]; exact h2
        · simp [hbd, hb'c, Ne.symm hcd] at hpos
      · simp [hbc, hbd] at hpos

/-- **The finite-resolution obstruction is vacuous.**  At every level `w ≥ 2` and for every window
`b` there is a balance vector with zero mass at `b`: the flow layer alone can never prove M6 at any
window.  The witnesses are the cycle enemies of C6 — the fixed point `0` and the `[L90]` 2-cycle
`{2/5, 3/5}` of denominator `5 = 3² - 2²`. -/
theorem exists_balanceVec_zero (w : ℕ) (hw : 2 ≤ w) (b : ℕ) : ∃ B : BalanceVec w, B.μ b = 0 := by
  have hppos : 0 < 2 ^ w := pow_pos (by norm_num) w
  by_cases hb0 : b = 0
  · -- the 2-cycle avoids the zero cell
    subst hb0
    have h4 : (4 : ℝ) ≤ 2 ^ w := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ w := by
            apply pow_le_pow_right₀ (by norm_num) hw
    have hsmall : 1 / (2 : ℝ) ^ w ≤ 2 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hc0 : cell w (2 / 5) ≠ 0 := cell_ne_zero hsmall (by norm_num)
    have hd0 : cell w (3 / 5) ≠ 0 := cell_ne_zero (by linarith) (by norm_num)
    rcases eq_or_ne (cell w (2 / 5)) (cell w (3 / 5)) with hcd | hcd
    · refine ⟨loopVec w (cell w (2 / 5)) (cell_lt w _) ?_, ?_⟩
      · have := edgeOk_two_fifths w
        rwa [← hcd] at this
      · simp [loopVec, Ne.symm hc0]
    · exact ⟨twoCycleVec w (cell w (2 / 5)) (cell w (3 / 5)) (cell_lt w _) (cell_lt w _) hcd
        (edgeOk_two_fifths w) (edgeOk_three_fifths w), by
          simp [twoCycleVec, Ne.symm hc0, Ne.symm hd0]⟩
  · exact ⟨loopVec w 0 hppos (edgeOk_zero w), by simp [loopVec, hb0]⟩

/-- **No level-`w` balance argument proves M6**: the hypothesis of `Z32.V4_of_forall_trap_mem` is
never satisfiable, at any level and any window. -/
theorem exists_trap_not_mem (w : ℕ) (hw : 2 ≤ w) (b : ℕ) :
    ∃ S : Finset ℕ, IsTrap w S ∧ b ∉ S := by
  obtain ⟨B, hB⟩ := exists_balanceVec_zero w hw b
  refine ⟨B.supp, B.isTrap_supp, fun hmem => ?_⟩
  have hpos := (B.mem_supp.mp hmem).2
  rw [hB] at hpos
  exact lt_irrefl 0 hpos

/-! ### The worked `w = 2` instance

At level `2` the carry graph is **complete**: all sixteen ordered pairs of cells are edges, so every
singleton is a trap and the obstruction sees nothing whatsoever at this resolution.  Kernel-checked
by `decide`.  (The graph does become sparse higher up — at level `w` each cell has at most the four
carries as out-edges, so `4·2ʷ` of the `4ʷ` pairs — but `Z32.exists_trap_not_mem` shows the
sparsity never helps.) -/

theorem edgeOk_complete_two {b b' : ℕ} (hb : b < 4) (hb' : b' < 4) : edgeOk 2 b b' = true := by
  interval_cases b <;> interval_cases b' <;> decide

/-- Every singleton is a trap at level `2`. -/
theorem isTrap_singleton_two {c : ℕ} (hc : c < 4) : IsTrap 2 ({c} : Finset ℕ) := by
  refine ⟨⟨c, Finset.mem_singleton_self c⟩, ?_, ?_⟩ <;>
    · intro b hb
      rw [Finset.mem_singleton] at hb
      subst hb
      exact ⟨b, Finset.mem_singleton_self b, edgeOk_complete_two hc hc⟩

/-! ## Cycle points and the [L90] denominator

A `p`-periodic point of the carry relation is rational with **odd** denominator `3^p - 2^p` — the
[L90] rational-cycle shape.  Combined with the 2-adic floor `Z32.dist_odd_denom` this is the
quantitative separation the sojourn dichotomy (C7, WP2) runs on.

C6 quotes the denominator shape as `(3^p - 2^p)·2^j`; the `2^j` is the solenoid fibre direction and
is invisible at finite resolution.  What a `p`-cycle of the carry relation contributes on the
circle is the **odd** factor alone, and that is exactly the factor the 2-adic floor consumes: the
orbit point `xₙ` has denominator `2ⁿ` and numerator odd, so it cannot sit closer than
`1/((3^p-2^p)2ⁿ)` to any of these rationals. -/

/-- `3^p - 2^p`, the denominator of a `p`-cycle of the carry relation ([L90]). -/
def cycleDenom (p : ℕ) : ℕ := 3 ^ p - 2 ^ p

theorem two_pow_le_three_pow (p : ℕ) : 2 ^ p ≤ 3 ^ p := Nat.pow_le_pow_left (by norm_num) p

theorem cycleDenom_cast (p : ℕ) : ((cycleDenom p : ℕ) : ℝ) = 3 ^ p - 2 ^ p := by
  rw [cycleDenom, Nat.cast_sub (two_pow_le_three_pow p)]
  push_cast
  ring

/-- **The denominator is odd** — the hypothesis `Z32.dist_odd_denom` needs. -/
theorem cycleDenom_odd {p : ℕ} (hp : 1 ≤ p) : Odd (cycleDenom p) := by
  have h3 : Odd (3 ^ p) := Odd.pow (by decide)
  have h2 : Even (2 ^ p) := (Nat.even_pow' (by omega)).mpr (by decide)
  exact Nat.Odd.sub_even (two_pow_le_three_pow p) h3 h2

theorem cycleDenom_pos {p : ℕ} (hp : 1 ≤ p) : 0 < cycleDenom p := by
  have : 2 ^ p < 3 ^ p := Nat.pow_lt_pow_left (by norm_num) (by omega)
  rw [cycleDenom]
  omega

/-- **Cycle-point classification (C6; the [L90] shape).**  A `p`-periodic point of the carry
relation `2y_{i+1} = 3yᵢ - sᵢ` is the rational `A/(3^p - 2^p)`. -/
theorem cycle_point_eq {p : ℕ} (hp : 1 ≤ p) {y : ℕ → ℝ} {s : ℕ → ℤ}
    (hstep : ∀ i < p, 2 * y (i + 1) = 3 * y i - (s i : ℝ)) (hper : y p = y 0) :
    ∃ A : ℤ, y 0 = (A : ℝ) / cycleDenom p := by
  have key : ∀ i, i ≤ p → ∃ A : ℤ, (2 : ℝ) ^ i * y i = 3 ^ i * y 0 - (A : ℝ) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨0, by norm_num⟩
    | succ i ih =>
      intro hi
      obtain ⟨A, hA⟩ := ih (by omega)
      refine ⟨3 * A + 2 ^ i * s i, ?_⟩
      have hs := hstep i (by omega)
      have hsplit : (2 : ℝ) ^ (i + 1) * y (i + 1) = 2 ^ i * (2 * y (i + 1)) := by ring
      rw [hsplit, hs]
      push_cast
      linear_combination (3 : ℝ) * hA
  obtain ⟨A, hA⟩ := key p le_rfl
  rw [hper] at hA
  have hlt : (2 : ℕ) ^ p < 3 ^ p := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hltR : (2 : ℝ) ^ p < 3 ^ p := by exact_mod_cast hlt
  refine ⟨A, ?_⟩
  rw [cycleDenom_cast p, eq_div_iff (by linarith : (3 : ℝ) ^ p - 2 ^ p ≠ 0)]
  linear_combination -hA

/-- **The 2-adic floor at a cycle point (C7).**  The `ξ = 1` orbit never comes closer than
`1/((3^p - 2^p)·2ⁿ)` to a `p`-periodic point of the carry relation. -/
theorem dist_cycle_point {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) {y : ℕ → ℝ} {s : ℕ → ℤ}
    (hstep : ∀ i < p, 2 * y (i + 1) = 3 * y i - (s i : ℝ)) (hper : y p = y 0) :
    1 / (((3 : ℝ) ^ p - 2 ^ p) * 2 ^ n) ≤ |x n - y 0| := by
  obtain ⟨A, hA⟩ := cycle_point_eq hp hstep hper
  have h := dist_odd_denom hn (cycleDenom_odd hp) A
  rw [← hA, cycleDenom_cast p] at h
  exact h

end Z32
