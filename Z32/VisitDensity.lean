/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.EscapeLadder
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The M6 grid: visit counts, densities, and the V-rungs (plan-A6+, WP0)

`plans/plan-A6+.html` §3.2 replaces the linear milestone ladder between M5 ("every arc is visited
infinitely often") and M7 ("the orbit is uniformly distributed") by a **grid**: a rung measuring
*how many* visits an arc receives, resolved *per arc* rather than uniformly.  This file is the
Lean form of that grid — the spine of WP0.

`Z32/EscapeLadder.lean` supplies the bottom row: `Z32.inArc` (a half-open arc that wraps around
`0` by itself, so no endpoint case split ever appears) and `Z32.VisitsIO` (visits infinitely
often).  Everything here counts those visits.

## The grid

For an orbit `n ↦ ξβⁿ` and an arc `[s, s+t)`:

| rung | predicate | meaning |
| --- | --- | --- |
| V0 | `Z32.VisitsIO` | visits infinitely often (`= M5(I)`) |
| V1 | `Z32.V1` | at least `c log N` visits before time `N` |
| V2 | `Z32.V2` | at least `c N^θ` visits before time `N` |
| V3 | `Z32.V3` | positive *upper* density |
| V4 | `Z32.V4` | positive *lower* density — **M6 at that arc** |
| V4S | `Z32.V4S` | syndetic: visits with bounded gaps |
| V5 | `Z32.V5` | asymptotic frequency `t` — M7 at that arc |

and the implications `V5 → V4 → V2 → V1 → V0`, `V4 → V3 → V0`, `V4S → V4` are proved below, so
the grid really is a grid.  Position-resolved throughout: `s` is an arbitrary real.

## M6 and its dyadic form

`Z32.M6 β ξ` — every arc of positive length has positive lower density — is the milestone.
`Z32.M6_iff_dyadic` reduces it to the countable family of dyadic windows `[b/2ʷ, (b+1)/2ʷ)`,
`b : ℤ`: the report's "dyadic-window form", proved here through the sub-arc lemma
`Z32.inArc_of_inArc_shift` and the covering lemma `Z32.exists_dyadic_subarc`.  Both directions are
elementary; the point of the reduction is that every downstream statistic (window counts, energies)
is stated at a dyadic level.

## What is *not* here

No rung above V0 is proved for any arc, at any gauge — that is the content of the plan, not of
this file.  V0 itself is shipped in `Z32/EscapeLadder.lean` (uniform to length `2/3`, positional to
`0.59278`).  The one ceiling worth recording next to the grid: the rungs below the V0 row cannot be
proved *uniformly in `ξ`*, because `Bugeaud.Pollington.exists_forall_dist_ge_of_cert` exhibits a
`ξ > 0` whose orbit avoids the arc of length `8/65` around `0` for ever.  Everything above V0 is
`ξ = 1` territory.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.

## Claim level

Formalization only, and definitional at that: this file introduces the vocabulary in which the M6
program is stated and proves the elementary relations between its rungs.  Nothing here is claimed
as new mathematics.

## References

* `plans/plan-A6+.html` §3.2 (the grid), §5 WP0 (this file), C2 (the V-rung namespace),
  C10a (the exact lemmas, in `Z32/DyadicOrbit.lean`).
* `plans/report2-weyl.html` Table C (the milestone ladder M0′–M8).
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
-/

namespace Z32

open Filter Topology

/-! ## Visit counts

The counting object is a `Finset` of *dates*, not of points: two dates may carry the same point in
general (they cannot for `ξ = 1`, `β = 3/2` — see `Z32.fract_injOn` in `Z32/DyadicOrbit.lean`),
and every statistic of the program counts dates. -/

open scoped Classical in
/-- The dates `n < N` at which the orbit `n ↦ ξβⁿ` lies in the arc `[s, s+t)`. -/
noncomputable def visits (β ξ s t : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => inArc s t (ξ * β ^ n)

/-- `A_N(I)`: the number of visits to the arc `[s, s+t)` before time `N`. -/
noncomputable def visitCount (β ξ s t : ℝ) (N : ℕ) : ℕ := (visits β ξ s t N).card

/-- The empirical frequency of visits to `[s, s+t)` among the first `N` dates. -/
noncomputable def visitRatio (β ξ s t : ℝ) (N : ℕ) : ℝ := (visitCount β ξ s t N : ℝ) / N

theorem mem_visits {β ξ s t : ℝ} {N n : ℕ} :
    n ∈ visits β ξ s t N ↔ n < N ∧ inArc s t (ξ * β ^ n) := by
  classical
  simp [visits]

theorem visits_subset_range (β ξ s t : ℝ) (N : ℕ) : visits β ξ s t N ⊆ Finset.range N := by
  intro n hn
  exact Finset.mem_range.mpr (mem_visits.mp hn).1

/-- The count never exceeds the number of dates. -/
theorem visitCount_le (β ξ s t : ℝ) (N : ℕ) : visitCount β ξ s t N ≤ N := by
  have h := Finset.card_le_card (visits_subset_range β ξ s t N)
  rw [Finset.card_range] at h
  exact h

/-- Division by a nonnegative denominator is monotone; used on `visitCount/N`, where `N = 0` must
not be excluded. -/
private theorem div_le_div_nonneg {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  gcongr

/-- Counts are monotone in the time horizon. -/
theorem visitCount_mono (β ξ s t : ℝ) {M N : ℕ} (h : M ≤ N) :
    visitCount β ξ s t M ≤ visitCount β ξ s t N := by
  refine Finset.card_le_card fun n hn => ?_
  obtain ⟨h1, h2⟩ := mem_visits.mp hn
  exact mem_visits.mpr ⟨lt_of_lt_of_le h1 h, h2⟩

/-- Counts are monotone in the arc: a visit to a longer arc is at least as frequent. -/
theorem visitCount_mono_arc {β ξ s t t' : ℝ} (h : t ≤ t') (N : ℕ) :
    visitCount β ξ s t N ≤ visitCount β ξ s t' N := by
  refine Finset.card_le_card fun n hn => ?_
  obtain ⟨h1, h2⟩ := mem_visits.mp hn
  exact mem_visits.mpr ⟨h1, inArc_mono h h2⟩

theorem visitRatio_nonneg (β ξ s t : ℝ) (N : ℕ) : 0 ≤ visitRatio β ξ s t N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem visitRatio_le_one (β ξ s t : ℝ) (N : ℕ) : visitRatio β ξ s t N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [visitRatio, hN]
  · rw [visitRatio, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast visitCount_le β ξ s t N

/-! ## Densities

`liminf` and `limsup` of the empirical frequency.  The two boundedness facts are isolated once and
for all: every downstream `liminf`/`limsup` step needs them explicitly (`isBoundedDefault` only
discharges them on bounded orders, and `ℝ` is not one). -/

/-- The **lower density** of visits to `[s, s+t)`. -/
noncomputable def lowerDensity (β ξ s t : ℝ) : ℝ := liminf (visitRatio β ξ s t) atTop

/-- The **upper density** of visits to `[s, s+t)`. -/
noncomputable def upperDensity (β ξ s t : ℝ) : ℝ := limsup (visitRatio β ξ s t) atTop

theorem isBoundedUnder_le_visitRatio (β ξ s t : ℝ) :
    IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) (visitRatio β ξ s t) :=
  isBoundedUnder_of ⟨1, fun N => visitRatio_le_one β ξ s t N⟩

theorem isBoundedUnder_ge_visitRatio (β ξ s t : ℝ) :
    IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ) (visitRatio β ξ s t) :=
  isBoundedUnder_of ⟨0, fun N => visitRatio_nonneg β ξ s t N⟩

theorem isCoboundedUnder_ge_visitRatio (β ξ s t : ℝ) :
    IsCoboundedUnder (· ≥ ·) (atTop : Filter ℕ) (visitRatio β ξ s t) :=
  (isBoundedUnder_le_visitRatio β ξ s t).isCoboundedUnder_ge

theorem isCoboundedUnder_le_visitRatio (β ξ s t : ℝ) :
    IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ) (visitRatio β ξ s t) :=
  (isBoundedUnder_ge_visitRatio β ξ s t).isCoboundedUnder_le

theorem lowerDensity_nonneg (β ξ s t : ℝ) : 0 ≤ lowerDensity β ξ s t :=
  le_liminf_of_le (isCoboundedUnder_ge_visitRatio β ξ s t)
    (Eventually.of_forall fun N => visitRatio_nonneg β ξ s t N)

theorem upperDensity_le_one (β ξ s t : ℝ) : upperDensity β ξ s t ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_visitRatio β ξ s t)
    (Eventually.of_forall fun N => visitRatio_le_one β ξ s t N)

theorem lowerDensity_le_upperDensity (β ξ s t : ℝ) :
    lowerDensity β ξ s t ≤ upperDensity β ξ s t :=
  liminf_le_limsup (isBoundedUnder_le_visitRatio β ξ s t) (isBoundedUnder_ge_visitRatio β ξ s t)

/-- Densities are monotone in the arc length. -/
theorem lowerDensity_mono_arc {β ξ s t t' : ℝ} (h : t ≤ t') :
    lowerDensity β ξ s t ≤ lowerDensity β ξ s t' := by
  refine liminf_le_liminf (Eventually.of_forall fun N => ?_)
    (isBoundedUnder_ge_visitRatio β ξ s t) (isCoboundedUnder_ge_visitRatio β ξ s t')
  exact div_le_div_nonneg (by exact_mod_cast visitCount_mono_arc h N) (Nat.cast_nonneg N)

/-! ## The V-rungs -/

/-- **V1** — at least `c log N` visits to `[s, s+t)` before time `N`. -/
def V1 (β ξ s t : ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ visitCount β ξ s t N

/-- **V2** — at least `c N^θ` visits to `[s, s+t)` before time `N`. -/
def V2 (β ξ s t : ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ θ ≤ visitCount β ξ s t N

/-- **V3** — the arc `[s, s+t)` has positive *upper* density of visits. -/
def V3 (β ξ s t : ℝ) : Prop := 0 < upperDensity β ξ s t

/-- **V4** — the arc `[s, s+t)` has positive *lower* density of visits: **M6 at this arc**. -/
def V4 (β ξ s t : ℝ) : Prop := 0 < lowerDensity β ξ s t

/-- **V4S** — visits to `[s, s+t)` are *syndetic*: they occur with gaps bounded by `B`. -/
def V4S (β ξ s t : ℝ) : Prop := ∃ B : ℕ, ∀ n : ℕ, ∃ k, n ≤ k ∧ k ≤ n + B ∧ inArc s t (ξ * β ^ k)

/-- **V5** — the arc `[s, s+t)` is visited with asymptotic frequency `t`: M7 at this arc. -/
def V5 (β ξ s t : ℝ) : Prop := Tendsto (visitRatio β ξ s t) atTop (𝓝 t)

/-! ### The grid is a grid

`V5 → V4 → V2 → V1 → V0` and `V4 → V3 → V0` and `V4S → V4`.  Nothing here is deep; the content is
that the rungs are stated so that these implications hold with no side conditions beyond `t > 0`
where the frequency itself must be positive. -/

/-- Unbounded visit counts give infinitely many visits: the bottom of the grid. -/
theorem visitsIO_of_visitCount_unbounded {β ξ s t : ℝ}
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ visitCount β ξ s t N) : VisitsIO β ξ s t := by
  by_contra hcon
  rw [VisitsIO, not_frequently] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hcon
  obtain ⟨N, hN⟩ := h (n₀ + 1)
  have hsub : visits β ξ s t N ⊆ Finset.range n₀ := by
    intro n hn
    obtain ⟨-, h2⟩ := mem_visits.mp hn
    by_contra hlt
    exact hn₀ n (not_lt.mp (fun hc => hlt (Finset.mem_range.mpr hc))) h2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  rw [visitCount] at hN
  omega

/-- A visit count that is eventually at least an unbounded function is unbounded. -/
theorem visitCount_unbounded_of_eventually_le {β ξ s t : ℝ} {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (h : ∀ᶠ N : ℕ in atTop, f N ≤ visitCount β ξ s t N) :
    ∀ K : ℕ, ∃ N : ℕ, K ≤ visitCount β ξ s t N := by
  intro K
  have hK : ∀ᶠ N : ℕ in atTop, (K : ℝ) ≤ f N := hf.eventually_ge_atTop (K : ℝ)
  obtain ⟨N, hN1, hN2⟩ := (hK.and h).exists
  exact ⟨N, by exact_mod_cast hN1.trans hN2⟩

theorem V1.visitsIO {β ξ s t : ℝ} (h : V1 β ξ s t) : VisitsIO β ξ s t := by
  obtain ⟨c, hc, hev⟩ := h
  refine visitsIO_of_visitCount_unbounded
    (visitCount_unbounded_of_eventually_le (f := fun N : ℕ => c * Real.log N) ?_ hev)
  exact Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem V2.V1 {β ξ s t : ℝ} (h : V2 β ξ s t) : V1 β ξ s t := by
  obtain ⟨θ, hθ, c, hc, hev⟩ := h
  -- elementary in place of an `isLittleO` import: `θ log N = log (N^θ) ≤ N^θ - 1 ≤ N^θ`
  refine ⟨c * θ, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hxpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hrpow : (0 : ℝ) < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hxpos θ
  have hlog : θ * Real.log (N : ℝ) ≤ (N : ℝ) ^ θ := by
    have h1 : Real.log ((N : ℝ) ^ θ) ≤ (N : ℝ) ^ θ - 1 := Real.log_le_sub_one_of_pos hrpow
    rw [Real.log_rpow hxpos] at h1
    linarith
  calc c * θ * Real.log (N : ℝ) = c * (θ * Real.log (N : ℝ)) := by ring
    _ ≤ c * (N : ℝ) ^ θ := by nlinarith
    _ ≤ visitCount β ξ s t N := hN

theorem V4.V2 {β ξ s t : ℝ} (h : V4 β ξ s t) : V2 β ξ s t := by
  have h' : 0 < lowerDensity β ξ s t := h
  refine ⟨1, one_pos, lowerDensity β ξ s t / 2, by linarith, ?_⟩
  have hlt : lowerDensity β ξ s t / 2 < lowerDensity β ξ s t := by linarith
  have hev : ∀ᶠ N : ℕ in atTop, lowerDensity β ξ s t / 2 < visitRatio β ξ s t N :=
    eventually_lt_of_lt_liminf hlt (isBoundedUnder_ge_visitRatio β ξ s t)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hxpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hone : ((N : ℝ)) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
  rw [hone]
  rw [visitRatio, lt_div_iff₀ hxpos] at hN
  linarith

theorem V4.V3 {β ξ s t : ℝ} (h : V4 β ξ s t) : V3 β ξ s t :=
  lt_of_lt_of_le h (lowerDensity_le_upperDensity β ξ s t)

theorem V3.visitsIO {β ξ s t : ℝ} (h : V3 β ξ s t) : VisitsIO β ξ s t := by
  refine visitsIO_of_visitCount_unbounded ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK⟩ := hcon
  -- bounded counts force `visitRatio ≤ K/N → 0`, hence `upperDensity ≤ 0`
  have hbd : visitRatio β ξ s t ≤ᶠ[atTop] fun N : ℕ => (K : ℝ) / N :=
    Eventually.of_forall fun N =>
      div_le_div_nonneg (by exact_mod_cast (hK N).le) (Nat.cast_nonneg N)
  have hzero : Tendsto (fun N : ℕ => (K : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)
  have hup : upperDensity β ξ s t ≤ 0 := by
    calc upperDensity β ξ s t ≤ limsup (fun N : ℕ => (K : ℝ) / N) atTop :=
          limsup_le_limsup hbd (isCoboundedUnder_le_visitRatio β ξ s t) hzero.isBoundedUnder_le
      _ = 0 := hzero.limsup_eq
  exact absurd h (not_lt.mpr hup)

theorem V5.V4 {β ξ s t : ℝ} (ht : 0 < t) (h : V5 β ξ s t) : V4 β ξ s t := by
  have h' : Tendsto (visitRatio β ξ s t) atTop (𝓝 t) := h
  show 0 < lowerDensity β ξ s t
  rw [lowerDensity, h'.liminf_eq]
  exact ht

/-- **Syndetic visits have positive lower density.** -/
theorem V4S.V4 {β ξ s t : ℝ} (h : V4S β ξ s t) : V4 β ξ s t := by
  classical
  obtain ⟨B, hB⟩ := h
  set b : ℕ := B + 1 with hb
  have hbpos : (0 : ℕ) < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  choose k hk1 hk2 hk3 using fun j : ℕ => hB (j * b)
  -- the chosen visits of consecutive blocks are strictly increasing, hence distinct
  have hmono : ∀ i j : ℕ, i < j → k i < k j := by
    intro i j hij
    have hstep : i * b + b ≤ j * b := by
      have h1 : (i + 1) * b ≤ j * b := Nat.mul_le_mul (Nat.succ_le_of_lt hij) (le_refl b)
      have h2 : (i + 1) * b = i * b + b := by ring
      omega
    have h1 : k i ≤ i * b + B := hk2 i
    have h2 : j * b ≤ k j := hk1 j
    omega
  have hcount : ∀ N : ℕ, N / b ≤ visitCount β ξ s t N := by
    intro N
    have hmaps : ∀ j ∈ Finset.range (N / b), k j ∈ visits β ξ s t N := by
      intro j hj
      have hj' : j < N / b := Finset.mem_range.mp hj
      have hblock : j * b + b ≤ N := by
        have h1 : (j + 1) * b ≤ (N / b) * b := Nat.mul_le_mul (Nat.succ_le_of_lt hj') (le_refl b)
        have h2 : (N / b) * b ≤ N := Nat.div_mul_le_self N b
        have h3 : (j + 1) * b = j * b + b := by ring
        omega
      have h4 : k j ≤ j * b + B := hk2 j
      exact mem_visits.mpr ⟨by omega, hk3 j⟩
    have hinj : Set.InjOn k (Finset.range (N / b)) := by
      intro i _ j _ hij
      by_contra hne
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact absurd hij (Nat.ne_of_lt (hmono i j hlt))
      · have hlt : j < i := lt_of_le_of_ne hge fun hc => hne hc.symm
        exact absurd hij.symm (Nat.ne_of_lt (hmono j i hlt))
    have := Finset.card_le_card_of_injOn k (fun j hj => hmaps j (Finset.mem_coe.mp hj)) hinj
    rw [Finset.card_range] at this
    exact this
  refine lt_of_lt_of_le (show (0 : ℝ) < 1 / (2 * b) by positivity) ?_
  refine le_liminf_of_le (isCoboundedUnder_ge_visitRatio β ξ s t) ?_
  filter_upwards [eventually_ge_atTop (2 * b)] with N hN
  have hN' : (2 : ℝ) * b ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hdiv : (N : ℝ) / b - 1 ≤ ((N / b : ℕ) : ℝ) := by
    have h1 : b * (N / b) + N % b = N := Nat.div_add_mod N b
    have h2 : N % b < b := Nat.mod_lt N hbpos
    have h3 : (N : ℝ) < (b : ℝ) * ((N / b : ℕ) : ℝ) + b := by
      have h4 : (N : ℕ) < b * (N / b) + b := by omega
      exact_mod_cast h4
    rw [sub_le_iff_le_add, div_le_iff₀ hbR]
    nlinarith
  have hge : ((N / b : ℕ) : ℝ) ≤ (visitCount β ξ s t N : ℝ) := by exact_mod_cast hcount N
  rw [visitRatio, le_div_iff₀ hNpos]
  have e1 : (N : ℝ) / b - 1 / (2 * b) * N = (N : ℝ) / (2 * b) := by field_simp; ring
  have e2 : (1 : ℝ) ≤ (N : ℝ) / (2 * b) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/-! ## M6 and the dyadic reduction -/

/-- **M6** at the orbit `n ↦ ξβⁿ`: every arc of positive length has positive lower density of
visits.  Milestone M6 itself is `β = 3/2`, `ξ = 1`. -/
def M6 (β ξ : ℝ) : Prop := ∀ s t : ℝ, 0 < t → V4 β ξ s t

/-- The dyadic form of M6: every dyadic window `[b/2ʷ, (b+1)/2ʷ)` has positive lower density. -/
def M6dyadic (β ξ : ℝ) : Prop := ∀ (w : ℕ) (b : ℤ), V4 β ξ ((b : ℝ) / 2 ^ w) (1 / 2 ^ w)

/-- **Sub-arc lemma**: a visit to the arc `[s+u, s+u+t')` is a visit to `[s, s+t)` whenever the
former sits inside the latter (`u ≥ 0`, `u + t' ≤ t ≤ 1`).  Because `inArc` is phrased through
`Int.fract`, no wrap-around case split is needed. -/
theorem inArc_of_inArc_shift {s t u t' x : ℝ} (hu : 0 ≤ u) (huv : u + t' ≤ t) (ht : t ≤ 1)
    (hx : inArc (s + u) t' x) : inArc s t x := by
  have hfr0 : 0 ≤ Int.fract (x - (s + u)) := Int.fract_nonneg _
  have hkey : x - s = Int.fract (x - (s + u)) + u + ((⌊x - (s + u)⌋ : ℤ) : ℝ) := by
    have := Int.floor_add_fract (x - (s + u))
    linarith
  have hsum : Int.fract (x - (s + u)) + u < 1 := by
    have : Int.fract (x - (s + u)) < t' := hx
    linarith
  unfold inArc
  rw [hkey, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, hsum⟩]
  have : Int.fract (x - (s + u)) < t' := hx
  linarith

/-- **Covering lemma**: every arc of length `t ∈ (0,1]` contains a dyadic window. -/
theorem exists_dyadic_subarc (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ (w : ℕ) (b : ℤ), 0 ≤ (b : ℝ) / 2 ^ w - s ∧ ((b : ℝ) / 2 ^ w - s) + 1 / 2 ^ w ≤ t := by
  obtain ⟨w, hw⟩ := pow_unbounded_of_one_lt (2 / t) (by norm_num : (1:ℝ) < 2)
  have hwpos : (0 : ℝ) < 2 ^ w := by positivity
  have hle : 2 / (2 : ℝ) ^ w ≤ t := by
    rw [div_le_iff₀ hwpos]
    rw [div_lt_iff₀ ht] at hw
    linarith
  refine ⟨w, ⌈s * 2 ^ w⌉, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ hwpos]
    exact Int.le_ceil _
  · have h1 : (⌈s * 2 ^ w⌉ : ℝ) < s * 2 ^ w + 1 := Int.ceil_lt_add_one _
    have h2 : (⌈s * 2 ^ w⌉ : ℝ) / 2 ^ w - s < 1 / 2 ^ w := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hwpos]
      have : (1 : ℝ) / 2 ^ w * 2 ^ w = 1 := by field_simp
      nlinarith [hwpos]
    have : (2 : ℝ) / 2 ^ w = 1 / 2 ^ w + 1 / 2 ^ w := by ring
    linarith

/-- **The dyadic reduction (WP0).**  M6 holds iff it holds at every dyadic window. -/
theorem M6_iff_dyadic (β ξ : ℝ) : M6 β ξ ↔ M6dyadic β ξ := by
  constructor
  · intro h w b
    exact h _ _ (by positivity)
  · intro h s t ht
    by_cases ht1 : t ≤ 1
    · obtain ⟨w, b, hu, huv⟩ := exists_dyadic_subarc s ht
      have hsub : lowerDensity β ξ ((b : ℝ) / 2 ^ w) (1 / 2 ^ w) ≤ lowerDensity β ξ s t := by
        refine liminf_le_liminf (Eventually.of_forall fun N => ?_)
          (isBoundedUnder_ge_visitRatio _ _ _ _) (isCoboundedUnder_ge_visitRatio _ _ _ _)
        refine div_le_div_nonneg ?_ (Nat.cast_nonneg N)
        refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
        obtain ⟨h1, h2⟩ := mem_visits.mp hn
        refine mem_visits.mpr ⟨h1, inArc_of_inArc_shift hu huv ht1 ?_⟩
        have : s + ((b : ℝ) / 2 ^ w - s) = (b : ℝ) / 2 ^ w := by ring
        rwa [this]
      exact lt_of_lt_of_le (h w b) hsub
    · -- an arc longer than `1` is everything
      rw [not_le] at ht1
      have hall : ∀ N : ℕ, visitCount β ξ s t N = N := by
        intro N
        have hset : visits β ξ s t N = Finset.range N := by
          ext n
          simp only [Finset.mem_range]
          exact ⟨fun hn => (mem_visits.mp hn).1,
            fun hn => mem_visits.mpr ⟨hn, lt_trans (Int.fract_lt_one _) ht1⟩⟩
        simp [visitCount, hset]
      have : lowerDensity β ξ s t = 1 := by
        have hone : ∀ᶠ N : ℕ in atTop, visitRatio β ξ s t N = 1 := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hNpos : (N : ℝ) ≠ 0 := by
            have : 0 < N := hN
            positivity
          rw [visitRatio, hall N, div_self hNpos]
        rw [lowerDensity, liminf_congr hone]
        simp
      show 0 < lowerDensity β ξ s t
      rw [this]; norm_num

end Z32
