/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.CertComplete
import Z32.EscapeBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

/-!
# The depth–size bound: what a block certificate costs in depth and blocks

(plan z32-transform, milestone M5, experiment X‑U §6, target T6)

A block certificate (`Z32.BlockCert.Cert`) proves a union `U ⊆ [0,1)` holds no orbit of the carry
relation `q·y_{n+1} = p·yₙ − sₙ`.  The certified unions have been getting larger — `20/39` in
[Dub08], then `25/36`, `17/24`, `43/60`, `0.754167` here — and target **T6** asked for a family
whose measure tends to `1`.  This file prices that: **a certificate cannot certify a set of
measure close to `1` without paying, in funnel depth or in blocks, like `1/δ`**.

## The two halves

Write `δ = |[0,1) ∖ U|`, let `T₀ = U` and `T_{k+1} = U ∩ f⁻¹(T_k)` be the exact funnel
(`Z32.funnel`), where `f⁻¹(S)` is the set of points of `[0,1)` with a successor in `S`
(`Z32.pre`).

* **Expansion.**  `|f⁻¹(S)| ≥ |S|` (`Z32.volume_le_volume_pre`), so the funnel loses at most `δ`
  per level: `|T_k| ≥ 1 − (k+1)δ` (`Z32.one_le_volume_funnel_add`).
* **Contraction.**  Past the certifying depth `K = c.levels.length` the block graph of an unranked
  certificate is a partial function, so the carry word of a confined orbit is forced by its first
  block, and two orbits sharing a block stay `(q/p)ʲ` apart
  (`Z32.BlockCert.abs_sub_le_of_memI_block`).  Hence `T_{K+j}` is covered by the `B` blocks, each
  holding a set of diameter `(q/p)ʲ`: `|T_{K+j}| ≤ B·(q/p)ʲ`
  (`Z32.BlockCert.volume_funnel_le_of_cert`).

Comparing them at depth `K + j` and optimising `j` gives the headline

```
    1 ≤ 2·δ·(K + 2 + log_{p/q}(2B)),     i.e.     1/(2δ) ≲ K + log_{p/q} B,
```

`Z32.depth_size` (one exponent), `Z32.depth_size_logb` (optimised), and
`Z32.BlockCert.cert_depth_size` for a certificate's own funnel.  Two corollaries read it
backwards: a valid certificate leaves a hole of positive measure
(`Z32.BlockCert.volume_hole_pos`) — a measure-theoretic sharpening of
`Z32.BlockCert.ok_eq_false_of_full` — and certifies a set of measure `< 1`
(`Z32.BlockCert.volume_certSet_lt_one`).  `Z32.BlockCert.hole_union_2536` is the bound on the
`25/36` record: `δ ≥ 1/44`, against the true `11/36`.

## What it costs T6

C‑8 asked for `δ_P ≤ C·(q/p)^{cP}`.  The bound turns that into `K_P + log_{p/q} B_P ≳
C⁻¹(p/q)^{cP}` — depth exponential in `P` — and since the funnel's common denominator is `G·p^K`,
the certificate *data* is then doubly exponential in `P`.  A parametric certificate of bounded
shape, valid for every `P`, does not exist in this format.  That is the reason experiment X‑U
dropped T6's stated form, and it is now a theorem rather than a derivation.

## The proof of the expansion half

The note's §6 derived `|f⁻¹(S)| ≥ |S|` from two counting facts — `Σ_s |g_s(S) ∩ [0,1)| = 2|S|`
exactly, and pointwise multiplicity `≤ 2`.  Neither is needed.  The branch preimage factors as

```
    f⁻¹ = slice p ∘ fold q,
```

where `fold q` (`Z32.fold`) is the `q`-to-one map `v ↦ fract(q·v)` and `slice n` (`Z32.slice`) is
the `n`-to-one map's preimage `{y ∈ [0,1) : fract(n·y) ∈ A}` — both written as finite unions of
*affine preimages*, never images, so that `Real.volume_preimage_mul_left` and translation
invariance apply to arbitrary sets and no image needs to be shown measurable.  Unfolding preserves
measure exactly (`Z32.volume_slice`, the `n` pieces are disjoint) and folding cannot shrink
(`Z32.subset_slice_fold`: `S ⊆ slice q (fold q S)`), which is the whole of the expansion half.
Nor does the contraction half need the Lebesgue measure of an interval list: `Real.volume_le_diam`
bounds the measure of each block's share by its diameter, for arbitrary sets.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), 951–958 — Corollary 1.2, the `20/39` union in print.
* [KK18] J. Kari, J. Kopra, *Cellular automata and powers of `p/q`*, RAIRO ITA **51** (2017/18) —
  Problem 6.1, the curve these records sit on.
* `plans/plan-z32-transform.html` milestone M5, target T6; `plans/note-z32transform-XU.html` §6.
-/

namespace Z32

open MeasureTheory Set
open scoped ENNReal

/-! ## The `n`-fold unfolding of a subset of `[0,1)` -/

/-- The `n`-fold unfolding of `A ⊆ [0,1)`: the set `{y ∈ [0,1) : fract (n·y) ∈ A}`, written as the
union of the `n` affine preimages `{y : n·y − i ∈ A}` so that no `Int.fract` ever enters a measure
computation. -/
def slice (n : ℕ) (A : Set ℝ) : Set ℝ :=
  ⋃ i ∈ Finset.range n, ((fun y => (n : ℝ) * y - (i : ℝ)) ⁻¹' A)

theorem mem_slice_iff {n : ℕ} {A : Set ℝ} {y : ℝ} :
    y ∈ slice n A ↔ ∃ i < n, (n : ℝ) * y - (i : ℝ) ∈ A := by
  simp [slice]

/-- The `i`-th piece of the unfolding lies in `[i/n, (i+1)/n)`, in the scaled form the proofs
below use. -/
theorem slice_piece_bounds {n i : ℕ} {A : Set ℝ} (hA : A ⊆ Ico (0 : ℝ) 1) {y : ℝ}
    (hy : (n : ℝ) * y - (i : ℝ) ∈ A) : (i : ℝ) ≤ (n : ℝ) * y ∧ (n : ℝ) * y < (i : ℝ) + 1 := by
  have h := hA hy
  simp only [mem_Ico] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem slice_subset_Ico {n : ℕ} {A : Set ℝ} (hA : A ⊆ Ico (0 : ℝ) 1) :
    slice n A ⊆ Ico (0 : ℝ) 1 := by
  intro y hy
  rw [mem_slice_iff] at hy
  obtain ⟨i, hi, hmem⟩ := hy
  obtain ⟨h1, h2⟩ := slice_piece_bounds hA hmem
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hin : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-- The Lebesgue measure of one affine piece: `y ↦ n·y − i` contracts by `1/n`, and holds for an
arbitrary `A` because the map is a measurable equivalence. -/
theorem volume_preimage_affine {n : ℕ} (hn : 0 < n) (i : ℕ) (A : Set ℝ) :
    volume ((fun y => (n : ℝ) * y - (i : ℝ)) ⁻¹' A) = ENNReal.ofReal (1 / n) * volume A := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hset : (fun y => (n : ℝ) * y - (i : ℝ)) ⁻¹' A
      = ((n : ℝ) * ·) ⁻¹' ((fun z => (-(i : ℝ)) + z) ⁻¹' A) := by
    ext y; simp [sub_eq_neg_add, add_comm]
  rw [hset, Real.volume_preimage_mul_left hn', measure_preimage_add]
  congr 1
  rw [abs_of_nonneg (by positivity), one_div]

private theorem nat_mul_ofReal_inv {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) * ENNReal.ofReal (1 / n) = 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_one_div, div_self hn'.ne']
  simp

/-- **Unfolding does not increase measure.**  Subadditivity over the `n` pieces; no measurability
hypothesis. -/
theorem volume_slice_le {n : ℕ} (hn : 0 < n) (A : Set ℝ) : volume (slice n A) ≤ volume A := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  rw [Finset.sum_congr rfl fun i _ => volume_preimage_affine hn i A, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← mul_assoc, nat_mul_ofReal_inv hn, one_mul]

/-- **Unfolding preserves measure.**  The `n` pieces are disjoint — each lives in its own
`[i/n, (i+1)/n)` — so the sum is exact. -/
theorem volume_slice {n : ℕ} (hn : 0 < n) {A : Set ℝ} (hA : A ⊆ Ico (0 : ℝ) 1)
    (hAm : MeasurableSet A) : volume (slice n A) = volume A := by
  have hmeas : ∀ i : ℕ, MeasurableSet ((fun y => (n : ℝ) * y - (i : ℝ)) ⁻¹' A) := fun i =>
    hAm.preimage (by fun_prop)
  have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint
      fun i => (fun y => (n : ℝ) * y - (i : ℝ)) ⁻¹' A := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    obtain ⟨h1, h2⟩ := slice_piece_bounds hA hyi
    obtain ⟨h3, h4⟩ := slice_piece_bounds hA hyj
    have e1 : (i : ℝ) < (j : ℝ) + 1 := by linarith
    have e2 : (j : ℝ) < (i : ℝ) + 1 := by linarith
    have e1' : i < j + 1 := by exact_mod_cast e1
    have e2' : j < i + 1 := by exact_mod_cast e2
    exact hij (by omega)
  rw [slice, measure_biUnion_finset hdisj fun i _ => hmeas i,
    Finset.sum_congr rfl fun i _ => volume_preimage_affine hn i A, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← mul_assoc, nat_mul_ofReal_inv hn, one_mul]

/-! ## The folding map -/

/-- The `q`-fold folding of `S ⊆ [0,1)`: the image of `S` under `v ↦ fract (q·v)`, written as a
union of preimages under the `q` affine inverses. -/
def fold (q : ℕ) (S : Set ℝ) : Set ℝ :=
  ⋃ i ∈ Finset.range q, ((fun y => (y + (i : ℝ)) / (q : ℝ)) ⁻¹' S ∩ Ico (0 : ℝ) 1)

theorem mem_fold_iff {q : ℕ} {S : Set ℝ} {y : ℝ} :
    y ∈ fold q S ↔ ∃ i < q, (y + (i : ℝ)) / (q : ℝ) ∈ S ∧ y ∈ Ico (0 : ℝ) 1 := by
  simp only [fold, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_preimage,
    exists_prop]

theorem fold_subset_Ico {q : ℕ} {S : Set ℝ} : fold q S ⊆ Ico (0 : ℝ) 1 := by
  intro y hy
  rw [mem_fold_iff] at hy
  obtain ⟨-, -, -, h⟩ := hy
  exact h

theorem measurableSet_fold {q : ℕ} {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (fold q S) := by
  refine Finset.measurableSet_biUnion _ fun i _ => ?_
  exact (hS.preimage (by fun_prop)).inter measurableSet_Ico

/-- **Folding then unfolding recovers the set.**  Every `v ∈ S` is the `⌊q·v⌋`-th unfolding of
`fract (q·v) ∈ fold q S`. -/
theorem subset_slice_fold {q : ℕ} (hq : 0 < q) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) :
    S ⊆ slice q (fold q S) := by
  intro v hv
  have hv' := hS hv
  simp only [mem_Ico] at hv'
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set i : ℕ := ⌊(q : ℝ) * v⌋₊ with hi
  have hqv0 : (0 : ℝ) ≤ (q : ℝ) * v := mul_nonneg hqR.le hv'.1
  have hle : (i : ℝ) ≤ (q : ℝ) * v := Nat.floor_le hqv0
  have hlt : (q : ℝ) * v < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hiq : i < q := by
    rw [hi, Nat.floor_lt hqv0]
    nlinarith [hv'.2]
  rw [mem_slice_iff]
  refine ⟨i, hiq, ?_⟩
  rw [mem_fold_iff]
  refine ⟨i, hiq, ?_, ?_, ?_⟩
  · have hval : ((q : ℝ) * v - (i : ℝ) + (i : ℝ)) / (q : ℝ) = v := by
      field_simp
      ring
    rw [hval]; exact hv
  · linarith
  · linarith

/-! ## The branch preimage of the carry relation -/

/-- `f⁻¹(S)`: the points of `[0,1)` with a successor in `S` under the carry relation
`q·v = p·y − s`. -/
def pre (p q : ℕ) (S : Set ℝ) : Set ℝ :=
  {y | y ∈ Ico (0 : ℝ) 1 ∧ ∃ v ∈ S, ∃ s : ℤ, (q : ℝ) * v = (p : ℝ) * y - (s : ℝ)}

theorem pre_subset_Ico {p q : ℕ} {S : Set ℝ} : pre p q S ⊆ Ico (0 : ℝ) 1 := fun _ hy => hy.1

/-- **The preimage is an unfolding of a folding.**  `f⁻¹(S) = slice p (fold q S)`: the carry
relation is "multiply by `p` mod 1, then divide by `q` in every admissible way". -/
theorem pre_eq_slice_fold {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {S : Set ℝ}
    (hS : S ⊆ Ico (0 : ℝ) 1) : pre p q S = slice p (fold q S) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  ext y
  constructor
  · rintro ⟨hy, v, hvS, s, hs⟩
    have hy' : (0 : ℝ) ≤ y ∧ y < 1 := ⟨hy.1, hy.2⟩
    have hv' := hS hvS
    simp only [mem_Ico] at hv'
    have hpy0 : (0 : ℝ) ≤ (p : ℝ) * y := mul_nonneg hpR.le hy'.1
    set i : ℕ := ⌊(p : ℝ) * y⌋₊ with hi
    have hle : (i : ℝ) ≤ (p : ℝ) * y := Nat.floor_le hpy0
    have hlt : (p : ℝ) * y < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hip : i < p := by
      rw [hi, Nat.floor_lt hpy0]
      nlinarith [hy'.2]
    -- the carry index `j = i − s` is a natural number below `q`
    have hjZ : (0 : ℤ) ≤ (i : ℤ) - s ∧ (i : ℤ) - s < (q : ℤ) := by
      constructor
      · by_contra hcon
        have hz : (i : ℤ) - s ≤ -1 := by omega
        have : (((i : ℤ) - s : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hz
        push_cast at this
        nlinarith [hv'.1]
      · by_contra hcon
        have hz : (q : ℤ) ≤ (i : ℤ) - s := by omega
        have : ((q : ℤ) : ℝ) ≤ (((i : ℤ) - s : ℤ) : ℝ) := by exact_mod_cast hz
        push_cast at this
        nlinarith [hv'.2]
    set j : ℕ := ((i : ℤ) - s).toNat with hj
    have hjcast : ((j : ℤ) : ℝ) = (i : ℝ) - (s : ℝ) := by
      rw [hj, Int.toNat_of_nonneg hjZ.1]; push_cast; ring
    have hjq : j < q := by omega
    rw [mem_slice_iff]
    refine ⟨i, hip, ?_⟩
    rw [mem_fold_iff]
    refine ⟨j, hjq, ?_, ?_, ?_⟩
    · have hval : ((p : ℝ) * y - (i : ℝ) + (j : ℝ)) / (q : ℝ) = v := by
        have : (j : ℝ) = (i : ℝ) - (s : ℝ) := by exact_mod_cast hjcast
        rw [this]
        field_simp
        linarith [hs]
      rw [hval]; exact hvS
    · linarith
    · linarith
  · intro hy
    rw [mem_slice_iff] at hy
    obtain ⟨i, hip, hmem⟩ := hy
    rw [mem_fold_iff] at hmem
    obtain ⟨j, hjq, hvS, hlo, hhi⟩ := hmem
    have hipR : (i : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hip
    refine ⟨⟨?_, ?_⟩, ((p : ℝ) * y - (i : ℝ) + (j : ℝ)) / (q : ℝ), hvS, (i : ℤ) - (j : ℤ), ?_⟩
    · nlinarith [Nat.cast_nonneg (α := ℝ) i]
    · nlinarith
    · field_simp
      push_cast
      ring

theorem measurableSet_pre {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {S : Set ℝ}
    (hS : S ⊆ Ico (0 : ℝ) 1) (hSm : MeasurableSet S) : MeasurableSet (pre p q S) := by
  rw [pre_eq_slice_fold hp hq hS, slice]
  exact Finset.measurableSet_biUnion _ fun i _ => (measurableSet_fold hSm).preimage (by fun_prop)

/-- **The branch preimage never loses measure**: `|f⁻¹(S)| ≥ |S|`.

This is the exact content of facts (i) and (ii) of the note's §6 — "the four branches have ratio
`q/p` and cover `[0,1)` with total multiplicity `p`", and "every point has exactly `q` successors"
— packaged as one inequality.  The proof is the factorisation `f⁻¹ = slice p ∘ fold q`: folding by
`q` is a `q`-to-one measure-preserving map, so it cannot shrink a set, and unfolding by `p`
preserves measure exactly. -/
theorem volume_le_volume_pre {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {S : Set ℝ}
    (hS : S ⊆ Ico (0 : ℝ) 1) (hSm : MeasurableSet S) : volume S ≤ volume (pre p q S) := by
  calc volume S ≤ volume (slice q (fold q S)) := measure_mono (subset_slice_fold hq hS)
    _ ≤ volume (fold q S) := volume_slice_le hq _
    _ = volume (slice p (fold q S)) :=
        (volume_slice hp fold_subset_Ico (measurableSet_fold hSm)).symm
    _ = volume (pre p q S) := by rw [pre_eq_slice_fold hp hq hS]

/-! ## The exact funnel -/

/-- The **exact funnel** of `U`: `T₀ = U` and `T_{k+1} = U ∩ f⁻¹(T_k)`, the points of `U` with a
chain of `k` successors inside `U`.  A certificate's `levels` are supersets of these. -/
def funnel (p q : ℕ) (U : Set ℝ) : ℕ → Set ℝ
  | 0 => U
  | k + 1 => U ∩ pre p q (funnel p q U k)

theorem funnel_subset_Ico {p q : ℕ} {U : Set ℝ} (hU : U ⊆ Ico (0 : ℝ) 1) :
    ∀ k, funnel p q U k ⊆ Ico (0 : ℝ) 1
  | 0 => hU
  | _ + 1 => fun _ hy => hU hy.1

theorem measurableSet_funnel {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ}
    (hU : U ⊆ Ico (0 : ℝ) 1) (hUm : MeasurableSet U) :
    ∀ k, MeasurableSet (funnel p q U k)
  | 0 => hUm
  | k + 1 =>
      hUm.inter (measurableSet_pre hp hq (funnel_subset_Ico hU k)
        (measurableSet_funnel hp hq hU hUm k))

/-- **The funnel loses measure only through the hole.**  With `δ = |[0,1) ∖ U|`,
`|T_k| ≥ 1 − (k+1)δ`. -/
theorem one_le_volume_funnel_add {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ}
    (hU : U ⊆ Ico (0 : ℝ) 1) (hUm : MeasurableSet U) (k : ℕ) :
    1 ≤ volume (funnel p q U k) + ((k : ℝ≥0∞) + 1) * volume (Ico (0 : ℝ) 1 \ U) := by
  induction k with
  | zero =>
    have h1 : volume (Ico (0 : ℝ) 1) ≤ volume (funnel p q U 0) + volume (Ico (0 : ℝ) 1 \ U) := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro y hy
      by_cases h : y ∈ U
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    simpa using h1
  | succ k ih =>
    have hstep : volume (funnel p q U k)
        ≤ volume (funnel p q U (k + 1)) + volume (Ico (0 : ℝ) 1 \ U) := by
      refine le_trans (volume_le_volume_pre hp hq (funnel_subset_Ico hU k)
        (measurableSet_funnel hp hq hU hUm k)) ?_
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro y hy
      by_cases h : y ∈ U
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr ⟨pre_subset_Ico hy, h⟩
    refine le_trans ih ?_
    have : volume (funnel p q U k) + ((k : ℝ≥0∞) + 1) * volume (Ico (0 : ℝ) 1 \ U)
        ≤ (volume (funnel p q U (k + 1)) + volume (Ico (0 : ℝ) 1 \ U))
          + ((k : ℝ≥0∞) + 1) * volume (Ico (0 : ℝ) 1 \ U) := by
      exact add_le_add hstep le_rfl
    refine le_trans this (le_of_eq ?_)
    push_cast
    ring

/-- The real-valued form of `Z32.one_le_volume_funnel_add`; every measure in sight is at most `1`,
so nothing is lost in `ENNReal.toReal`. -/
theorem one_le_volume_funnel_toReal {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ}
    (hU : U ⊆ Ico (0 : ℝ) 1) (hUm : MeasurableSet U) (k : ℕ) :
    1 ≤ (volume (funnel p q U k)).toReal
      + ((k : ℝ) + 1) * (volume (Ico (0 : ℝ) 1 \ U)).toReal := by
  have hIco : volume (Ico (0 : ℝ) 1) = 1 := by simp
  have hf : volume (funnel p q U k) ≤ 1 := hIco ▸ measure_mono (funnel_subset_Ico hU k)
  have hd : volume (Ico (0 : ℝ) 1 \ U) ≤ 1 := hIco ▸ measure_mono Set.sdiff_subset
  have hfne : volume (funnel p q U k) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hf
  have hdne : volume (Ico (0 : ℝ) 1 \ U) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd
  have hcne : ((k : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  have hmne : ((k : ℝ≥0∞) + 1) * volume (Ico (0 : ℝ) 1 \ U) ≠ ⊤ := ENNReal.mul_ne_top hcne hdne
  have hsum : volume (funnel p q U k) + ((k : ℝ≥0∞) + 1) * volume (Ico (0 : ℝ) 1 \ U) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfne, hmne⟩
  have h := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hsum).mpr
    (one_le_volume_funnel_add hp hq hU hUm k)
  rw [ENNReal.toReal_one, ENNReal.toReal_add hfne hmne, ENNReal.toReal_mul] at h
  have hcast : ((k : ℝ≥0∞) + 1).toReal = (k : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_one, ENNReal.toReal_natCast]
  rwa [hcast] at h

/-- **The depth–size bound, one exponent at a time.**  If the funnel at depth `K + j` has measure
at most `B`, then `(K + j + 1)·δ + B ≥ 1`.

The two sides pull against each other: the funnel can only lose `δ` per level
(`Z32.one_le_volume_funnel_add`), while a certificate of depth `K` with `B` blocks confines it to
`B` intervals of length `(q/p)ʲ` (`Z32.BlockCert.volume_funnel_le_of_cert`). -/
theorem depth_size {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ} (hU : U ⊆ Ico (0 : ℝ) 1)
    (hUm : MeasurableSet U) {K j : ℕ} {B : ℝ}
    (hcov : (volume (funnel p q U (K + j))).toReal ≤ B) :
    1 ≤ ((K : ℝ) + j + 1) * (volume (Ico (0 : ℝ) 1 \ U)).toReal + B := by
  have h := one_le_volume_funnel_toReal hp hq hU hUm (K + j)
  push_cast at h
  linarith

/-- **The depth–size bound, in the form that prices a target.**  A union of measure `1 − δ` whose
funnel is confined by `B` blocks from depth `K` on obeys
`1/(2δ) ≤ K + 2 + log_{p/q}(2B)`, written multiplicatively so that `δ = 0` needs no side
condition.

So `δ` cannot be made small without paying in depth or in blocks: driving `δ` down like
`C·(q/p)^{cP}` — the rate conjecture C‑8 asked for — forces `K + log_{p/q} B` to grow like
`(p/q)^{cP}`, exponentially in `P`. -/
theorem depth_size_logb {p q : ℕ} (hq : 0 < q) (hqp : q < p) {U : Set ℝ}
    (hU : U ⊆ Ico (0 : ℝ) 1) (hUm : MeasurableSet U) {K B : ℕ} (hB : 0 < B)
    (hcov : ∀ j, (volume (funnel p q U (K + j))).toReal ≤ (B : ℝ) * ((q : ℝ) / (p : ℝ)) ^ j) :
    1 ≤ 2 * (volume (Ico (0 : ℝ) 1 \ U)).toReal
          * ((K : ℝ) + 2 + Real.logb ((p : ℝ) / (q : ℝ)) (2 * B)) := by
  have hp : 0 < p := lt_trans hq hqp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hb : (1 : ℝ) < (p : ℝ) / (q : ℝ) := by
    rw [lt_div_iff₀ hqR, one_mul]; exact_mod_cast hqp
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hx : (0 : ℝ) < 2 * B := by linarith
  set L : ℝ := Real.logb ((p : ℝ) / (q : ℝ)) (2 * B) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hb (by linarith)
  set j : ℕ := ⌈L⌉₊ with hj
  have hjL : (j : ℝ) ≤ L + 1 := le_of_lt (by rw [hj]; exact Nat.ceil_lt_add_one hL0)
  have hpow : 2 * (B : ℝ) ≤ ((p : ℝ) / (q : ℝ)) ^ j := le_pow_natCeil_logb hb hx
  have hpowpos : (0 : ℝ) < ((p : ℝ) / (q : ℝ)) ^ j := by positivity
  -- the confinement bound at this exponent is below `1/2`
  have hhalf : (B : ℝ) * ((q : ℝ) / (p : ℝ)) ^ j ≤ 1 / 2 := by
    have hqp' : ((q : ℝ) / (p : ℝ)) ^ j = (((p : ℝ) / (q : ℝ)) ^ j)⁻¹ := by
      rw [← inv_pow]
      congr 1
      rw [inv_div]
    rw [hqp', ← div_eq_mul_inv, div_le_iff₀ hpowpos]
    linarith
  have hmain := depth_size hp hq hU hUm (K := K) (j := j) ((hcov j).trans hhalf)
  have hδ : 0 ≤ (volume (Ico (0 : ℝ) 1 \ U)).toReal := ENNReal.toReal_nonneg
  nlinarith [hmain, hδ, hjL]

/-! ## From a funnel point to an orbit -/

/-- One canonical successor of `y`: `fract(p·y)/q`, always in `[0,1)`.  Its only role is to extend
a finite chain to a total sequence, which is the shape the certificate lemmas consume. -/
noncomputable def nextPt (p q : ℕ) (y : ℝ) : ℝ := Int.fract ((p : ℝ) * y) / (q : ℝ)

/-- The orbit of `y` under the canonical successor. -/
noncomputable def orbit (p q : ℕ) (y : ℝ) : ℕ → ℝ := fun n => (nextPt p q)^[n] y

theorem nextPt_nonneg (p q : ℕ) (y : ℝ) : 0 ≤ nextPt p q y :=
  div_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg q)

theorem nextPt_lt_one {q : ℕ} (hq : 0 < q) (p : ℕ) (y : ℝ) : nextPt p q y < 1 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [nextPt, div_lt_one (by linarith)]
  exact lt_of_lt_of_le (Int.fract_lt_one _) hqR

theorem nextPt_rec {q : ℕ} (hq : 0 < q) (p : ℕ) (y : ℝ) :
    (q : ℝ) * nextPt p q y = (p : ℝ) * y - ((⌊(p : ℝ) * y⌋ : ℤ) : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [nextPt, Int.fract]
  field_simp

theorem orbit_zero (p q : ℕ) (y : ℝ) : orbit p q y 0 = y := rfl

theorem orbit_succ (p q : ℕ) (y : ℝ) (n : ℕ) :
    orbit p q y (n + 1) = nextPt p q (orbit p q y n) :=
  Function.iterate_succ_apply' _ _ _

/-- **A funnel point is the start of a confined orbit.**  Membership in `T_N` is the *existence*
of a chain of `N` successors inside `U`; the canonical successor extends that chain to a total
sequence obeying the carry relation everywhere, which is the shape
`Z32.BlockCert.Cert.memL_blocks_of_le` consumes. -/
theorem exists_chain_of_mem_funnel {p q : ℕ} (hq : 0 < q) {U : Set ℝ} (hU : U ⊆ Ico (0 : ℝ) 1) :
    ∀ (N : ℕ) {y : ℝ}, y ∈ funnel p q U N →
      ∃ (z : ℕ → ℝ) (w : ℕ → ℤ), z 0 = y ∧ (∀ n, 0 ≤ z n) ∧ (∀ n, z n < 1) ∧
        (∀ n, (q : ℝ) * z (n + 1) = (p : ℝ) * z n - (w n : ℝ)) ∧ (∀ n ≤ N, z n ∈ U) := by
  intro N
  induction N with
  | zero =>
    intro y hy
    have hy' := hU hy
    refine ⟨orbit p q y, fun n => ⌊(p : ℝ) * orbit p q y n⌋, rfl, ?_, ?_, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hy'.1
      | succ m => rw [orbit_succ]; exact nextPt_nonneg _ _ _
    · intro n
      cases n with
      | zero => exact hy'.2
      | succ m => rw [orbit_succ]; exact nextPt_lt_one hq _ _
    · intro n; rw [orbit_succ]; exact nextPt_rec hq _ _
    · intro n hn
      obtain rfl : n = 0 := by omega
      exact hy
  | succ N ih =>
    intro y hy
    obtain ⟨hyU, hyIco, v, hv, s, hs⟩ := hy
    obtain ⟨z, w, hz0, hznn, hz1, hzrec, hzU⟩ := ih hv
    refine ⟨fun n => match n with | 0 => y | m + 1 => z m,
      fun n => match n with | 0 => s | m + 1 => w m, rfl, ?_, ?_, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hyIco.1
      | succ m => exact hznn m
    · intro n
      cases n with
      | zero => exact hyIco.2
      | succ m => exact hz1 m
    · intro n
      cases n with
      | zero => show (q : ℝ) * z 0 = (p : ℝ) * y - (s : ℝ); rw [hz0]; exact hs
      | succ m => exact hzrec m
    · intro n hn
      cases n with
      | zero => exact hyU
      | succ m => exact hzU m (by omega)

namespace BlockCert

variable {c : Cert}

/-! ## What a certificate confines -/

/-- The set a certificate describes, inside the window: `⋃ c.U ∩ [0,1)`. -/
def certSet (c : Cert) : Set ℝ := {y : ℝ | memL c.D c.closed c.U y} ∩ Ico (0 : ℝ) 1

theorem measurableSet_memL (D : ℤ) (cl : Bool) (L : List Ivl) :
    MeasurableSet {y : ℝ | memL D cl L y} := by
  have hrw : {y : ℝ | memL D cl L y} = ⋃ I ∈ L.toFinset, {y : ℝ | memI D cl I y} := by
    ext y; simp [memL, List.mem_toFinset]
  rw [hrw]
  refine Finset.measurableSet_biUnion _ fun I _ => ?_
  cases cl with
  | false =>
    have : {y : ℝ | memI D false I y} = (fun y => (D : ℝ) * y) ⁻¹' Ico ((I.1 : ℝ)) ((I.2 : ℝ)) := by
      ext y; simp [memI, rleR]
    rw [this]
    exact measurableSet_Ico.preimage (by fun_prop)
  | true =>
    have : {y : ℝ | memI D true I y} = (fun y => (D : ℝ) * y) ⁻¹' Icc ((I.1 : ℝ)) ((I.2 : ℝ)) := by
      ext y; simp [memI, rleR, and_comm]
    rw [this]
    exact measurableSet_Icc.preimage (by fun_prop)

theorem certSet_subset_Ico (c : Cert) : certSet c ⊆ Ico (0 : ℝ) 1 := fun _ hy => hy.2

theorem measurableSet_certSet (c : Cert) : MeasurableSet (certSet c) :=
  (measurableSet_memL _ _ _).inter measurableSet_Ico

private theorem eq_of_mem_of_len_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h with
  | [x], _ => simp only [List.mem_singleton] at ha hb; rw [ha, hb]

/-- **Two orbits that start in the same block stay within `(q/p)ʲ`.**  For an unranked certificate
the block itinerary is forced by the starting block, so both orbits carry the *same* carry word for
`j` steps — and two orbits with the same word are `(q/p)ʲ` apart.

This is the finite-range form of `Z32.BlockCert.Cert.eq_of_memI_block`, which gets equality out of
an orbit confined forever; here the confinement lasts `K + j` steps and the conclusion is
quantitative. -/
theorem abs_sub_le_of_memI_block (hc : c.ok = true) (hst : c.strata = []) {j : ℕ}
    {z z' : ℕ → ℝ} {w w' : ℕ → ℤ}
    (hz0 : ∀ n, 0 ≤ z n) (hz1 : ∀ n, z n < 1)
    (hzrec : ∀ n, (c.q : ℝ) * z (n + 1) = (c.p : ℝ) * z n - (w n : ℝ))
    (hzU : ∀ n ≤ c.levels.length + j, memL c.D c.closed c.U (z n))
    (hz0' : ∀ n, 0 ≤ z' n) (hz1' : ∀ n, z' n < 1)
    (hzrec' : ∀ n, (c.q : ℝ) * z' (n + 1) = (c.p : ℝ) * z' n - (w' n : ℝ))
    (hzU' : ∀ n ≤ c.levels.length + j, memL c.D c.closed c.U (z' n))
    {I : Ivl} (hI : I ∈ c.blocks)
    (h0 : memI c.D c.closed I (z 0)) (h0' : memI c.D c.closed I (z' 0)) :
    |z 0 - z' 0| ≤ ((c.q : ℝ) / (c.p : ℝ)) ^ j := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  have hq0 : 0 < c.q := by omega
  have hp0 : 0 < c.p := by omega
  have hqR : (0 : ℝ) < (c.q : ℝ) := by exact_mod_cast hq0
  have hpR : (0 : ℝ) < (c.p : ℝ) := by exact_mod_cast hp0
  have hblk : ∀ n ≤ j, memL c.D c.closed c.blocks (z n) := fun n hn =>
    Cert.memL_blocks_of_le hc hz0 hz1 hzrec (N := c.levels.length + j) hzU (by omega)
  have hblk' : ∀ n ≤ j, memL c.D c.closed c.blocks (z' n) := fun n hn =>
    Cert.memL_blocks_of_le hc hz0' hz1' hzrec' (N := c.levels.length + j) hzU' (by omega)
  -- the two orbits share a block, hence a carry word, at every time up to `j`
  have key : ∀ n, n ≤ j → ∃ J ∈ c.blocks, memI c.D c.closed J (z n) ∧ memI c.D c.closed J (z' n)
      ∧ ∀ i < n, w i = w' i := by
    intro n
    induction n with
    | zero => intro _; exact ⟨I, hI, h0, h0', by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨J, hJ, hzJ, hz'J, hword⟩ := ih (by omega)
      obtain ⟨J1, hJ1, hzJ1⟩ := hblk (m + 1) hm
      obtain ⟨J1', hJ1', hz'J1'⟩ := hblk' (m + 1) hm
      have e1 : (w m, J1) ∈ outEdges c.D c.p c.q c.closed c.blocks J :=
        Cert.mem_outEdges_of_memI hc hz0 hz1 hzrec hJ1 hzJ hzJ1
      have e2 : (w' m, J1') ∈ outEdges c.D c.p c.q c.closed c.blocks J :=
        Cert.mem_outEdges_of_memI hc hz0' hz1' hzrec' hJ1' hz'J hz'J1'
      have heq := eq_of_mem_of_len_le_one (outEdges_length_le_one hc hst hJ) e1 e2
      refine ⟨J1, hJ1, hzJ1, ?_, ?_⟩
      · have hJJ : J1' = J1 := (congrArg Prod.snd heq).symm
        rw [← hJJ]; exact hz'J1'
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hword i h
        · subst h; exact congrArg Prod.fst heq
  obtain ⟨-, -, -, -, hwords⟩ := key j le_rfl
  -- equal carry words separate the two orbits at the rate `(p/q)ⁿ`
  have hgap : ∀ n, n ≤ j → (c.q : ℝ) ^ n * (z n - z' n) = (c.p : ℝ) ^ n * (z 0 - z' 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ihm := ih (by omega)
      have e1 := hzrec m
      have e2 := hzrec' m
      rw [hwords m (by omega)] at e1
      have hexp : (c.q : ℝ) ^ (m + 1) * (z (m + 1) - z' (m + 1))
          = (c.q : ℝ) ^ m * ((c.q : ℝ) * z (m + 1) - (c.q : ℝ) * z' (m + 1)) := by ring
      rw [hexp, e1, e2]
      have hpow : (c.p : ℝ) ^ (m + 1) = (c.p : ℝ) * (c.p : ℝ) ^ m := by ring
      rw [hpow]
      linear_combination (c.p : ℝ) * ihm
  have hjj := hgap j le_rfl
  have hzz : |z j - z' j| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [hz0 j, hz1' j]; linarith [hz0' j, hz1 j]]
  have habs : |z 0 - z' 0| * (c.p : ℝ) ^ j = |z j - z' j| * (c.q : ℝ) ^ j := by
    have hcon := congrArg abs hjj
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hqR.le j),
      abs_of_nonneg (pow_nonneg hpR.le j)] at hcon
    linarith
  have hfin : |z 0 - z' 0| * (c.p : ℝ) ^ j ≤ (c.q : ℝ) ^ j := by
    rw [habs]
    nlinarith [pow_pos hqR j, abs_nonneg (z j - z' j)]
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact hfin

/-- **A certificate confines its own funnel.**  Past the certifying depth `K = c.levels.length`,
each further level contracts by `q/p` inside every one of the `B = c.blocks.length` blocks, so
`|T_{K+j}| ≤ B·(q/p)ʲ`.

Both halves of the depth–size bound are now available for the same set: this one, and the
expansion bound `Z32.one_le_volume_funnel_add`, which cannot lose more than `δ` per level. -/
theorem volume_funnel_le_of_cert (hc : c.ok = true) (hst : c.strata = []) (j : ℕ) :
    volume (funnel c.p c.q (certSet c) (c.levels.length + j))
      ≤ (c.blocks.length : ℝ≥0∞) * ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j) := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  have hq0 : 0 < c.q := by omega
  set K := c.levels.length with hK
  set T := funnel c.p c.q (certSet c) (K + j) with hT
  -- every point of the funnel starts a confined orbit, hence lies in a block
  have hchain : ∀ y ∈ T, ∃ (z : ℕ → ℝ) (w : ℕ → ℤ), z 0 = y ∧ (∀ n, 0 ≤ z n) ∧ (∀ n, z n < 1) ∧
      (∀ n, (c.q : ℝ) * z (n + 1) = (c.p : ℝ) * z n - (w n : ℝ)) ∧
      (∀ n ≤ K + j, memL c.D c.closed c.U (z n)) := by
    intro y hy
    obtain ⟨z, w, hz0, hznn, hz1, hzrec, hzU⟩ :=
      exists_chain_of_mem_funnel hq0 (certSet_subset_Ico c) (K + j) hy
    exact ⟨z, w, hz0, hznn, hz1, hzrec, fun n hn => (hzU n hn).1⟩
  have hcover : T ⊆ ⋃ I ∈ c.blocks.toFinset, (T ∩ {y : ℝ | memI c.D c.closed I y}) := by
    intro y hy
    obtain ⟨z, w, hz0, hznn, hz1, hzrec, hmemL⟩ := hchain y hy
    have hb := Cert.memL_blocks_of_le hc hznn hz1 hzrec (N := K + j) hmemL (n := 0) (by omega)
    rw [hz0] at hb
    obtain ⟨I, hI, hIm⟩ := hb
    exact Set.mem_biUnion (List.mem_toFinset.mpr hI) ⟨hy, hIm⟩
  -- each block holds an interval of length `(q/p)ʲ` of the funnel
  have hpiece : ∀ I ∈ c.blocks.toFinset,
      volume (T ∩ {y : ℝ | memI c.D c.closed I y})
        ≤ ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j) := by
    intro I hIf
    have hI : I ∈ c.blocks := List.mem_toFinset.mp hIf
    refine le_trans (Real.volume_le_diam _) (Metric.ediam_le ?_)
    rintro x ⟨hxT, hxI⟩ y ⟨hyT, hyI⟩
    obtain ⟨z, w, hz0, hznn, hz1, hzrec, hzU⟩ := hchain x hxT
    obtain ⟨z', w', hz0', hznn', hz1', hzrec', hzU'⟩ := hchain y hyT
    have habs := abs_sub_le_of_memI_block hc hst hznn hz1 hzrec hzU hznn' hz1' hzrec' hzU' hI
      (by rw [hz0]; exact hxI) (by rw [hz0']; exact hyI)
    rw [hz0, hz0'] at habs
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal habs
  calc volume T ≤ ∑ I ∈ c.blocks.toFinset, volume (T ∩ {y : ℝ | memI c.D c.closed I y}) :=
        le_trans (measure_mono hcover) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _I ∈ c.blocks.toFinset, ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j) :=
        Finset.sum_le_sum hpiece
    _ = (c.blocks.toFinset.card : ℝ≥0∞) * ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (c.blocks.length : ℝ≥0∞) * ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j) := by
        gcongr
        exact_mod_cast c.blocks.toFinset_card_le

/-- **The depth–size bound for a block certificate.**  For every valid unranked certificate, with
`K = c.levels.length` the funnel depth, `B = c.blocks.length` the block count and
`δ = |[0,1) ∖ ⋃c.U|` the hole,
`1 ≤ 2·δ·(K + 2 + log_{p/q}(2B))`, i.e. `1/(2δ) ≤ K + 2 + log_{p/q}(2B)`.

Both inputs are theorems of this file: the funnel cannot lose more than `δ` per level
(`Z32.one_le_volume_funnel_add`, the exact `|f⁻¹(S)| ≥ |S|` of `Z32.volume_le_volume_pre`), and
past depth `K` the certificate confines it to `B` intervals of length `(q/p)ʲ`
(`Z32.BlockCert.volume_funnel_le_of_cert`). -/
theorem cert_depth_size (hc : c.ok = true) (hst : c.strata = []) (hne : c.blocks ≠ []) :
    1 ≤ 2 * (volume (Ico (0 : ℝ) 1 \ certSet c)).toReal
          * ((c.levels.length : ℝ) + 2
              + Real.logb ((c.p : ℝ) / (c.q : ℝ)) (2 * c.blocks.length)) := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  have hq0 : 0 < c.q := by omega
  refine depth_size_logb hq0 hqp (certSet_subset_Ico c) (measurableSet_certSet c)
    (K := c.levels.length) (B := c.blocks.length) (List.length_pos_iff.mpr hne) ?_
  intro j
  have h := volume_funnel_le_of_cert hc hst j
  have hxnn : (0 : ℝ) ≤ ((c.q : ℝ) / (c.p : ℝ)) ^ j := by positivity
  have hnetop : ((c.blocks.length : ℝ≥0∞) * ENNReal.ofReal (((c.q : ℝ) / (c.p : ℝ)) ^ j)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hTfin : volume (funnel c.p c.q (certSet c) (c.levels.length + j)) ≠ ⊤ :=
    ne_top_of_le_ne_top hnetop h
  have hstep := (ENNReal.toReal_le_toReal hTfin hnetop).mpr h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hxnn] at hstep

/-- **A valid certificate must remove a set of positive measure.**  Sharpening
`Z32.BlockCert.ok_eq_false_of_full`: not only can a certificate not cover all of `[0,1)`, it cannot
cover a set of full measure, and the hole it leaves is at least
`1 / (2(K + 2 + log_{p/q}(2B)))`. -/
theorem volume_hole_pos (hc : c.ok = true) (hst : c.strata = []) (hne : c.blocks ≠ []) :
    0 < (volume (Ico (0 : ℝ) 1 \ certSet c)).toReal := by
  rcases lt_or_eq_of_le (ENNReal.toReal_nonneg (a := volume (Ico (0 : ℝ) 1 \ certSet c))) with h | h
  · exact h
  · exfalso
    have hb := cert_depth_size hc hst hne
    rw [← h] at hb
    simp only [mul_zero, zero_mul] at hb
    linarith

/-- **The certified set has measure `< 1`.**  The same statement read forwards. -/
theorem volume_certSet_lt_one (hc : c.ok = true) (hst : c.strata = []) (hne : c.blocks ≠ []) :
    (volume (certSet c)).toReal < 1 := by
  have hsplit : volume (Ico (0 : ℝ) 1 ∩ certSet c) + volume (Ico (0 : ℝ) 1 \ certSet c)
      = volume (Ico (0 : ℝ) 1) := measure_inter_add_sdiff _ (measurableSet_certSet c)
  have hinter : Ico (0 : ℝ) 1 ∩ certSet c = certSet c :=
    Set.inter_eq_self_of_subset_right (certSet_subset_Ico c)
  have hIco : volume (Ico (0 : ℝ) 1) = 1 := by simp
  rw [hinter, hIco] at hsplit
  have hfin1 : volume (certSet c) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hIco]; exact measure_mono (certSet_subset_Ico c)
  have hfin2 : volume (Ico (0 : ℝ) 1 \ certSet c) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hIco]; exact measure_mono Set.sdiff_subset
  have := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_one] at this
  linarith [volume_hole_pos hc hst hne]

/-- **The bound, on the file's own smallest record.**  `Z32.BlockCert.certUnion2536` certifies 25
of the 36 cells of the grid at depth `K = 11` with `B = 17` blocks, so the general bound reads
`δ ≥ 1/(2(13 + log_{3/2} 34)) ≥ 1/44`.

The record's actual hole is `11/36 = 0.305…`, so at this size the bound is slack by a factor of
about thirteen: it is not a competitive estimate for one set, it is the statement that the slack
*closes* as `δ → 0`, which is what prices target T6. -/
theorem hole_union_2536 :
    1 / 44 ≤ (volume (Ico (0 : ℝ) 1 \ certSet certUnion2536)).toReal := by
  have hK : certUnion2536.levels.length = 11 := by decide
  have hB : certUnion2536.blocks.length = 17 := by decide
  have hp : certUnion2536.p = 3 := rfl
  have hq : certUnion2536.q = 2 := rfl
  have h := cert_depth_size (c := certUnion2536) certUnion2536_ok rfl (by decide)
  rw [hK, hB, hp, hq] at h
  norm_num at h
  have hL : Real.logb (3 / 2) 34 ≤ 9 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    rw [show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hδ : 0 ≤ (volume (Ico (0 : ℝ) 1 \ certSet certUnion2536)).toReal := ENNReal.toReal_nonneg
  nlinarith [h, hL, hδ]

end BlockCert

end Z32
