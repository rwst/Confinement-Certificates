/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.SmallInterval
import Z32.BlockCert
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Int
import Mathlib.Order.Preorder.Finite

/-!
# The escape ladder: which arcs `{ξ(p/q)ⁿ}` must visit (plan-M5A9, milestone N1)

`plans/plan-M5A9.html` §5 asks for the *ladder* below milestone M5 — "the orbit `{(3/2)ⁿ}` is dense
in `[0,1]`" — as a formal predicate family, together with every rung the corpus can already reach.
This file is that ladder.  Everything in it is a **complement** of the confinement statements of
`Z32/SmallInterval.lean` and `Z32/BlockCert.lean`: an orbit that cannot stay inside a set must
leave it infinitely often, which is a visit to the complementary arc.

## The predicate family

* `Z32.inArc s t x` — `x` lies, modulo one, in the half-open arc of length `t` starting at `s`.
  It is `Int.fract (x - s) < t`, so the arc **wraps around `0` by itself** and `s` may be any real
  number: no endpoint case split anywhere below.  This is exactly the shape [Dub09AA] Theorem 1 is
  stated in (`Z32.dubickas_theorem_1`), which is why the uniform rung is a two-line corollary.
* `Z32.VisitsIO β ξ s t` — the orbit `n ↦ ξβⁿ` meets that arc for infinitely many `n`.
* `Z32.M5 β t` — the rung: *every* arc of length `t` is visited infinitely often by the orbit of
  *every* `ξ ≠ 0`.  `M5(t)` for all `t > 0` is density for all `ξ ≠ 0`; milestone M5 itself is the
  single instance `ξ = 1`, `β = 3/2`.

## The rungs

| rung | statement | source |
| --- | --- | --- |
| uniform, `1 - 1/p` | `Z32.M5_one_sub_inv` | `Z32.dubickas_theorem_1` (`p < q²`, all `s`) |
| uniform, `2/3` at `3/2` | `Z32.M5_two_thirds` | idem at `(3,2)` |
| uniform, `2/3`, *open* arcs | `Z32.visits_open_arc_two_thirds` | idem, complement is closed of length `1/p` |
| uniform, `3/4` at `4/3` | `Z32.M5_four_three_three_quarters` | idem at `(4,3)` |
| positional, `5/8` | `Z32.visits_arc_five_eighths` | `Z32.not_eventually_mem_sixth_3_8` |
| positional, `0.59278` | `Z32.visits_arc_frontier` | `Z32.BlockCert.certFrontier` |
| positional, `17/24` at `4/3` | `Z32.visits_arc_four_three` | `Z32.BlockCert.certFourThree` |
| positional, `4/5` at `5/2` | `Z32.visits_arc_five_two` | `Z32.BlockCert.certFiveTwo` |
| union, `19/39` (closed) | `Z32.visits_compl_dub08` | `Z32.BlockCert.certDub08` |
| union, `5/12` | `Z32.visits_compl_union_seven_twelfths` | `Z32.BlockCert.certUnion712` |
| union, `1/3` | `Z32.visits_compl_union_two_thirds` | `Z32.BlockCert.certUnion23` |
| union, `11/36` | `Z32.visits_compl_union_record` | `Z32.BlockCert.certUnion2536` |
| M2, infinitely many limit points | `Z32.limitSet_infinite` | `Z32.M5_two_thirds` |

The four *positional* rungs are the sharp ones: they beat the uniform `2/3` at the positions where
the atlas of `plans/plan-cert32.html` §4.4 certifies a window, and `0.59278` is the best any
certificate of this family will ever give at `3/2` (experiment X2: nothing certifies at any
position once the window exceeds `1467/3600`).  The union rungs are *not* arcs — an orbit's
complement of a union of windows is a union of gaps — so they are stated as membership in the
explicit complement.

## Limit sets

`Z32.limitSet β ξ` is the set of subsequential limits of `n ↦ {ξβⁿ}`.  Frequent visits to a compact
set put a limit point in it (`Z32.mem_limitSet_of_frequently`), which upgrades two rungs:

* `Z32.limitSet_meets_arc_five_eighths` — every orbit has a limit point in
  `[0,1/6] ∪ [13/24,1]`;
* `Z32.limitSet_meets_union_record_compl` — every orbit has a limit point in a closed set of total
  length `11/36 = 0.3055…`, the complement of the `25/36` record entry.  Compare the best explicit
  statement in print, [Dub08] Corollary 1.2, whose complement has length `19/39 = 0.4871…`
  (`Z32.visits_compl_dub08`).

The last section proves the **M2 rung** of the ladder, `Z32.limitSet_infinite`: for every `ξ ≠ 0`
the orbit has *infinitely many* limit points ([Vij40] 1940).  It is a corollary of the uniform rung
`Z32.M5_two_thirds` — see the section header for why the textbook shadowing route is not available
here — and it is the one rung of `plans/plan-M5A9.html` Figure 2 below M5 that the corpus did not
already have.

## What is *not* here

The uniform ladder stops at `2/3`, and not for want of trying: the engine sweep behind the atlas
(plan-cert32 milestone M2 — a different M2 from the rung above — experiment X2 of §4.4) certifies
`100%` of positions at length `1/3`, `79.2%` one grid step above it, and nothing at all from
`0.4083` on, so no engine of this family will produce a uniform rung below `2/3`.  The next rung
down is a different theorem, not a better certificate.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.  The two analytic inputs are `Z32.dubickas_theorem_1` ([Dub09AA] Theorem 1, proved
in `Z32/SmallInterval.lean` by the Sturmian route) and `Z32.BlockCert.Cert.not_confined` (the
kernel-checked block certificates), both themselves axiom-free.

## Claim level

Formalization only.  The uniform rung is Dubickas's 2009 theorem read through its complement; the
positional and union rungs are complements of entries already shipped at plan-cert32 milestones
M2/M3/M6; the M2 rung is Vijayaraghavan's 1940 theorem.  Nothing here is claimed as new
mathematics; what is new is that the ladder is machine-checked and stated in one predicate family,
and that the M2 rung is derived from the uniform rung rather than from shadowing.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [Vij40] T. Vijayaraghavan, *On the fractional parts of the powers of a number* (1940) — the
  sequence `{ξ(3/2)ⁿ}` has infinitely many limit points.
* [Dub08] A. Dubickas, *On the fractional parts of powers of rational numbers*, 2008 —
  Corollary 1.2, the `20/39` union in print.
* [KK18] Problem 6.1 — the union-largeness curve the record entry sits on.
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, Acta Arith. **70.2** (1995), 125–147.
* `plans/plan-M5A9.html` §2 (corrections C3, C5, C6), §4 (the rung table), §5 (milestone N1).
* `plans/plan-cert32.html` §4.4 (the atlas), §11 (milestones M2, M3, M6).
-/

namespace Z32

open Filter Topology BlockCert

/-! ## The ladder predicate

Three definitions and their glue.  Everything downstream is stated with them, so the endpoint
conventions of `FLP.ZSet` (half-open, `ξ > 0`, no wrap) never leak into a rung. -/

/-- `inArc s t x` — the point `x`, read modulo one, lies in the half-open arc of length `t`
beginning at `s`.  Because it is phrased through `Int.fract (x - s)`, the arc wraps around `0`
on its own and `s` may be any real number. -/
def inArc (s t x : ℝ) : Prop := Int.fract (x - s) < t

/-- The visit relation: the orbit `n ↦ ξβⁿ` meets the arc `[s, s+t)` infinitely often. -/
def VisitsIO (β ξ s t : ℝ) : Prop := ∃ᶠ n in atTop, inArc s t (ξ * β ^ n)

/-- **The rung `M5(t)`** at base `β`: every arc of length `t` is visited infinitely often by the
orbit of every `ξ ≠ 0`. -/
def M5 (β t : ℝ) : Prop := ∀ ξ : ℝ, ξ ≠ 0 → ∀ s : ℝ, VisitsIO β ξ s t

/-- The elementary form of `VisitsIO`: escapes at arbitrarily late times. -/
theorem visitsIO_iff {β ξ s t : ℝ} :
    VisitsIO β ξ s t ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Int.fract (ξ * β ^ n - s) < t :=
  frequently_atTop

/-- Longer arcs are easier to hit. -/
theorem inArc_mono {s t t' x : ℝ} (h : t ≤ t') (hx : inArc s t x) : inArc s t' x :=
  lt_of_lt_of_le hx h

/-- Monotonicity of the visit relation in the arc length. -/
theorem VisitsIO.mono {β ξ s t t' : ℝ} (h : t ≤ t') (hv : VisitsIO β ξ s t) : VisitsIO β ξ s t' :=
  Filter.Frequently.mono hv fun _ hn => inArc_mono h hn

/-- **The ladder is a ladder**: a rung implies every rung above it. -/
theorem M5.mono {β t t' : ℝ} (h : M5 β t) (htt : t ≤ t') : M5 β t' :=
  fun ξ hξ s => (h ξ hξ s).mono htt

/-- Arcs see only the fractional part. -/
theorem inArc_add_intCast {s t x : ℝ} (m : ℤ) : inArc s t (x + m) ↔ inArc s t x := by
  have h : x + (m : ℝ) - s = x - s + (m : ℝ) := by ring
  simp only [inArc, h, Int.fract_add_intCast]

/-- Arcs see only the fractional part, in the form the certificates produce it. -/
theorem inArc_fract {s t x : ℝ} : inArc s t (Int.fract x) ↔ inArc s t x := by
  have h : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, inArc_add_intCast]

/-! ### Escape is a visit

The two bridges the whole file runs on.  The first reads an escape *from a closed arc* — the shape
of [Dub09AA] Theorem 1 — as a visit to the complementary half-open arc.  The second does the same
for the half-open windows of the block certificates, where the orbit point is already a fractional
part and the window sits inside `[0,1]`. -/

/-- **Escaping the closed arc `[s, s+t]` is visiting the arc `[s+t, s+1)`.** -/
theorem inArc_compl_of_lt_fract {s t x : ℝ} (ht : 0 ≤ t) (h : t < Int.fract (x - s)) :
    inArc (s + t) (1 - t) x := by
  have h0 := Int.fract_nonneg (x - s)
  have h1 := Int.fract_lt_one (x - s)
  have hfl := Int.floor_add_fract (x - s)
  have hx : x - (s + t) = Int.fract (x - s) - t + ((⌊x - s⌋ : ℤ) : ℝ) := by linarith
  unfold inArc
  rw [hx, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  linarith

/-- **Missing the window `[s, s+t) ⊆ [0,1]` is visiting the arc `[s+t, s+1)`.** -/
theorem inArc_compl_of_notMem_Ico {s t x : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1)
    (h : Int.fract x ∉ Set.Ico s (s + t)) : inArc (s + t) (1 - t) x := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hkey : Int.fract (x - (s + t)) = Int.fract (Int.fract x - (s + t)) := by
    have e : Int.fract x - (s + t) = x - (s + t) + ((-⌊x⌋ : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [e, Int.fract_add_intCast]
  rw [Set.mem_Ico, not_and_or, not_le, not_lt] at h
  unfold inArc
  rw [hkey]
  rcases h with h | h
  · have e : Int.fract x - (s + t) = Int.fract x - s - t + 1 + ((-1 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    linarith
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    linarith

/-- **The packaging used by every certificate rung.**  If no tail of the orbit stays inside the
window `[s, s+t) ⊆ [0,1]`, the complementary arc is visited infinitely often. -/
theorem visitsIO_of_not_eventually_mem_Ico {β ξ s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t ≤ 1)
    (h : ∀ N : ℕ, ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * β ^ n) ∈ Set.Ico s (s + t)) :
    VisitsIO β ξ (s + t) (1 - t) := by
  rw [visitsIO_iff]
  intro N
  by_contra hcon
  push Not at hcon
  refine h N fun n hn => ?_
  by_contra hmem
  exact absurd (inArc_compl_of_notMem_Ico hs ht hst hmem) (not_lt.mpr (hcon n hn))

/-! ## The uniform rung

[Dub09AA] Theorem 1 says that for coprime `1 < q < p < q²` no orbit stays in a closed arc of length
`1/p`, *at any position*.  Complemented, that is the uniform rung `M5(1 - 1/p)`: at `(3,2)` every
arc of length `2/3`, at `(4,3)` every arc of length `3/4`. -/

/-- **The uniform rung.**  For coprime `1 < q < p < q²`, every arc of length `1 - 1/p` is visited
infinitely often by the orbit of every `ξ ≠ 0`. -/
theorem M5_one_sub_inv {p q : ℕ} (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q)
    (hcop : Nat.Coprime p q) : M5 ((p : ℝ) / q) (1 - 1 / (p : ℝ)) := by
  intro ξ hξ a
  rw [visitsIO_iff]
  intro N
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  obtain ⟨n, hn, hlt⟩ := dubickas_theorem_1 hq hpq hpq2 hcop hξ (a - 1 / (p : ℝ)) N
  have h := inArc_compl_of_lt_fract (s := a - 1 / (p : ℝ)) (t := 1 / (p : ℝ))
    (by positivity) hlt
  refine ⟨n, hn, ?_⟩
  have he : a - 1 / (p : ℝ) + 1 / (p : ℝ) = a := by ring
  rw [he] at h
  exact h

/-- **`M5(2/3)` at `3/2`** — every arc of length `2/3` is visited infinitely often by every
`ξ ≠ 0`.  This is the anchor of the ladder of `plans/plan-M5A9.html` §4, and it holds for *closed*
arcs and wrap-around arcs alike, because `Z32.inArc` is stated through `Int.fract (x - s)`. -/
theorem M5_two_thirds : M5 ((3 : ℝ) / 2) (2 / 3) := by
  have h := M5_one_sub_inv (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by decide)
  norm_num at h
  exact h

/-- **The anchor rung, sharpened to open arcs.**  Every *open* arc of length `2/3` is visited
infinitely often too — not only the half-open one — because its complement is a **closed** arc of
length exactly `1/3 = 1/p`, which is precisely where [Dub09AA] Theorem 1 bites.  At any shorter arc
this sharpening is unavailable, which is one more way to see that `2/3` is the natural stop. -/
theorem visits_open_arc_two_thirds {ξ : ℝ} (hξ : ξ ≠ 0) (a : ℝ) :
    ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n - a) ∈ Set.Ioo (0 : ℝ) (2 / 3) := by
  rw [frequently_atTop]
  intro N
  obtain ⟨n, hn, hlt⟩ := dubickas_theorem_1 (p := 3) (q := 2) (by norm_num) (by norm_num)
    (by norm_num) (by decide) hξ (a - 1 / 3) N
  norm_num at hlt
  refine ⟨n, hn, ?_⟩
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n - (a - 1 / 3))
  have hfl := Int.floor_add_fract (ξ * ((3 : ℝ) / 2) ^ n - (a - 1 / 3))
  have e : ξ * ((3 : ℝ) / 2) ^ n - a
      = Int.fract (ξ * ((3 : ℝ) / 2) ^ n - (a - 1 / 3)) - 1 / 3 +
        ((⌊ξ * ((3 : ℝ) / 2) ^ n - (a - 1 / 3)⌋ : ℤ) : ℝ) := by linarith
  rw [Set.mem_Ioo, e, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨by linarith, by linarith⟩

/-- **`M5(3/4)` at `4/3`** — the same rung at the atlas's second base. -/
theorem M5_four_three_three_quarters : M5 ((4 : ℝ) / 3) (3 / 4) := by
  have h := M5_one_sub_inv (p := 4) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by decide)
  norm_num at h
  exact h

/-- Every arc of length at least `2/3` is visited infinitely often — the rung in the monotone form
of `plans/plan-M5A9.html` §4. -/
theorem M5_of_two_thirds_le {t : ℝ} (ht : 2 / 3 ≤ t) : M5 ((3 : ℝ) / 2) t :=
  M5_two_thirds.mono ht

/-! ## Positional rungs from the atlas

Below `2/3` no rung can be uniform in `s` by this machinery, but at the positions where the M2
sweep certified a window the complement is longer than `2/3` — up to `0.625` at the flagship window
and `0.59278` at the engine frontier.  Each rung here is one block certificate, read backwards. -/

/-- **The flagship positional rung, arc length `5/8 = 0.625`.**  The arc `[13/24, 1) ∪ [0, 1/6)` is
visited infinitely often by the orbit of every `ξ ≠ 0` — the complement of the window
`[1/6, 13/24)` of `Z32.ZSet_three_two_sixth_3_8`. -/
theorem visits_arc_five_eighths {ξ : ℝ} (hξ : ξ ≠ 0) :
    VisitsIO ((3 : ℝ) / 2) ξ (13 / 24) (5 / 8) := by
  have harc : (13 / 24 : ℝ) = 1 / 6 + 3 / 8 := by norm_num
  have hlen : (5 / 8 : ℝ) = 1 - 3 / 8 := by norm_num
  rw [harc, hlen]
  refine visitsIO_of_not_eventually_mem_Ico (by norm_num) (by norm_num) (by norm_num) fun N => ?_
  rw [show (1 : ℝ) / 6 + 3 / 8 = 13 / 24 by norm_num]
  exact not_eventually_mem_sixth_3_8 hξ

/-- The engine frontier as an eventual statement: no orbit is eventually confined to the longest
window the M2 sweep certifies, `[961/3600, 2427/3600)` of length `0.40722…`. -/
theorem not_eventually_mem_frontier {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (961 / 3600 : ℝ) (961 / 3600 + 1466 / 3600) := by
  refine not_eventually_mem_Ico_of_cert_base certFrontier_ok (3 / 2) (by norm_num [certFrontier])
    (fun y h1 h2 => ?_) hξ
  refine ⟨(1532144403, 3869421921), by simp [certFrontier], ?_, ?_⟩ <;>
    simp only [certFrontier, rleR] <;> push_cast <;> linarith

/-- **The frontier positional rung, arc length `2134/3600 = 0.59278…`** — the best rung any
certificate of this family can give at `3/2`, since the M2 sweep certifies nothing at any position
once the window exceeds `1467/3600`. -/
theorem visits_arc_frontier {ξ : ℝ} (hξ : ξ ≠ 0) :
    VisitsIO ((3 : ℝ) / 2) ξ (2427 / 3600) (2134 / 3600) := by
  have harc : (2427 / 3600 : ℝ) = 961 / 3600 + 1466 / 3600 := by norm_num
  have hlen : (2134 / 3600 : ℝ) = 1 - 1466 / 3600 := by norm_num
  rw [harc, hlen]
  exact visitsIO_of_not_eventually_mem_Ico (by norm_num) (by norm_num) (by norm_num)
    fun _ => not_eventually_mem_frontier hξ

/-- The `(4,3)` window as an eventual statement. -/
theorem not_eventually_mem_four_three {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * ((4 : ℝ) / 3) ^ n) ∈
      Set.Ico (1 / 3 : ℝ) (1 / 3 + 7 / 24) := by
  refine not_eventually_mem_Ico_of_cert_base certFourThree_ok (4 / 3)
    (by norm_num [certFourThree]) (fun y h1 h2 => ?_) hξ
  refine ⟨(8192, 15360), by simp [certFourThree], ?_, ?_⟩ <;>
    simp only [certFourThree, rleR] <;> push_cast <;> linarith

/-- **A positional rung at the second base, arc length `17/24 = 0.7083…`**: the arc
`[5/8, 1) ∪ [0, 1/3)` is visited infinitely often by every orbit of base `4/3`.  Longer than the
uniform `3/4`?  No — shorter; it is the *position* that is new, the uniform rung covers every arc
of length `3/4` and this one is the complement of a window past the `1/p` line. -/
theorem visits_arc_four_three {ξ : ℝ} (hξ : ξ ≠ 0) :
    VisitsIO ((4 : ℝ) / 3) ξ (5 / 8) (17 / 24) := by
  have harc : (5 / 8 : ℝ) = 1 / 3 + 7 / 24 := by norm_num
  have hlen : (17 / 24 : ℝ) = 1 - 7 / 24 := by norm_num
  rw [harc, hlen]
  exact visitsIO_of_not_eventually_mem_Ico (by norm_num) (by norm_num) (by norm_num)
    fun _ => not_eventually_mem_four_three hξ

/-- The `(5,2)` window as an eventual statement — a base in the regime `p > q²`, where [Dub09AA]
Theorem 1 has nothing to say and only the certificate works. -/
theorem not_eventually_mem_five_two {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * ((5 : ℝ) / 2) ^ n) ∈
      Set.Ico (1 / 5 : ℝ) (1 / 5 + 1 / 5) := by
  refine not_eventually_mem_Ico_of_cert_base certFiveTwo_ok (5 / 2)
    (by norm_num [certFiveTwo]) (fun y h1 h2 => ?_) hξ
  refine ⟨(5, 10), by simp [certFiveTwo], ?_, ?_⟩ <;>
    simp only [certFiveTwo, rleR] <;> push_cast <;> linarith

/-- **A positional rung at a base with `p > q²`, arc length `4/5`.**  There is no uniform rung at
`5/2` at all — `Z32.M5_one_sub_inv` needs `p < q²` — so this is the only kind of rung available at
this base. -/
theorem visits_arc_five_two {ξ : ℝ} (hξ : ξ ≠ 0) :
    VisitsIO ((5 : ℝ) / 2) ξ (2 / 5) (4 / 5) := by
  have harc : (2 / 5 : ℝ) = 1 / 5 + 1 / 5 := by norm_num
  have hlen : (4 / 5 : ℝ) = 1 - 1 / 5 := by norm_num
  rw [harc, hlen]
  exact visitsIO_of_not_eventually_mem_Ico (by norm_num) (by norm_num) (by norm_num)
    fun _ => not_eventually_mem_five_two hξ

/-! ## Union rungs

The four union entries of the atlas certify a *union* of windows, so their complements are unions
of gaps rather than single arcs.  Each rung below says: the orbit lands in the explicit complement
infinitely often.  The glue is the eventual form of `Cert.not_confined`, with the base named. -/

/-- `Cert.not_eventually_confined` with the base written as a real literal. -/
theorem not_eventually_confined_base {c : Cert} (hc : c.ok = true) (β : ℝ)
    (hβ : (c.p : ℝ) / c.q = β) {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → memL c.D c.closed c.U (Int.fract (ξ * β ^ n))) : False := by
  subst hβ
  exact Cert.not_eventually_confined hc hξ h

/-- **[Dub08] Corollary 1.2, complemented.**  Every orbit lands infinitely often in
`[0, 8/39) ∪ (18/39, 21/39) ∪ (31/39, 1)`, a set of total length `19/39 = 0.4871…` — the strongest
*published* union statement at `3/2`, read as a visit theorem.  The gaps are open because the
certified set is closed. -/
theorem visits_compl_dub08 {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (8 / 39) ∪ Set.Ioo (18 / 39 : ℝ) (21 / 39) ∪ Set.Ioo (31 / 39 : ℝ) 1 := by
  rw [frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  refine not_eventually_confined_base certDub08_ok (3 / 2) (by norm_num [certDub08]) hξ
    (N := N) fun n hn => ?_
  have h0 := Int.fract_nonneg (ξ * ((3 : ℝ) / 2) ^ n)
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n)
  have hy := hcon n hn
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioo, not_or, not_and, not_lt] at hy
  obtain ⟨⟨g1, g2⟩, g3⟩ := hy
  have hg1 : (8 : ℝ) / 39 ≤ Int.fract (ξ * ((3 : ℝ) / 2) ^ n) := g1 h0
  rcases le_or_gt (Int.fract (ξ * ((3 : ℝ) / 2) ^ n)) (18 / 39) with h | h
  · exact ⟨(216, 486), by simp [certDub08], by
      simp only [certDub08]; push_cast; linarith, by
      simp only [certDub08, rleR]; push_cast; linarith⟩
  · have hg2 : (21 : ℝ) / 39 ≤ Int.fract (ξ * ((3 : ℝ) / 2) ^ n) := g2 h
    rcases le_or_gt (Int.fract (ξ * ((3 : ℝ) / 2) ^ n)) (31 / 39) with h' | h'
    · exact ⟨(567, 837), by simp [certDub08], by
        simp only [certDub08]; push_cast; linarith, by
        simp only [certDub08, rleR]; push_cast; linarith⟩
    · exact absurd (g3 h') (by linarith)

/-- **The `7/12` union, complemented**: every orbit lands infinitely often in
`[1/6, 1/4) ∪ [1/3, 5/12) ∪ [2/3, 3/4) ∪ [5/6, 1)`, of total length `5/12`. -/
theorem visits_compl_union_seven_twelfths {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (1 / 6 : ℝ) (1 / 4) ∪ Set.Ico (1 / 3 : ℝ) (5 / 12) ∪
        Set.Ico (2 / 3 : ℝ) (3 / 4) ∪ Set.Ico (5 / 6 : ℝ) 1 := by
  rw [frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  refine not_eventually_confined_base certUnion712_ok (3 / 2) (by norm_num [certUnion712]) hξ
    (N := N) fun n hn => ?_
  have h0 := Int.fract_nonneg (ξ * ((3 : ℝ) / 2) ^ n)
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n)
  have hy := hcon n hn
  simp only [Set.mem_union, Set.mem_Ico, not_or, not_and, not_lt] at hy
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hy
  set y := Int.fract (ξ * ((3 : ℝ) / 2) ^ n) with hydef
  rcases lt_or_ge y (1 / 6) with h | h
  · exact ⟨(0, 4374), by simp [certUnion712], by
      simp only [certUnion712]; push_cast; linarith, by
      simp only [certUnion712, rleR]; push_cast; linarith⟩
  · have h := g1 h
    rcases lt_or_ge y (1 / 3) with h' | h'
    · exact ⟨(6561, 8748), by simp [certUnion712], by
        simp only [certUnion712]; push_cast; linarith, by
        simp only [certUnion712, rleR]; push_cast; linarith⟩
    · have h' := g2 h'
      rcases lt_or_ge y (2 / 3) with h'' | h''
      · exact ⟨(10935, 17496), by simp [certUnion712], by
          simp only [certUnion712]; push_cast; linarith, by
          simp only [certUnion712, rleR]; push_cast; linarith⟩
      · have h'' := g3 h''
        rcases lt_or_ge y (5 / 6) with h''' | h'''
        · exact ⟨(19683, 21870), by simp [certUnion712], by
            simp only [certUnion712]; push_cast; linarith, by
            simp only [certUnion712, rleR]; push_cast; linarith⟩
        · exact absurd (g4 h''') (by linarith)

/-- **The `2/3` union, complemented**: every orbit lands infinitely often in
`[1/9, 1/6) ∪ [4/9, 1/2) ∪ [5/9, 11/18) ∪ [7/9, 5/6) ∪ [8/9, 1)`, of total length `1/3`.  Worth
pairing with [KK18] Corollary 4.8: a *nonempty* union of the same total length `2/3` exists, so the
complement statement is about this union, never about the number `2/3`. -/
theorem visits_compl_union_two_thirds {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (1 / 9 : ℝ) (1 / 6) ∪ Set.Ico (4 / 9 : ℝ) (1 / 2) ∪
        Set.Ico (5 / 9 : ℝ) (11 / 18) ∪ Set.Ico (7 / 9 : ℝ) (5 / 6) ∪ Set.Ico (8 / 9 : ℝ) 1 := by
  rw [frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  refine not_eventually_confined_base certUnion23_ok (3 / 2) (by norm_num [certUnion23]) hξ
    (N := N) fun n hn => ?_
  have h0 := Int.fract_nonneg (ξ * ((3 : ℝ) / 2) ^ n)
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n)
  have hy := hcon n hn
  simp only [Set.mem_union, Set.mem_Ico, not_or, not_and, not_lt] at hy
  obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := hy
  set y := Int.fract (ξ * ((3 : ℝ) / 2) ^ n) with hydef
  rcases lt_or_ge y (1 / 9) with h | h
  · exact ⟨(0, 39366), by simp [certUnion23], by
      simp only [certUnion23]; push_cast; linarith, by
      simp only [certUnion23, rleR]; push_cast; linarith⟩
  · have h := g1 h
    rcases lt_or_ge y (4 / 9) with h' | h'
    · exact ⟨(59049, 157464), by simp [certUnion23], by
        simp only [certUnion23]; push_cast; linarith, by
        simp only [certUnion23, rleR]; push_cast; linarith⟩
    · have h' := g2 h'
      rcases lt_or_ge y (5 / 9) with h'' | h''
      · exact ⟨(177147, 196830), by simp [certUnion23], by
          simp only [certUnion23]; push_cast; linarith, by
          simp only [certUnion23, rleR]; push_cast; linarith⟩
      · have h'' := g3 h''
        rcases lt_or_ge y (7 / 9) with h₄ | h₄
        · exact ⟨(216513, 275562), by simp [certUnion23], by
            simp only [certUnion23]; push_cast; linarith, by
            simp only [certUnion23, rleR]; push_cast; linarith⟩
        · have h₄ := g4 h₄
          rcases lt_or_ge y (8 / 9) with h₅ | h₅
          · exact ⟨(295245, 314928), by simp [certUnion23], by
              simp only [certUnion23]; push_cast; linarith, by
              simp only [certUnion23, rleR]; push_cast; linarith⟩
          · exact absurd (g5 h₅) (by linarith)

/-- **The `25/36` record entry, complemented**: every orbit lands infinitely often in
`[1/12, 1/9) ∪ [11/36, 4/9) ∪ [2/3, 25/36) ∪ [3/4, 5/6) ∪ [8/9, 11/12)`, a set of total length
`11/36 = 0.3055…`.  This is the tightest "where must the orbit return" statement the atlas
supports; the published comparison is `19/39 = 0.4871…` (`Z32.visits_compl_dub08`). -/
theorem visits_compl_union_record {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (1 / 12 : ℝ) (1 / 9) ∪ Set.Ico (11 / 36 : ℝ) (4 / 9) ∪
        Set.Ico (2 / 3 : ℝ) (25 / 36) ∪ Set.Ico (3 / 4 : ℝ) (5 / 6) ∪
          Set.Ico (8 / 9 : ℝ) (11 / 12) := by
  rw [frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  refine not_eventually_confined_base certUnion2536_ok (3 / 2) (by norm_num [certUnion2536]) hξ
    (N := N) fun n hn => ?_
  have h0 := Int.fract_nonneg (ξ * ((3 : ℝ) / 2) ^ n)
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n)
  have hy := hcon n hn
  simp only [Set.mem_union, Set.mem_Ico, not_or, not_and, not_lt] at hy
  obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := hy
  set y := Int.fract (ξ * ((3 : ℝ) / 2) ^ n) with hydef
  rcases lt_or_ge y (1 / 12) with h | h
  · exact ⟨(0, 531441), by simp [certUnion2536], by
      simp only [certUnion2536]; push_cast; linarith, by
      simp only [certUnion2536, rleR]; push_cast; linarith⟩
  · have h := g1 h
    rcases lt_or_ge y (11 / 36) with h' | h'
    · exact ⟨(708588, 1948617), by simp [certUnion2536], by
        simp only [certUnion2536]; push_cast; linarith, by
        simp only [certUnion2536, rleR]; push_cast; linarith⟩
    · have h' := g2 h'
      rcases lt_or_ge y (2 / 3) with h'' | h''
      · exact ⟨(2834352, 4251528), by simp [certUnion2536], by
          simp only [certUnion2536]; push_cast; linarith, by
          simp only [certUnion2536, rleR]; push_cast; linarith⟩
      · have h'' := g3 h''
        rcases lt_or_ge y (3 / 4) with h₄ | h₄
        · exact ⟨(4428675, 4782969), by simp [certUnion2536], by
            simp only [certUnion2536]; push_cast; linarith, by
            simp only [certUnion2536, rleR]; push_cast; linarith⟩
        · have h₄ := g4 h₄
          rcases lt_or_ge y (8 / 9) with h₅ | h₅
          · exact ⟨(5314410, 5668704), by simp [certUnion2536], by
              simp only [certUnion2536]; push_cast; linarith, by
              simp only [certUnion2536, rleR]; push_cast; linarith⟩
          · have h₅ := g5 h₅
            exact ⟨(5845851, 6377292), by simp [certUnion2536], by
              simp only [certUnion2536]; push_cast; linarith, by
              simp only [certUnion2536, rleR]; push_cast; linarith⟩

/-! ## Limit sets

A rung says the orbit *returns* to a set infinitely often.  When the set is compact this upgrades
to a statement about the limit set: some subsequential limit lies in it. -/

/-- The limit set of the orbit: its subsequential limits. -/
def limitSet (β ξ : ℝ) : Set ℝ :=
  {y | ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun k => Int.fract (ξ * β ^ φ k)) atTop (𝓝 y)}

/-- **Frequent visits to a compact set put a limit point in it.** -/
theorem mem_limitSet_of_frequently {β ξ : ℝ} {C : Set ℝ} (hC : IsCompact C)
    (h : ∃ᶠ n in atTop, Int.fract (ξ * β ^ n) ∈ C) : ∃ y ∈ C, y ∈ limitSet β ξ := by
  obtain ⟨ψ, hψ, hmem⟩ := extraction_of_frequently_atTop h
  obtain ⟨y, hyC, χ, hχ, htend⟩ :=
    hC.tendsto_subseq (x := fun k => Int.fract (ξ * β ^ ψ k)) hmem
  exact ⟨y, hyC, ψ ∘ χ, hψ.comp hχ, htend⟩

/-- Unwrapping an arc: a point of the arc `[s, s+t)` with `s ≤ 1` has its fractional part in
`[s, 1)` or in `[0, s+t-1)`. -/
theorem fract_mem_of_inArc {s t x : ℝ} (hs1 : s ≤ 1) (h : inArc s t x) :
    Int.fract x ∈ Set.Ico s 1 ∪ Set.Ico 0 (s + t - 1) := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hkey : Int.fract (x - s) = Int.fract (Int.fract x - s) := by
    have e : Int.fract x - s = x - s + ((-⌊x⌋ : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [e, Int.fract_add_intCast]
  unfold inArc at h
  rw [hkey] at h
  rcases le_or_gt s (Int.fract x) with hcase | hcase
  · exact Or.inl ⟨hcase, h1⟩
  · refine Or.inr ⟨h0, ?_⟩
    have e : Int.fract x - s = Int.fract x - s + 1 + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [e, Int.fract_add_intCast,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h
    linarith

/-- **The flagship rung as a limit-set statement.**  Every orbit of base `3/2` has a limit point in
`[0, 1/6] ∪ [13/24, 1]`, a closed set of total length `5/8`. -/
theorem limitSet_meets_arc_five_eighths {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ y ∈ Set.Icc (0 : ℝ) (1 / 6) ∪ Set.Icc (13 / 24 : ℝ) 1,
      y ∈ limitSet ((3 : ℝ) / 2) ξ := by
  refine mem_limitSet_of_frequently (isCompact_Icc.union isCompact_Icc) ?_
  refine Filter.Frequently.mono (visits_arc_five_eighths hξ) fun n hn => ?_
  have h := fract_mem_of_inArc (by norm_num) hn
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2.le⟩
  · exact Or.inl ⟨h1, by norm_num at h2 ⊢; linarith⟩

/-- **The record entry as a limit-set statement.**  Every orbit of base `3/2` has a limit point in
a closed set of total length `11/36 = 0.3055…`. -/
theorem limitSet_meets_union_record_compl {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ y ∈ Set.Icc (1 / 12 : ℝ) (1 / 9) ∪ Set.Icc (11 / 36 : ℝ) (4 / 9) ∪
      Set.Icc (2 / 3 : ℝ) (25 / 36) ∪ Set.Icc (3 / 4 : ℝ) (5 / 6) ∪
        Set.Icc (8 / 9 : ℝ) (11 / 12), y ∈ limitSet ((3 : ℝ) / 2) ξ := by
  refine mem_limitSet_of_frequently
    ((((isCompact_Icc.union isCompact_Icc).union isCompact_Icc).union isCompact_Icc).union
      isCompact_Icc) ?_
  refine (visits_compl_union_record hξ).mono fun n hn => ?_
  rcases hn with ((((h | h) | h) | h) | h) <;>
    [exact Or.inl (Or.inl (Or.inl (Or.inl (Set.Ico_subset_Icc_self h))));
     exact Or.inl (Or.inl (Or.inl (Or.inr (Set.Ico_subset_Icc_self h))));
     exact Or.inl (Or.inl (Or.inr (Set.Ico_subset_Icc_self h)));
     exact Or.inl (Or.inr (Set.Ico_subset_Icc_self h));
     exact Or.inr (Set.Ico_subset_Icc_self h)]

/-! ## The M2 rung: infinitely many limit points

[Vij40] proves that `{ξ(3/2)ⁿ}` has infinitely many limit points for every `ξ > 0`.  It is the one
rung of the ladder of `plans/plan-M5A9.html` §4 below M5 that the corpus did not have, and
`plans/plan-M5A9.html` §5 lists it as N1's stretch item together with a warning: the textbook route
(a finite limit set is shadowed by a periodic orbit, whose carry word contradicts
`Z32.not_isEventuallyPeriodic_carry`) needs a shadowing step that is **false as stated** here.  The
reason is correction C1 of that plan: the `ξ`-dynamics is a *two-branch relation*, not the Lorenz
map `y ↦ {3y/2}` — `y_{n+1}` depends on the parity of `⌊ξ(3/2)ⁿ⌋` as well as on `yₙ` — so a point
of a finite limit set has **two** admissible successors, differing by exactly `1/2`, and an
itinerary through a finite graph of out-degree two need not be eventually periodic.

The route below avoids shadowing altogether and uses only the ladder:

1. every limit point `a` has a limit point `b` with `3a - 2b ∈ ℤ` (the carry identity survives to
   the limit because `ℤ` is closed) — `Z32.exists_succ_mem_limitSet`;
2. iterate: in a *finite* limit set the chain repeats, and the two congruences
   `2ᵐb ≡ 3ᵐa`, `2ⁿb ≡ 3ⁿa (mod 1)` force `(3ⁿ2ᵐ - 3ᵐ2ⁿ)·b ∈ ℤ`, so every limit point is rational
   with an explicit denominator — `Z32.exists_den_of_finite_limitSet`;
3. one denominator `D` serves all of them, so the orbit of `Dξ` is eventually within `1/6` of `ℤ`
   — an arc of length `1/3`;
4. `Z32.M5_two_thirds` says the complementary arc of length `2/3` is visited infinitely often.
   Contradiction.

So the M2 rung is a *corollary of the uniform rung* rather than of the aperiodicity lemma, and it
needs nothing about `ξ = 1`. -/

/-- The carry identity, in fractional parts: `3yₙ - 2y_{n+1} = 2x_{n+1} - 3xₙ ∈ ℤ`. -/
theorem three_fract_sub_two_fract_isInt (ξ : ℝ) (n : ℕ) :
    ∃ z : ℤ, 3 * Int.fract (ξ * ((3 : ℝ) / 2) ^ n) -
      2 * Int.fract (ξ * ((3 : ℝ) / 2) ^ (n + 1)) = z := by
  refine ⟨2 * ⌊ξ * ((3 : ℝ) / 2) ^ (n + 1)⌋ - 3 * ⌊ξ * ((3 : ℝ) / 2) ^ n⌋, ?_⟩
  have h1 := Int.floor_add_fract (ξ * ((3 : ℝ) / 2) ^ n)
  have h2 := Int.floor_add_fract (ξ * ((3 : ℝ) / 2) ^ (n + 1))
  have h3 : ξ * ((3 : ℝ) / 2) ^ (n + 1) = 3 / 2 * (ξ * ((3 : ℝ) / 2) ^ n) := by ring
  push_cast
  linarith

/-- **Every limit point has a successor limit point**, one carry step away: `3a - 2b ∈ ℤ`.  This is
the whole dynamical content of the M2 rung, and it is soft — the carry identity is preserved in the
limit because `ℤ` is closed in `ℝ`. -/
theorem exists_succ_mem_limitSet {ξ a : ℝ} (ha : a ∈ limitSet ((3 : ℝ) / 2) ξ) :
    ∃ b ∈ limitSet ((3 : ℝ) / 2) ξ, ∃ z : ℤ, 3 * a - 2 * b = z := by
  obtain ⟨φ, hφ, htend⟩ := ha
  obtain ⟨b, -, χ, hχ, htend'⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq
      (x := fun k => Int.fract (ξ * ((3 : ℝ) / 2) ^ (φ k + 1)))
      (fun k => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  have hmem : b ∈ limitSet ((3 : ℝ) / 2) ξ :=
    ⟨fun k => φ (χ k) + 1, fun i j hij => by simpa using hφ (hχ hij), htend'⟩
  have htA : Tendsto (fun k => Int.fract (ξ * ((3 : ℝ) / 2) ^ φ (χ k))) atTop (𝓝 a) :=
    htend.comp hχ.tendsto_atTop
  have htotal : Tendsto (fun k => 3 * Int.fract (ξ * ((3 : ℝ) / 2) ^ φ (χ k)) -
      2 * Int.fract (ξ * ((3 : ℝ) / 2) ^ (φ (χ k) + 1))) atTop (𝓝 (3 * a - 2 * b)) :=
    (htA.const_mul 3).sub (htend'.const_mul 2)
  have hint : (3 * a - 2 * b) ∈ Set.range ((↑) : ℤ → ℝ) := by
    refine Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto htotal ?_
    filter_upwards with k
    obtain ⟨z, hz⟩ := three_fract_sub_two_fract_isInt ξ (φ (χ k))
    exact ⟨z, hz.symm⟩
  obtain ⟨z, hz⟩ := hint
  exact ⟨b, hmem, z, hz.symm⟩

/-- **A finite limit set consists of rationals**, with an explicit denominator: iterating the
successor relation inside a finite set repeats, and the resulting pair of congruences pins the
point.  No shadowing, no periodicity of the carry word. -/
theorem exists_den_of_finite_limitSet {ξ : ℝ} (hfin : (limitSet ((3 : ℝ) / 2) ξ).Finite)
    {a : ℝ} (ha : a ∈ limitSet ((3 : ℝ) / 2) ξ) :
    ∃ D : ℤ, 0 < D ∧ ∃ z : ℤ, (D : ℝ) * a = z := by
  choose g hgmem w hw using fun (x : ↥(limitSet ((3 : ℝ) / 2) ξ)) => exists_succ_mem_limitSet x.2
  set G : ↥(limitSet ((3 : ℝ) / 2) ξ) → ↥(limitSet ((3 : ℝ) / 2) ξ) := fun x => ⟨g x, hgmem x⟩
    with hGdef
  set x0 : ↥(limitSet ((3 : ℝ) / 2) ξ) := ⟨a, ha⟩ with hx0
  have key : ∀ k : ℕ, ∃ z : ℤ, (2 : ℝ) ^ k * ((G^[k] x0 : ↥(limitSet ((3 : ℝ) / 2) ξ)) : ℝ)
      = 3 ^ k * a + z := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [hx0]⟩
    | succ k ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨3 * z - 2 ^ k * w (G^[k] x0), ?_⟩
      have hstep : 3 * ((G^[k] x0 : ↥(limitSet ((3 : ℝ) / 2) ξ)) : ℝ) -
          2 * ((G (G^[k] x0) : ↥(limitSet ((3 : ℝ) / 2) ξ)) : ℝ) = (w (G^[k] x0) : ℝ) :=
        hw (G^[k] x0)
      rw [Function.iterate_succ_apply' G k x0]
      push_cast
      linear_combination 3 * hz - (2 : ℝ) ^ k * hstep
  obtain ⟨m, n, hmn, heq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun k : ℕ => ((G^[k] x0 : ↥(limitSet ((3 : ℝ) / 2) ξ)) : ℝ))
      (fun k => (G^[k] x0).2) hfin
  obtain ⟨z1, hz1⟩ := key m
  obtain ⟨z2, hz2⟩ := key n
  rw [← heq] at hz2
  have hcpos : (0 : ℤ) < 3 ^ n * 2 ^ m - 3 ^ m * 2 ^ n := by
    obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
    have hd : d ≠ 0 := by omega
    have hlt : (2 : ℤ) ^ d < 3 ^ d := pow_lt_pow_left₀ (by norm_num) (by norm_num) hd
    have e : (3 : ℤ) ^ (m + d) * 2 ^ m - 3 ^ m * 2 ^ (m + d) = 3 ^ m * 2 ^ m * (3 ^ d - 2 ^ d) := by
      ring
    rw [e]
    exact mul_pos (mul_pos (pow_pos (by norm_num) m) (pow_pos (by norm_num) m)) (by linarith)
  set c : ℤ := 3 ^ n * 2 ^ m - 3 ^ m * 2 ^ n with hc
  have hcb : (c : ℝ) * ((G^[m] x0 : ↥(limitSet ((3 : ℝ) / 2) ξ)) : ℝ)
      = 3 ^ n * (z1 : ℝ) - 3 ^ m * (z2 : ℝ) := by
    rw [hc]
    push_cast
    linear_combination (3 : ℝ) ^ n * hz1 - (3 : ℝ) ^ m * hz2
  refine ⟨c * 3 ^ m, mul_pos hcpos (pow_pos (by norm_num) m),
    2 ^ m * (3 ^ n * z1 - 3 ^ m * z2) - c * z1, ?_⟩
  push_cast
  linear_combination (2 : ℝ) ^ m * hcb - (c : ℝ) * hz1

/-- One denominator for the whole (finite) limit set. -/
theorem exists_common_den {ξ : ℝ} (hfin : (limitSet ((3 : ℝ) / 2) ξ).Finite) :
    ∃ D : ℤ, 0 < D ∧ ∀ a ∈ limitSet ((3 : ℝ) / 2) ξ, ∃ z : ℤ, (D : ℝ) * a = z := by
  classical
  haveI : Fintype ↥(limitSet ((3 : ℝ) / 2) ξ) := hfin.fintype
  choose Dn hDpos hDz using fun (x : ↥(limitSet ((3 : ℝ) / 2) ξ)) =>
    exists_den_of_finite_limitSet hfin x.2
  refine ⟨∏ x : ↥(limitSet ((3 : ℝ) / 2) ξ), Dn x, Finset.prod_pos fun x _ => hDpos x, ?_⟩
  intro a ha
  obtain ⟨e, he⟩ :=
    Finset.dvd_prod_of_mem Dn (Finset.mem_univ (⟨a, ha⟩ : ↥(limitSet ((3 : ℝ) / 2) ξ)))
  obtain ⟨z, hz⟩ := hDz ⟨a, ha⟩
  refine ⟨e * z, ?_⟩
  rw [he]
  push_cast
  linear_combination (e : ℝ) * hz

/-- **A finite limit set is approached uniformly**: the orbit is eventually within `ε` of it. -/
theorem eventually_near_limitSet {ξ : ℝ} {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∃ a ∈ limitSet ((3 : ℝ) / 2) ξ,
      |Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - a| < ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  have hCcompact : IsCompact (Set.Icc (0 : ℝ) 1 ∩
      ⋂ a ∈ limitSet ((3 : ℝ) / 2) ξ, {x : ℝ | ε ≤ |x - a|}) := by
    refine isCompact_Icc.inter_right (isClosed_biInter fun a _ => ?_)
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  have hfreq : ∃ᶠ n in atTop, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (0 : ℝ) 1 ∩ ⋂ a ∈ limitSet ((3 : ℝ) / 2) ξ, {x : ℝ | ε ≤ |x - a|} := by
    refine hcon.mono fun n hn => ?_
    refine ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    push Not at hn
    exact fun a ha => hn a ha
  obtain ⟨y, hyC, hyL⟩ := mem_limitSet_of_frequently hCcompact hfreq
  have h := hyC.2
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at h
  have := h y hyL
  simp only [sub_self, abs_zero] at this
  linarith

/-- Two arcs that cannot both hold: `[-1/6, 1/6)` and `[1/6, 5/6)`. -/
theorem not_inArc_two_thirds_of_inArc_third {x : ℝ} (h : inArc (-(1 / 6)) (1 / 3) x) :
    ¬ inArc (1 / 6) (2 / 3) x := by
  unfold inArc at h ⊢
  rw [show x - -(1 / 6) = x + 1 / 6 by ring] at h
  have h0 := Int.fract_nonneg (x + 1 / 6)
  have hfl := Int.floor_add_fract (x + 1 / 6)
  have e : x - 1 / 6 = Int.fract (x + 1 / 6) - 1 / 3 + 1 + ((⌊x + 1 / 6⌋ - 1 : ℤ) : ℝ) := by
    push_cast; linarith
  rw [e, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact not_lt.mpr (by linarith)

/-- **The M2 rung ([Vij40]).**  For every `ξ ≠ 0` the orbit `{ξ(3/2)ⁿ}` has infinitely many limit
points.

Proved here from `Z32.M5_two_thirds` alone: a finite limit set would be rational with a common
denominator `D` (`Z32.exists_den_of_finite_limitSet`), the orbit of `Dξ` would then be eventually
inside an arc of length `1/3` around `0`, and the uniform rung visits its complement — an arc of
length `2/3` — infinitely often.

Claim level: formalization only.  This is Vijayaraghavan's 1940 theorem; only the proof route is
new, and it is new because the textbook one does not survive contact with the two-branch carry
relation (`plans/plan-M5A9.html` correction C1). -/
theorem limitSet_infinite {ξ : ℝ} (hξ : ξ ≠ 0) : (limitSet ((3 : ℝ) / 2) ξ).Infinite := by
  intro hfin
  obtain ⟨D, hDpos, hD⟩ := exists_common_den hfin
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hnear := eventually_near_limitSet (ξ := ξ) (ε := 1 / (6 * D)) (by positivity)
  have hηne : (D : ℝ) * ξ ≠ 0 := mul_ne_zero (ne_of_gt hD0) hξ
  have hev : ∀ᶠ n in atTop, inArc (-(1 / 6)) (1 / 3) ((D : ℝ) * ξ * ((3 : ℝ) / 2) ^ n) := by
    refine hnear.mono fun n hn => ?_
    obtain ⟨a, haL, hclose⟩ := hn
    obtain ⟨z, hz⟩ := hD a haL
    have hsplit : (D : ℝ) * ξ * ((3 : ℝ) / 2) ^ n
        = (D : ℝ) * Int.fract (ξ * ((3 : ℝ) / 2) ^ n) +
          ((D * ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ : ℤ) : ℝ) := by
      have h0 := Int.floor_add_fract (ξ * ((3 : ℝ) / 2) ^ n)
      push_cast
      linear_combination -(D : ℝ) * h0
    have habs : |(D : ℝ) * Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - (z : ℝ)| < 1 / 6 := by
      have e : (D : ℝ) * Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - (z : ℝ)
          = (D : ℝ) * (Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - a) := by rw [← hz]; ring
      rw [e, abs_mul, abs_of_pos hD0]
      calc (D : ℝ) * |Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - a|
          < (D : ℝ) * (1 / (6 * D)) := by exact mul_lt_mul_of_pos_left hclose hD0
        _ = 1 / 6 := by field_simp
    rw [abs_lt] at habs
    unfold inArc
    have e : (D : ℝ) * ξ * ((3 : ℝ) / 2) ^ n - -(1 / 6)
        = ((D : ℝ) * Int.fract (ξ * ((3 : ℝ) / 2) ^ n) - (z : ℝ) + 1 / 6) +
          ((z + D * ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ : ℤ) : ℝ) := by
      rw [hsplit]; push_cast; ring
    rw [e, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    linarith
  obtain ⟨n, hvn, hen⟩ := ((M5_two_thirds ((D : ℝ) * ξ) hηne (1 / 6)).and_eventually hev).exists
  exact not_inArc_two_thirds_of_inArc_third hen hvn

/-- **Sanity: `ξ ≠ 0` is not decoration.**  The zero orbit has exactly one limit point, so the M2
rung is false without the hypothesis — and the limit set is not infinite for trivial reasons. -/
theorem limitSet_zero : limitSet ((3 : ℝ) / 2) 0 = {0} := by
  ext y
  simp only [limitSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨φ, -, htend⟩
    exact (by simpa using htend : (0 : ℝ) = y).symm
  · rintro rfl
    exact ⟨id, strictMono_id, by simp⟩

/-! ### The milestone-M5 point

Every statement above is uniform in `ξ ≠ 0`; milestone M5 of `plans/plan-M5A9.html` is the single
point `ξ = 1`.  These are its instances — the current state of the ladder at the point that
matters. -/

/-- At `ξ = 1`: every arc of length `2/3` is visited infinitely often by `{(3/2)ⁿ}`. -/
theorem visits_one_two_thirds (s : ℝ) : VisitsIO ((3 : ℝ) / 2) 1 s (2 / 3) :=
  M5_two_thirds 1 one_ne_zero s

/-- At `ξ = 1`: the arc `[13/24, 1) ∪ [0, 1/6)` of length `5/8` is visited infinitely often. -/
theorem visits_one_arc_five_eighths : VisitsIO ((3 : ℝ) / 2) 1 (13 / 24) (5 / 8) :=
  visits_arc_five_eighths one_ne_zero

/-- At `ξ = 1`: `{(3/2)ⁿ}` has infinitely many limit points ([Vij40]). -/
theorem limitSet_one_infinite : (limitSet ((3 : ℝ) / 2) 1).Infinite :=
  limitSet_infinite one_ne_zero

end Z32
