/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.Dictionary
import Z32.DubickasWord

/-!
# Block certificates: kernel-checked emptiness of `Z_{p/q}(U)` (milestones M3, M6)

The engines of `plans/plan-cert32.html` milestone M2 (`Z32/atlas.c`, `Z32/verify_atlas.py`) decide
confinement questions numerically.  This file is the **bridge**: it turns one of their outputs into
a Lean theorem, checked by the kernel with `decide` — no `native_decide`, no floating point, no
cited axiom.

## What a certificate is

Fix coprime `p > q > 1` and write the orbit as `xₙ = ⌊ξ(p/q)ⁿ⌋`, `yₙ = {ξ(p/q)ⁿ}`, with carry word
`sₙ = q·x_{n+1} − p·xₙ` ([Dub09AA] (2), `Z32.carry`).  Eliminating `x` gives `Z32.carry_eq`,

`q·y_{n+1} = p·yₙ − sₙ`,  `sₙ ∈ {−q+1, …, p−1}`,

so confinement of `y` to a finite union of rational intervals `U` is survival under a
`(p+q−1)`-branch interval map (four branches at `3/2`, six at `4/3`).  A **certificate** for `U` is
a funnel of interval lists

`T₀ = U ⊇ T₁ ⊇ ⋯ ⊇ T_K =: H`

subject to two checks, both pure integer arithmetic over one common denominator `D`:

* `Z32.BlockCert.funnelOk` — for every `I ∈ T_k`, every carry `s` and every `J ∈ U`, the piece
  `{y ∈ J : (py−s)/q ∈ I}` lies inside a **single** interval of `T_{k+1}`.  Consequence: a confined
  orbit lies in `T_k` for every `k`, hence in the **blocks** `H`.
* `Z32.BlockCert.funcOk` — the block graph is deterministic *up to rank*: with the blocks stratified
  by a rank, no block has a successor of larger rank, and each has at most one successor of its own
  rank.  Consequence: the rank along a confined orbit is a non-increasing sequence of naturals,
  hence eventually constant, and from that point the block itinerary is *deterministic*, so by
  pigeonhole it is eventually periodic, and with it the carry word.  Taking `strata := []` gives
  every block rank `0` and recovers the plain "at most one outgoing edge" condition, which is what
  seven of the eight entries below use.

But the carry word of every `ξ ≠ 0` is **aperiodic** (`Z32.not_isEventuallyPeriodic_carry`, proved
in `Z32/DubickasWord.lean`).  Hence no `ξ ≠ 0` is confined to `U`.

This is the plan's `CYCLE` certificate.  Note what it does *not* need: no finiteness criterion for
the survivor set, no decoupling, no generalization of [FLP95] Theorem 3.2 beyond window length
`1/p` — which is why plan risk R-8 is closed by it (see plan §4.4).  It also does not need `ξ > 0`,
and it applies to unions verbatim.

## Main results

* `Z32.BlockCert.Cert.not_confined` — the soundness theorem: a valid certificate for `U` forbids
  every `ξ ≠ 0` from having its whole `(p/q)`-power orbit confined to `U` (mod 1).  The base is the
  certificate's own, and `ok` checks that it is admissible, so there is no side hypothesis.
* `Z32.BlockCert.Cert.not_eventually_confined` — the same for *eventual* confinement.
* `Z32.BlockCert.ZSet_eq_empty_of_cert` — the `FLP.ZSet` form, for a window covered by `U`.

Eight certified entries, each `decide`-checked.  Six at `3/2`:

* `Z32.ZSet_three_two_sixth_3_8` — `Z_{3/2}(1/6, 13/24) = ∅`, window length `3/8 = 0.375 > 1/3`:
  the **first entry beyond the [FLP95] line** (which stops at `1/p = 1/3`) and beyond [Dub09AA]
  (all `s`, but only at length `1/3`).  `Z32.not_eventually_mem_sixth_3_8` is its eventual form.
* `Z32.ZSet_three_two_frontier` — `Z_{3/2}(961/3600, 2427/3600) = ∅`, length
  `1466/3600 = 0.40722…`: the **engine frontier** of plan §4.4 experiment X2.
* `Z32.dubickas_2008_cor_1_2` — `[8/39,18/39] ∪ [21/39,31/39]`, total length `20/39`: [Dub08]
  Corollary 1.2 **as printed, with both intervals closed**, the strongest published *explicit*
  union-emptiness result.  The only entry here that needs both of the certificate's general
  features (closed endpoints and a rank stratification); see the convention note below.
* `Z32.union_seven_twelfths_empty`, `Z32.union_two_thirds_empty`, `Z32.union_record_empty` —
  unions of total length `7/12`, `2/3` and `25/36 = 0.6944…`, all past `20/39`.  Note that
  [KK18] Corollary 4.8 exhibits a *nonempty* union of the **same** total length `2/3`: total
  length alone decides nothing.

and two at other bases (milestone M6):

* `Z32.ZSet_four_three_beyond_line` — `Z_{4/3}(1/3, 5/8) = ∅`, length `7/24 = 0.2916… > 1/4`: the
  `(4,3)` analogue of the first entry, past the length-`1/p` line at a second base.
* `Z32.ZSet_five_two_fifth` — `Z_{5/2}(1/5, 2/5) = ∅`, in the regime `p > q²` that [Dub09AA] §4
  leaves open.  Read its docstring before quoting it: the engine certifies every *rational* window
  of length `1/p` tested in that regime, but the open statement is about *every real* position, and
  the cover argument that would bridge the two is measured to fail.

The certified windows are not vacuous: at `[1/6, 13/24)` the surviving set of the interval map is
the 3-cycle `4/19 → 6/19 → 9/19` (carries `0, 0, 1`), which is nonempty.  What the certificate
rules out is a *real number* whose fractional parts follow it, and that is exactly what
aperiodicity of the carry word forbids.  Three lemmas record that the checks have teeth:
`Z32.BlockCert.ok_eq_false_of_full` (`[0,1)` fails), `ok_eq_false_of_full_closed` (so does `[0,1]`
with a rank of its own) and `ok_eq_false_of_not_coprime` (a non-coprime base is refused — at
`4/2 = 2` the point `ξ = 1/3` really is periodic).

## Conventions

Intervals are half-open, `[a/D, b/D)`, the corpus `Ico` standard (`FLP.ZSet`), unless the
certificate sets `closed := true`, in which case every interval it mentions is `[a/D, b/D]`.  The
carry is [Dub09AA]'s `sₙ = q·x_{n+1} − p·xₙ`, the negative of the `e` printed by `Z32/atlas.c`.

**The convention is not cosmetic where the literature is closed.**  Emptiness for a larger set is a
stronger statement, so a closed-interval result implies its half-open shadow and not conversely.
[Dub08] Corollary 1.2 is printed closed, and the gap is real rather than notational: the closed set
genuinely holds a 4-cycle of the interval map through the right endpoint,
`6/13 → 9/13 → 7/13 → 4/13 → 6/13`, which the half-open set does not contain.  That cycle is also
why the half-open machinery alone does not reach it — with the endpoints in, the hold set acquires
infinitely many transients feeding two disjoint cycles, and *no* partition into blocks with one
outgoing edge each exists at any depth (measured to depth 40).  What does exist, at depth 3, is a
rank stratification, which is why `funcOk` is stated by rank.  Both features are opt-in and default
to the old behaviour, so the other entries are unchanged.

The base `p/q` is likewise a certificate field defaulting to `3/2`, so a `(3,2)` certificate never
mentions it (milestone M6).

The certificates are generated by `Z32/gencert.py`, which re-runs the exact pruning and emits the
funnel; nothing in this file trusts the engines — the kernel rechecks both conditions from scratch.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — the aperiodicity lemma, proved in `Z32/DubickasWord.lean`.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), no. 7, 951–958 — Corollary 1.2.
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **70.2** (1995), 125–147.
* [KK18] J. Kari, J. Kopra, *Cellular automata and powers of `p/q`*, RAIRO ITA **51** (2017/18) —
  Corollary 4.8, Problem 6.1.
* [Aki08] S. Akiyama, *Mahler's `Z`-number and `3/2` number systems*, Unif. Distrib. Theory **3**
  (2008), no. 2, 91–99 — Theorems 2.4/2.5 (nonempty sets for `p > q²`), Conjecture 1.4.
* `plans/plan-cert32.html` §4.1, §4.4 (the certificate), §11.2 (M6, the parametric engine), §9
  (file plan); `Z32/README.md`.
-/

namespace Z32.BlockCert

open ForMathlib.SubwordComplexity

/-! ## Integer intervals

Everything is scaled by one common denominator `D`, so that every check below is an inequality
between integers: no rational arithmetic reaches the kernel.  `min` and `max` are expanded by hand
into disjunctions for the same reason — an order-theoretic `max` on `ℤ` unfolds through
`LinearOrder` projections, which `decide` does not enjoy. -/

/-- An interval with scaled endpoints `a`, `b`: either `[a/D, b/D)` or `[a/D, b/D]`, according to
the certificate's `closed` flag. -/
abbrev Ivl := ℤ × ℤ

/-- The right-endpoint comparison: `≤` for closed intervals, `<` for half-open ones.  Every
`closed`-dependent step of the development factors through this and its integer form `rle`. -/
def rleR : Bool → ℝ → ℝ → Prop
  | true, x, y => x ≤ y
  | false, x, y => x < y

/-- The integer form of `rleR`, the only shape the kernel ever evaluates. -/
def rle : Bool → ℤ → ℤ → Bool
  | true, x, y => decide (x ≤ y)
  | false, x, y => decide (x < y)

/-- `y` lies in `[I.1/D, I.2/D)` (`cl = false`) or `[I.1/D, I.2/D]` (`cl = true`), written
multiplicatively. -/
def memI (D : ℤ) (cl : Bool) (I : Ivl) (y : ℝ) : Prop :=
  (I.1 : ℝ) ≤ (D : ℝ) * y ∧ rleR cl ((D : ℝ) * y) (I.2 : ℝ)

/-- `y` lies in the union of the intervals of `L`. -/
def memL (D : ℤ) (cl : Bool) (L : List Ivl) (y : ℝ) : Prop := ∃ I ∈ L, memI D cl I y

/-! ### The carry alphabet

From `q·y_{n+1} = p·yₙ − sₙ` with `yₙ, y_{n+1} ∈ [0,1)` one gets `−q < sₙ < p`, so the alphabet is
`{−q+1, …, p−1}` — exactly `p + q − 1` letters (four at `(3,2)`, six at `(4,3)`).  Built by an
explicit structural recursion rather than `List.range` + `List.map`, because the kernel unfolds it
directly and because membership is then a two-line induction. -/

/-- `[a, a+1, …, a+n−1]`. -/
def carriesFrom (a : ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => a :: carriesFrom (a + 1) n

/-- The `p + q − 1` carries `sₙ = q·x_{n+1} − p·xₙ` available to the base `p/q`. -/
def carries (p q : ℕ) : List ℤ := carriesFrom (1 - (q : ℤ)) (p + q - 1)

theorem mem_carriesFrom : ∀ (n : ℕ) (a s : ℤ), a ≤ s → s < a + n → s ∈ carriesFrom a n
  | 0, a, s, h1, h2 => absurd h2 (by simp only [Nat.cast_zero, add_zero]; omega)
  | n + 1, a, s, h1, h2 => by
    rcases eq_or_lt_of_le h1 with h | h
    · rw [carriesFrom, ← h]; exact List.mem_cons_self ..
    · refine List.mem_cons_of_mem _ (mem_carriesFrom n (a + 1) s (by omega) ?_)
      push_cast at h2 ⊢
      omega

/-- Every integer strictly between `−q` and `p` is a carry. -/
theorem mem_carries {p q : ℕ} {s : ℤ} (h1 : -(q : ℤ) < s) (h2 : s < (p : ℤ)) : s ∈ carries p q :=
  mem_carriesFrom _ _ _ (by omega) (by omega)

/-! ## The two checks -/

/-- `x ≤ max a b`, without `max`. -/
def leMax (x a b : ℤ) : Bool := decide (x ≤ a) || decide (x ≤ b)

/-- `min a b ≤ x`, without `min`. -/
def minLe (a b x : ℤ) : Bool := decide (a ≤ x) || decide (b ≤ x)

/-- Scaled by `pD`, the piece `{y ∈ J : (py−s)/q ∈ I}` is `[max A B, min C E)` with
`A = q·I.1 + s·D`, `B = p·J.1`, `C = q·I.2 + s·D`, `E = p·J.2`. -/
def pieceA (D : ℤ) (q : ℕ) (I : Ivl) (s : ℤ) : ℤ := q * I.1 + s * D

/-- Right endpoint of the branch-`s` preimage of `I`, scaled by `pD`; see `pieceA`. -/
def pieceC (D : ℤ) (q : ℕ) (I : Ivl) (s : ℤ) : ℤ := q * I.2 + s * D

/-- The piece `{y ∈ J : (py−s)/q ∈ I}` is empty, or contained in one interval of `next`.

The piece is `[max A B, min C E⟩` with the certificate's own right-endpoint convention, so it is
empty exactly when `min C E` fails to be strictly-or-weakly above `max A B` — that is, under the
*flipped* convention `rle (!cl)`, which is why the four emptiness disjuncts carry `!cl` while the
containment test `[max A B, min C E⟩ ⊆ [pK.1, pK.2⟩` is the plain `≤` for either convention. -/
def pieceOk (D : ℤ) (p q : ℕ) (cl : Bool) (next : List Ivl) (I J : Ivl) (s : ℤ) : Bool :=
  rle (!cl) (pieceC D q I s) (pieceA D q I s) ||
  rle (!cl) (pieceC D q I s) (p * J.1) ||
  rle (!cl) (p * J.2) (pieceA D q I s) ||
  rle (!cl) (p * J.2) (p * J.1) ||
  next.any fun K =>
    leMax (p * K.1) (pieceA D q I s) (p * J.1) && minLe (pieceC D q I s) (p * J.2) (p * K.2)

/-- One funnel step: `U ∩ f⁻¹(cur) ⊆ next`, interval by interval. -/
def levelOk (D : ℤ) (p q : ℕ) (cl : Bool) (U cur next : List Ivl) : Bool :=
  cur.all fun I => (carries p q).all fun s => U.all fun J => pieceOk D p q cl next I J s

/-- The whole funnel `cur ⊇ levels[0] ⊇ levels[1] ⊇ ⋯`. -/
def funnelOk (D : ℤ) (p q : ℕ) (cl : Bool) (U : List Ivl) : List Ivl → List (List Ivl) → Bool
  | _, [] => true
  | cur, next :: rest => levelOk D p q cl U cur next && funnelOk D p q cl U next rest

/-- The last level of the funnel: the blocks. -/
def finalLevel : List Ivl → List (List Ivl) → List Ivl
  | cur, [] => cur
  | _, next :: rest => finalLevel next rest

/-- The branch-`s` image of `I` meets `J`: `max (pI.1) (qJ.1+sD) ⟨ min (pI.2) (qJ.2+sD)`, expanded,
with `⟨` the certificate's own convention — closed intervals meet when they merely touch. -/
def hits (D : ℤ) (p q : ℕ) (cl : Bool) (I J : Ivl) (s : ℤ) : Bool :=
  rle cl (p * I.1) (p * I.2) && rle cl (p * I.1) (q * J.2 + s * D) &&
    rle cl (q * J.1 + s * D) (p * I.2) && rle cl (q * J.1 + s * D) (q * J.2 + s * D)

/-- All `(carry, block)` pairs reachable from the block `I`. -/
def outEdges (D : ℤ) (p q : ℕ) (cl : Bool) (H : List Ivl) (I : Ivl) : List (ℤ × Ivl) :=
  (carries p q).flatMap fun s => (H.filter fun J => hits D p q cl I J s).map fun J => (s, J)

/-! ### Ranked determinism

Requiring *one* outgoing edge per block is more than the soundness proof needs, and more than some
hold sets can supply: a set whose hold set carries transients feeding a cycle has blocks with two
successors, one of them a strictly-nearer-the-cycle block.  What the proof actually needs is that
the itinerary is *eventually* forced, and that follows from a rank:

* successors never increase the rank, so the rank along an orbit is non-increasing, hence
  eventually constant (it is a `ℕ`);
* each block has at most one successor of its **own** rank, so from that moment the itinerary is
  deterministic.

`strata` lists the blocks by rank, lowest first; `strata = []` gives every block rank `0` and
recovers the plain "at most one outgoing edge" condition verbatim. -/

/-- The rank of `I`: the index of the first stratum containing it (`0` if `strata` is empty). -/
def rank : List (List Ivl) → Ivl → ℕ
  | [], _ => 0
  | st :: rest, I => if I ∈ st then 0 else rank rest I + 1

/-- The block transition relation is deterministic **up to rank**: no successor of a block has
larger rank, and at most one has equal rank. -/
def funcOk (D : ℤ) (p q : ℕ) (cl : Bool) (H : List Ivl) (strata : List (List Ivl)) : Bool :=
  H.all fun I =>
    (outEdges D p q cl H I).all (fun e => decide (rank strata e.2 ≤ rank strata I)) &&
      decide (((outEdges D p q cl H I).filter fun e =>
        decide (rank strata e.2 = rank strata I)).length ≤ 1)

/-- A **block certificate** for the set `⋃ U` at the base `p/q`: the base, a common denominator,
the set itself, the funnel of levels ending in the blocks, and — where the block graph is not
outright functional — a rank stratification of the blocks.

`p` and `q` default to the `3/2` of this file's headline entries, so a `(3,2)` certificate never
mentions them. -/
structure Cert where
  /-- The common denominator of every endpoint. -/
  D : ℤ
  /-- The numerator of the base `p/q`; `ok` checks `q < p` and `gcd p q = 1`. -/
  p : ℕ := 3
  /-- The denominator of the base `p/q`; `ok` checks `1 < q`. -/
  q : ℕ := 2
  /-- Are the intervals closed on the right?  Closed is the *stronger* statement. -/
  closed : Bool := false
  /-- The certified set, as a list of intervals `[a/D, b/D⟩`. -/
  U : List Ivl
  /-- The funnel `T₁, …, T_K`; `T₀` is `U` itself and `T_K` is the block list. -/
  levels : List (List Ivl)
  /-- The blocks by rank, lowest first; `[]` means "every block has rank `0`". -/
  strata : List (List Ivl) := []

namespace Cert

/-- The blocks of the certificate: the last level of the funnel. -/
def blocks (c : Cert) : List Ivl := finalLevel c.U c.levels

/-- The certificate is valid: positive denominator, an admissible base `p/q` (coprime, `p > q > 1`
— exactly the hypotheses of the aperiodicity lemma `Z32.not_isEventuallyPeriodic_carry`), the
funnel closes, the block graph is deterministic up to rank.  Decidable by kernel evaluation, so
`Cert.not_confined` needs no side hypothesis beyond `ok` itself. -/
def ok (c : Cert) : Bool :=
  decide (0 < c.D) && decide (1 < c.q) && decide (c.q < c.p) && decide (Nat.gcd c.p c.q = 1) &&
    funnelOk c.D c.p c.q c.closed c.U c.U c.levels &&
    funcOk c.D c.p c.q c.closed c.blocks c.strata

end Cert

/-! ## Soundness

### The convention lemmas

Everything the proof needs to know about `closed` is here: `rleR` transports across `≤` on either
side, across a positive rescaling, and is the pointwise negation of its own flip. -/

private theorem rle_iff (cl : Bool) (x y : ℤ) : rle cl x y = true ↔ rleR cl (x : ℝ) (y : ℝ) := by
  cases cl <;> simp [rle, rleR]

private theorem rleR_le {cl : Bool} {x y : ℝ} (h : rleR cl x y) : x ≤ y := by
  cases cl <;> simp only [rleR] at h <;> linarith

private theorem rleR_trans_left {cl : Bool} {x y z : ℝ} (h : x ≤ y) (h2 : rleR cl y z) :
    rleR cl x z := by cases cl <;> simp only [rleR] at h2 ⊢ <;> linarith

private theorem rleR_trans_right {cl : Bool} {x y z : ℝ} (h : rleR cl x y) (h2 : y ≤ z) :
    rleR cl x z := by cases cl <;> simp only [rleR] at h ⊢ <;> linarith

/-- Transport along a positive rescaling: `rleR cl x y` says `x - y` is `≤ 0` (resp. `< 0`), and
that survives multiplication by any `k > 0`. -/
private theorem rleR_scale {cl : Bool} {x y u v k : ℝ} (hk : 0 < k) (h : rleR cl x y)
    (h1 : u - v ≤ k * (x - y)) : rleR cl u v := by
  cases cl
  · simp only [rleR] at h ⊢; nlinarith [mul_pos hk (sub_pos.mpr h)]
  · simp only [rleR] at h ⊢; nlinarith [mul_nonneg hk.le (sub_nonneg.mpr h)]

/-- Cancellation of a positive factor.  At `(3,2)` the last step of a funnel step divided by the
literal `3`; at a general base the factor is the variable `p`, so `rleR_scale` with `k = 1/p` would
drag a division through `linarith`.  This states the same fact without one. -/
private theorem rleR_cancel {cl : Bool} {k x y : ℝ} (hk : 0 < k) (h : rleR cl (k * x) (k * y)) :
    rleR cl x y := by
  cases cl
  · simp only [rleR] at h ⊢; exact lt_of_mul_lt_mul_left h hk.le
  · simp only [rleR] at h ⊢; exact le_of_mul_le_mul_left h hk

/-- The flip `!cl` is the negation: a nonempty piece cannot pass the emptiness test. -/
private theorem not_rleR_flip {cl : Bool} {A C t : ℝ} (hA : A ≤ t) (hC : rleR cl t C) :
    ¬ rleR (!cl) C A := by
  cases cl <;> simp only [rleR, Bool.not_true, Bool.not_false] at hC ⊢ <;> intro h <;> linarith

private theorem eq_of_mem_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l with
  | [] => exact absurd ha (by simp)
  | [_] => rw [List.mem_singleton] at ha hb; rw [ha, hb]
  | _ :: _ :: _ => simp at h

/-- A sequence with values in a finite list repeats. -/
private theorem exists_lt_eq {α : Type*} [DecidableEq α] {L : List α} {B : ℕ → α}
    (hB : ∀ n, B n ∈ L) : ∃ i j, i < j ∧ B i = B j := by
  have hcard : L.toFinset.card < (Finset.range (L.length + 1)).card := by
    rw [Finset.card_range]
    exact Nat.lt_succ_of_le L.toFinset_card_le
  obtain ⟨x, _, z, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := B) fun a _ => List.mem_toFinset.mpr (hB a)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨x, z, h, heq⟩
  · exact ⟨z, x, h, heq.symm⟩

variable {c : Cert} {ξ : ℝ}

/-- Everything `ok` certifies, unpacked once. -/
private theorem ok_parts (hc : c.ok = true) :
    0 < c.D ∧ 1 < c.q ∧ c.q < c.p ∧ Nat.gcd c.p c.q = 1 ∧
      funnelOk c.D c.p c.q c.closed c.U c.U c.levels = true ∧
      funcOk c.D c.p c.q c.closed c.blocks c.strata = true := by
  simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

/-- **The funnel and the block graph, at the level of the model.**  This is everything the
soundness theorem below establishes *before* aperiodicity enters: the funnel pushes a confined
orbit into the blocks, and consecutive blocks are joined by an edge of the block graph labelled by
the carry.

It is stated for an abstract sequence `y` in `[0,1)` obeying the two-branch recursion rather than
for `yFract`, because that is exactly the **model** orbit of `Z32/ModelEntropy.lean`, where the
block path — not the contradiction — is what the counting argument consumes.
`Cert.not_confined` instantiates it at `y = yFract`. -/
theorem Cert.exists_block_path (hc : c.ok = true) {y : ℕ → ℝ} {w : ℕ → ℤ}
    (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n < 1) (hmem : ∀ n, memL c.D c.closed c.U (y n))
    (hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ)) :
    ∃ B : ℕ → Ivl, (∀ n, B n ∈ c.blocks) ∧ (∀ n, memI c.D c.closed (B n) (y n)) ∧
      ∀ n, (w n, B (n + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (B n) := by
  obtain ⟨-, hq1, hqp, -, hfun, -⟩ := ok_parts hc
  have hq0' : 0 < c.q := by omega
  have hp0' : 0 < c.p := by omega
  have hqR : (0 : ℝ) < c.q := by exact_mod_cast hq0'
  have hpR : (0 : ℝ) < c.p := by exact_mod_cast hp0'
  have hwmem : ∀ n, w n ∈ carries c.p c.q := by
    intro n
    have h := hrec n
    have e1 : (c.p : ℝ) * y n < (c.p : ℝ) * 1 := mul_lt_mul_of_pos_left (hy1 n) hpR
    have e2 : (c.q : ℝ) * y (n + 1) < (c.q : ℝ) * 1 := mul_lt_mul_of_pos_left (hy1 (n + 1)) hqR
    have e3 : 0 ≤ (c.p : ℝ) * y n := mul_nonneg hpR.le (hy0 n)
    have e4 : 0 ≤ (c.q : ℝ) * y (n + 1) := mul_nonneg hqR.le (hy0 (n + 1))
    have hlo : -(c.q : ℤ) < w n := by
      have h' : -((c.q : ℕ) : ℝ) < (w n : ℝ) := by linarith
      exact_mod_cast h'
    have hhi : w n < (c.p : ℤ) := by
      have h' : (w n : ℝ) < ((c.p : ℕ) : ℝ) := by linarith
      exact_mod_cast h'
    exact mem_carries hlo hhi
  -- the key algebraic identity, scaled by `pD`
  have hkey : ∀ n, (c.q : ℝ) * ((c.D : ℝ) * y (n + 1)) + (w n : ℝ) * c.D
      = (c.p : ℝ) * ((c.D : ℝ) * y n) := by
    intro n
    have h : (c.D : ℝ) * ((c.q : ℝ) * y (n + 1)) = (c.D : ℝ) * ((c.p : ℝ) * y n - (w n : ℝ)) := by
      rw [hrec n]
    nlinarith [h]
  -- one funnel step
  have hstep : ∀ cur next : List Ivl, levelOk c.D c.p c.q c.closed c.U cur next = true →
      (∀ n, memL c.D c.closed cur (y n)) → ∀ n, memL c.D c.closed next (y n) := by
    intro cur next hlev hcur n
    obtain ⟨I, hI, hIm⟩ := hcur (n + 1)
    obtain ⟨J, hJ, hJm⟩ := hmem n
    have hpc : pieceOk c.D c.p c.q c.closed next I J (w n) = true := by
      simp only [levelOk, List.all_eq_true] at hlev
      exact hlev I hI (w n) (hwmem n) J hJ
    set t : ℝ := (c.p : ℝ) * ((c.D : ℝ) * y n) with htdef
    have hA : ((pieceA c.D c.q I (w n) : ℤ) : ℝ) ≤ t := by
      have h1 : (c.q : ℝ) * (I.1 : ℝ) ≤ (c.q : ℝ) * ((c.D : ℝ) * y (n + 1)) :=
        mul_le_mul_of_nonneg_left hIm.1 hqR.le
      simp only [pieceA, htdef]; push_cast; linarith [hkey n]
    have hB : (((c.p : ℤ) * J.1 : ℤ) : ℝ) ≤ t := by
      have h1 : (c.p : ℝ) * (J.1 : ℝ) ≤ (c.p : ℝ) * ((c.D : ℝ) * y n) :=
        mul_le_mul_of_nonneg_left hJm.1 hpR.le
      simp only [htdef]; push_cast; linarith
    have hC : rleR c.closed t ((pieceC c.D c.q I (w n) : ℤ) : ℝ) := by
      refine rleR_scale (k := (c.q : ℝ)) hqR hIm.2 ?_
      simp only [pieceC, htdef]; push_cast; linarith [hkey n]
    have hE : rleR c.closed t (((c.p : ℤ) * J.2 : ℤ) : ℝ) := by
      refine rleR_scale (k := (c.p : ℝ)) hpR hJm.2 ?_
      simp only [htdef]; push_cast; linarith
    -- the piece is not empty, so the covering disjunct must hold
    have hne1 := (rle_iff (!c.closed) (pieceC c.D c.q I (w n)) (pieceA c.D c.q I (w n))).not.mpr
      (not_rleR_flip hA hC)
    have hne2 := (rle_iff (!c.closed) (pieceC c.D c.q I (w n)) ((c.p : ℤ) * J.1)).not.mpr
      (not_rleR_flip hB hC)
    have hne3 := (rle_iff (!c.closed) ((c.p : ℤ) * J.2) (pieceA c.D c.q I (w n))).not.mpr
      (not_rleR_flip hA hE)
    have hne4 := (rle_iff (!c.closed) ((c.p : ℤ) * J.2) ((c.p : ℤ) * J.1)).not.mpr
      (not_rleR_flip hB hE)
    simp only [pieceOk, minLe, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.and_eq_true, leMax] at hpc
    rcases hpc with ((((h | h) | h) | h) | ⟨K, hK, hKlo, hKhi⟩)
    · exact absurd h hne1
    · exact absurd h hne2
    · exact absurd h hne3
    · exact absurd h hne4
    · refine ⟨K, hK, ?_, ?_⟩
      · have h3 : (c.p : ℝ) * (K.1 : ℝ) ≤ t := by
          rcases hKlo with h | h
          · have h' : (((c.p : ℤ) * K.1 : ℤ) : ℝ) ≤ ((pieceA c.D c.q I (w n) : ℤ) : ℝ) := by
              exact_mod_cast h
            push_cast at h'; linarith
          · have h' : (((c.p : ℤ) * K.1 : ℤ) : ℝ) ≤ (((c.p : ℤ) * J.1 : ℤ) : ℝ) := by
              exact_mod_cast h
            have hB' := hB
            push_cast at h' hB'
            linarith
        rw [htdef] at h3
        exact le_of_mul_le_mul_left h3 hpR
      · have h3 : rleR c.closed t (((c.p : ℤ) * K.2 : ℤ) : ℝ) := by
          rcases hKhi with h | h
          · exact rleR_trans_right hC (by exact_mod_cast h)
          · exact rleR_trans_right hE (by exact_mod_cast h)
        refine rleR_cancel (k := (c.p : ℝ)) hpR ?_
        have e2 : (c.p : ℝ) * (K.2 : ℝ) = (((c.p : ℤ) * K.2 : ℤ) : ℝ) := by push_cast; ring
        rw [htdef] at h3
        rw [e2]
        exact h3
  -- the whole funnel
  have hfin : ∀ (cur : List Ivl) (levels : List (List Ivl)),
      funnelOk c.D c.p c.q c.closed c.U cur levels = true →
      (∀ n, memL c.D c.closed cur (y n)) → ∀ n, memL c.D c.closed (finalLevel cur levels) (y n) := by
    intro cur levels
    induction levels generalizing cur with
    | nil => intro _ h; exact h
    | cons next rest ih =>
      intro hf hcur
      simp only [funnelOk, Bool.and_eq_true] at hf
      exact ih next hf.2 (hstep cur next hf.1 hcur)
  have hH : ∀ n, memL c.D c.closed c.blocks (y n) := hfin c.U c.levels hfun hmem
  -- the block itinerary
  choose Bl hBmem hBm using hH
  have hedge : ∀ n, (w n, Bl (n + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (Bl n) := by
    intro n
    set t : ℝ := (c.p : ℝ) * ((c.D : ℝ) * y n) with htdef
    have h1 : (((c.p : ℤ) * (Bl n).1 : ℤ) : ℝ) ≤ t := by
      have h := mul_le_mul_of_nonneg_left (hBm n).1 hpR.le
      simp only [htdef]; push_cast; linarith
    have h2 : rleR c.closed t (((c.p : ℤ) * (Bl n).2 : ℤ) : ℝ) := by
      refine rleR_scale (k := (c.p : ℝ)) hpR (hBm n).2 ?_
      simp only [htdef]; push_cast; linarith
    have h3 : (((c.q : ℤ) * (Bl (n + 1)).1 + w n * c.D : ℤ) : ℝ) ≤ t := by
      have h := mul_le_mul_of_nonneg_left (hBm (n + 1)).1 hqR.le
      simp only [htdef]; push_cast; linarith [hkey n]
    have h4 : rleR c.closed t (((c.q : ℤ) * (Bl (n + 1)).2 + w n * c.D : ℤ) : ℝ) := by
      refine rleR_scale (k := (c.q : ℝ)) hqR (hBm (n + 1)).2 ?_
      simp only [htdef]; push_cast; linarith [hkey n]
    simp only [outEdges, List.mem_flatMap, List.mem_map, List.mem_filter]
    refine ⟨w n, hwmem n, Bl (n + 1), ⟨hBmem (n + 1), ?_⟩, rfl⟩
    simp only [hits, Bool.and_eq_true]
    exact ⟨⟨⟨(rle_iff _ _ _).mpr (rleR_trans_left h1 h2),
              (rle_iff _ _ _).mpr (rleR_trans_left h1 h4)⟩,
              (rle_iff _ _ _).mpr (rleR_trans_left h3 h2)⟩,
              (rle_iff _ _ _).mpr (rleR_trans_left h3 h4)⟩
  exact ⟨Bl, hBmem, hBm, hedge⟩

/-- **Soundness of a block certificate.**  If `c.ok` then no `ξ ≠ 0` has its whole `(p/q)`-power
orbit confined, mod 1, to the set described by `c.U`.

The proof: the funnel pushes the orbit into the blocks (`Cert.exists_block_path`); the rank of the
block is non-increasing along the orbit, hence eventually constant, and from that moment the block
graph is a partial function, so the itinerary is deterministic, hence eventually periodic by
pigeonhole, hence the carry word is eventually periodic — contradicting
`Z32.not_isEventuallyPeriodic_carry`.

Nothing here is special to `3/2`: the aperiodicity lemma holds for every coprime `p > q > 1`, and
`c.ok` checks exactly those three conditions on the certificate's own base, which is why this
theorem needs no side hypothesis. -/
theorem Cert.not_confined (hc : c.ok = true) (hξ : ξ ≠ 0) :
    ¬ ∀ n, memL c.D c.closed c.U (yFract c.p c.q ξ 0 n) := by
  intro hy
  obtain ⟨-, hq1, hqp, hcop, -, hfunc⟩ := ok_parts hc
  have hq0' : 0 < c.q := by omega
  simp only [funcOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfunc
  have hrank : ∀ I ∈ c.blocks, ∀ e ∈ outEdges c.D c.p c.q c.closed c.blocks I,
      rank c.strata e.2 ≤ rank c.strata I := fun I hI =>
    by simpa only [List.all_eq_true, decide_eq_true_eq] using (hfunc I hI).1
  have hone : ∀ I ∈ c.blocks, ((outEdges c.D c.p c.q c.closed c.blocks I).filter fun e =>
      decide (rank c.strata e.2 = rank c.strata I)).length ≤ 1 := fun I hI => (hfunc I hI).2
  set y : ℕ → ℝ := yFract c.p c.q ξ 0 with hydef
  set w : ℕ → ℤ := carry c.p c.q ξ 0 with hwdef
  -- the `p+q−1`-branch recursion
  have hy0 : ∀ n, 0 ≤ y n := fun n => yFract_nonneg n
  have hy1 : ∀ n, y n < 1 := fun n => yFract_lt_one n
  have hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ) := by
    intro n
    have h := carry_eq (p := c.p) (q := c.q) (ξ := ξ) (ν := 0) hq0' n
    simp only [mul_zero, sub_zero] at h
    rw [hwdef, hydef]
    linarith
  obtain ⟨Bl, hBmem, -, hedge⟩ := Cert.exists_block_path hc hy0 hy1 hy hrec
  -- the rank of the block is non-increasing, hence eventually constant
  have hmono : ∀ n, rank c.strata (Bl (n + 1)) ≤ rank c.strata (Bl n) := fun n =>
    hrank (Bl n) (hBmem n) _ (hedge n)
  have hanti : ∀ i d, rank c.strata (Bl (i + d)) ≤ rank c.strata (Bl i) := by
    intro i d
    induction d with
    | zero => exact le_rfl
    | succ d ih => exact le_trans (hmono (i + d)) ih
  have hne : (Set.range fun n => rank c.strata (Bl n)).Nonempty := ⟨rank c.strata (Bl 0), 0, rfl⟩
  obtain ⟨N, hNeq⟩ : ∃ N, rank c.strata (Bl N) = sInf (Set.range fun n => rank c.strata (Bl n)) :=
    Nat.sInf_mem hne
  have hN : ∀ n, N ≤ n → rank c.strata (Bl n) = rank c.strata (Bl N) := by
    intro n hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact le_antisymm (hanti N d) (hNeq ▸ Nat.sInf_le ⟨N + d, rfl⟩)
  -- past `N` the itinerary is deterministic
  have hdet : ∀ n m, N ≤ n → N ≤ m → Bl n = Bl m → w n = w m ∧ Bl (n + 1) = Bl (m + 1) := by
    intro n m hn hm hnm
    have key : ∀ k, N ≤ k →
        (w k, Bl (k + 1)) ∈ (outEdges c.D c.p c.q c.closed c.blocks (Bl k)).filter
        fun e => decide (rank c.strata e.2 = rank c.strata (Bl k)) := by
      intro k hk
      refine List.mem_filter.mpr ⟨hedge k, ?_⟩
      simp only [decide_eq_true_eq]
      exact (hN (k + 1) (le_trans hk (Nat.le_succ k))).trans (hN k hk).symm
    have h1 := key n hn
    have h2 := key m hm
    rw [← hnm] at h2
    have := eq_of_mem_of_length_le_one (hone (Bl n) (hBmem n)) h1 h2
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  -- pigeonhole on the tail: the itinerary repeats, hence is eventually periodic
  obtain ⟨i, j, hij, hBij⟩ :=
    exists_lt_eq (L := c.blocks) (B := fun k => Bl (N + k)) fun k => hBmem (N + k)
  have hprop : ∀ k, Bl (N + i + k) = Bl (N + j + k) := by
    intro k
    induction k with
    | zero => simpa using hBij
    | succ k ih => exact (hdet (N + i + k) (N + j + k) (by omega) (by omega) ih).2
  refine not_isEventuallyPeriodic_carry (p := c.p) (q := c.q) (ξ := ξ) (ν := 0)
    hq1 hqp hcop hξ ⟨N + i, j - i, by omega, ?_⟩
  intro k hk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hidx : N + i + r + (j - i) = N + j + r := by omega
  rw [← hwdef, hidx]
  exact ((hdet (N + i + r) (N + j + r) (by omega) (by omega) (hprop r)).1).symm

/-- **The eventual form.**  A valid certificate also forbids *eventual* confinement: shifting the
orbit by `N` gives a genuinely confined orbit for the same set. -/
theorem Cert.not_eventually_confined (hc : c.ok = true) (hξ : ξ ≠ 0) {N : ℕ}
    (h : ∀ n, N ≤ n → memL c.D c.closed c.U (Int.fract (ξ * ((c.p : ℝ) / c.q) ^ n))) : False := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := ok_parts hc
  have hbase : (0 : ℝ) < (c.p : ℝ) / c.q :=
    div_pos (by exact_mod_cast (by omega : 0 < c.p)) (by exact_mod_cast (by omega : 0 < c.q))
  have hpow : (0 : ℝ) < ((c.p : ℝ) / c.q) ^ N := pow_pos hbase N
  refine Cert.not_confined (c := c) (ξ := ξ * ((c.p : ℝ) / c.q) ^ N) hc
    (by exact mul_ne_zero hξ hpow.ne') fun n => ?_
  have hval : yFract c.p c.q (ξ * ((c.p : ℝ) / c.q) ^ N) 0 n
      = Int.fract (ξ * ((c.p : ℝ) / c.q) ^ (N + n)) := by
    simp only [yFract, orb, add_zero]
    rw [mul_assoc, ← pow_add]
  rw [hval]
  exact h _ (Nat.le_add_right _ _)


/-! ## From a certificate to `FLP.ZSet`

`FLP.ZSet 3 2 s t` is `{ξ > 0 : {ξ(3/2)ⁿ} ∈ [s, s+t) ∀ n}`.  A certificate kills a *superset* of
the window, so any window covered by `c.U` gets an empty `Z`-set — and, by the shift trick, no
orbit is even *eventually* confined to it. -/

/-- `yFract` at shift `0` is the plain fractional part of the orbit. -/
theorem yFract_shift_zero (p q : ℕ) (ξ : ℝ) (n : ℕ) :
    yFract p q ξ 0 n = Int.fract (ξ * ((p : ℝ) / q) ^ n) := by
  simp only [yFract, orb, add_zero]

/-- **The `Z`-set form.**  If every point of the window `[s, s+t)` is covered by the certified
set, then `Z_{p/q}(s, s+t) = ∅`. -/
theorem ZSet_eq_empty_of_cert {c : Cert} (hc : c.ok = true) {s t : ℝ}
    (hU : ∀ y : ℝ, s ≤ y → y < s + t → memL c.D c.closed c.U y) : FLP.ZSet c.p c.q s t = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ξ ⟨hξ, h⟩
  refine Cert.not_confined hc (ne_of_gt hξ) fun n => ?_
  rw [yFract_shift_zero]
  have hn := h n
  rw [Set.mem_Ico] at hn
  exact hU _ hn.1 hn.2

/-- **The eventual form.**  No `ξ ≠ 0` has `{ξ(p/q)ⁿ}` eventually inside a certified window. -/
theorem not_eventually_mem_Ico_of_cert {c : Cert} (hc : c.ok = true) {s t : ℝ}
    (hU : ∀ y : ℝ, s ≤ y → y < s + t → memL c.D c.closed c.U y) {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n, N ≤ n → Int.fract (ξ * ((c.p : ℝ) / c.q) ^ n) ∈ Set.Ico s (s + t) := by
  intro h
  refine Cert.not_eventually_confined hc hξ (N := N) fun n hn => ?_
  have := h n hn
  rw [Set.mem_Ico] at this
  exact hU _ this.1 this.2

/-! ### Reading a certificate at a named base

The three theorems above carry the certificate's own `(↑c.p)/(↑c.q)`, while a statement about a
concrete base is written with a real literal such as `(3 : ℝ)/2`.  These three lemmas do that
translation once, so that each entry below supplies only the (definitional) base equation. -/

/-- `Cert.not_confined` with the base named. -/
theorem not_confined_base {c : Cert} (hc : c.ok = true) (β : ℝ) (hβ : (c.p : ℝ) / c.q = β)
    {ξ : ℝ} (hξ : ξ ≠ 0) : ¬ ∀ n, memL c.D c.closed c.U (Int.fract (ξ * β ^ n)) := by
  intro h
  refine Cert.not_confined hc hξ fun n => ?_
  rw [yFract_shift_zero, hβ]
  exact h n

/-- `ZSet_eq_empty_of_cert` with the base named. -/
theorem ZSet_eq_empty_of_cert_base {c : Cert} (hc : c.ok = true) {P Q : ℕ} (hp : c.p = P)
    (hq : c.q = Q) {s t : ℝ} (hU : ∀ y : ℝ, s ≤ y → y < s + t → memL c.D c.closed c.U y) :
    FLP.ZSet P Q s t = ∅ := by
  subst hp; subst hq; exact ZSet_eq_empty_of_cert hc hU

/-- `not_eventually_mem_Ico_of_cert` with the base named. -/
theorem not_eventually_mem_Ico_of_cert_base {c : Cert} (hc : c.ok = true) (β : ℝ)
    (hβ : (c.p : ℝ) / c.q = β) {s t : ℝ}
    (hU : ∀ y : ℝ, s ≤ y → y < s + t → memL c.D c.closed c.U y) {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n, N ≤ n → Int.fract (ξ * β ^ n) ∈ Set.Ico s (s + t) := by
  subst hβ; exact not_eventually_mem_Ico_of_cert hc hU hξ

/-- **A single-window certificate, read off its own interval.**  When the certified set `U` is the
one half-open interval `[a/D, b/D)`, the certificate proves emptiness of exactly that window, and
the covering hypothesis of `ZSet_eq_empty_of_cert_base` is pure endpoint arithmetic.  Doing it once
here turns each window entry below into a single application, which is what makes the thirty-entry
table of the `p > q²` regime affordable to state. -/
theorem ZSet_eq_empty_of_window {c : Cert} (hc : c.ok = true) {P Q : ℕ} (hp : c.p = P)
    (hq : c.q = Q) {a b : ℤ} (hU : c.U = [(a, b)]) (hcl : c.closed = false) {s t : ℝ}
    (hs : (a : ℝ) = s * c.D) (hb : (b : ℝ) = (s + t) * c.D) : FLP.ZSet P Q s t = ∅ := by
  obtain ⟨hD, -⟩ := ok_parts hc
  have hDR : (0 : ℝ) < (c.D : ℝ) := by exact_mod_cast hD
  refine ZSet_eq_empty_of_cert_base hc hp hq fun y h1 h2 => ?_
  refine ⟨(a, b), by simp [hU], ?_, ?_⟩
  · show (a : ℝ) ≤ (c.D : ℝ) * y
    rw [hs]; nlinarith
  · show rleR c.closed ((c.D : ℝ) * y) ((b : ℝ))
    rw [hcl, hb]; show (c.D : ℝ) * y < (s + t) * (c.D : ℝ)
    nlinarith



/-! ## Certified entries

Each certificate below is emitted by `Z32/gencert.py` and re-checked here by the kernel.
-/

/-- Certificate for `[8/39,18/39] u [21/39,31/39]`, total length `20/39`; funnel depth 3, 12 block(s) in 4 rank strata.  Generated by `Z32/gencert.py --closed --ranked 39 8 18 21 31`. -/
def certDub08 : Cert where
  D := 1053
  closed := true
  U := [(216, 486), (567, 837)]
  levels := [
    [(216, 324), (378, 486), (567, 675), (729, 837)],
    [(216, 216), (252, 324), (378, 450), (486, 486), (567, 567), (603, 675), (729, 801), (837, 837)],
    [(216, 216), (252, 300), (324, 324), (378, 378), (402, 450), (486, 486), (567, 567), (603, 651), (675, 675), (729, 729), (753, 801), (837, 837)]]
  strata := [
    [(324, 324), (486, 486), (567, 567), (729, 729)],
    [(216, 216), (378, 378), (675, 675), (837, 837)],
    [(402, 450), (603, 651)],
    [(252, 300), (753, 801)]]

theorem certDub08_ok : certDub08.ok = true := by decide
/-- Certificate for `[4/24,13/24)`, total length `3/8`; funnel depth 8, 3 block(s).  Generated by `Z32/gencert.py 24 4 13`. -/
def certWindow38 : Cert where
  D := 157464
  U := [(26244, 85293)]
  levels := [
    [(26244, 56862), (69984, 85293)],
    [(26244, 37908), (46656, 56862), (69984, 85293)],
    [(31104, 37908), (46656, 56862), (69984, 77760), (83592, 85293)],
    [(31104, 37908), (46656, 51840), (55728, 56862), (73224, 77760), (83592, 85293)],
    [(31104, 34560), (37152, 37908), (48816, 51840), (55728, 56862), (73224, 77760), (83592, 85293)],
    [(32544, 34560), (37152, 37908), (48816, 51840), (55728, 56862), (73224, 75528), (77256, 77760), (85032, 85293)],
    [(32544, 34560), (37152, 37908), (48816, 50352), (51504, 51840), (56688, 56862), (74184, 75528), (77256, 77760), (85032, 85293)],
    [(32544, 37908), (49456, 56862), (74184, 85293)]]

theorem certWindow38_ok : certWindow38.ok = true := by decide
/-- Certificate for `[0/12,2/12) u [3/12,4/12) u [5/12,8/12) u [9/12,10/12)`, total length `7/12`; funnel depth 7, 1 block(s).  Generated by `Z32/gencert.py 12 0 2 3 4 5 8 9 10`. -/
def certUnion712 : Cert where
  D := 26244
  U := [(0, 4374), (6561, 8748), (10935, 17496), (19683, 21870)]
  levels := [
    [(0, 2916), (7290, 8748), (10935, 11664), (13122, 14580), (16038, 17496), (19683, 20412)],
    [(0, 2916), (7290, 7776), (10935, 11664), (13122, 14580), (16038, 16524), (19683, 20412)],
    [(0, 2268), (7290, 7776), (10935, 11016), (13122, 13932), (16038, 16524), (19683, 19764)],
    [(0, 1512), (1944, 2268), (7290, 7344), (10935, 11016), (13122, 13176), (13608, 13932), (16038, 16092), (19683, 19764)],
    [(0, 1008), (1296, 1512), (1944, 1980), (7290, 7344), (13122, 13176), (13608, 13644), (16038, 16092)],
    [(0, 672), (864, 1008), (1296, 1320), (1944, 1980), (13608, 13644)],
    [(0, 1320)]]

theorem certUnion712_ok : certUnion712.ok = true := by decide
/-- Certificate for `[0/18,2/18) u [3/18,8/18) u [9/18,10/18) u [11/18,14/18) u [15/18,16/18)`, total length `2/3`; funnel depth 9, 12 block(s).  Generated by `Z32/gencert.py 18 0 2 3 8 9 10 11 14 15 16`. -/
def certUnion23 : Cert where
  D := 354294
  U := [(0, 39366), (59049, 157464), (177147, 196830), (216513, 275562), (295245, 314928)]
  levels := [
    [(0, 39366), (59049, 104976), (118098, 157464), (177147, 196830), (216513, 223074), (236196, 275562), (295245, 314928)],
    [(0, 30618), (59049, 69984), (78732, 104976), (118098, 148716), (177147, 188082), (216513, 223074), (236196, 266814), (295245, 306180)],
    [(0, 20412), (26244, 30618), (59049, 69984), (78732, 99144), (118098, 138510), (144342, 148716), (177147, 188082), (216513, 217242), (236196, 256608), (262440, 266814), (295245, 306180)],
    [(0, 13608), (17496, 20412), (26244, 26730), (59049, 66096), (78732, 92340), (96228, 99144), (118098, 131706), (135594, 138510), (144342, 144828), (177147, 184194), (216513, 217242), (236196, 249804), (253692, 256608), (262440, 262926), (295245, 302292)],
    [(0, 9072), (11664, 13608), (17496, 17820), (26244, 26730), (59049, 61560), (64152, 66096), (78732, 87804), (90396, 92340), (96228, 96552), (118098, 127170), (129762, 131706), (135594, 135918), (144342, 144828), (177147, 179658), (182250, 184194), (236196, 245268), (247860, 249804), (253692, 254016), (262440, 262926), (295245, 297756), (300348, 302292)],
    [(0, 6048), (7776, 9072), (11664, 11880), (17496, 17820), (60264, 61560), (64152, 64368), (78732, 84780), (86508, 87804), (90396, 90612), (96228, 96552), (118098, 124146), (125874, 127170), (129762, 129978), (135594, 135918), (178362, 179658), (182250, 182466), (236196, 242244), (243972, 245268), (247860, 248076), (253692, 254016), (296460, 297756), (300348, 300564)],
    [(0, 4032), (5184, 6048), (7776, 7920), (11664, 11880), (60264, 60408), (64152, 64368), (78732, 82764), (83916, 84780), (86508, 86652), (90396, 90612), (118098, 122130), (123282, 124146), (125874, 126018), (129762, 129978), (178362, 178506), (182250, 182466), (236196, 240228), (241380, 242244), (243972, 244116), (247860, 248076), (296460, 296604), (300348, 300564)],
    [(0, 2688), (3402, 4032), (5184, 5280), (7776, 7920), (60264, 60408), (78732, 81420), (82134, 82764), (83916, 84012), (86508, 86652), (118098, 120786), (121500, 122130), (123282, 123378), (125874, 126018), (178362, 178506), (236196, 238884), (239598, 240228), (241380, 241476), (243972, 244116), (296460, 296604)],
    [(0, 5280), (78732, 80524), (81000, 81420), (82188, 82252), (83916, 84012), (118098, 120786), (121554, 121618), (123282, 123378), (236196, 237988), (238464, 238884), (239652, 239716), (241380, 241476)]]

theorem certUnion23_ok : certUnion23.ok = true := by decide

/-- Certificate for `[961/3600,2427/3600)`, total length `733/1800`; funnel depth 13, 2 block(s).  Generated by `Z32/gencert.py 3600 961 2427`. -/
def certFrontier : Cert where
  D := 5739562800
  U := [(1532144403, 3869421921)]
  levels := [
    [(1532144403, 2579614614), (2934617202, 3869421921)],
    [(1532144403, 1719743076), (1956411468, 2579614614), (2934617202, 3632930676)],
    [(1532144403, 1719743076), (1956411468, 2421953784), (2934617202, 3059682984), (3217461912, 3632930676)],
    [(1532144403, 1614635856), (1956411468, 2039788656), (2144974608, 2421953784), (2934617202, 3059682984), (3217461912, 3527823456)],
    [(1532144403, 1614635856), (1956411468, 2039788656), (2144974608, 2351882304), (2934617202, 2989611504), (3217461912, 3273046704), (3343170672, 3527823456)],
    [(1532144403, 1567921536), (1956411468, 1993074336), (2144974608, 2182031136), (2228780448, 2351882304), (2934617202, 2989611504), (3217461912, 3273046704), (3343170672, 3481109136)],
    [(1532144403, 1567921536), (1956411468, 1993074336), (2144974608, 2182031136), (2228780448, 2320739424), (2934617202, 2958468624), (3217461912, 3241903824), (3343170672, 3367875024), (3399041232, 3481109136)],
    [(1532144403, 1547159616), (1956411468, 1972312416), (2144974608, 2161269216), (2228780448, 2245250016), (2266027488, 2320739424), (2934617202, 2958468624), (3217461912, 3241903824), (3343170672, 3367875024), (3399041232, 3460347216)],
    [(1532144403, 1547159616), (1956411468, 1972312416), (2144974608, 2161269216), (2228780448, 2245250016), (2266027488, 2306898144), (2934617202, 2944627344), (3217461912, 3228062544), (3343170672, 3354033744), (3399041232, 3410020944), (3423872592, 3460347216)],
    [(1532144403, 1537932096), (1956411468, 1963084896), (2144974608, 2152041696), (2228780448, 2236022496), (2266027488, 2273347296), (2282581728, 2306898144), (2934617202, 2944627344), (3217461912, 3228062544), (3343170672, 3354033744), (3399041232, 3410020944), (3423872592, 3451119696)],
    [(1532144403, 1537932096), (1956411468, 1963084896), (2144974608, 2152041696), (2228780448, 2236022496), (2266027488, 2273347296), (2282581728, 2300746464), (2934617202, 2938475664), (3217461912, 3221910864), (3343170672, 3347882064), (3399041232, 3403869264), (3423872592, 3428752464), (3434908752, 3451119696)],
    [(1532144403, 1533830976), (1956411468, 1958983776), (2144974608, 2147940576), (2228780448, 2231921376), (2266027488, 2269246176), (2282581728, 2285834976), (2289939168, 2300746464), (2934617202, 2938475664), (3217461912, 3221910864), (3343170672, 3347882064), (3399041232, 3403869264), (3423872592, 3428752464), (3434908752, 3447018576)],
    [(1532144403, 2298012384), (2934617202, 3447018576)]]

theorem certFrontier_ok : certFrontier.ok = true := by decide

/-- Certificate for `[0/36,3/36) u [4/36,11/36) u [16/36,24/36) u [25/36,27/36) u [30/36,32/36) u [33/36,36/36)`, total length `25/36`; funnel depth 11, 17 block(s).  Generated by `Z32/gencert.py 36 0 3 4 11 16 24 25 27 30 32 33 36`. -/
def certUnion2536 : Cert where
  D := 6377292
  U := [(0, 531441), (708588, 1948617), (2834352, 4251528), (4428675, 4782969), (5314410, 5668704), (5845851, 6377292)]
  levels := [
    [(0, 531441), (708588, 1299078), (1417176, 1653372), (1771470, 1948617), (2834352, 3424842), (3542940, 3779136), (3897234, 4251528), (4428675, 4782969), (5314410, 5550606), (5845851, 5904900), (6022998, 6377292)],
    [(0, 393660), (472392, 531441), (708588, 1102248), (1180980, 1299078), (1417176, 1574640), (1771470, 1810836), (1889568, 1948617), (2834352, 3228012), (3306744, 3424842), (3542940, 3700404), (3897234, 3936600), (4015332, 4251528), (4428675, 4645188), (4723920, 4782969), (5314410, 5353776), (5432508, 5550606), (6022998, 6062364), (6141096, 6377292)],
    [(0, 354294), (472392, 531441), (708588, 734832), (787320, 1062882), (1180980, 1207224), (1259712, 1299078), (1417176, 1443420), (1495908, 1574640), (1889568, 1948617), (2834352, 2860596), (2913084, 3188646), (3306744, 3332988), (3385476, 3424842), (3542940, 3569184), (3621672, 3700404), (4015332, 4251528), (4428675, 4605822), (4723920, 4782969), (5432508, 5458752), (5511240, 5550606), (6141096, 6377292)],
    [(0, 253692), (288684, 354294), (472392, 489888), (524880, 531441), (787320, 804816), (826686, 962280), (997272, 1062882), (1259712, 1299078), (1495908, 1513404), (1548396, 1574640), (1889568, 1907064), (1942056, 1948617), (2913084, 2930580), (2952450, 3088044), (3123036, 3188646), (3385476, 3424842), (3621672, 3639168), (3674160, 3700404), (4015332, 4032828), (4067820, 4251528), (4428675, 4505220), (4540212, 4605822), (4723920, 4741416), (4776408, 4782969), (5511240, 5550606), (6141096, 6158592), (6193584, 6377292)],
    [(0, 169128), (192456, 236196), (288684, 300348), (314928, 341172), (349920, 354294), (524880, 531441), (826686, 877716), (901044, 944784), (997272, 1008936), (1023516, 1049760), (1058508, 1062882), (1259712, 1271376), (1294704, 1299078), (1548396, 1574640), (1942056, 1948617), (2952450, 3003480), (3026808, 3070548), (3123036, 3134700), (3149280, 3175524), (3184272, 3188646), (3385476, 3397140), (3420468, 3424842), (3674160, 3700404), (4067820, 4079484), (4094064, 4251528), (4443984, 4487724), (4540212, 4551876), (4566456, 4592700), (4601448, 4605822), (4776408, 4782969), (5511240, 5522904), (5546232, 5550606), (6193584, 6205248), (6219828, 6377292)],
    [(0, 112752), (128304, 157464), (192456, 200232), (209952, 227448), (233280, 236196), (323676, 341172), (349920, 354294), (836892, 866052), (901044, 908820), (918540, 936036), (941868, 944784), (1032264, 1049760), (1058508, 1062882), (1294704, 1299078), (1548396, 1556172), (1571724, 1574640), (2962656, 2991816), (3026808, 3034584), (3044304, 3061800), (3067632, 3070548), (3158028, 3175524), (3184272, 3188646), (3420468, 3424842), (3674160, 3681936), (3697488, 3700404), (4094064, 4128084), (4129056, 4136832), (4143636, 4251528), (4443984, 4451760), (4461480, 4478976), (4484808, 4487724), (4575204, 4592700), (4601448, 4605822), (5546232, 5550606), (6219828, 6253848), (6254820, 6262596), (6269400, 6377292)],
    [(0, 75168), (85536, 104976), (128304, 133488), (139968, 151632), (154548, 157464), (215784, 227448), (233280, 236196), (323676, 328860), (339228, 341172), (836892, 842076), (848556, 860220), (863136, 866052), (924372, 936036), (941868, 944784), (1032264, 1037448), (1047816, 1049760), (1571724, 1574640), (2962656, 2967840), (2974320, 2985984), (2988900, 2991816), (3050136, 3061800), (3067632, 3070548), (3158028, 3163212), (3173580, 3175524), (3697488, 3700404), (4100868, 4120308), (4143636, 4169232), (4169880, 4175064), (4179600, 4251528), (4467312, 4478976), (4484808, 4487724), (4575204, 4580388), (4590756, 4592700), (6226632, 6246072), (6269400, 6294996), (6295644, 6300828), (6305364, 6377292)],
    [(0, 50112), (57024, 69984), (85536, 88992), (93312, 101088), (103032, 104976), (143856, 151632), (155520, 157464), (215784, 219240), (226152, 227448), (339228, 341172), (852444, 860220), (864108, 866052), (924372, 927828), (934740, 936036), (1047816, 1049760), (2978208, 2985984), (2989872, 2991816), (3050136, 3053592), (3060504, 3061800), (3173580, 3175524), (4100868, 4104324), (4108644, 4116420), (4118364, 4120308), (4151088, 4166964), (4170852, 4172796), (4179600, 4196664), (4197096, 4200552), (4203576, 4251528), (4467312, 4470768), (4477680, 4478976), (4590756, 4592700), (6226632, 6230088), (6234408, 6242184), (6244128, 6246072), (6276852, 6292728), (6296616, 6298560), (6305364, 6322428), (6322860, 6326316), (6329340, 6377292)],
    [(0, 33408), (38016, 46656), (57024, 59328), (62208, 67392), (68688, 69984), (95904, 101088), (103680, 104976), (143856, 146160), (150768, 151632), (226152, 227448), (852444, 854748), (859356, 860220), (934740, 936036), (2978208, 2980512), (2985120, 2985984), (3060504, 3061800), (4111236, 4116420), (4119012, 4120308), (4151088, 4153392), (4156272, 4161492), (4162752, 4164048), (4166100, 4166964), (4184568, 4195152), (4197744, 4199040), (4203576, 4214952), (4215240, 4217544), (4219560, 4251528), (4477680, 4478976), (6237000, 6242184), (6244776, 6246072), (6276852, 6279156), (6282036, 6287256), (6288516, 6289812), (6291864, 6292728), (6310332, 6320916), (6323508, 6324804), (6329340, 6340716), (6341004, 6343308), (6345324, 6377292)],
    [(0, 22272), (25344, 31104), (38016, 39552), (41472, 44928), (45792, 46656), (63936, 67392), (69120, 69984), (95904, 97440), (100512, 101088), (150768, 151632), (859356, 860220), (2985120, 2985984), (4111236, 4112772), (4115844, 4116420), (4158000, 4161456), (4163184, 4164048), (4166100, 4166964), (4184568, 4186104), (4188024, 4191504), (4192344, 4193208), (4194576, 4195152), (4206888, 4213944), (4215672, 4216536), (4219560, 4227144), (4227336, 4228872), (4230216, 4251528), (6237000, 6238536), (6241608, 6242184), (6283764, 6287220), (6288948, 6289812), (6291864, 6292728), (6310332, 6311868), (6313788, 6317268), (6318108, 6318972), (6320340, 6320916), (6332652, 6339708), (6341436, 6342300), (6345324, 6352908), (6353100, 6354636), (6355980, 6377292)],
    [(0, 101088), (4115844, 4116420), (4158000, 4159024), (4161072, 4161456), (4189176, 4191480), (4192632, 4193208), (4194576, 4195152), (4206888, 4207912), (4209192, 4211512), (4212072, 4212648), (4213560, 4213944), (4221768, 4226472), (4227624, 4228200), (4230216, 4235272), (4235400, 4236424), (4237320, 4251528), (6241608, 6377292)]]

theorem certUnion2536_ok : certUnion2536.ok = true := by decide

/-! ### The two-cell arc `‖·‖ < 1/5` (the nearest-integer family)

The certified sets above are windows and unions chosen by the search.  This one is a *named*
family: `[0, c) ∪ [1-c, 1)` is `{y : ‖y‖ < c}` up to the single point `1-c`, so a certificate for
it bounds how close to an integer the whole orbit can stay.  [Dub10] proves the case `c = 1/3`
**nonempty**, and [Dub09AA] Theorem 1 reaches only `c ≤ 1/6` (an arc of length `1/p = 1/3`), so
`c = 1/5` sits strictly between what is known possible and what is known impossible.  Closing the
endpoints kills it — `gencert.py --closed` finds no certificate to depth 60 — exactly as with
[Dub08]'s union. -/

/-- Certificate for `[0/5,1/5) u [4/5,5/5)`, total length `2/5`; funnel depth 1, 2 block(s).  Generated by `Z32/gencert.py 5 0 1 4 5`. -/
def certTwoCellFifth : Cert where
  D := 15
  U := [(0, 3), (12, 15)]
  levels := [
    [(0, 2), (13, 15)]]

theorem certTwoCellFifth_ok : certTwoCellFifth.ok = true := by decide

/-! ### A second and a third base (milestone M6)

Nothing above uses `3/2`.  These two entries run the same soundness theorem at other bases: `4/3`,
where the certificate reaches past [Dub09AA]'s length-`1/p` line exactly as it does at `3/2`, and
`5/2`, which lies in the regime `p > q²` that [Dub09AA] §4 leaves open. -/

/-- Certificate for `[8/24,15/24)`, total length `7/24`; funnel depth 5, 2 block(s).  Generated by `Z32/gencert.py --pq 4 3 24 8 15`. -/
def certFourThree : Cert where
  D := 24576
  p := 4
  q := 3
  U := [(8192, 15360)]
  levels := [
    [(8192, 11520), (12288, 15360)],
    [(8192, 8640), (9216, 11520), (12288, 14784)],
    [(8192, 8640), (9216, 11088), (12288, 12624), (13056, 14784)],
    [(8192, 8316), (9216, 9468), (9792, 11088), (12288, 12624), (13056, 14460)],
    [(8192, 10845), (12288, 14460)]]

theorem certFourThree_ok : certFourThree.ok = true := by decide

/-- Certificate for `[1/5,2/5)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 5 1 2`. -/
def certFiveTwo : Cert where
  D := 25
  p := 5
  q := 2
  U := [(5, 10)]
  levels := [
    [(7, 9)]]

theorem certFiveTwo_ok : certFiveTwo.ok = true := by decide


/-! ### The `p > q²` table (thirty windows in the regime [Dub09AA] §4 leaves open)

`certFiveTwo` above is one window in this regime.  These thirty are the rest of the measured
column: at each of the five bases `(5,2)`, `(7,2)`, `(9,2)`, `(10,3)`, `(11,3)`, the window
`[i/6, i/6 + 1/p)` for `i = 0, …, 5`.  Every one certifies at funnel depth **1** — the regime is
not hard for this method, it is only out of reach of [Dub09AA]'s counting endgame, which needs
`p < q²`.  What they are *not* is the open theorem: that quantifies over all real `s`, and the
cover route to it fails (see `Z32.ZSet_five_two_fifth`). -/

/-- Certificate for `[0/30,6/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 0 6`. -/
def certGridFiveTwo0 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(0, 30)]
  levels := [
    [(0, 12)]]

theorem certGridFiveTwo0_ok : certGridFiveTwo0.ok = true := by decide

/-- Certificate for `[5/30,11/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 5 11`. -/
def certGridFiveTwo1 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(25, 55)]
  levels := [
    [(40, 52)]]

theorem certGridFiveTwo1_ok : certGridFiveTwo1.ok = true := by decide

/-- Certificate for `[10/30,16/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 10 16`. -/
def certGridFiveTwo2 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(50, 80)]
  levels := [
    [(50, 62)]]

theorem certGridFiveTwo2_ok : certGridFiveTwo2.ok = true := by decide

/-- Certificate for `[15/30,21/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 15 21`. -/
def certGridFiveTwo3 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(75, 105)]
  levels := [
    [(90, 102)]]

theorem certGridFiveTwo3_ok : certGridFiveTwo3.ok = true := by decide

/-- Certificate for `[20/30,26/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 20 26`. -/
def certGridFiveTwo4 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(100, 130)]
  levels := [
    [(100, 112)]]

theorem certGridFiveTwo4_ok : certGridFiveTwo4.ok = true := by decide

/-- Certificate for `[25/30,31/30)`, total length `1/5`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 5 2 30 25 31`. -/
def certGridFiveTwo5 : Cert where
  D := 150
  p := 5
  q := 2
  U := [(125, 155)]
  levels := [
    [(140, 152)]]

theorem certGridFiveTwo5_ok : certGridFiveTwo5.ok = true := by decide

/-- Certificate for `[0/42,6/42)`, total length `1/7`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 0 6`. -/
def certGridSevenTwo0 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(0, 42)]
  levels := [
    [(0, 12)]]

theorem certGridSevenTwo0_ok : certGridSevenTwo0.ok = true := by decide

/-- Certificate for `[7/42,13/42)`, total length `1/7`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 7 13`. -/
def certGridSevenTwo1 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(49, 91)]
  levels := [
    [(56, 68)]]

theorem certGridSevenTwo1_ok : certGridSevenTwo1.ok = true := by decide

/-- Certificate for `[14/42,20/42)`, total length `1/7`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 14 20`. -/
def certGridSevenTwo2 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(98, 140)]
  levels := [
    [(112, 124)]]

theorem certGridSevenTwo2_ok : certGridSevenTwo2.ok = true := by decide

/-- Certificate for `[21/42,27/42)`, total length `1/7`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 21 27`. -/
def certGridSevenTwo3 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(147, 189)]
  levels := [
    [(168, 180)]]

theorem certGridSevenTwo3_ok : certGridSevenTwo3.ok = true := by decide

/-- Certificate for `[28/42,34/42)`, total length `1/7`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 28 34`. -/
def certGridSevenTwo4 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(196, 238)]
  levels := [
    [(224, 236)]]

theorem certGridSevenTwo4_ok : certGridSevenTwo4.ok = true := by decide

/-- Certificate for `[35/42,41/42)`, total length `1/7`; funnel depth 1, 2 block(s).  Generated by `Z32/gencert.py --pq 7 2 42 35 41`. -/
def certGridSevenTwo5 : Cert where
  D := 294
  p := 7
  q := 2
  U := [(245, 287)]
  levels := [
    [(245, 250), (280, 287)]]

theorem certGridSevenTwo5_ok : certGridSevenTwo5.ok = true := by decide

/-- Certificate for `[0/18,2/18)`, total length `1/9`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 0 2`. -/
def certGridNineTwo0 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(0, 18)]
  levels := [
    [(0, 4)]]

theorem certGridNineTwo0_ok : certGridNineTwo0.ok = true := by decide

/-- Certificate for `[3/18,5/18)`, total length `1/9`; funnel depth 1, 2 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 3 5`. -/
def certGridNineTwo1 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(27, 45)]
  levels := [
    [(27, 28), (42, 45)]]

theorem certGridNineTwo1_ok : certGridNineTwo1.ok = true := by decide

/-- Certificate for `[6/18,8/18)`, total length `1/9`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 6 8`. -/
def certGridNineTwo2 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(54, 72)]
  levels := [
    [(66, 70)]]

theorem certGridNineTwo2_ok : certGridNineTwo2.ok = true := by decide

/-- Certificate for `[9/18,11/18)`, total length `1/9`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 9 11`. -/
def certGridNineTwo3 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(81, 99)]
  levels := [
    [(90, 94)]]

theorem certGridNineTwo3_ok : certGridNineTwo3.ok = true := by decide

/-- Certificate for `[12/18,14/18)`, total length `1/9`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 12 14`. -/
def certGridNineTwo4 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(108, 126)]
  levels := [
    [(114, 118)]]

theorem certGridNineTwo4_ok : certGridNineTwo4.ok = true := by decide

/-- Certificate for `[15/18,17/18)`, total length `1/9`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 9 2 18 15 17`. -/
def certGridNineTwo5 : Cert where
  D := 162
  p := 9
  q := 2
  U := [(135, 153)]
  levels := [
    [(138, 142)]]

theorem certGridNineTwo5_ok : certGridNineTwo5.ok = true := by decide

/-- Certificate for `[0/30,3/30)`, total length `1/10`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 0 3`. -/
def certGridTenThree0 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(0, 30)]
  levels := [
    [(0, 9)]]

theorem certGridTenThree0_ok : certGridTenThree0.ok = true := by decide

/-- Certificate for `[5/30,8/30)`, total length `1/10`; funnel depth 1, 2 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 5 8`. -/
def certGridTenThree1 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(50, 80)]
  levels := [
    [(50, 54), (75, 80)]]

theorem certGridTenThree1_ok : certGridTenThree1.ok = true := by decide

/-- Certificate for `[10/30,13/30)`, total length `1/10`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 10 13`. -/
def certGridTenThree2 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(100, 130)]
  levels := [
    [(120, 129)]]

theorem certGridTenThree2_ok : certGridTenThree2.ok = true := by decide

/-- Certificate for `[15/30,18/30)`, total length `1/10`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 15 18`. -/
def certGridTenThree3 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(150, 180)]
  levels := [
    [(165, 174)]]

theorem certGridTenThree3_ok : certGridTenThree3.ok = true := by decide

/-- Certificate for `[20/30,23/30)`, total length `1/10`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 20 23`. -/
def certGridTenThree4 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(200, 230)]
  levels := [
    [(210, 219)]]

theorem certGridTenThree4_ok : certGridTenThree4.ok = true := by decide

/-- Certificate for `[25/30,28/30)`, total length `1/10`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 10 3 30 25 28`. -/
def certGridTenThree5 : Cert where
  D := 300
  p := 10
  q := 3
  U := [(250, 280)]
  levels := [
    [(255, 264)]]

theorem certGridTenThree5_ok : certGridTenThree5.ok = true := by decide

/-- Certificate for `[0/66,6/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 0 6`. -/
def certGridElevenThree0 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(0, 66)]
  levels := [
    [(0, 18)]]

theorem certGridElevenThree0_ok : certGridElevenThree0.ok = true := by decide

/-- Certificate for `[11/66,17/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 11 17`. -/
def certGridElevenThree1 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(121, 187)]
  levels := [
    [(165, 183)]]

theorem certGridElevenThree1_ok : certGridElevenThree1.ok = true := by decide

/-- Certificate for `[22/66,28/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 22 28`. -/
def certGridElevenThree2 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(242, 308)]
  levels := [
    [(264, 282)]]

theorem certGridElevenThree2_ok : certGridElevenThree2.ok = true := by decide

/-- Certificate for `[33/66,39/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 33 39`. -/
def certGridElevenThree3 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(363, 429)]
  levels := [
    [(363, 381)]]

theorem certGridElevenThree3_ok : certGridElevenThree3.ok = true := by decide

/-- Certificate for `[44/66,50/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 44 50`. -/
def certGridElevenThree4 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(484, 550)]
  levels := [
    [(528, 546)]]

theorem certGridElevenThree4_ok : certGridElevenThree4.ok = true := by decide

/-- Certificate for `[55/66,61/66)`, total length `1/11`; funnel depth 1, 1 block(s).  Generated by `Z32/gencert.py --pq 11 3 66 55 61`. -/
def certGridElevenThree5 : Cert where
  D := 726
  p := 11
  q := 3
  U := [(605, 671)]
  levels := [
    [(627, 645)]]

theorem certGridElevenThree5_ok : certGridElevenThree5.ok = true := by decide

/-- **The base is guarded, and not as a formality.**  Coprimality is a hypothesis of the
aperiodicity lemma this file contradicts, and it is *needed*: at `p/q = 4/2 = 2` the point `ξ = 1/3`
has the genuinely periodic orbit `1/3 → 2/3 → 1/3`, with periodic carry word `0, 2, 0, 2, …`, so a
certificate at such a base would prove a falsehood.  `ok` refuses it. -/
theorem ok_eq_false_of_not_coprime {c : Cert} (h : Nat.gcd c.p c.q ≠ 1) : c.ok = false := by
  simp [Cert.ok, h]

/-- **The check has teeth.**  The whole interval `[0,1)` passes the funnel condition trivially —
it traps every orbit — but its single block has all four carries outgoing, so `funcOk` rejects it.
Guards against a `Cert.ok` that is accidentally true of everything. -/
theorem ok_eq_false_of_full :
    ({ D := 1, U := [(0, 1)], levels := [[(0, 1)]] } : Cert).ok = false := by decide

/-- **The two new fields have teeth as well.**  Neither closing the intervals nor handing the
block a rank of its own rescues `[0,1]`: a self-loop is an edge of *equal* rank, and the single
block has four of them. -/
theorem ok_eq_false_of_full_closed :
    ({ D := 1, closed := true, U := [(0, 1)], levels := [[(0, 1)]],
       strata := [[(0, 1)]] } : Cert).ok = false := by decide


end Z32.BlockCert

/-! ## The certified atlas entries

Restated in the corpus' own vocabulary.  Each of these is `decide`-checked end to end: the only
axioms are `propext`, `Classical.choice`, `Quot.sound` (see `Z32/README.md`, trust ledger). -/

namespace Z32

open BlockCert

/-- **First entry beyond the [FLP95] line.**  `Z_{3/2}(1/6, 13/24) = ∅`: no `ξ > 0` has every
`{ξ(3/2)ⁿ}` in `[1/6, 13/24)`, a window of length `3/8 = 0.375 > 1/3`.

[FLP95] Corollary 1.4a certifies emptiness only at length `1/p = 1/3`, and [Dub09AA] Theorem 1
covers every position but again only at length `1/3`; the block certificate goes past both.  Found
by the M2 sweep (plan §4.4, experiment X2), checked here by the kernel. -/
theorem ZSet_three_two_sixth_3_8 : FLP.ZSet 3 2 (1 / 6 : ℝ) (3 / 8) = ∅ := by
  refine ZSet_eq_empty_of_cert_base certWindow38_ok rfl rfl fun y h1 h2 => ?_
  refine ⟨(26244, 85293), by simp [certWindow38], ?_, ?_⟩ <;>
    simp only [certWindow38, rleR] <;> push_cast <;> linarith

/-- **The engine frontier.**  `Z_{3/2}(961/3600, 2427/3600) = ∅`, a window of length
`1466/3600 = 0.40722…` — the longest single window certified by the M2 sweep (plan §4.4, X2:
nothing at all is certified at any position once the length exceeds `1467/3600`). -/
theorem ZSet_three_two_frontier : FLP.ZSet 3 2 (961 / 3600 : ℝ) (1466 / 3600) = ∅ := by
  refine ZSet_eq_empty_of_cert_base certFrontier_ok rfl rfl fun y h1 h2 => ?_
  refine ⟨(1532144403, 3869421921), by simp [certFrontier], ?_, ?_⟩ <;>
    simp only [certFrontier, rleR] <;> push_cast <;> linarith

/-- **Eventual confinement is impossible too**, at the flagship window: the shift trick turns an
eventually confined orbit into a genuine `Z`-number.  Stated for every `ξ ≠ 0`, not just `ξ > 0` —
the block certificate never uses the sign. -/
theorem not_eventually_mem_sixth_3_8 {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n, N ≤ n → Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Ico (1 / 6 : ℝ) (13 / 24) := by
  have h : (13 / 24 : ℝ) = 1 / 6 + 3 / 8 := by norm_num
  rw [h]
  refine not_eventually_mem_Ico_of_cert_base certWindow38_ok (3 / 2)
    (by norm_num [certWindow38]) (fun y h1 h2 => ?_) hξ
  refine ⟨(26244, 85293), by simp [certWindow38], ?_, ?_⟩ <;>
    simp only [certWindow38, rleR] <;> push_cast <;> linarith

/-- **[Dub08] Corollary 1.2, as printed.**  No `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` inside the **closed**
set `[8/39, 18/39] ∪ [21/39, 31/39]`, of total length `20/39 = 0.5128…` — the strongest *explicit*
union-emptiness statement in the literature surveyed at plan milestone M0.  Stated for every
`ξ ≠ 0`, not just `ξ > 0`.

The closed form is genuinely stronger than its half-open shadow, and not by a notational margin:
the closed set contains the 4-cycle `6/13 → 9/13 → 7/13 → 4/13 → 6/13` of the interval map, which
runs through the right endpoint `18/39 = 6/13` and is invisible to `Ico`.  That cycle is exactly
what the certificate's rank-`0` stratum is: the funnel needs depth 3 rather than 1, the blocks are
the twelve raw components rather than four merged hulls, and they stratify into

* rank `0` — the 4-cycle `{4/13, 6/13, 7/13, 9/13}`, one outgoing edge each;
* rank `2` — the two fat blocks holding the 2-cycle `{2/5, 3/5}`, which also escape downward;
* ranks `1`, `3` — transients.

A block graph that is a partial function outright, as in the other five entries here, cannot
express that; `Z32.BlockCert.funcOk`'s rank condition can. -/
theorem dubickas_2008_cor_1_2 {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (8 / 39 : ℝ) (18 / 39) ∪ Set.Icc (21 / 39 : ℝ) (31 / 39) := by
  intro h
  refine not_confined_base certDub08_ok (3 / 2) (by norm_num [certDub08]) hξ fun n => ?_
  rcases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(216, 486), by simp [certDub08], ?_, ?_⟩ <;>
      simp only [certDub08, rleR] <;> push_cast <;> linarith
  · refine ⟨(567, 837), by simp [certDub08], ?_, ?_⟩ <;>
      simp only [certDub08, rleR] <;> push_cast <;> linarith

/-- **A certified-empty union of total length `7/12`**, past [Dub08]'s `20/39`. -/
theorem union_seven_twelfths_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 6) ∪ Set.Ico (1 / 4 : ℝ) (1 / 3) ∪ Set.Ico (5 / 12 : ℝ) (2 / 3) ∪
        Set.Ico (3 / 4 : ℝ) (5 / 6) := by
  intro h
  refine not_confined_base certUnion712_ok (3 / 2) (by norm_num [certUnion712]) hξ fun n => ?_
  rcases h n with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · refine ⟨(0, 4374), by simp [certUnion712], ?_, ?_⟩ <;>
      simp only [certUnion712, rleR] <;> push_cast <;> linarith
  · refine ⟨(6561, 8748), by simp [certUnion712], ?_, ?_⟩ <;>
      simp only [certUnion712, rleR] <;> push_cast <;> linarith
  · refine ⟨(10935, 17496), by simp [certUnion712], ?_, ?_⟩ <;>
      simp only [certUnion712, rleR] <;> push_cast <;> linarith
  · refine ⟨(19683, 21870), by simp [certUnion712], ?_, ?_⟩ <;>
      simp only [certUnion712, rleR] <;> push_cast <;> linarith

/-- **A certified-empty union of total length `2/3`.**  Worth pairing with [KK18] Corollary 4.8,
which exhibits a *nonempty* union of the **same** total length `2/3` (`[0,1/6) ∪ [1/3,2/3) ∪
[5/6,1)`): total length alone decides nothing, which is why the atlas of plan §4.4 is a table and
not an inequality. -/
theorem union_two_thirds_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 9) ∪ Set.Ico (1 / 6 : ℝ) (4 / 9) ∪ Set.Ico (1 / 2 : ℝ) (5 / 9) ∪
        Set.Ico (11 / 18 : ℝ) (7 / 9) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) := by
  intro h
  refine not_confined_base certUnion23_ok (3 / 2) (by norm_num [certUnion23]) hξ fun n => ?_
  rcases h n with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · refine ⟨(0, 39366), by simp [certUnion23], ?_, ?_⟩ <;>
      simp only [certUnion23, rleR] <;> push_cast <;> linarith
  · refine ⟨(59049, 157464), by simp [certUnion23], ?_, ?_⟩ <;>
      simp only [certUnion23, rleR] <;> push_cast <;> linarith
  · refine ⟨(177147, 196830), by simp [certUnion23], ?_, ?_⟩ <;>
      simp only [certUnion23, rleR] <;> push_cast <;> linarith
  · refine ⟨(216513, 275562), by simp [certUnion23], ?_, ?_⟩ <;>
      simp only [certUnion23, rleR] <;> push_cast <;> linarith
  · refine ⟨(295245, 314928), by simp [certUnion23], ?_, ?_⟩ <;>
      simp only [certUnion23, rleR] <;> push_cast <;> linarith

/-- **The formalized union-largeness record: total length `25/36 = 0.6944…`.**  The M2 engine
climbs further under refinement (`0.7417` at 240 cells, plan §4.4 X3), but the funnel of that
certificate is too wide to hand to `decide`; `25/36` is what the kernel checks today, against
[Dub08] Corollary 1.2's `20/39 = 0.5128…` in print.

A record *on the curve* of [KK18] Problem 6.1 — not a solution of it. -/
theorem union_record_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 12) ∪ Set.Ico (1 / 9 : ℝ) (11 / 36) ∪ Set.Ico (4 / 9 : ℝ) (2 / 3) ∪
        Set.Ico (25 / 36 : ℝ) (3 / 4) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) ∪ Set.Ico (11 / 12 : ℝ) 1 := by
  intro h
  refine not_confined_base certUnion2536_ok (3 / 2) (by norm_num [certUnion2536]) hξ fun n => ?_
  rcases h n with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
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
      simp only [certUnion2536, rleR] <;> push_cast <;> linarith


/-- **The nearest-integer family, at `c = 1/5`.**  No `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` inside
`[0, 1/5) ∪ [4/5, 1)`, a union of total length `2/5`.

The interest is not its length — `Z32.union_record_empty` certifies `25/36` — but its *shape*: the
set is `{y : ‖y‖ < 1/5}` together with the single point `4/5`, so the statement bounds how close to
an integer a whole orbit can stay.  Against it, [Dub10] exhibits `ξ` with `‖ξ(3/2)ⁿ‖ < 1/3` for
every `n`, and [Dub09AA] Theorem 1 covers arcs of length `1/p = 1/3`, i.e. `‖·‖ ≤ 1/6` only.  The
engine puts the frontier of this family between `1/5` and `0.21`: at `21/100` no certificate exists
to depth 60. -/
theorem two_cell_fifth_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1 := by
  intro h
  refine not_confined_base certTwoCellFifth_ok (3 / 2) (by norm_num [certTwoCellFifth]) hξ
    fun n => ?_
  rcases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(0, 3), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
      simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith
  · refine ⟨(12, 15), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
      simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith

/-- **The eventual form** of `Z32.two_cell_fifth_empty`: no `ξ ≠ 0` has its orbit inside
`[0, 1/5) ∪ [4/5, 1)` from any index on, so the orbit leaves that union infinitely often. -/
theorem not_eventually_two_cell_fifth {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1 := by
  intro h
  refine Cert.not_eventually_confined certTwoCellFifth_ok hξ (N := N) fun n hn => ?_
  have hb : ((certTwoCellFifth.p : ℝ) / certTwoCellFifth.q) = 3 / 2 := by
    norm_num [certTwoCellFifth]
  rw [hb]
  rcases h n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(0, 3), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
      simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith
  · refine ⟨(12, 15), by simp [certTwoCellFifth], ?_, ?_⟩ <;>
      simp only [certTwoCellFifth, rleR] <;> push_cast <;> linarith

/-- **The distance to the nearest integer exceeds `1/5` infinitely often**, for every `ξ ≠ 0`:
there is no `ξ ≠ 0` with `‖ξ(3/2)ⁿ‖ < 1/5` for all `n`.  This is `Z32.two_cell_fifth_empty` in the
nearest-integer coordinate, `‖x‖ = |x - round x|`. -/
theorem not_forall_abs_sub_round_lt_fifth {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → |ξ * ((3 : ℝ) / 2) ^ n - round (ξ * ((3 : ℝ) / 2) ^ n)| < 1 / 5 := by
  intro h
  refine not_eventually_two_cell_fifth hξ (N := N) fun n hnN => ?_
  have hn := h n hnN
  rw [abs_sub_round_eq_min, min_lt_iff] at hn
  have h0 := Int.fract_nonneg (ξ * ((3 : ℝ) / 2) ^ n)
  have h1 := Int.fract_lt_one (ξ * ((3 : ℝ) / 2) ^ n)
  simp only [Set.mem_union, Set.mem_Ico]
  rcases hn with h2 | h2
  · exact Or.inl ⟨h0, h2⟩
  · exact Or.inr ⟨by linarith, h1⟩

/-! ## A second and a third base (milestone M6)

The block certificate never needed `3/2`: `Z32.not_isEventuallyPeriodic_carry` holds for every
coprime `p > q > 1`, and `Z32.BlockCert.Cert.ok` checks those conditions on the certificate's own
base, so `Cert.not_confined` applies verbatim.  These two entries are what that buys. -/

/-- **Past the [Dub09AA] line at a second base.**  `Z_{4/3}(1/3, 5/8) = ∅`: no `ξ > 0` has every
`{ξ(4/3)ⁿ}` in `[1/3, 5/8)`, a window of length `7/24 = 0.29166… > 1/4`.

`1/p = 1/4` is exactly where [Dub09AA] Theorem 1 stops at this base (it certifies every window of
length `1/p` for `1 < q < p < q²`; that general statement is `Z32.ZSet_eq_empty_of_lt_sq`, proved
in `Z32/SmallInterval.lean` by the Sturmian route).  So this is the `(4,3)` analogue of
`Z32.ZSet_three_two_sixth_3_8`, and it is the first entry of the atlas at a base other than `3/2`.

What the engine sweep behind it establishes is a **lower bound** on the `(4,3)` frontier, not the
frontier: certificates exist at every length up to `70/240 = 0.29166…` (10 positions at denominator
`240`, funnel depth `≤ 20`), and a scan of `72/240 … 94/240` found none — but that scan ran only to
depth 14, and `(4,3)` is the base where the length-`1/4` windows need depth **26**, so its silence
is not evidence.  So: at least `1.17×` the published `1/p` line here, against `1.22×`
(`0.40722` over `1/3`) at `(3,2)`. -/
theorem ZSet_four_three_beyond_line : FLP.ZSet 4 3 (1 / 3 : ℝ) (7 / 24) = ∅ := by
  refine ZSet_eq_empty_of_cert_base certFourThree_ok rfl rfl fun y h1 h2 => ?_
  refine ⟨(8192, 15360), by simp [certFourThree], ?_, ?_⟩ <;>
    simp only [certFourThree, rleR] <;> push_cast <;> linarith

/-- **An entry in the regime `p > q²`.**  `Z_{5/2}(1/5, 2/5) = ∅`: no `ξ > 0` has every
`{ξ(5/2)ⁿ}` in `[1/5, 2/5)`.

The certificate is as small as they come and can be checked by hand: the only branch whose
preimage meets `[1/5, 2/5)` is `s = 1`, giving the single survivor `[7/25, 9/25)`, which has one
outgoing edge (again `s = 1`).  So a confined orbit has the constant carry word `1, 1, 1, …`, and
`Z32.not_isEventuallyPeriodic_carry` forbids that for `ξ ≠ 0`.

**What this is and is not.**  [Dub09AA] §4 states that his Theorem 1 — emptiness at length `1/p`
for *every* real `s` — is open when `p > q²`, because the final counting step needs `p < q²`.  The
block certificate has no such step, and the engine finds every tested length-`1/p` window at
`(5,2)`, `(7,2)`, `(9,2)`, `(10,3)`, `(11,3)` certifiable.  But that is a *finite* list of rational
windows, and the natural upgrade to all real `s` — certify a cover by windows of length
`1/N + 1/p`, then apply `Z32.ZSet_mono` — **fails**: measured at `(5,2)`, `(7,2)`, `(9,2)`,
`(10,3)`, the fattened windows go FAT (hundreds to thousands of surviving components), and at
`(5,2)` with `N = 20` only `8` of the `20` cover elements certify.  So this entry is one window,
not the open theorem, and there is no tension with [Aki08] Theorems 2.4/2.5, which build *nonempty*
Cantor sets in exactly this regime.  Deciding the open statement is not something this method
reaches; see plan §11.2. -/
theorem ZSet_five_two_fifth : FLP.ZSet 5 2 (1 / 5 : ℝ) (1 / 5) = ∅ := by
  refine ZSet_eq_empty_of_cert_base certFiveTwo_ok rfl rfl fun y h1 h2 => ?_
  refine ⟨(5, 10), by simp [certFiveTwo], ?_, ?_⟩ <;>
    simp only [certFiveTwo, rleR] <;> push_cast <;> linarith


/-! ### The open regime as a table

[Dub09AA] §4 leaves the length-`1/p` statement open for `p > q²`, because the counting endgame of
his Theorem 1 needs `p < q²`.  `Z32.ZSet_five_two_fifth` is one window there; these five theorems
are the measured column, six positions at each of five bases, all at funnel depth 1.  They remain a
finite list of rational windows, not the open theorem — the cover route to all real `s` fails, as
recorded at `Z32.ZSet_five_two_fifth`. -/

/-- **Thirty windows in the regime `p > q²`, at the base `5/2`.**  `Z_{5/2}(s, s+1/5) = ∅`
for `s = 0, 1/6, 1/3, 1/2, 2/3, 5/6`. -/
theorem ZSet_five_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 5 2 s (1 / 5) = ∅ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZSet_eq_empty_of_window certGridFiveTwo0_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo0]) (by norm_num [certGridFiveTwo0])
  · exact ZSet_eq_empty_of_window certGridFiveTwo1_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo1]) (by norm_num [certGridFiveTwo1])
  · exact ZSet_eq_empty_of_window certGridFiveTwo2_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo2]) (by norm_num [certGridFiveTwo2])
  · exact ZSet_eq_empty_of_window certGridFiveTwo3_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo3]) (by norm_num [certGridFiveTwo3])
  · exact ZSet_eq_empty_of_window certGridFiveTwo4_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo4]) (by norm_num [certGridFiveTwo4])
  · exact ZSet_eq_empty_of_window certGridFiveTwo5_ok rfl rfl rfl rfl
      (by norm_num [certGridFiveTwo5]) (by norm_num [certGridFiveTwo5])

/-- **Thirty windows in the regime `p > q²`, at the base `7/2`.**  `Z_{7/2}(s, s+1/7) = ∅`
for `s = 0, 1/6, 1/3, 1/2, 2/3, 5/6`. -/
theorem ZSet_seven_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 7 2 s (1 / 7) = ∅ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZSet_eq_empty_of_window certGridSevenTwo0_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo0]) (by norm_num [certGridSevenTwo0])
  · exact ZSet_eq_empty_of_window certGridSevenTwo1_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo1]) (by norm_num [certGridSevenTwo1])
  · exact ZSet_eq_empty_of_window certGridSevenTwo2_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo2]) (by norm_num [certGridSevenTwo2])
  · exact ZSet_eq_empty_of_window certGridSevenTwo3_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo3]) (by norm_num [certGridSevenTwo3])
  · exact ZSet_eq_empty_of_window certGridSevenTwo4_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo4]) (by norm_num [certGridSevenTwo4])
  · exact ZSet_eq_empty_of_window certGridSevenTwo5_ok rfl rfl rfl rfl
      (by norm_num [certGridSevenTwo5]) (by norm_num [certGridSevenTwo5])

/-- **Thirty windows in the regime `p > q²`, at the base `9/2`.**  `Z_{9/2}(s, s+1/9) = ∅`
for `s = 0, 1/6, 1/3, 1/2, 2/3, 5/6`. -/
theorem ZSet_nine_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 9 2 s (1 / 9) = ∅ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZSet_eq_empty_of_window certGridNineTwo0_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo0]) (by norm_num [certGridNineTwo0])
  · exact ZSet_eq_empty_of_window certGridNineTwo1_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo1]) (by norm_num [certGridNineTwo1])
  · exact ZSet_eq_empty_of_window certGridNineTwo2_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo2]) (by norm_num [certGridNineTwo2])
  · exact ZSet_eq_empty_of_window certGridNineTwo3_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo3]) (by norm_num [certGridNineTwo3])
  · exact ZSet_eq_empty_of_window certGridNineTwo4_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo4]) (by norm_num [certGridNineTwo4])
  · exact ZSet_eq_empty_of_window certGridNineTwo5_ok rfl rfl rfl rfl
      (by norm_num [certGridNineTwo5]) (by norm_num [certGridNineTwo5])

/-- **Thirty windows in the regime `p > q²`, at the base `10/3`.**  `Z_{10/3}(s, s+1/10) = ∅`
for `s = 0, 1/6, 1/3, 1/2, 2/3, 5/6`. -/
theorem ZSet_ten_three_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 10 3 s (1 / 10) = ∅ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZSet_eq_empty_of_window certGridTenThree0_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree0]) (by norm_num [certGridTenThree0])
  · exact ZSet_eq_empty_of_window certGridTenThree1_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree1]) (by norm_num [certGridTenThree1])
  · exact ZSet_eq_empty_of_window certGridTenThree2_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree2]) (by norm_num [certGridTenThree2])
  · exact ZSet_eq_empty_of_window certGridTenThree3_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree3]) (by norm_num [certGridTenThree3])
  · exact ZSet_eq_empty_of_window certGridTenThree4_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree4]) (by norm_num [certGridTenThree4])
  · exact ZSet_eq_empty_of_window certGridTenThree5_ok rfl rfl rfl rfl
      (by norm_num [certGridTenThree5]) (by norm_num [certGridTenThree5])

/-- **Thirty windows in the regime `p > q²`, at the base `11/3`.**  `Z_{11/3}(s, s+1/11) = ∅`
for `s = 0, 1/6, 1/3, 1/2, 2/3, 5/6`. -/
theorem ZSet_eleven_three_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 11 3 s (1 / 11) = ∅ := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZSet_eq_empty_of_window certGridElevenThree0_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree0]) (by norm_num [certGridElevenThree0])
  · exact ZSet_eq_empty_of_window certGridElevenThree1_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree1]) (by norm_num [certGridElevenThree1])
  · exact ZSet_eq_empty_of_window certGridElevenThree2_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree2]) (by norm_num [certGridElevenThree2])
  · exact ZSet_eq_empty_of_window certGridElevenThree3_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree3]) (by norm_num [certGridElevenThree3])
  · exact ZSet_eq_empty_of_window certGridElevenThree4_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree4]) (by norm_num [certGridElevenThree4])
  · exact ZSet_eq_empty_of_window certGridElevenThree5_ok rfl rfl rfl rfl
      (by norm_num [certGridElevenThree5]) (by norm_num [certGridElevenThree5])

end Z32
