/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The second comparator challenge: what the *schemas* paper claims

This file is the **trusted statement of record** for the second paper, *Confinement schemas and
the reach of block certificates for powers of rational numbers modulo one* — the companion of
`Challenge.lean`, which does the same job for [Ste26].  It is consumed by
`leanprover/comparator` through `comparator2.json` (`lake test`).

Like `Challenge.lean` it imports *nothing but Mathlib*, re-declares — verbatim — the definitions
that occur in the certified theorems, and then states those theorems with `sorry` proofs.
`Solution2.lean` and `SolutionRecord2.lean` merely import the real development.  Comparator then
checks that

1. every constant in the transitive closure of these statements is **identical** in the challenge
   and the solution environments (so `Z32.SchemaCertified` here really is the predicate the
   development proves things about, and `FLP.ZSet` really is the set of [FLP95] §1),
2. the solution's proofs use **no axioms beyond those permitted** by the config — `propext`,
   `Quot.sound`, `Classical.choice`, the "std3" of the paper's Appendix A — and
3. the solution's environment is **re-accepted by the Lean kernel** from a fresh export, with no
   `.olean` loaded, so every `Cert.ok = true` behind a "computed" row is re-evaluated from the
   raw integer data.

## The statements, by section of the paper

The `✓` column marks the eleven statements `comparator2.json` names.  They are exactly the
paper's lettered results — Theorems A to E — less Thm. D(ii), which is out of reach of this
format (see below).  Everything else here is stated for the record and proved by the
development, but is not part of what a `lake test` run certifies; adding any of it back to
`comparator2.json` costs nothing but the run time.

| ✓ | Section | Paper | Statements below |
| --- | --- | --- | --- |
| ✓ | §3 | Thm. 3.5, 3.6 (Thm. A) | the depth-`K` schema and its closed form |
| ✓ | §3 | Cor. 3.7 (Thm. B) | the depth-one schema on the single parameter `ε` |
| | §3 | Cor. 3.9, Thm. 3.10 | the integer-`θ` positions and the thirty grid entries |
| | §3 | Cor. 3.11 | continua of *real* positions at the base `5/2`, depths one to three |
| ✓ | §4 | Thm. 4.4 row one (Thm. C) | the escape rate, uniform in `(p, q, s, K)` |
| | §4 | Tab. 1, Cor. 4.5 | the escape rate tabulated on the nine unranked certificates |
| ✓ | §5 | Thm. 5.5 (Thm. D(i)) | completeness on the finite-hold-set class |
| | §5 | Thm. 5.2, Thm. 5.10 | determinism, and the five closed-endpoint entries |
| ✓ | §6 | Thm. 6.3 (Thm. D(iii)) | the depth–size bound, in both its forms |
| ✓ | §7 | Thm. 7.1 (Thm. E) | the ranked frontier `Z_{3/2}(2/7, 3/7) = ∅`, all four forms |

## What is deliberately *not* here

Three groups of the paper's statements quantify over a **block certificate** — `Z32.BlockCert.Cert`
together with its decision procedure `Cert.ok` — rather than over reals and windows:

* Thm. 4.2, Prop. 4.3(ii) and Thm. 4.4 row two (the certificate half of the escape bound),
* Thm. 5.6, 5.7, 5.8 and Cor. 5.9 (the obstruction: `Cert.ok = false` for an infinite hold set),
* Cor. 6.4 and Ex. 6.5 (the hole of a valid certificate).

Restating those against Mathlib alone would mean re-declaring the whole certificate format and its
`Bool`-valued validity checker here — several hundred lines of the very decision procedure whose
verdicts the challenge exists to keep at arm's length.  A challenge that carries it is no longer a
document one can audit by reading.  Their *consequences* on concrete sets are stated instead:
every "computed" row of the paper that speaks about real numbers — Tab. 1, Cor. 4.5, Thm. 5.10,
Thm. 7.1 — is below.  Conj. 7.2 and Rem. 7.3 are not formalized at all, as Appendix A says.

Thm. 5.7 is Thm. D(ii), so exactly one of the paper's five lettered results is out of reach of the
challenge format, and `comparator2.json` certifies the other four and a half.

The config names `Solution2`, not `SolutionRecord2`: the one statement below that needs the extra
module is Tab. 1 row 6 (`Z32.escape_union_7083`), which rests on `Z32.BlockCert.certUnion7083` and
costs about 100 seconds and 12 gigabytes to kernel-check.  It is not among the certified eleven, so
a `comparator2.json` run does not pay that; `comparator.json` still does.

Nothing here is proved; the `sorry`s are the point.  The proofs live in `Z32/SymbolicCert.lean`,
`Z32/DepthKSchema.lean`, `Z32/EscapeBound.lean`, `Z32/CertComplete.lean`, `Z32/DepthSize.lean`,
`Z32/RankedFrontier.lean` and `Z32/UnionRecord.lean`.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **70** (1995), 125–147.
* [Bug04] Y. Bugeaud, *Linear mod one transformations and the distribution of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **114** (2004), 301–311.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), no. 7, 951–958.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [KK17] J. Kari, J. Kopra, *Cellular automata and powers of `p/q`*, RAIRO Theor. Inform. Appl.
  **51** (2017), 191–204.
* [Ste26] R. Stephan, *Confinement certificates for powers of rational numbers modulo one*,
  preprint, 2026.
-/

namespace FLP

/-- The **`Z`-set** `Z_{p/q}(s, s+t) = {ξ > 0 : {ξ(p/q)ⁿ} ∈ [s, s+t) for all n}` ([FLP95] §1).

Verbatim the definition of `FLP/Basic.lean`; comparator rejects the solution if it is not. -/
def ZSet (p q : ℕ) (s t : ℝ) : Set ℝ :=
  {ξ | 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * ((p : ℝ) / q) ^ n) ∈ Set.Ico s (s + t)}

end FLP

namespace Z32

/-! ## The orbit of §2

Verbatim `Z32/DubickasWord.lean`; only `Z32.holdSet_finite_imp` below mentions them. -/

section Defs

variable (p q : ℕ) (ξ ν : ℝ)

/-- The shifted orbit `ξ(p/q)ⁿ + ν` of [Dub09AA] §2. -/
noncomputable def orb (n : ℕ) : ℝ := ξ * ((p : ℝ) / q) ^ n + ν

/-- The fractional part `yₙ = {ξ(p/q)ⁿ + ν}`. -/
noncomputable def yFract (n : ℕ) : ℝ := Int.fract (orb p q ξ ν n)

end Defs

/-! ## The three parameters of the schema (Definition 3.1)

Verbatim `Z32/SymbolicCert.lean`. -/

/-- `θ = (p − q)s`, the only way the position enters. -/
noncomputable def schemaTheta (p q : ℕ) (s : ℝ) : ℝ := ((p : ℝ) - q) * s

/-- `ε = {(p − q)s}`, the single number the depth-one layer depends on. -/
noncomputable def schemaEps (p q : ℕ) (s : ℝ) : ℝ := Int.fract (schemaTheta p q s)

/-- **The certified positions** of Corollary 3.7, with denominators cleared: `ε = 0`, or
`q/p ≤ ε`, or `ε` in the band `[q²/(p(p+q)), q/(p+q)]`. -/
def SchemaCertified (p q : ℕ) (s : ℝ) : Prop :=
  schemaEps p q s = 0 ∨ (q : ℝ) ≤ p * schemaEps p q s ∨
    ((q : ℝ) ^ 2 ≤ (p : ℝ) * ((p : ℝ) + q) * schemaEps p q s ∧
      ((p : ℝ) + q) * schemaEps p q s ≤ q)

/-! ## The escape data of Definition 3.3

Verbatim `Z32/DepthKSchema.lean`. -/

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

/-- **The certified positions at depth `K`** — the paper's "`s` escapes at depth `K`". -/
def SchemaCertifiedK (p q : ℕ) (s : ℝ) (K : ℕ) : Prop :=
  ∃ w : ℕ → ℝ, Escape p q (schemaEps p q s) K w

/-- **The closed-form band at depth `K`** (Theorem 3.6, display (4)): the `ε` whose all-low marked
orbit escapes at step `K`. -/
def LowBand (p q : ℕ) (e : ℝ) (K : ℕ) : Prop :=
  (q : ℝ) ^ (K + 1) * ((p : ℝ) - q) ≤ p * e * ((p : ℝ) ^ (K + 1) - (q : ℝ) ^ (K + 1)) ∧
    e * ((p : ℝ) ^ (K + 1) - (q : ℝ) ^ (K + 1)) ≤ (q : ℝ) ^ K * ((p : ℝ) - q)

/-! ## The escape budget of Definition 4.1

Verbatim `Z32/EscapeBound.lean`. -/

/-- **The escape budget.**  `A` combinatorial steps — the certificate's own contribution — then
`1 + ⌈log_q (X(p/q)^A + 1)⌉ + ⌈log_{p/q}(q/L)⌉` arithmetic ones. -/
noncomputable def escapeSteps (p q A : ℕ) (X L : ℝ) : ℕ :=
  A + 1 + ⌈Real.logb q (X * ((p : ℝ) / q) ^ A + 1)⌉₊
    + ⌈Real.logb ((p : ℝ) / q) ((q : ℝ) / L)⌉₊

/-! ## The denominator and the hold set of §5

Verbatim `Z32/CertComplete.lean`. -/

/-- `D · y` is an integer. -/
def HasDenom (D : ℕ) (y : ℝ) : Prop := ∃ a : ℤ, (D : ℝ) * y = a

/-- A point of the recurrent part: rational with a denominator coprime to `q`. -/
def CoprimeDenom (q : ℕ) (y : ℝ) : Prop := ∃ D : ℕ, 0 < D ∧ Nat.Coprime D q ∧ HasDenom D y

/-- The **hold set** `ℋ_{p/q}(U)` of Definition 5.1: the points of `U` that carry an infinite
orbit of the model relation `q·y_{n+1} = p·yₙ − sₙ` inside `U`. -/
def holdSet (p q : ℕ) (U : Set ℝ) : Set ℝ :=
  {z | ∃ (y : ℕ → ℝ) (w : ℕ → ℤ), y 0 = z ∧ (∀ n, y n ∈ U) ∧
    ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n}

/-! ## The exact funnel of §6

Verbatim `Z32/DepthSize.lean`. -/

open MeasureTheory Set

/-- `f⁻¹(S)`: the points of `[0,1)` with a successor in `S` under the carry relation
`q·v = p·y − s`. -/
def pre (p q : ℕ) (S : Set ℝ) : Set ℝ :=
  {y | y ∈ Ico (0 : ℝ) 1 ∧ ∃ v ∈ S, ∃ s : ℤ, (q : ℝ) * v = (p : ℝ) * y - (s : ℝ)}

/-- The **exact funnel** of `U`: `T₀ = U` and `T_{k+1} = U ∩ f⁻¹(T_k)`. -/
def funnel (p q : ℕ) (U : Set ℝ) : ℕ → Set ℝ
  | 0 => U
  | k + 1 => U ∩ pre p q (funnel p q U k)

/-! ## §3 — the schema and the rotation -/

section SymbolicCert

variable {p q : ℕ} {ξ s : ℝ}

/-- **Corollary 3.7 (Theorem B), the certificate schema.**  `Z_{p/q}(s, s + 1/p) = ∅` for every
real position `s` whose `ε = {(p−q)s}` is certified — at every coprime base `p > q > 1`, and with
no assumption on the arithmetic nature of `ξ`. -/
theorem ZSet_eq_empty_of_certified (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hcert : SchemaCertified p q s) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := sorry

/-- **Corollary 3.9(i).**  `Z_{p/q}(0, 1/p) = ∅` at every coprime base `p > q > 1`. -/
theorem ZSet_zero_eq_empty (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) :
    FLP.ZSet p q 0 (1 / (p : ℝ)) = ∅ := sorry

/-- **Corollary 3.9(i).**  Every position with `(p − q)s ∈ ℤ` is certified — at the base `3/2`
these are the halves, at `10/3` the sevenths. -/
theorem ZSet_eq_empty_of_theta_int (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {m : ℤ} (hs : ((p : ℝ) - q) * s = m) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := sorry

/-- **Corollary 3.9(ii).**  `Z_{p/q}(1/2, 1/2 + 1/p) = ∅` whenever `p − q` is even (then `ε = 0`)
or `2q ≤ p` (then `ε = 1/2 ≥ q/p`). -/
theorem ZSet_half_eq_empty (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (h : (p - q) % 2 = 0 ∨ 2 * q ≤ p) :
    FLP.ZSet p q (1 / 2) (1 / (p : ℝ)) = ∅ := sorry

/-- **Theorem 3.10** at the base `5/2`: the six positions `s = j/6`, `j < 6`. -/
theorem ZSet_five_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 5 2 ((j : ℝ) / 6) (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

/-- **Theorem 3.10** at the base `7/2`. -/
theorem ZSet_seven_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 7 2 ((j : ℝ) / 6) (1 / ((7 : ℕ) : ℝ)) = ∅ := sorry

/-- **Theorem 3.10** at the base `9/2`. -/
theorem ZSet_nine_two (j : ℕ) (hj : j < 6) :
    FLP.ZSet 9 2 ((j : ℝ) / 6) (1 / ((9 : ℕ) : ℝ)) = ∅ := sorry

/-- **Theorem 3.10** at the base `10/3`. -/
theorem ZSet_ten_three (j : ℕ) (hj : j < 6) :
    FLP.ZSet 10 3 ((j : ℝ) / 6) (1 / ((10 : ℕ) : ℝ)) = ∅ := sorry

/-- **Theorem 3.10** at the base `11/3`. -/
theorem ZSet_eleven_three (j : ℕ) (hj : j < 6) :
    FLP.ZSet 11 3 ((j : ℝ) / 6) (1 / ((11 : ℕ) : ℝ)) = ∅ := sorry

/-- **Corollary 3.11, depth 0.**  At the base `5/2`, *every real* `s` with `{3s} ≥ 2/5` has
`Z_{5/2}(s, s + 1/5) = ∅` — a continuum of positions in a regime where [Dub09AA] §4 leaves the
question open and [Dub19] needs `ξ` algebraic. -/
theorem ZSet_five_two_upper {s : ℝ} (h : (2 : ℝ) / 5 ≤ Int.fract (3 * s)) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

/-- **Corollary 3.11, depth 1.**  Every real `s` with `{3s} ∈ [4/35, 2/7]`. -/
theorem ZSet_five_two_band {s : ℝ} (h1 : (4 : ℝ) / 35 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 2 / 7) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

/-- **Corollary 3.11**, the depth-one band as an interval of positions: every real `s` in
`[4/105, 2/21]`. -/
theorem ZSet_five_two_interval {s : ℝ} (h1 : (4 : ℝ) / 105 ≤ s) (h2 : s ≤ 2 / 21) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

end SymbolicCert

section DepthKSchema

variable {p q K : ℕ} {e s ξ : ℝ} {w : ℕ → ℝ}

/-- **Theorem 3.5 (Theorem A).**  `Z_{p/q}(s, s + 1/p) = ∅` for every real position `s` that
escapes at depth `K`, at every coprime base `p > q > 1`, and with no assumption on the arithmetic
nature of `ξ`. -/
theorem ZSet_eq_empty_of_certifiedK (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hcert : SchemaCertifiedK p q s K) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := sorry

/-- **Theorem 3.6 (Theorem A, closed form).**  `Z_{p/q}(s, s + 1/p) = ∅` whenever
`ε = {(p−q)s}` lies in the depth-`K` band of display (4). -/
theorem ZSet_eq_empty_of_lowBand (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hb : LowBand p q (schemaEps p q s) K) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := sorry

/-- **Corollary 3.11, depth 2.**  Every real `s` with `{3s} ∈ [8/195, 4/39]`, an interval strictly
inside the band on which the depth-one schema says nothing. -/
theorem ZSet_five_two_depth_two {s : ℝ} (h1 : (8 : ℝ) / 195 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 4 / 39) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

/-- **Corollary 3.11, depth 3.**  Every real `s` with `{3s} ∈ [16/1015, 8/203]`. -/
theorem ZSet_five_two_depth_three {s : ℝ} (h1 : (16 : ℝ) / 1015 ≤ Int.fract (3 * s))
    (h2 : Int.fract (3 * s) ≤ 8 / 203) : FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

/-- **Corollary 3.11**, the depth-two band as an interval of positions: every real `s` in
`[8/585, 4/117]`. -/
theorem ZSet_five_two_depth_two_interval {s : ℝ} (h1 : (8 : ℝ) / 585 ≤ s) (h2 : s ≤ 4 / 117) :
    FLP.ZSet 5 2 s (1 / ((5 : ℕ) : ℝ)) = ∅ := sorry

end DepthKSchema

/-! ## §4 — the escape rate -/

section EscapeBound

variable {p q : ℕ} {ξ ν : ℝ}

/-- **Theorem 4.4, row one (Theorem C).**  Every `ξ` with `0 < L ≤ ξ ≤ X` leaves the window
`[s, s + 1/p)` within `ℰ(K + 2, X, L)` steps, whenever `s` escapes at depth `K`. -/
theorem exists_fract_notMem_le_of_certifiedK {K : ℕ} {s : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hcert : SchemaCertifiedK p q s K)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ escapeSteps p q (K + 2) X Lo,
      Int.fract (ξ * ((p : ℝ) / q) ^ n) ∉ Set.Ico s (s + 1 / (p : ℝ)) := sorry

end EscapeBound

namespace BlockCert

/-- **Table 1, row 1.**  Every `ξ ∈ [1, X]` has some `n ≤ 14 + α` with `{ξ(3/2)ⁿ} ∉ [1/6, 13/24)`,
where `2^α ≥ X(3/2)³ + 1`. -/
theorem escape_sixth_3_8 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 3 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 14 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 6 : ℝ) (13 / 24) := sorry

/-- **Corollary 4.5.**  Every `ξ ∈ [1, 10⁶]` leaves `[1/6, 13/24)` within `36` steps. -/
theorem escape_sixth_3_8_million {ξ : ℝ} (h1 : 1 ≤ ξ) (hX : ξ ≤ 10 ^ 6) :
    ∃ n ≤ 36, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 6 : ℝ) (13 / 24) := sorry

/-- **Table 1, row 2**, the longest single certified window. -/
theorem escape_frontier {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 2 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 18 + α,
      Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉ Set.Ico (961 / 3600 : ℝ) (2427 / 3600) := sorry

/-- **Table 1, row 3**: the union of total length `7/12`. -/
theorem escape_union_712 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 1 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 11 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 6) ∪ Set.Ico (1 / 4 : ℝ) (1 / 3) ∪ Set.Ico (5 / 12 : ℝ) (2 / 3) ∪
        Set.Ico (3 / 4 : ℝ) (5 / 6) := sorry

/-- **Table 1, row 4**: the union of total length `2/3`. -/
theorem escape_union_23 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 12 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 24 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 9) ∪ Set.Ico (1 / 6 : ℝ) (4 / 9) ∪ Set.Ico (1 / 2 : ℝ) (5 / 9) ∪
        Set.Ico (11 / 18 : ℝ) (7 / 9) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) := sorry

/-- **Table 1, row 5**: the union of total length `25/36`. -/
theorem escape_union_2536 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 17 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 31 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 12) ∪ Set.Ico (1 / 9 : ℝ) (11 / 36) ∪ Set.Ico (4 / 9 : ℝ) (2 / 3) ∪
        Set.Ico (25 / 36 : ℝ) (3 / 4) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) ∪
        Set.Ico (11 / 12 : ℝ) 1 := sorry

/-- **Table 1, row 7**: the two-cell union `[0, 1/5) ∪ [4/5, 1)`, the nearest-integer entry, and
the counterexample of §4.3 to a bound in `X` alone. -/
theorem escape_two_cell_fifth {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 2 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 6 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1 := sorry

/-- **Table 1, row 8**, at the base `4/3`. -/
theorem escape_four_three {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((4 : ℝ) / 3) ^ 2 + 1 ≤ 3 ^ α) :
    ∃ n ≤ 12 + α, Int.fract (ξ * ((4 : ℝ) / 3) ^ n) ∉ Set.Ico (1 / 3 : ℝ) (5 / 8) := sorry

/-- **Table 1, row 9**, at the base `5/2`, in the regime `p > q²`. -/
theorem escape_five_two_fifth {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((5 : ℝ) / 2) ^ 1 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 4 + α, Int.fract (ξ * ((5 : ℝ) / 2) ^ n) ∉ Set.Ico (1 / 5 : ℝ) (2 / 5) := sorry

end BlockCert

/-- **Table 1, row 6**, the union record of total length `17/24`.  This is the entry that costs
about 100 seconds and 12 gigabytes to kernel-check; `SolutionRecord2` is the module that carries
it, and `comparator2.json` — which does not certify this row — names `Solution2` instead. -/
theorem escape_union_7083 {ξ X : ℝ} {α : ℕ} (h1 : 1 ≤ ξ) (hX : ξ ≤ X)
    (hα : X * ((3 : ℝ) / 2) ^ 100 + 1 ≤ 2 ^ α) :
    ∃ n ≤ 120 + α, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∉
      Set.Ico (0 : ℝ) (1 / 24) ∪
      Set.Ico (1 / 16 : ℝ) (3 / 16) ∪
      Set.Ico (5 / 24 : ℝ) (11 / 48) ∪
      Set.Ico (1 / 4 : ℝ) (1 / 3) ∪
      Set.Ico (17 / 48 : ℝ) (3 / 8) ∪
      Set.Ico (5 / 12 : ℝ) (7 / 16) ∪
      Set.Ico (23 / 48 : ℝ) (17 / 24) ∪
      Set.Ico (3 / 4 : ℝ) (37 / 48) ∪
      Set.Ico (19 / 24 : ℝ) (5 / 6) ∪
      Set.Ico (41 / 48 : ℝ) (15 / 16) ∪
      Set.Ico (23 / 24 : ℝ) (47 / 48) := sorry

/-! ## §5 — completeness and the obstruction -/

section CertComplete

variable {p q : ℕ}

/-- **Theorem 5.2 (determinism).**  A point has at most one successor in `[0,1)` whose denominator
is coprime to `q`: on the recurrent class the model relation is a *function*. -/
theorem step_unique {u v v' : ℝ} {s s' : ℤ}
    (hu : CoprimeDenom q u) (hv : CoprimeDenom q v) (hv' : CoprimeDenom q v')
    (h1 : (q : ℝ) * v = p * u - s) (h2 : (q : ℝ) * v' = p * u - s')
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hv0' : 0 ≤ v') (hv1' : v' < 1) : v = v' := sorry

/-- **Theorem 5.5 (Theorem D(i)), completeness on the finite-hold-set class.**  If the hold set of
`U` is finite then no `ξ ≠ 0` keeps its orbit in `U` — with no certificate in sight, and no
hypothesis on how the held orbits are arranged. -/
theorem holdSet_finite_imp (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {U : Set ℝ} (hfin : (holdSet p q U).Finite)
    {ξ : ℝ} (hξ : ξ ≠ 0) : ∃ n, yFract p q ξ 0 n ∉ U := sorry

end CertComplete

namespace BlockCert

/-- **Theorem 5.10**, first entry: the closed two-cell arc `[0, 1/5] ∪ [4/5, 1]`, the one
Corollary 5.9 refuses to every *unranked* certificate. -/
theorem two_cell_fifth_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (0 : ℝ) (1 / 5) ∪ Set.Icc (4 / 5 : ℝ) 1 := sorry

/-- **Theorem 5.10**, the flagship window with both endpoints: the closed `[1/6, 13/24]`. -/
theorem sixth_3_8_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Icc (1 / 6 : ℝ) (13 / 24) := sorry

/-- **Theorem 5.10**, the engine frontier with both endpoints: the closed `[961/3600, 2427/3600]`.
-/
theorem frontier_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (961 / 3600 : ℝ) (2427 / 3600) := sorry

/-- **Theorem 5.10** at the base `4/3`: the closed `[1/3, 5/8]`. -/
theorem four_three_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((4 : ℝ) / 3) ^ n) ∈ Set.Icc (1 / 3 : ℝ) (5 / 8) := sorry

/-- **Theorem 5.10** at the base `5/2`: the closed `[1/5, 2/5]`. -/
theorem five_two_fifth_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((5 : ℝ) / 2) ^ n) ∈ Set.Icc (1 / 5 : ℝ) (2 / 5) := sorry

end BlockCert

/-! ## §6 — the depth–size bound -/

/-- **Theorem 6.3, one exponent at a time.**  If the exact funnel at depth `K + j` has measure at
most `B`, then `(K + j + 1)·δ + B ≥ 1`, where `δ = |[0,1) ∖ U|`. -/
theorem depth_size {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ} (hU : U ⊆ Ico (0 : ℝ) 1)
    (hUm : MeasurableSet U) {K j : ℕ} {B : ℝ}
    (hcov : volume.real (funnel p q U (K + j)) ≤ B) :
    1 ≤ ((K : ℝ) + j + 1) * volume.real (Ico (0 : ℝ) 1 \ U) + B := sorry

/-- **Theorem 6.3 (Theorem D(iii)), in the form that prices a target.**  A union whose funnel is
confined by `B` blocks from depth `K` on obeys `1 ≤ 2δ(K + 2 + log_{p/q} 2B)`, so the hole cannot
be made small without paying in depth or in blocks like `1/δ` — a negative answer to [KK17]
Problem 6.1 for this certificate format. -/
theorem depth_size_logb {p q : ℕ} (hq : 0 < q) (hqp : q < p) {U : Set ℝ}
    (hU : U ⊆ Ico (0 : ℝ) 1) (hUm : MeasurableSet U) {K B : ℕ} (hB : 0 < B)
    (hcov : ∀ j, volume.real (funnel p q U (K + j)) ≤ (B : ℝ) * ((q : ℝ) / (p : ℝ)) ^ j) :
    1 ≤ 2 * volume.real (Ico (0 : ℝ) 1 \ U)
          * ((K : ℝ) + 2 + Real.logb ((p : ℝ) / (q : ℝ)) (2 * B)) := sorry

/-! ## §7 — the ranked frontier and its exact ceiling -/

/-- **Theorem 7.1 (Theorem E).**  `Z_{3/2}(2/7, 3/7) = ∅`: a window of length
`3/7 = 0.428571…`, past the corpus record `0.40722` and past [Dub19] Theorem 1.2's
`31/81 = 0.38271…`, the longest single window excluded in print. -/
theorem ZSet_three_two_two_seven : FLP.ZSet 3 2 (2 / 7 : ℝ) (3 / 7) = ∅ := sorry

/-- **Theorem 7.1**, closed form: no `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` in the *closed* `[2/7, 5/7]`. -/
theorem two_seven_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Icc (2 / 7 : ℝ) (5 / 7) := sorry

/-- **Theorem 7.1**, eventual form: the orbit leaves `[2/7, 5/7]` infinitely often. -/
theorem not_eventually_two_seven {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Icc (2 / 7 : ℝ) (5 / 7) := sorry

/-- **Theorem 7.1**, nearest-integer form: `‖ξ(3/2)ⁿ‖ < 2/7 = 0.285714…` infinitely often, for
every `ξ ≠ 0`, where `‖x‖ = |x - round x|`. -/
theorem not_forall_two_seven_le_abs_sub_round {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → (2 : ℝ) / 7 ≤ |ξ * ((3 : ℝ) / 2) ^ n - round (ξ * ((3 : ℝ) / 2) ^ n)| :=
  sorry

end Z32
