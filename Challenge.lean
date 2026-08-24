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

/-!
# The comparator challenge: what this repository claims, stated against Mathlib alone

This file is the **trusted statement of record** for `leanprover/comparator` (see
`comparator.json` and `lake test`).  It imports *nothing but Mathlib*, re-declares — verbatim —
the one definition that occurs in the certified theorems, `FLP.ZSet`, and then states those
theorems with `sorry` proofs.  `Solution.lean` and `SolutionRecord.lean` merely import the real
development.  Comparator then checks that

1. every constant in the transitive closure of these statements is **identical** in the challenge
   and the solution environments (so `FLP.ZSet` here really is the set the repository proves
   things about — a window `[s, s+t)` that had drifted, or a `ZSet` quietly redefined with `≤` in
   place of `<`, would be caught here),
2. the solution's proofs use **no axioms beyond those permitted** by the config, and
3. the solution's environment is **re-accepted by the Lean kernel** from a fresh export, with no
   `.olean` loaded — so each block certificate's `Cert.ok = true` is re-evaluated from the raw
   integer data, with no appeal to the C engines that discovered it.

Consequently, auditing this repository's headline claims reduces to reading *this file*.

Unlike a challenge that has to mirror a development's module structure (definitions compiled by
the equation compiler share generated matchers when they sit in one module), everything needed
here is a single non-recursive definition, so one module suffices.

## The configuration

One config, `comparator.json`, certifies every statement below in a single run.  It permits
**three axioms** — `propext`, `Quot.sound`, `Classical.choice`, the classical core of Lean,
abbreviated "std3" in the paper — and no more.  That uniformity *is* the claim: the paper asserts
that no statement in it rests on cited literature, on a `sorry`, or on native compilation, so an
axiom appearing anywhere in the closure of a certified theorem is reported as `Illegal axiom
detected` rather than tolerated.  The sections below group the statements the way the paper does:

| Section | Paper | Theorems |
| --- | --- | --- |
| the classical pillars | §4, §6 | [FLP95] Cor. 1.4a and [Dub09AA] Thm. 1, formalized |
| Theorem A | §5 | residues of `⌊ξ(3/2)ⁿ⌋ mod m` are not eventually constant |
| Theorem B | §7 | single windows past the length-`1/p` line, at two bases |
| Theorem C | §7 | certified-empty unions, incl. [Dub08] Cor. 1.2 as printed |
| Theorem C, the record | §7 | the union of total length `17/24` (see the cost note below) |
| Theorem D | §7.4 | `‖ξ(3/2)ⁿ‖ ≥ 1/5` infinitely often |
| past the square | §7.6 | thirty windows in the regime `p > q²` |

The config names `SolutionRecord` rather than `Solution`, because the union record of
Theorem `union_record_7083_empty` is among the statements it certifies.  That certificate costs
about 100 seconds and 12 gigabytes to check, and the development isolates it in
`Z32/UnionRecord.lean` so that nothing else pays that; a `lake test` run therefore wants a
machine with about 16 GB of memory.

Nothing here is proved; the `sorry`s are the point.  The proofs live in `Z32/EscapeCert.lean`,
`Z32/ResidueCapture.lean`, `Z32/SmallInterval.lean`, `Z32/BlockCert.lean` and
`Z32/UnionRecord.lean`.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arith. **70** (1995), 125–147.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), no. 7, 951–958.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [KK17] J. Kari, J. Kopra, *Cellular automata and powers of `p/q`*, RAIRO Theor. Inform. Appl.
  **51** (2017), 191–204.
-/

namespace FLP

/-- The **`Z`-set** `Z_{p/q}(s, s+t) = {ξ > 0 : {ξ(p/q)ⁿ} ∈ [s, s+t) for all n}` ([FLP95] §1):
the positive reals whose entire `(p/q)`-power orbit stays in the interval `[s, s+t)`.

Verbatim the definition of `FLP/Basic.lean`; comparator rejects the solution if it is not. -/
def ZSet (p q : ℕ) (s t : ℝ) : Set ℝ :=
  {ξ | 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * ((p : ℝ) / q) ^ n) ∈ Set.Ico s (s + t)}

end FLP

namespace Z32

/-! ## The two classical pillars (§4, §6) -/

/-- **[FLP95] Corollary 1.4a**, as a kernel-checked replay of the finite computation indicated
there: `Z_{3/2}(s, s+1/3) = ∅` at each of the five positions `s = 0, 1/6, 1/3, 1/2, 2/3`. -/
theorem FLP_cor_one_four_a {s : ℝ} (hs : s ∈ ({0, 1 / 6, 1 / 3, 1 / 2, 2 / 3} : Set ℝ)) :
    FLP.ZSet 3 2 s (1 / 3) = ∅ := sorry

/-- **[Dub09AA] Theorem 1.**  For coprime `1 < q < p < q²`, every real `ξ ≠ 0` and every real `s`,
the parts `{ξ(p/q)ⁿ}` leave the closed interval `[s, s + 1/p]` (mod 1) infinitely often. -/
theorem dubickas_theorem_1 {p q : ℕ} {ξ : ℝ} (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q)
    (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0) (s : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / q) ^ n - s) := sorry

/-- **[Dub09AA] Theorem 1, `Z`-set form**: for coprime `1 < q < p < q²` the set
`Z_{p/q}(s, s + 1/p)` is empty for *every* real `s`. -/
theorem ZSet_eq_empty_of_lt_sq {p q : ℕ} (hq : 1 < q) (hpq : q < p) (hpq2 : p < q * q)
    (hcop : Nat.Coprime p q) (s : ℝ) : FLP.ZSet p q s (1 / (p : ℝ)) = ∅ := sorry

/-- **The `(3,2)` headline of the length-`1/3` line**: `Z_{3/2}(s, s + 1/3) = ∅` for *every* real
`s`, irrational positions included. -/
theorem ZSet_three_two_third_empty (s : ℝ) : FLP.ZSet 3 2 s (1 / 3) = ∅ := sorry

/-! ## Theorem A — the residue corollary (§5) -/

/-- **Theorem A.**  For every real `ξ > 0` and every integer `m ≥ 3`, the residues
`⌊ξ(3/2)ⁿ⌋ mod m` are not eventually constant. -/
theorem residue_not_eventually_constant {ξ : ℝ} (hξ : 0 < ξ) {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ (r : ℤ) (N : ℕ), ∀ n, N ≤ n → ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) = r := sorry

/-- Theorem A in its infinitely-often form: past any index the residue still changes. -/
theorem exists_residue_change {ξ : ℝ} (hξ : 0 < ξ) {m : ℕ} (hm : 3 ≤ m) (N : ℕ) :
    ∃ n, N ≤ n ∧ ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ ⌊ξ * (3 / 2 : ℝ) ^ N⌋ % (m : ℤ) := sorry

/-- Theorem A at `ξ = 1`: the residues of `⌊(3/2)ⁿ⌋` modulo any `m ≥ 3` do not stabilize. -/
theorem residue_not_eventually_constant_one {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ (r : ℤ) (N : ℕ), ∀ n, N ≤ n → ⌊(3 / 2 : ℝ) ^ n⌋ % (m : ℤ) = r := sorry

/-! ## Theorem B — single windows past the length-`1/p` line (§7) -/

/-- **Theorem B, first entry.**  `Z_{3/2}(1/6, 13/24) = ∅`: a window of length `3/8 > 1/3`. -/
theorem ZSet_three_two_sixth_3_8 : FLP.ZSet 3 2 (1 / 6 : ℝ) (3 / 8) = ∅ := sorry

/-- **Theorem B, the engine frontier.**  `Z_{3/2}(961/3600, 2427/3600) = ∅`, a window of length
`1466/3600 = 0.40722…`. -/
theorem ZSet_three_two_frontier : FLP.ZSet 3 2 (961 / 3600 : ℝ) (1466 / 3600) = ∅ := sorry

/-- **Theorem B, eventual form.**  No `ξ ≠ 0` has `{ξ(3/2)ⁿ} ∈ [1/6, 13/24)` for all sufficiently
large `n`. -/
theorem not_eventually_mem_sixth_3_8 {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n, N ≤ n → Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Ico (1 / 6 : ℝ) (13 / 24) := sorry

/-- **Theorem B at a second base.**  `Z_{4/3}(1/3, 5/8) = ∅`, a window of length `7/24 > 1/4`. -/
theorem ZSet_four_three_beyond_line : FLP.ZSet 4 3 (1 / 3 : ℝ) (7 / 24) = ∅ := sorry

/-! ## Theorem C — certified-empty unions (§7) -/

/-- **[Dub08] Corollary 1.2, as printed.**  No `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` inside the **closed**
set `[8/39, 18/39] ∪ [21/39, 31/39]`, of total length `20/39`. -/
theorem dubickas_2008_cor_1_2 {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (8 / 39 : ℝ) (18 / 39) ∪ Set.Icc (21 / 39 : ℝ) (31 / 39) := sorry

/-- **Theorem C**: a certified-empty union of total length `7/12`, past [Dub08]'s `20/39`. -/
theorem union_seven_twelfths_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 6) ∪ Set.Ico (1 / 4 : ℝ) (1 / 3) ∪ Set.Ico (5 / 12 : ℝ) (2 / 3) ∪
        Set.Ico (3 / 4 : ℝ) (5 / 6) := sorry

/-- **Theorem C**: a certified-empty union of total length `2/3` — the same total length as the
*nonempty* union of [KK17] Corollary 4.8, so total length alone decides nothing. -/
theorem union_two_thirds_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 9) ∪ Set.Ico (1 / 6 : ℝ) (4 / 9) ∪ Set.Ico (1 / 2 : ℝ) (5 / 9) ∪
        Set.Ico (11 / 18 : ℝ) (7 / 9) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) := sorry

/-- **Theorem C**: a certified-empty union of total length `25/36 = 0.6944…`. -/
theorem union_record_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 12) ∪ Set.Ico (1 / 9 : ℝ) (11 / 36) ∪ Set.Ico (4 / 9 : ℝ) (2 / 3) ∪
        Set.Ico (25 / 36 : ℝ) (3 / 4) ∪ Set.Ico (5 / 6 : ℝ) (8 / 9) ∪ Set.Ico (11 / 12 : ℝ) 1 :=
  sorry

/-! ## Theorem C — the union record (§7)

Proved in `Z32/UnionRecord.lean`, the one module whose kernel check is expensive; see the module
docstring. -/

/-- **Theorem C, the record.**  No `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` inside this union of eleven
intervals, of total length `17/24 = 0.70833…`, against `20/39 = 0.5128…` in print. -/
theorem union_record_7083_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
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

/-! ## Theorem D — the nearest-integer family (§7.4) -/

/-- **Theorem D, cell form.**  No `ξ ≠ 0` has every `{ξ(3/2)ⁿ}` inside `[0, 1/5) ∪ [4/5, 1)`. -/
theorem two_cell_fifth_empty {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Ico (0 : ℝ) (1 / 5) ∪ Set.Ico (4 / 5 : ℝ) 1 := sorry

/-- **Theorem D.**  For every `ξ ≠ 0` there are infinitely many `n` with `‖ξ(3/2)ⁿ‖ ≥ 1/5`, where
`‖x‖ = |x - round x|` is the distance to the nearest integer. -/
theorem not_forall_abs_sub_round_lt_fifth {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ} :
    ¬ ∀ n : ℕ, N ≤ n → |ξ * ((3 : ℝ) / 2) ^ n - round (ξ * ((3 : ℝ) / 2) ^ n)| < 1 / 5 := sorry

/-! ## The regime `p > q²` (§7.6), where [Dub09AA] §4 leaves the question open -/

/-- One entry in the regime `p > q²`: `Z_{5/2}(1/5, 2/5) = ∅`. -/
theorem ZSet_five_two_fifth : FLP.ZSet 5 2 (1 / 5 : ℝ) (1 / 5) = ∅ := sorry

/-- Six of the thirty windows of length `1/p` in the regime `p > q²`, at the base `5/2`. -/
theorem ZSet_five_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 5 2 s (1 / 5) = ∅ := sorry

/-- Six of the thirty windows of length `1/p` in the regime `p > q²`, at the base `7/2`. -/
theorem ZSet_seven_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 7 2 s (1 / 7) = ∅ := sorry

/-- Six of the thirty windows of length `1/p` in the regime `p > q²`, at the base `9/2`. -/
theorem ZSet_nine_two_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 9 2 s (1 / 9) = ∅ := sorry

/-- Six of the thirty windows of length `1/p` in the regime `p > q²`, at the base `10/3`. -/
theorem ZSet_ten_three_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 10 3 s (1 / 10) = ∅ := sorry

/-- Six of the thirty windows of length `1/p` in the regime `p > q²`, at the base `11/3`. -/
theorem ZSet_eleven_three_grid {s : ℝ}
    (hs : s = 0 ∨ s = 1 / 6 ∨ s = 1 / 3 ∨ s = 1 / 2 ∨ s = 2 / 3 ∨ s = 5 / 6) :
    FLP.ZSet 11 3 s (1 / 11) = ∅ := sorry

end Z32
