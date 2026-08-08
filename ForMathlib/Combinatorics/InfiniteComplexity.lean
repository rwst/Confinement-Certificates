/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.SubwordComplexity
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Morse–Hedlund for infinite words: complexity growth and left-special factors

The **infinite** Morse–Hedlund dichotomy, in the form consumed by symbolic-dynamics arguments
about digit expansions: a word over a finite alphabet that is *not* eventually periodic has,
for every length `m`, a factor of length `m` admitting **two different left extensions**.

This complements `ForMathlib.Combinatorics.SubwordComplexity`, which proves the *finite-window*
form (low complexity on `[0, L)` forces a long periodic factor).  Here the window is all of `ℕ`,
the alphabet is finite, and the conclusion is the left-special factor rather than a period.

## Main results

* `IsEventuallyPeriodic` — `∃ N p, 0 < p ∧ ∀ k ≥ N, u (k + p) = u k`.
* `pComplexity u k` — the number of distinct length-`k` factors of `u` occurring anywhere.
* `isEventuallyPeriodic_of_rightDeterministic` — if the length-`k` factor always determines the
  next letter, the word is eventually periodic (pigeonhole + forward propagation).
* `pComplexity_lt_succ_of_not_isEventuallyPeriodic` — hence `p_u(k) < p_u(k+1)` for every `k`
  when `u` is not eventually periodic (Morse–Hedlund's floor `p_u(k) ≥ k + 1`).
* `exists_leftSpecial_of_not_isEventuallyPeriodic` — the main result: for every `m` there are
  positions `i, j` with `u i ≠ u j` but `u (i+1+t) = u (j+1+t)` for all `t < m`.

## Proof

Two counting steps, in opposite directions:

1. *Right extensions.* Dropping the **last** letter maps length-`(k+1)` factors **onto** the
   length-`k` factors, so `p_u` is non-decreasing; at a plateau `p_u(k+1) = p_u(k)` the map is
   also injective, i.e. the length-`k` factor determines the next letter.  Pigeonhole on the
   infinitely many positions then yields two positions carrying the same length-`k` factor, and
   determinism propagates the offset forward forever: `u` is eventually periodic.
2. *Left extensions.* Dropping the **first** letter maps length-`(m+1)` factors **into** the
   length-`m` factors, and it is injective as soon as no length-`m` factor is left-special.
   That would force `p_u(m+1) ≤ p_u(m)`, contradicting step 1.

## References

* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866.
* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, 2012: Theorem A.3 (the complexity floor `p(m) ≥ m + 1`) and the proof of Theorem 3.1,
  which consumes exactly the left-special conclusion proved here.
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-- A word `u : ℕ → α` is **eventually periodic**: there are a preperiod `N` and a period `p > 0`
with `u (k + p) = u k` for every `k ≥ N`. -/
def IsEventuallyPeriodic (u : ℕ → α) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ k, N ≤ k → u (k + p) = u k

/-- The set of length-`k` factors occurring somewhere in the infinite word `u`. -/
def factorSet (u : ℕ → α) (k : ℕ) : Set (Fin k → α) := Set.range (factor u k)

@[simp]
lemma mem_factorSet {u : ℕ → α} {k : ℕ} {v : Fin k → α} :
    v ∈ factorSet u k ↔ ∃ i, factor u k i = v := Iff.rfl

/-- **Right-determinism at level `k`**: the length-`k` factor determines the letter following
it. -/
def RightDeterministic (u : ℕ → α) (k : ℕ) : Prop :=
  ∀ i j : ℕ, (∀ t, t < k → u (i + t) = u (j + t)) → u (i + k) = u (j + k)

/-- Dropping the **first** letter of a length-`(k+1)` factor at `i` yields the length-`k` factor
at `i + 1`. -/
lemma factor_comp_succ (u : ℕ → α) (k i : ℕ) :
    (factor u (k + 1) i) ∘ Fin.succ = factor u k (i + 1) := by
  funext s
  simp only [Function.comp_apply, factor, Fin.val_succ]
  congr 1
  omega

/-- Determinism at level `k` propagates a repetition of length-`k` factors forward forever. -/
lemma isEventuallyPeriodic_of_factor_eq (u : ℕ → α) {k x y : ℕ} (h : RightDeterministic u k)
    (hlt : x < y) (hfac : factor u k x = factor u k y) : IsEventuallyPeriodic u := by
  have key : ∀ n, u (x + n) = u (y + n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      rcases Nat.lt_or_ge n k with hnk | hnk
      · exact (factor_eq_iff u k x y).mp hfac n hnk
      · have hstep : ∀ t, t < k → u (x + (n - k) + t) = u (y + (n - k) + t) := by
          intro t ht
          have hIH := IH (n - k + t) (by omega)
          rw [← Nat.add_assoc, ← Nat.add_assoc] at hIH
          exact hIH
        have hdet := h (x + (n - k)) (y + (n - k)) hstep
        have ex : x + (n - k) + k = x + n := by omega
        have ey : y + (n - k) + k = y + n := by omega
        rw [ex, ey] at hdet
        exact hdet
  refine ⟨x, y - x, by omega, ?_⟩
  intro m hm
  have := key (m - x)
  have ex : x + (m - x) = m := by omega
  have ey : y + (m - x) = m + (y - x) := by omega
  rw [ex, ey] at this
  exact this.symm

section Finite

variable [Finite α]

lemma finite_factorSet (u : ℕ → α) (k : ℕ) : (factorSet u k).Finite := Set.toFinite _

/-- The **subword complexity** `p_u(k)` of an infinite word `u` over a finite alphabet: the
number of distinct length-`k` factors of `u`. -/
noncomputable def pComplexity (u : ℕ → α) (k : ℕ) : ℕ := (factorSet u k).ncard

omit [Finite α] in
/-- Truncating a length-`(k+1)` factor to its first `k` letters maps the length-`(k+1)` factors
**onto** the length-`k` factors. -/
lemma image_factorSet_castSucc (u : ℕ → α) (k : ℕ) :
    (fun v : Fin (k + 1) → α => v ∘ Fin.castSucc) '' factorSet u (k + 1) = factorSet u k := by
  rw [factorSet, factorSet, ← Set.range_comp]
  refine congrArg Set.range ?_
  funext i
  exact (factor_castSucc u k i).symm

/-- Subword complexity is non-decreasing in the factor length. -/
lemma pComplexity_mono (u : ℕ → α) (k : ℕ) : pComplexity u k ≤ pComplexity u (k + 1) := by
  rw [pComplexity, pComplexity, ← image_factorSet_castSucc u k]
  exact Set.ncard_image_le (finite_factorSet u (k + 1))

/-- **A complexity plateau forces determinism.**  If there are as many length-`(k+1)` factors as
length-`k` factors, then the length-`k` factor determines the next letter. -/
lemma rightDeterministic_of_pComplexity_eq (u : ℕ → α) {k : ℕ}
    (h : pComplexity u (k + 1) = pComplexity u k) : RightDeterministic u k := by
  intro i j hij
  have hinj : Set.InjOn (fun v : Fin (k + 1) → α => v ∘ Fin.castSucc) (factorSet u (k + 1)) :=
    Set.injOn_of_ncard_image_eq (by rw [image_factorSet_castSucc u k]; exact h.symm)
      (finite_factorSet u (k + 1))
  have hmi : factor u (k + 1) i ∈ factorSet u (k + 1) := ⟨i, rfl⟩
  have hmj : factor u (k + 1) j ∈ factorSet u (k + 1) := ⟨j, rfl⟩
  have hgij : (factor u (k + 1) i) ∘ Fin.castSucc = (factor u (k + 1) j) ∘ Fin.castSucc := by
    rw [← factor_castSucc, ← factor_castSucc]
    exact (factor_eq_iff u k i j).mpr hij
  have := congrFun (hinj hmi hmj hgij) (Fin.last k)
  simpa [factor, Fin.val_last] using this

/-- **Determinism forces eventual periodicity.**  Pigeonhole on the infinitely many positions
gives two carrying the same length-`k` factor; determinism propagates the offset forever. -/
lemma isEventuallyPeriodic_of_rightDeterministic (u : ℕ → α) {k : ℕ}
    (h : RightDeterministic u k) : IsEventuallyPeriodic u := by
  obtain ⟨x, y, hxy, hfac⟩ := Finite.exists_ne_map_eq_of_infinite (factor u k)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact isEventuallyPeriodic_of_factor_eq u h hlt hfac
  · exact isEventuallyPeriodic_of_factor_eq u h hlt hfac.symm

/-- **Morse–Hedlund's complexity floor.**  A word that is not eventually periodic has strictly
increasing subword complexity; in particular `p_u(k) ≥ k + 1`. -/
theorem pComplexity_lt_succ_of_not_isEventuallyPeriodic {u : ℕ → α}
    (hu : ¬ IsEventuallyPeriodic u) (k : ℕ) : pComplexity u k < pComplexity u (k + 1) :=
  lt_of_le_of_ne (pComplexity_mono u k) fun h =>
    hu (isEventuallyPeriodic_of_rightDeterministic u
      (rightDeterministic_of_pComplexity_eq u h.symm))

/-- **Left-special factors exist at every length.**  If `u` is not eventually periodic then for
every `m` there are positions `i, j` carrying the same length-`m` factor one step later, but
different letters at `i` and `j`: the common factor has two distinct left extensions.

This is the combinatorial input to Bugeaud's Theorem 3.1 (`Bugeaud.theorem_3_1`). -/
theorem exists_leftSpecial_of_not_isEventuallyPeriodic {u : ℕ → α}
    (hu : ¬ IsEventuallyPeriodic u) (m : ℕ) :
    ∃ i j : ℕ, u i ≠ u j ∧ ∀ t, t < m → u (i + 1 + t) = u (j + 1 + t) := by
  by_contra hcon
  -- no left-special factor: the length-`m` factor at `i+1` determines the letter at `i`
  have hdet : ∀ i j : ℕ, (∀ t, t < m → u (i + 1 + t) = u (j + 1 + t)) → u i = u j := by
    intro i j hij
    by_contra hne
    exact hcon ⟨i, j, hne, hij⟩
  -- hence dropping the first letter is injective on length-`(m+1)` factors
  have hinj : Set.InjOn (fun v : Fin (m + 1) → α => v ∘ Fin.succ) (factorSet u (m + 1)) := by
    rintro v ⟨i, rfl⟩ w ⟨j, rfl⟩ hvw
    simp only [factor_comp_succ] at hvw
    have hij : ∀ t, t < m → u (i + 1 + t) = u (j + 1 + t) := (factor_eq_iff u m _ _).mp hvw
    have h0 : u i = u j := hdet i j hij
    funext s
    refine Fin.cases ?_ ?_ s
    · simpa [factor] using h0
    · intro t
      have := congrFun hvw t
      have e : i + 1 + (t : ℕ) = i + ((t : ℕ) + 1) := by omega
      have e' : j + 1 + (t : ℕ) = j + ((t : ℕ) + 1) := by omega
      simpa [factor, Fin.val_succ, e, e'] using this
  have hsub : (fun v : Fin (m + 1) → α => v ∘ Fin.succ) '' factorSet u (m + 1) ⊆ factorSet u m := by
    rintro _ ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i + 1, (factor_comp_succ u m i).symm⟩
  have hle : pComplexity u (m + 1) ≤ pComplexity u m := by
    calc pComplexity u (m + 1)
        = ((fun v : Fin (m + 1) → α => v ∘ Fin.succ) '' factorSet u (m + 1)).ncard :=
          hinj.ncard_image.symm
      _ ≤ pComplexity u m := Set.ncard_le_ncard hsub (finite_factorSet u m)
  exact absurd hle (not_le.mpr (pComplexity_lt_succ_of_not_isEventuallyPeriodic hu m))

end Finite

end ForMathlib.SubwordComplexity
