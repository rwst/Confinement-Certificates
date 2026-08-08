/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Common

/-!
# The finite Morse–Hedlund complexity floor

The **finite-word Morse–Hedlund lemma** in the form needed by the digit-block
program [A4+]: a finite word of low subword complexity contains a long periodic
factor.  This is milestone **M-6** of [A4+] and the combinatorial input to the
Morse–Hedlund floor `p_{3^m}(n) ≥ n+1` (Theorem B3, milestone M-7).

## Statement

A word is read as a function `u : ℕ → α` on the window `[0, L)`.  For `k ≤ L`,
the length-`k` factor at position `i` is the tuple
`factor u k i = (u i, u (i+1), …, u (i+k-1))`, and `subwordComplexity u L k`
counts the distinct length-`k` factors occurring in the window.  The main result
is

* `finite_morse_hedlund` — if `1 ≤ n`, `3 * n ≤ L`, and
  `subwordComplexity u L n ≤ n`, then there are `a` and `1 ≤ p ≤ n` such that `u`
  has period `p` on the factor `[a, a + (L - 2n))`: low complexity forces a long
  periodic factor.

## Proof route: determinism-propagation, not Fine–Wilf

The classical *infinite* Morse–Hedlund theorem, and the [CdL00] special-factor
route that gate G3 of the plan [A4+ §4] anticipated, both pass through Fine–Wilf.
This file takes a self-contained **determinism-propagation** route that needs
neither Fine–Wilf nor the special-factor machinery:

1. On the fixed window `S = [0, L - n]`, the complexity `Ccount u S ·` is
   non-decreasing (`Ccount_mono`: dropping the last letter of a length-`(k+1)`
   factor is a surjection onto the length-`k` factors).
2. Since `Ccount u S 0 = 1` and `Ccount u S n ≤ n`, complexity cannot strictly
   increase `n` times, so there is a **plateau** level `k < n` with
   `Ccount u S k = Ccount u S (k + 1)`.
3. A plateau forces **right-determinism** at level `k` (`det_of_Ccount_eq`, via
   `Finset.injOn_of_card_image_eq`): two positions carrying the same length-`k`
   factor carry the same next letter.
4. Pigeonhole over the first `Ccount u S k + 1` positions yields two equal
   length-`k` factors at a small offset `p ≤ n`, and determinism propagates the
   period-`p` relation `u t = u (t + p)` across the window (`periodic_extend`).

No arithmetic of `3^m` enters — the file is pure word combinatorics, footprint
std3 (ForMathlib-strict: sorry-free, no cited axioms).

## References

* [A4+] `plan-A4+.html` (this repository, 2026-07): §3.3 (Theorem B3), §4 (gate
  G3), §5.2 (this file).
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60**
  (1938), 815–866.  (The classical infinite complexity dichotomy.)
* [CdL00] A. Carpi, A. de Luca, *Special factors, periodicity, and an
  application to Sturmian words*, Acta Inform. **36** (2000), 983–1006.  (The
  special-factor route this proof sidesteps.)
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-- The length-`k` **factor** of the word `u : ℕ → α` starting at position `i`:
the tuple `(u i, u (i+1), …, u (i+k-1))`, indexed by `Fin k`. -/
def factor (u : ℕ → α) (k i : ℕ) : Fin k → α := fun s => u (i + s)

/-- The number of distinct length-`k` factors of `u` occurring at the positions
of `S` — the subword complexity restricted to the position set `S`. -/
def Ccount [DecidableEq α] (u : ℕ → α) (S : Finset ℕ) (k : ℕ) : ℕ :=
  (S.image (factor u k)).card

/-- The **subword complexity** `p_u(k)` of `u` on the window `[0, len)`: the
number of distinct length-`k` factors occurring at the `len - k + 1` positions
`0, 1, …, len - k`. -/
def subwordComplexity [DecidableEq α] (u : ℕ → α) (len k : ℕ) : ℕ :=
  Ccount u (Finset.range (len - k + 1)) k

/-- Two length-`k` factors are equal iff the words agree on the length-`k`
window: `factor u k i = factor u k i' ↔ ∀ s < k, u (i+s) = u (i'+s)`. -/
lemma factor_eq_iff (u : ℕ → α) (k i i' : ℕ) :
    factor u k i = factor u k i' ↔ ∀ s, s < k → u (i + s) = u (i' + s) := by
  constructor
  · intro h s hs
    have := congrFun h ⟨s, hs⟩
    simpa [factor] using this
  · intro h
    funext s
    simpa [factor] using h s.val s.isLt

/-- Dropping the last letter of the length-`(k+1)` factor yields the length-`k`
factor: `factor u k i = factor u (k+1) i ∘ Fin.castSucc`. -/
lemma factor_castSucc (u : ℕ → α) (k i : ℕ) :
    factor u k i = (factor u (k + 1) i) ∘ Fin.castSucc := by
  funext s
  simp [factor, Fin.val_castSucc]

/-- The set of length-`k` factors on `S` is the set of length-`(k+1)` factors on
`S` truncated to their first `k` coordinates. -/
lemma image_factor_castSucc [DecidableEq α] (u : ℕ → α) (k : ℕ) (S : Finset ℕ) :
    (S.image (factor u (k + 1))).image (fun v : Fin (k + 1) → α => v ∘ Fin.castSucc)
      = S.image (factor u k) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact (factor_castSucc u k i).symm

/-- Subword complexity on a fixed position set is **non-decreasing** in the
factor length. -/
lemma Ccount_mono [DecidableEq α] (u : ℕ → α) (k : ℕ) (S : Finset ℕ) :
    Ccount u S k ≤ Ccount u S (k + 1) := by
  rw [Ccount, Ccount, ← image_factor_castSucc u k S]
  exact Finset.card_image_le

/-- **Unique right-extension at a complexity plateau (determinism).**  If the
numbers of length-`k` and length-`(k+1)` factors on `S` agree, then any two
positions of `S` carrying the same length-`k` factor also carry the same next
letter. -/
lemma det_of_Ccount_eq [DecidableEq α] (u : ℕ → α) (k : ℕ) (S : Finset ℕ)
    (hC : Ccount u S k = Ccount u S (k + 1))
    {i i' : ℕ} (hi : i ∈ S) (hi' : i' ∈ S)
    (hfac : factor u k i = factor u k i') :
    u (i + k) = u (i' + k) := by
  set X := S.image (factor u (k + 1)) with hX
  have hcard : (X.image (fun v : Fin (k + 1) → α => v ∘ Fin.castSucc)).card = X.card := by
    rw [image_factor_castSucc u k S]; exact hC
  have hinj := Finset.injOn_of_card_image_eq hcard
  have hgi : (factor u (k + 1) i) ∘ Fin.castSucc = (factor u (k + 1) i') ∘ Fin.castSucc := by
    rw [← factor_castSucc, ← factor_castSucc]; exact hfac
  have hmem_i : factor u (k + 1) i ∈ X := Finset.mem_image_of_mem _ hi
  have hmem_i' : factor u (k + 1) i' ∈ X := Finset.mem_image_of_mem _ hi'
  have heq := hinj (Finset.mem_coe.mpr hmem_i) (Finset.mem_coe.mpr hmem_i') hgi
  have := congrFun heq (Fin.last k)
  simpa [factor, Fin.val_last] using this

/-- **Periodicity propagation.**  Given right-determinism on `[0, bound]` at
level `k` and a length-`k` repetition of offset `p` starting at `i₀`, the
period-`p` relation `u t = u (t + p)` propagates from `i₀` up to depth
`bound + k`.  This is the engine that turns a local repetition into a long
periodic factor. -/
lemma periodic_extend (u : ℕ → α) {k p bound i₀ : ℕ} (hp : 1 ≤ p)
    (Det : ∀ i i', i ≤ bound → i' ≤ bound →
      (∀ s, s < k → u (i + s) = u (i' + s)) → u (i + k) = u (i' + k))
    (hbase : ∀ s, s < k → u (i₀ + s) = u (i₀ + p + s)) :
    ∀ t, i₀ ≤ t → t + p ≤ bound + k → u t = u (t + p) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht0 htb
    by_cases hlt : t < i₀ + k
    · -- base region: `t = i₀ + s` with `s < k`, given by the shared factor
      have hs : t - i₀ < k := by omega
      have hb := hbase (t - i₀) hs
      have e1 : i₀ + (t - i₀) = t := by omega
      have e2 : i₀ + p + (t - i₀) = t + p := by omega
      rw [e1, e2] at hb
      exact hb
    · -- step region: apply determinism at `t - k` and `t - k + p`
      have hge : i₀ + k ≤ t := by omega
      have key : ∀ s, s < k → u ((t - k) + s) = u ((t - k + p) + s) := by
        intro s hs
        have hih := IH (t - k + s) (by omega) (by omega) (by omega)
        have e3 : (t - k + s) + p = (t - k + p) + s := by omega
        rw [e3] at hih
        exact hih
      have hdet := Det (t - k) (t - k + p) (by omega) (by omega) key
      have e4 : (t - k) + k = t := by omega
      have e5 : (t - k + p) + k = t + p := by omega
      rw [e4, e5] at hdet
      exact hdet

/-- **The finite Morse–Hedlund floor (the G3-frozen form of [A4+ §4]).**  If a
word `u`, read on the window `[0, L)` with `L ≥ 3n`, has at most `n` distinct
length-`n` factors, then `u` contains a factor of length `L - 2n` that is
`p`-periodic for some `1 ≤ p ≤ n`.

Equivalently: *low subword complexity forces a long periodic factor.*  Its
contrapositive is the Morse–Hedlund floor `p_u(n) ≥ n + 1` used by Theorem B3. -/
theorem finite_morse_hedlund [DecidableEq α] (u : ℕ → α) {n L : ℕ}
    (hn : 1 ≤ n) (hL : 3 * n ≤ L)
    (hcomplex : subwordComplexity u L n ≤ n) :
    ∃ a p : ℕ, 1 ≤ p ∧ p ≤ n ∧ a + (L - 2 * n) ≤ L ∧
      ∀ t, a ≤ t → t + p < a + (L - 2 * n) → u t = u (t + p) := by
  -- Work on the fixed window `S = [0, L - n]`.
  set S := Finset.range (L - n + 1) with hS
  have memS : ∀ i, i ∈ S ↔ i ≤ L - n := by
    intro i; rw [hS, Finset.mem_range]; omega
  have hSne : S.Nonempty := ⟨0, by rw [memS]; omega⟩
  have hCn : Ccount u S n ≤ n := by rw [hS]; exact hcomplex
  -- `Ccount u S 0 = 1`: there is exactly one empty factor.
  have hC0 : Ccount u S 0 = 1 := by
    have hle : Ccount u S 0 ≤ 1 := by
      rw [Ccount]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨i, _, rfl⟩ := ha
      obtain ⟨j, _, rfl⟩ := hb
      funext s; exact s.elim0
    have hge : 1 ≤ Ccount u S 0 := by
      rw [Ccount]; exact Finset.card_pos.mpr (hSne.image _)
    omega
  have hmono : Monotone (Ccount u S) :=
    monotone_nat_of_le_succ (fun k => Ccount_mono u k S)
  -- Complexity climbs from `1` and stays `≤ n`, so it plateaus below `n`.
  have hplateau : ∃ k, k < n ∧ Ccount u S k = Ccount u S (k + 1) := by
    by_contra hcon
    push Not at hcon
    have hstep : ∀ k, k < n → Ccount u S k + 1 ≤ Ccount u S (k + 1) := by
      intro k hk
      have h1 : Ccount u S k ≤ Ccount u S (k + 1) := hmono (Nat.le_succ k)
      have h2 : Ccount u S k ≠ Ccount u S (k + 1) := hcon k hk
      omega
    have hgrow : ∀ j, j ≤ n → 1 + j ≤ Ccount u S j := by
      intro j
      induction j with
      | zero => intro _; rw [hC0]
      | succ m ih =>
        intro hm
        have := ih (by omega)
        have hs := hstep m (by omega)
        omega
    have := hgrow n (le_refl n)
    omega
  obtain ⟨k, hkn, hCk⟩ := hplateau
  have hCkn : Ccount u S k ≤ n := le_trans (hmono (show k ≤ n by omega)) hCn
  -- Pigeonhole among the first `Ccount u S k + 1` positions: a repetition.
  have hmaps : Set.MapsTo (factor u k) ↑(Finset.range (Ccount u S k + 1))
      ↑(S.image (factor u k)) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_range] at hi
    rw [Finset.mem_coe]
    apply Finset.mem_image_of_mem
    rw [memS]; omega
  have hcardlt : (S.image (factor u k)).card < (Finset.range (Ccount u S k + 1)).card := by
    rw [Finset.card_range]
    show Ccount u S k < Ccount u S k + 1
    exact Nat.lt_succ_self _
  obtain ⟨x, hx, y, hy, hxy, hfacxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt hmaps
  rw [Finset.mem_range] at hx hy
  -- The ordered core: a repetition `a < b` at offset `≤ n` propagates.
  have main : ∀ a b, a < b → b ≤ Ccount u S k → factor u k a = factor u k b →
      ∃ a' p, 1 ≤ p ∧ p ≤ n ∧ a' + (L - 2 * n) ≤ L ∧
        ∀ t, a' ≤ t → t + p < a' + (L - 2 * n) → u t = u (t + p) := by
    intro a b hab hbb hfacab
    have hp1 : 1 ≤ b - a := by omega
    have hbase : ∀ s, s < k → u (a + s) = u (a + (b - a) + s) := by
      intro s hs
      have := (factor_eq_iff u k a b).mp hfacab s hs
      have e : a + (b - a) = b := by omega
      rw [e]; exact this
    have Det : ∀ i i', i ≤ L - n → i' ≤ L - n →
        (∀ s, s < k → u (i + s) = u (i' + s)) → u (i + k) = u (i' + k) := by
      intro i i' hi hi' hs
      apply det_of_Ccount_eq u k S hCk ((memS i).mpr hi) ((memS i').mpr hi')
      exact (factor_eq_iff u k i i').mpr hs
    have hprop := periodic_extend u hp1 Det hbase
    refine ⟨a, b - a, hp1, by omega, by omega, ?_⟩
    intro t ht htlen
    apply hprop t ht
    omega
  rcases Nat.lt_or_ge x y with hlt | hge
  · exact main x y hlt (by omega) hfacxy
  · have hlt' : y < x := lt_of_le_of_ne hge (Ne.symm hxy)
    exact main y x hlt' (by omega) hfacxy.symm

end ForMathlib.SubwordComplexity
