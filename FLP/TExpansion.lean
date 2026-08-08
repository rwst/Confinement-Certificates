/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# `T`-expansion injectivity (FLP95, Lemma 2.2, injectivity half)

The `T`-map `T(g) = ⌈(pg+a)/q⌉` produces, from a starting integer `g`, a **symbol stream**
`(i_{g₀}, i_{g₁}, …)` where `gₙ = Tⁿ(g)` and `i` is the ceiling defect `iSym` of `FLP.Basic`.
The Flatto–Lagarias–Pollington argument needs only the *injectivity* half of their Lemma 2.2:

> **distinct starting integers have distinct `T`-symbol streams.**

This is the combinatorial engine behind Theorem 3.2 (`FLP.ZEmpty`): two would-be `Z`-numbers
`ξ' < ξ''` in the same trapped orbit share their entire `T`-symbol stream (their `θ`-orbits
coincide, hence their `f`-symbols, hence — since `σ(j) ≡ -pj-a` is injective mod `q` — their
`T`-symbols), so by this theorem `⌊ξ'⌋ = ⌊ξ''⌋`, contradicting `ξ'' - ξ' ∈ ℤ_{>0}`.

## Proof (`plan-FLT.html` §3.4)

The whole content is one monotone induction.  With `g ≤ g'` sharing their first `k+1` symbols,
`q^{k+1} ∣ g' - g` (`dvd_sub_of_prefix`):

* the first symbol pins `g ≡ g' (mod q)` (`iSym` determines `g mod q` because `p` is a unit
  mod `q`), so `g' = g + q·d`;
* the shift identity `T(g + qd) = T(g) + pd` (`FLP.TMap_add_qmul`) turns the tail into the same
  problem for `T(g) ≤ T(g')` with `T(g') - T(g) = p·d`; the induction hypothesis gives
  `q^k ∣ p·d`, and `gcd(p, q) = 1` upgrades this to `q^k ∣ d`, whence `q^{k+1} ∣ q·d = g' - g`.

Choosing `k` with `q^{k+1} > g' - g` forces `g = g'` (`eq_of_Tsym_eq`).  No bijection counting,
no "each string occurs exactly once".

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Lemma 2.2.
-/

namespace FLP

variable {p q a : ℕ}

/-- The `n`-th **`T`-symbol** of `g`: the ceiling defect `i_{gₙ}` of `gₙ = Tⁿ(g)`. -/
def Tsym (p q a g n : ℕ) : ℕ := iSym p q a ((TMap p q a)^[n] g)

theorem Tsym_zero (g : ℕ) : Tsym p q a g 0 = iSym p q a g := rfl

/-- The stream shifts under `T`: the `(n+1)`-th symbol of `g` is the `n`-th symbol of `T(g)`. -/
theorem Tsym_succ (g n : ℕ) : Tsym p q a g (n + 1) = Tsym p q a (TMap p q a g) n := by
  unfold Tsym
  rw [Function.iterate_succ_apply]

/-- The first symbol pins `g` modulo `q`: equal `iSym` and `g ≤ g'` give `q ∣ g' - g`
(because the symbol `i_g ≡ -(pg+a)` and `p` is a unit mod `q`). -/
theorem dvd_sub_of_iSym_eq (hq : 0 < q) (hcop : Nat.Coprime p q) {g g' : ℕ} (hle : g ≤ g')
    (h : iSym p q a g = iSym p q a g') : q ∣ g' - g := by
  -- `pg + a + i_g ≡ 0` and `pg' + a + i_{g'} ≡ 0` with `i_g = i_{g'}` give `p·g ≡ p·g' [MOD q]`.
  have e1 : (p * g + a + iSym p q a g) % q = 0 := iSym_add_modEq hq
  have e2 : (p * g' + a + iSym p q a g') % q = 0 := iSym_add_modEq hq
  rw [← h] at e2
  have hpg : p * g ≡ p * g' [MOD q] := by
    have : p * g + a + iSym p q a g ≡ p * g' + a + iSym p q a g [MOD q] := by
      unfold Nat.ModEq; rw [e1, e2]
    exact (Nat.ModEq.add_right_cancel' _ (Nat.ModEq.add_right_cancel' _ this))
  have hg : g ≡ g' [MOD q] := hpg.cancel_left_of_coprime hcop.symm
  exact (Nat.modEq_iff_dvd' hle).mp hg

/-- **Prefix lemma** (monotone form): if `g ≤ g'` share their first `k+1` `T`-symbols, then
`q^{k+1} ∣ g' - g`.  The heart of Lemma 2.2. -/
theorem dvd_sub_of_prefix (hq : 0 < q) (hcop : Nat.Coprime p q) :
    ∀ (k g g' : ℕ), g ≤ g' → (∀ n ≤ k, Tsym p q a g n = Tsym p q a g' n) →
      q ^ (k + 1) ∣ g' - g := by
  intro k
  induction k with
  | zero =>
    intro g g' hle h
    simpa using dvd_sub_of_iSym_eq hq hcop hle (by simpa [Tsym_zero] using h 0 (le_refl 0))
  | succ k ih =>
    intro g g' hle h
    -- first symbol ⟹ `q ∣ g' - g`, write `g' = g + q·d`
    have hqd : q ∣ g' - g :=
      dvd_sub_of_iSym_eq hq hcop hle (by simpa [Tsym_zero] using h 0 (Nat.zero_le _))
    obtain ⟨d, hd⟩ := hqd
    have hg' : g' = g + q * d := by omega
    -- tail: `T(g) ≤ T(g')` and `T(g') - T(g) = p·d`
    have hT : TMap p q a g' = TMap p q a g + p * d := by
      rw [hg', TMap_add_qmul hq]
    have hTle : TMap p q a g ≤ TMap p q a g' := by rw [hT]; exact Nat.le_add_right _ _
    have htail : ∀ n ≤ k, Tsym p q a (TMap p q a g) n = Tsym p q a (TMap p q a g') n := by
      intro n hn
      rw [← Tsym_succ, ← Tsym_succ]
      exact h (n + 1) (by omega)
    have hdvd : q ^ (k + 1) ∣ (TMap p q a g' - TMap p q a g) := ih _ _ hTle htail
    rw [hT, Nat.add_sub_cancel_left] at hdvd
    -- `q^{k+1} ∣ p·d`, coprimality ⟹ `q^{k+1} ∣ d`, hence `q^{k+2} ∣ q·d = g' - g`
    have hdvd' : q ^ (k + 1) ∣ d := (Nat.Coprime.pow_left _ hcop.symm).dvd_of_dvd_mul_left hdvd
    obtain ⟨e, he⟩ := hdvd'
    refine ⟨e, ?_⟩
    rw [hg'] at *
    rw [Nat.add_sub_cancel_left, he]
    ring

/-- **`T`-expansion injectivity** (FLP95 Lemma 2.2, injectivity half): distinct starting
integers have distinct `T`-symbol streams.  Stated in the contrapositive form consumed by
`FLP.ZEmpty`: equal streams force equal starting integers. -/
theorem eq_of_Tsym_eq (hq : 2 ≤ q) (hcop : Nat.Coprime p q) {g g' : ℕ}
    (h : ∀ n, Tsym p q a g n = Tsym p q a g' n) : g = g' := by
  have hq0 : 0 < q := by omega
  wlog hle : g ≤ g' generalizing g g'
  · exact (this (fun n => (h n).symm) (le_of_lt (not_le.mp hle))).symm
  by_contra hne
  set D := g' - g with hD
  have hDpos : 0 < D := by omega
  have hdvd : q ^ (D + 1) ∣ D :=
    dvd_sub_of_prefix hq0 hcop D g g' hle (fun n _ => h n)
  have hgt : D < q ^ (D + 1) :=
    calc D < D + 1 := Nat.lt_succ_self D
      _ < 2 ^ (D + 1) := Nat.lt_two_pow_self
      _ ≤ q ^ (D + 1) := Nat.pow_le_pow_left hq (D + 1)
  exact absurd (Nat.le_of_dvd hDpos hdvd) (not_le.mpr hgt)

end FLP
