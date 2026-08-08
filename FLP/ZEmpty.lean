/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Decoupling
import FLP.TExpansion
import Mathlib.Tactic

/-!
# Finite survivor set ⟹ empty `Z`-set (FLP95, Theorem 3.2)

> **Theorem 3.2.** If the survivor set `R_{p/q}(s) = S_{p/q, {(p−q)s}}` is finite, then
> `Z_{p/q}(s, s + 1/p) = ∅`.

This is where the two dynamics of `FLP.Decoupling` collide.  Suppose `ξ` were a `Z`-number.
Its fractional coordinates `θₙ` all lie in the survivor set (`FLP.thetaPart_mem` plus the fact
that every tail `θ_{n+m}` also stays trapped), so by finiteness two of them coincide,
`θ_k = θ_{k+l}` with `l ≥ 1` (pigeonhole).  Then:

* the `θ`-orbits from `k` and `k+l` agree forever (`θ_{k+m} = θ_{k+l+m}`);
* hence — via the symbol match `⌊(p/q)θ + α⌋ = i_g` (`FLP.decouple`) — the `T`-symbol streams
  of `g_k` and `g_{k+l}` agree, so `g_k = g_{k+l}` by `FLP.eq_of_Tsym_eq`;
* but then `ξ(p/q)^{k+l} = g_{k+l} + s + θ_{k+l}/q = g_k + s + θ_k/q = ξ(p/q)^k`, contradicting
  `ξ(p/q)^{k+l} = (p/q)^l · ξ(p/q)^k > ξ(p/q)^k` (`p/q > 1`, `ξ > 0`).

Per `plan-FLT.html` §3.3 the argument avoids Theorem 1.1(A) ("at most one `Z`-number per unit
interval"): the decomposition `ξ(p/q)ⁿ = gₙ + s + θₙ/q` makes the final step direct.

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Theorem 3.2.
-/

namespace FLP

open Set

/-- **FLP95 Theorem 3.2**: if the survivor set `S_{p/q, {(p−q)s}}` is finite, then the `Z`-set
`Z_{p/q}(s, s + 1/p)` is empty.  Here `q/p = 1/(p/q)` is the survivor threshold, so
`R_{p/q}(s)` of the paper is exactly `survivors (p/q) {(p−q)s}`. -/
theorem ZSet_eq_empty_of_survivors_finite {p q : ℕ} {s : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hcop : Nat.Coprime p q) (hs : 0 ≤ s)
    (hSfin : (survivors ((p : ℝ) / q) (alphaSym p q s)).Finite) :
    ZSet p q s (1 / p) = ∅ := by
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hβ1 : 1 < (p : ℝ) / q := by
    rw [lt_div_iff₀ hq0]
    have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  rw [Set.eq_empty_iff_forall_notMem]
  intro ξ hmem
  have hξ : 0 < ξ := hmem.1
  -- shift identities for the two orbits
  have theta_shift : ∀ n m,
      (lmo ((p : ℝ) / q) (alphaSym p q s))^[m] (thetaPart p q s ξ n)
        = thetaPart p q s ξ (n + m) := by
    intro n m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih]
        exact ((decouple hq2 hqp hs hξ hmem (n + m)).2.1).symm
  have g_shift : ∀ n m,
      (TMap p q (aSym p q s))^[m] (gPart p q ξ n) = gPart p q ξ (n + m) := by
    intro n m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih]
        exact ((decouple hq2 hqp hs hξ hmem (n + m)).1).symm
  -- each θₙ is a survivor
  have hthr : (1 : ℝ) / ((p : ℝ) / q) = (q : ℝ) / p := one_div_div _ _
  have hmem_surv : ∀ n,
      thetaPart p q s ξ n ∈ survivors ((p : ℝ) / q) (alphaSym p q s) := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [hthr]; exact thetaPart_mem hp hq hmem n
    · intro m
      rw [theta_shift, hthr]
      exact (thetaPart_mem hp hq hmem (n + m)).2
  -- pigeonhole: two coordinates coincide
  haveI : Finite (survivors ((p : ℝ) / q) (alphaSym p q s)) := hSfin.to_subtype
  obtain ⟨k, k', hne, hFeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨thetaPart p q s ξ n, hmem_surv n⟩ :
        survivors ((p : ℝ) / q) (alphaSym p q s)))
  have hθeq : thetaPart p q s ξ k = thetaPart p q s ξ k' := by
    simpa using Subtype.ext_iff.mp hFeq
  -- the impossible coincidence, from the smaller index to the larger
  have main : ∀ a b : ℕ, a < b →
      thetaPart p q s ξ a = thetaPart p q s ξ b → False := by
    intro a b hab hθab
    -- θ-orbits from a and b coincide
    have hθshift : ∀ m, thetaPart p q s ξ (a + m) = thetaPart p q s ξ (b + m) := by
      intro m; rw [← theta_shift a m, ← theta_shift b m, hθab]
    -- g_a = g_b via equal T-symbol streams
    have hg_eq : gPart p q ξ a = gPart p q ξ b := by
      apply eq_of_Tsym_eq (p := p) (q := q) (a := aSym p q s) hq2 hcop
      intro m
      have hsa := (decouple hq2 hqp hs hξ hmem (a + m)).2.2
      have hsb := (decouple hq2 hqp hs hξ hmem (b + m)).2.2
      have hga : Tsym p q (aSym p q s) (gPart p q ξ a) m
          = iSym p q (aSym p q s) (gPart p q ξ (a + m)) := by
        rw [Tsym, g_shift]
      have hgb : Tsym p q (aSym p q s) (gPart p q ξ b) m
          = iSym p q (aSym p q s) (gPart p q ξ (b + m)) := by
        rw [Tsym, g_shift]
      rw [hga, hgb]
      have hZ : (iSym p q (aSym p q s) (gPart p q ξ (a + m)) : ℤ)
          = iSym p q (aSym p q s) (gPart p q ξ (b + m)) := by
        rw [← hsa, ← hsb, hθshift m]
      exact_mod_cast hZ
    -- orbit values collide
    have horb : orbitVal p q ξ a = orbitVal p q ξ b := by
      rw [orbit_decomp hp hq hξ a, orbit_decomp hp hq hξ b, hg_eq, hθab]
    have hlt : orbitVal p q ξ a < orbitVal p q ξ b := by
      rw [orbitVal, orbitVal]
      exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hβ1 hab) hξ
    linarith
  rcases lt_trichotomy k k' with h | h | h
  · exact main k k' h hθeq
  · exact hne h
  · exact main k' k h hθeq.symm

end FLP
