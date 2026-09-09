/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.CertComplete

/-!
# Every coprime denominator is a cycle, and what a certificate must therefore remove

(plan z32-transform, experiment X‑U, conjecture C‑8)

`Z32/CertComplete.lean` proved one direction of the plan's conjecture **C‑2**: a `P`-periodic point
of the carry relation `q·y_{n+1} = p·yₙ − sₙ` has denominator dividing `p^P − q^P`.  This file
proves the **converse**, and reads off what it costs a certificate.

## The recurrent map in closed form

`Z32.step_unique` says a point of `[0,1)` whose denominator is coprime to `q` has at most one
successor of the same kind.  Here that successor is *named*: over the denominator `D` the map is

```
    a / D  ↦  (p · a · q⁻¹ mod D) / D,
```

multiplication by the unit `p/q` of `ZMod D` (`Z32.cycOrbit`, `Z32.cycOrbit_rec`).  Two things
follow at once, and neither is visible from the relation itself:

* **there are no transients in the recurrent set** — every point with `gcd(D, p·q) = 1` is
  *purely* periodic (`Z32.cycOrbit_periodic`), because multiplication by a unit is a bijection;
* **C‑2 has a converse** — every point of denominator dividing `p^P − q^P` is periodic with period
  dividing `P` (`Z32.cycOrbit_period_dvd`), so with `Z32.cyclePoint_eq_base` the `P`-periodic points
  are *exactly* the `A/(p^P − q^P)`; and every coprime denominator at all is periodic
  (`Z32.exists_periodic_orbit`).

## The price for a certificate

Periodic orbits are dense in `[0,1)`, and every one of them that `U` contains *entirely* is a
point of `Z32.holdSet p q U`.  An unranked certificate needs that set finite
(`Z32.BlockCert.Cert.eq_of_memI_block`), so:

* `Z32.BlockCert.Cert.ok_eq_false_of_infinite_cycles` — **the removed set must be a transversal.**
  If infinitely many distinct points of denominator coprime to `p·q` keep their whole orbit inside
  `U`, then `c.ok = false` at every depth.  Equivalently: `[0,1) ∖ U` must meet all but finitely
  many of the cycles.

That is conjecture C‑8's descriptive half, corrected and turned into a theorem.  C‑8 read "the
record unions remove ε-neighborhoods of the period-`≤P` cycle spine"; what a certificate actually
forces is the opposite arrangement — the *low*-period spine is what may survive (experiment X‑U
finds the record unions keeping exactly the fixed point `0`, and at two of them the 3-cycle
`2/19 → 3/19 → 14/19`, out of 531 292 orbits of period `≤ 14`), while the removed set has to be a
hitting set for all the others.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [L90] J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56**
  (1990), 33–53 — the cycle denominator `p^P − q^P`.
* `plans/plan-z32-transform.html` §7.2 conjecture C‑8, §8 experiment X‑U, target T6;
  `plans/note-z32transform-XU.html`; data `Z32/data/transform/union_autopsy.txt`.
-/

namespace Z32

variable {p q : ℕ}

/-! ## The orbit of a coprime denominator -/

/-- The orbit of `a / D` under the recurrent map, in closed form: multiplication by `p·q⁻¹` in
`ZMod D`.  Meaningful when `Nat.Coprime D (p * q)`; for other `D` the value is junk. -/
noncomputable def cycOrbit (p q D a : ℕ) (n : ℕ) : ℝ :=
  (((((p : ZMod D) * (q : ZMod D)⁻¹) ^ n * (a : ZMod D)).val : ℕ) : ℝ) / (D : ℝ)

theorem cycOrbit_nonneg (p q D a n : ℕ) : 0 ≤ cycOrbit p q D a n := by
  unfold cycOrbit
  positivity

theorem cycOrbit_lt_one {D : ℕ} (hD : 0 < D) (p q a n : ℕ) : cycOrbit p q D a n < 1 := by
  have : NeZero D := ⟨hD.ne'⟩
  unfold cycOrbit
  rw [div_lt_one (by exact_mod_cast hD)]
  exact_mod_cast ZMod.val_lt _

theorem cycOrbit_zero {D a : ℕ} (hD : 0 < D) (haD : a < D) (p q : ℕ) :
    cycOrbit p q D a 0 = (a : ℝ) / (D : ℝ) := by
  have : NeZero D := ⟨hD.ne'⟩
  unfold cycOrbit
  rw [pow_zero, one_mul, ZMod.val_natCast_of_lt haD]

/-- **The recursion.**  `cycOrbit` really is an orbit of the carry relation: there are integer
carries `w n` with `q · y (n+1) = p · y n − w n`.

The reason is one line in `ZMod D`: `q · (p·q⁻¹)^{n+1} · a = p · (p·q⁻¹)^n · a`, because
`q · q⁻¹ = 1` when `q` and `D` are coprime; so `D` divides `p·(uₙ) − q·(u_{n+1})` over `ℤ`. -/
theorem cycOrbit_rec {D : ℕ} (hD : 0 < D) (hcop : Nat.Coprime D (p * q)) (a : ℕ) :
    ∃ w : ℕ → ℤ, ∀ n, (q : ℝ) * cycOrbit p q D a (n + 1)
      = (p : ℝ) * cycOrbit p q D a n - (w n : ℝ) := by
  have : NeZero D := ⟨hD.ne'⟩
  have hqc : Nat.Coprime q D := (Nat.Coprime.coprime_dvd_right (dvd_mul_left q p) hcop).symm
  have hqq : (q : ZMod D) * (q : ZMod D)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqc
  set c : ZMod D := (p : ZMod D) * (q : ZMod D)⁻¹ with hc
  -- the key congruence, in `ZMod D`
  have key : ∀ n : ℕ, ((q * (c ^ (n + 1) * (a : ZMod D)).val : ℕ) : ZMod D)
      = ((p * (c ^ n * (a : ZMod D)).val : ℕ) : ZMod D) := by
    intro n
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, pow_succ, hc]
    calc (q : ZMod D) * (c ^ n * c * (a : ZMod D))
        = ((q : ZMod D) * (q : ZMod D)⁻¹) * ((p : ZMod D) * (c ^ n * (a : ZMod D))) := by
          rw [hc]; ring
      _ = (p : ZMod D) * (c ^ n * (a : ZMod D)) := by rw [hqq, one_mul]
  have hdvd : ∀ n : ℕ, (D : ℤ) ∣
      ((p * (c ^ n * (a : ZMod D)).val : ℕ) : ℤ) - ((q * (c ^ (n + 1) * (a : ZMod D)).val : ℕ) : ℤ) := by
    intro n
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    rw [show (((p * (c ^ n * (a : ZMod D)).val : ℕ) : ZMod D)) = _ from (key n).symm]
    ring
  choose W hW using hdvd
  refine ⟨W, fun n => ?_⟩
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have := hW n
  have hR : ((p : ℝ) * ((c ^ n * (a : ZMod D)).val : ℕ)) - ((q : ℝ) * ((c ^ (n + 1) * (a : ZMod D)).val : ℕ))
      = (D : ℝ) * (W n : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this
    linarith [this]
  unfold cycOrbit
  field_simp
  linarith [hR]

/-- **No transients.**  Multiplication by a unit is a bijection, so the orbit of a point whose
denominator is coprime to `p·q` is *purely* periodic. -/
theorem cycOrbit_periodic {D : ℕ} (hD : 0 < D) (hcop : Nat.Coprime D (p * q)) (a : ℕ) :
    ∃ T : ℕ, 0 < T ∧ ∀ n, cycOrbit p q D a (n + T) = cycOrbit p q D a n := by
  have : NeZero D := ⟨hD.ne'⟩
  have hqc : Nat.Coprime q D := (Nat.Coprime.coprime_dvd_right (dvd_mul_left q p) hcop).symm
  have hpc : Nat.Coprime p D := (Nat.Coprime.coprime_dvd_right (dvd_mul_right p q) hcop).symm
  have hqq : (q : ZMod D) * (q : ZMod D)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqc
  have hpp : (p : ZMod D) * (p : ZMod D)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one p hpc
  set c : ZMod D := (p : ZMod D) * (q : ZMod D)⁻¹ with hc
  have hunit : IsUnit c := by
    refine IsUnit.of_mul_eq_one ((p : ZMod D)⁻¹ * (q : ZMod D)) ?_
    calc c * ((p : ZMod D)⁻¹ * (q : ZMod D))
        = ((p : ZMod D) * (p : ZMod D)⁻¹) * ((q : ZMod D) * (q : ZMod D)⁻¹) := by rw [hc]; ring
      _ = 1 := by rw [hpp, hqq, one_mul]
  set u : (ZMod D)ˣ := hunit.unit with hu
  refine ⟨orderOf u, orderOf_pos u, fun n => ?_⟩
  have hcu : ((u : (ZMod D)ˣ) : ZMod D) = c := hunit.unit_spec
  have hone : c ^ orderOf u = 1 := by
    have h1 : (u : (ZMod D)ˣ) ^ orderOf u = 1 := pow_orderOf_eq_one u
    have h2 := congrArg (fun z : (ZMod D)ˣ => ((z : ZMod D))) h1
    rw [Units.val_pow_eq_pow_val, hcu, Units.val_one] at h2
    exact h2
  unfold cycOrbit
  rw [← hc, pow_add, hone, mul_one]

/-- **The converse of C‑2.**  Every point `a/D` of `[0,1)` with `gcd(D, p·q) = 1` lies on a
periodic orbit of the carry relation, all of whose points have denominator dividing `D`. -/
theorem exists_periodic_orbit {D a : ℕ} (hD : 0 < D) (hcop : Nat.Coprime D (p * q)) (haD : a < D) :
    ∃ (y : ℕ → ℝ) (w : ℕ → ℤ) (T : ℕ), 0 < T ∧ y 0 = (a : ℝ) / (D : ℝ) ∧
      (∀ n, 0 ≤ y n) ∧ (∀ n, y n < 1) ∧ (∀ n, y (n + T) = y n) ∧
      (∀ n, HasDenom D (y n)) ∧
      (∀ n, (q : ℝ) * y (n + 1) = (p : ℝ) * y n - (w n : ℝ)) := by
  obtain ⟨w, hw⟩ := cycOrbit_rec hD hcop a
  obtain ⟨T, hT, hper⟩ := cycOrbit_periodic hD hcop a
  refine ⟨cycOrbit p q D a, w, T, hT, cycOrbit_zero hD haD p q, fun n => cycOrbit_nonneg p q D a n,
    fun n => cycOrbit_lt_one hD p q a n, hper, fun n => ?_, hw⟩
  refine ⟨(((((p : ZMod D) * (q : ZMod D)⁻¹) ^ n * (a : ZMod D)).val : ℕ) : ℤ), ?_⟩
  unfold cycOrbit
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

/-- **The converse of C‑2, in its exact form.**  If `D` divides `p^P − q^P` then every point
`a/D` is periodic with period dividing `P`.  With `Z32.cyclePoint_eq_base` (the direction M4
proved) this says: the `P`-periodic points of the carry relation are *exactly* the `A/(p^P−q^P)`. -/
theorem cycOrbit_period_dvd {D a P : ℕ} (hD : 0 < D) (hcop : Nat.Coprime p q)
    (hdvd : (D : ℤ) ∣ (p : ℤ) ^ P - (q : ℤ) ^ P) (n : ℕ) :
    cycOrbit p q D a (n + P) = cycOrbit p q D a n := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp
  have : NeZero D := ⟨hD.ne'⟩
  -- `D` is automatically coprime to `q`: a common prime would divide `p^P` too
  have hqD : Nat.Coprime q D := by
    have hg1 : (Nat.gcd q D : ℤ) ∣ (q : ℤ) ^ P :=
      dvd_pow (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q D)) hP.ne'
    have hg2 : (Nat.gcd q D : ℤ) ∣ (p : ℤ) ^ P - (q : ℤ) ^ P :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q D)) hdvd
    have hg4 : Nat.gcd q D ∣ p ^ P := by
      have hg3 : (Nat.gcd q D : ℤ) ∣ (p : ℤ) ^ P := by simpa using dvd_add hg2 hg1
      exact_mod_cast hg3
    have hcp : Nat.Coprime q (p ^ P) := Nat.Coprime.pow_right P hcop.symm
    have hdd : Nat.gcd q D ∣ Nat.gcd q (p ^ P) := Nat.dvd_gcd (Nat.gcd_dvd_left q D) hg4
    rw [hcp] at hdd
    exact Nat.eq_one_of_dvd_one hdd
  have hqq : (q : ZMod D) * (q : ZMod D)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqD
  have hpq : ((p : ZMod D)) ^ P = ((q : ZMod D)) ^ P := by
    have h0 : (((p : ℤ) ^ P - (q : ℤ) ^ P : ℤ) : ZMod D) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr hdvd
    push_cast at h0
    linear_combination h0
  have hone : ((p : ZMod D) * (q : ZMod D)⁻¹) ^ P = 1 := by
    rw [mul_pow, hpq, ← mul_pow, hqq, one_pow]
  unfold cycOrbit
  rw [pow_add, hone, mul_one]

/-! ## The two cycles the largeness records keep

Experiment X‑U runs the census of all 531 292 orbits of period `≤ 14` at base `3/2` against the
four largeness records.  Every record breaks all of them but one or two, and the survivors are
these: the fixed point `0`, and — at the `43/60` and `89/120` records — one 3-cycle. -/

/-- The 3-cycle `2/19 → 3/19 → 14/19` of the carry relation at `3/2`, with carry word `0, -1, 2`.
It is the only cycle of period `≤ 14` other than the fixed point `0` that survives inside the
`43/60` and `89/120` largeness records. -/
theorem carry_cycle_nineteen :
    (2 : ℝ) * (3 / 19) = 3 * (2 / 19) - (0 : ℤ) ∧
    (2 : ℝ) * (14 / 19) = 3 * (3 / 19) - (-1 : ℤ) ∧
    (2 : ℝ) * (2 / 19) = 3 * (14 / 19) - (2 : ℤ) := by
  norm_num

namespace BlockCert

/-- **Cycle transversal.**  An unranked certificate breaks all but finitely many cycles: if
infinitely many distinct points of denominator coprime to `p·q` keep their whole orbit inside `U`,
the certificate check is `false` at every depth.

This is the corrected, proved form of conjecture C‑8's descriptive half. -/
theorem Cert.ok_eq_false_of_infinite_cycles {c : Cert} (hst : c.strata = [])
    {D A : ℕ → ℕ} (hD : ∀ j, 0 < D j) (hcop : ∀ j, Nat.Coprime (D j) (c.p * c.q))
    (hA : ∀ j, A j < D j)
    (hinj : Function.Injective fun j => ((A j : ℝ) / (D j : ℝ)))
    (hmem : ∀ j n, memL c.D c.closed c.U (cycOrbit c.p c.q (D j) (A j) n)) :
    c.ok = false := by
  refine Cert.ok_eq_false_of_infinite_hold hst (z := fun j => (A j : ℝ) / (D j : ℝ)) hinj ?_
  intro j
  obtain ⟨w, hw⟩ := cycOrbit_rec (hD j) (hcop j) (A j)
  exact ⟨cycOrbit c.p c.q (D j) (A j), w, cycOrbit_zero (hD j) (hA j) c.p c.q,
    fun n => cycOrbit_nonneg _ _ _ _ n, fun n => cycOrbit_lt_one (hD j) _ _ _ n,
    fun n => hmem j n, hw⟩

end BlockCert

end Z32
