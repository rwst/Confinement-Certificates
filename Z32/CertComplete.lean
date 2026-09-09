/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.BlockCert

/-!
# Completeness of the certificate scheme (plan z32-transform, milestone M4, target T5)

`Z32/BlockCert.lean` proves the certificate scheme **sound**: a valid certificate for `U` forbids
every `ξ ≠ 0` from keeping its whole orbit `{ξ(p/q)ⁿ}` inside `U`.  This file proves the converse
half — what the scheme *can* decide, and what obstructs it — on the class the plan names: sets
whose **hold set** is finite.

## The hold set

`Z32.holdSet p q U` is the set of points of `U` that carry an infinite orbit of the carry relation
`q·y_{n+1} = p·yₙ − sₙ` inside `U`.  It is the model-level survivor set: a certificate's blocks
cover it, and a real orbit confined to `U` runs inside it.

## Main results

* `Z32.holdSet_finite_imp` (**T5(i), completeness**) — if `holdSet p q U` is finite then no `ξ ≠ 0`
  has its orbit confined to `U`, so `U`'s verdict is *empty*: on that class the scheme's answer is
  never "unknown", and the answer is always the one a certificate would give.
* `Z32.isEventuallyPeriodic_of_finite_range` — the engine behind it: an orbit of the carry relation
  in `[0,1)` taking only finitely many values has an eventually periodic carry word.  Two steps:
  a value visited twice is rational with denominator `p^P − q^P` (`Z32.hasDenom_of_return`, the
  plan's conjecture **C‑2** at every base), and a point whose denominator is coprime to `q` has at
  most **one** successor in `[0,1)` whose denominator is coprime to `q` (`Z32.step_unique`), so the
  recurrent part of the dynamics is *deterministic*.
* `Z32.BlockCert.Cert.eq_of_memI_block` (**T5(iii), the obstruction**) — for an *unranked*
  certificate (`strata = []`) two confined orbits that ever share a block are equal.  Hence
  `Z32.BlockCert.Cert.ok_eq_false_of_infinite_hold`: a set with infinitely many hold points admits
  no unranked certificate **at any depth**.
* `Z32.cyclePoint_eq_base` (**C‑2 at every base**) — a `P`-periodic point of the carry relation is
  `A/(p^P − q^P)`; the corpus had `Z32.cycle_point_eq` at `3/2` only.
* `Z32.BlockCert.certTwoCellFifthClosed` and four more closed-convention entries — the certificates
  the corrected picture predicts, one of them for a set this corpus had recorded as refused.

## What the plan asked for, and what is here

T5(i) asks for "a certificate exists at computable depth"; what is proved is the *conclusion* the
certificate would give (`Z_{p/q}(U) = ∅`), on the same class, plus the structure theory that says
which certificate shape can work.  Producing the `Cert` **data** from the finite hold set — the
funnel as an explicit list of integer intervals — is the one step not formalized here; it is
combinatorics of interval lists, not dynamics, and `Z32/gencert.py` does it.

T5(iii) asked for "the closed-convention obstruction is exactly an endpoint-touching cycle".  That
is **false as stated**: the closed `[0,1/5] ∪ [4/5,1]` has the endpoint cycle `1/5 ↔ 4/5` and a
certificate all the same (`certTwoCellFifthClosed`, depth 1), and so does the closed `[Dub08]`
union.  The true obstruction to the *unranked* scheme is an **infinite hold set**, which is what an
endpoint cycle usually produces: at `[0,1/5] ∪ [4/5,1]` the points `(1/5)(2/3)^k` are all held, and
`Z32.BlockCert.Cert.ok_eq_false_of_covers_two_cell` turns the engine's "no certificate to depth 60" into a
theorem.  Ranks are exactly the device that survives an infinite hold set, which is why [Dub08]
needed them.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — the aperiodicity lemma `Z32.not_isEventuallyPeriodic_carry`.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), 951–958 — Corollary 1.2, the ranked entry.
* [L90] J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56**
  (1990), 33–53 — the denominator `p^P − q^P` of a `P`-cycle, here at a general base.
* `plans/plan-z32-transform.html` §5.2 (β2), targets T5, conjectures C‑2 and C‑5;
  `plans/note-z32transform-M4.html`.
-/

namespace Z32

open ForMathlib.SubwordComplexity

variable {p q : ℕ}

/-! ## Scaled points

Everything below turns on one invariant of the carry relation: the **denominator** of a point,
and specifically whether it is coprime to `q`.  `HasDenom D y` says `D·y` is an integer; it is
deliberately not "the" denominator, so that two points can always be put over a common one. -/

/-- `D · y` is an integer. -/
def HasDenom (D : ℕ) (y : ℝ) : Prop := ∃ a : ℤ, (D : ℝ) * y = a

theorem HasDenom.of_dvd {D E : ℕ} {y : ℝ} (hDE : D ∣ E) (h : HasDenom D y) : HasDenom E y := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨k, rfl⟩ := hDE
  exact ⟨k * a, by push_cast; rw [← ha]; ring⟩

/-- A point of the recurrent part: rational with a denominator coprime to `q`.  The whole
completeness argument is the statement that this class is forward-deterministic. -/
def CoprimeDenom (q : ℕ) (y : ℝ) : Prop := ∃ D : ℕ, 0 < D ∧ Nat.Coprime D q ∧ HasDenom D y

/-- **The determinism lemma.**  A point has at most one successor in `[0,1)` whose denominator is
coprime to `q`.

Why: with `u, v, v'` over a common denominator `D` coprime to `q`, the recursion reads
`q·b = p·a − s·D` and `q·c = p·a − s'·D`, so `D ∣ q(b − c)`, hence `D ∣ b − c`; and `b`, `c` both
lie in `[0, D)`.  The `q` admissible carries at a point of `[0,1)` are `q` consecutive integers,
so exactly one of them keeps the denominator coprime to `q` — that is the arithmetic reason the
recurrent dynamics is a *function* and not a relation. -/
theorem step_unique {u v v' : ℝ} {s s' : ℤ}
    (hu : CoprimeDenom q u) (hv : CoprimeDenom q v) (hv' : CoprimeDenom q v')
    (h1 : (q : ℝ) * v = p * u - s) (h2 : (q : ℝ) * v' = p * u - s')
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hv0' : 0 ≤ v') (hv1' : v' < 1) : v = v' := by
  obtain ⟨D₁, hD₁, hc₁, hu'⟩ := hu
  obtain ⟨D₂, hD₂, hc₂, hv''⟩ := hv
  obtain ⟨D₃, hD₃, hc₃, hv'''⟩ := hv'
  set D : ℕ := D₁ * D₂ * D₃ with hDdef
  have hD : 0 < D := by positivity
  have hcop : Nat.Coprime D q := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc₁ hc₂) hc₃
  obtain ⟨a, ha⟩ : HasDenom D u := hu'.of_dvd ⟨D₂ * D₃, by rw [hDdef]; ring⟩
  obtain ⟨b, hb⟩ : HasDenom D v := hv''.of_dvd ⟨D₁ * D₃, by rw [hDdef]; ring⟩
  obtain ⟨c, hc⟩ : HasDenom D v' := hv'''.of_dvd ⟨D₁ * D₂, by rw [hDdef]; ring⟩
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  -- the two scaled recursions
  have e1 : (q : ℝ) * b = p * a - s * D := by
    rw [← hb, ← ha]; linear_combination (D : ℝ) * h1
  have e2 : (q : ℝ) * c = p * a - s' * D := by
    rw [← hc, ← ha]; linear_combination (D : ℝ) * h2
  have e3 : (q : ℤ) * (b - c) = (s' - s) * D := by
    have : (q : ℝ) * ((b : ℝ) - c) = ((s' : ℝ) - s) * D := by linarith
    exact_mod_cast this
  -- `D ∣ b - c`
  have hcopZ : IsCoprime ((D : ℤ)) ((q : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop
  have hdvd : (D : ℤ) ∣ (q : ℤ) * (b - c) := ⟨s' - s, by rw [e3]; ring⟩
  have hdvd' : (D : ℤ) ∣ (b - c) := hcopZ.dvd_of_dvd_mul_left hdvd
  -- both scaled points lie in `[0, D)`
  have hb0 : 0 ≤ b := by
    have : (0 : ℝ) ≤ (b : ℝ) := by rw [← hb]; positivity
    exact_mod_cast this
  have hbD : b < D := by
    have : (b : ℝ) < (D : ℝ) := by rw [← hb]; nlinarith
    exact_mod_cast this
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ (c : ℝ) := by rw [← hc]; positivity
    exact_mod_cast this
  have hcD : c < D := by
    have : (c : ℝ) < (D : ℝ) := by rw [← hc]; nlinarith
    exact_mod_cast this
  have hbc : b = c := by
    obtain ⟨k, hk⟩ := hdvd'
    have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
    have hbD' : b < (D : ℤ) := by exact_mod_cast hbD
    have hcD' : c < (D : ℤ) := by exact_mod_cast hcD
    have hb0' : (0 : ℤ) ≤ b := by exact_mod_cast hb0
    have hc0' : (0 : ℤ) ≤ c := by exact_mod_cast hc0
    rcases lt_trichotomy k 0 with hk0 | rfl | hk0
    · have : (D : ℤ) * k ≤ -(D : ℤ) := by nlinarith
      omega
    · omega
    · have : (D : ℤ) ≤ (D : ℤ) * k := by nlinarith
      omega
  have : (D : ℝ) * v = (D : ℝ) * v' := by rw [hb, hc, hbc]
  exact mul_left_cancel₀ (ne_of_gt hDR) this

/-! ## Iterating the recursion, and the cycle denominator (C‑2 at every base) -/

/-- `qᵏ·y_{n+k} = pᵏ·yₙ − A` for an integer `A`: the carry relation iterated. -/
theorem exists_int_iterate {y : ℕ → ℝ} {w : ℕ → ℤ}
    (hrec : ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n) (n : ℕ) :
    ∀ k : ℕ, ∃ A : ℤ, (q : ℝ) ^ k * y (n + k) = (p : ℝ) ^ k * y n - A := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨(p : ℤ) * A + (q : ℤ) ^ k * w (n + k), ?_⟩
    have h := hrec (n + k)
    have e : n + (k + 1) = (n + k) + 1 := by omega
    rw [e]
    have : (q : ℝ) ^ (k + 1) * y (n + k + 1) = (q : ℝ) ^ k * ((q : ℝ) * y (n + k + 1)) := by ring
    rw [this, h]
    push_cast
    linear_combination (p : ℝ) * hA

/-- `p^P − q^P`, the denominator of a `P`-cycle of the carry relation ([L90] at a general base;
the plan's conjecture **C‑2**). -/
def cycleDenom (p q P : ℕ) : ℕ := p ^ P - q ^ P

theorem cycleDenom_cast (hqp : q ≤ p) (P : ℕ) :
    ((cycleDenom p q P : ℕ) : ℝ) = (p : ℝ) ^ P - (q : ℝ) ^ P := by
  rw [cycleDenom, Nat.cast_sub (Nat.pow_le_pow_left hqp P)]
  push_cast
  ring

theorem cycleDenom_pos (hqp : q < p) {P : ℕ} (hP : 0 < P) : 0 < cycleDenom p q P := by
  have : q ^ P < p ^ P := Nat.pow_lt_pow_left hqp hP.ne'
  rw [cycleDenom]; omega

/-- **The cycle denominator is coprime to `q`** — the fact that makes the recurrent dynamics
deterministic.  Any common divisor of `q` and `p^P − q^P` divides `p^P`, hence divides
`gcd (p^P) q = 1`. -/
theorem cycleDenom_coprime (hcop : Nat.Coprime p q) (hqp : q ≤ p) {P : ℕ} (hP : 0 < P) :
    Nat.Coprime (cycleDenom p q P) q := by
  have hle : q ^ P ≤ p ^ P := Nat.pow_le_pow_left hqp P
  set d : ℕ := Nat.gcd (cycleDenom p q P) q with hd
  have h1 : d ∣ cycleDenom p q P := Nat.gcd_dvd_left _ _
  have h2 : d ∣ q := Nat.gcd_dvd_right _ _
  have h3 : d ∣ q ^ P := h2.trans (dvd_pow_self q hP.ne')
  have h4 : d ∣ p ^ P := by
    have : cycleDenom p q P + q ^ P = p ^ P := by rw [cycleDenom]; omega
    rw [← this]
    exact Nat.dvd_add h1 h3
  have h5 : d ∣ Nat.gcd (p ^ P) q := Nat.dvd_gcd h4 h2
  have h6 : Nat.gcd (p ^ P) q = 1 := Nat.Coprime.pow_left P hcop
  rw [h6] at h5
  exact Nat.eq_one_of_dvd_one h5

/-- **C‑2 at every base**: a point that the orbit returns to is rational with denominator
`p^P − q^P`, `P` the length of the return — and so is every point of the loop.

This is the [L90] rational-cycle shape, proved at an arbitrary coprime base `p > q > 1` (the
corpus had it at `3/2` only, `Z32.cycle_point_eq`), and stated for a *segment* of an orbit rather
than for a periodic sequence, which is the form the completeness proof consumes. -/
theorem hasDenom_of_return (hqp : q < p) {y : ℕ → ℝ} {w : ℕ → ℤ}
    (hrec : ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n)
    {a b m : ℕ} (hab : y a = y b) (ham : a ≤ m) (hmb : m ≤ b) :
    HasDenom (cycleDenom p q (b - a)) (y m) := by
  obtain ⟨A, hA⟩ := exists_int_iterate hrec m (b - m)
  obtain ⟨B, hB⟩ := exists_int_iterate hrec a (m - a)
  rw [show m + (b - m) = b by omega] at hA
  rw [show a + (m - a) = m by omega] at hB
  rw [← hab] at hA
  rw [show b - a = (m - a) + (b - m) by omega]
  set i := m - a with hi
  set j := b - m with hj
  refine ⟨(p : ℤ) ^ i * A + B * (q : ℤ) ^ j, ?_⟩
  rw [cycleDenom_cast (le_of_lt hqp) (i + j)]
  push_cast
  linear_combination (-((q : ℝ) ^ j)) * hB + (-((p : ℝ) ^ i)) * hA

/-- **C‑2 in the plan's phrasing**: a `P`-periodic point of the carry relation
`q·y_{i+1} = p·yᵢ − sᵢ` is the rational `A/(p^P − q^P)`, at **every** coprime base `p > q` — the
corpus had this at `3/2` only (`Z32.cycle_point_eq`, proved in `Z32/BalanceVectors.lean`). -/
theorem cyclePoint_eq_base (hqp : q < p) {P : ℕ} {y : ℕ → ℝ} {w : ℕ → ℤ}
    (hrec : ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n) (hper : y P = y 0) :
    ∃ A : ℤ, ((p : ℝ) ^ P - (q : ℝ) ^ P) * y 0 = A := by
  obtain ⟨A, hA⟩ :=
    hasDenom_of_return hqp hrec (a := 0) (b := P) (m := 0) hper.symm le_rfl (Nat.zero_le P)
  rw [Nat.sub_zero, cycleDenom_cast hqp.le] at hA
  exact ⟨A, hA⟩


/-! ## Completeness on the finite-hold-set class (T5(i))

The two lemmas above combine into the statement the plan calls completeness: on the class of sets
whose hold set is finite, the scheme's verdict is always *empty*, and it is right.  Nothing about
intervals enters — the only hypothesis is that the orbit takes finitely many values. -/

/-- **The completeness engine.**  An orbit of the carry relation inside `[0,1)` that takes only
finitely many values has an **eventually periodic** carry word.

Proof: some value `v` recurs infinitely often, so from the first visit on every point of the orbit
lies on a loop, hence (`hasDenom_of_return`) is a rational with denominator `p^P − q^P`, coprime to
`q`.  On that class the relation is a *function* (`step_unique`), so equal values at two times force
equal values ever after; the orbit is therefore periodic from the first visit, and with it the
carry word. -/
theorem isEventuallyPeriodic_of_finite_range (hqp : q < p) (hcop : Nat.Coprime p q)
    {y : ℕ → ℝ} {w : ℕ → ℤ} (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n < 1)
    (hrec : ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n)
    (hfin : (Set.range y).Finite) : IsEventuallyPeriodic w := by
  -- some value is taken infinitely often
  have hpig : ∃ v : ℝ, {n | y n = v}.Infinite := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set ℕ) ⊆ ⋃ v ∈ Set.range y, {n | y n = v} := fun n _ =>
      Set.mem_biUnion (Set.mem_range_self n) rfl
    have hfin2 : (⋃ v ∈ Set.range y, {n | y n = v}).Finite :=
      hfin.biUnion fun v _ => h v
    exact Set.infinite_univ (hfin2.subset hsub)
  obtain ⟨v, hv⟩ := hpig
  obtain ⟨n₀, hn₀⟩ := hv.nonempty
  -- from `n₀` on, every point lies on a loop, hence has a denominator coprime to `q`
  have hrecd : ∀ m, n₀ ≤ m → CoprimeDenom q (y m) := by
    intro m hm
    obtain ⟨b, hb, hmb⟩ := hv.exists_gt m
    exact ⟨cycleDenom p q (b - n₀), cycleDenom_pos hqp (by omega),
      cycleDenom_coprime hcop hqp.le (by omega),
      hasDenom_of_return hqp hrec (hn₀.trans hb.symm) hm (by omega)⟩
  -- hence the dynamics is deterministic there
  have hdet : ∀ m m', n₀ ≤ m → n₀ ≤ m' → y m = y m' → y (m + 1) = y (m' + 1) := by
    intro m m' hm hm' he
    refine step_unique (s' := w m') (hrecd m hm) (hrecd (m + 1) (by omega))
      (hrecd (m' + 1) (by omega)) (hrec m) ?_ (hy0 _) (hy1 _) (hy0 _) (hy1 _)
    rw [he]; exact hrec m'
  obtain ⟨n₁, hn₁, hlt⟩ := hv.exists_gt n₀
  refine ⟨n₀, n₁ - n₀, by omega, ?_⟩
  have hper : ∀ i, y (n₀ + i + (n₁ - n₀)) = y (n₀ + i) := by
    intro i
    induction i with
    | zero =>
      rw [show n₀ + 0 + (n₁ - n₀) = n₁ by omega, show n₀ + 0 = n₀ by omega, hn₁, hn₀]
    | succ i ih =>
      rw [show n₀ + (i + 1) + (n₁ - n₀) = (n₀ + i + (n₁ - n₀)) + 1 by omega,
        show n₀ + (i + 1) = (n₀ + i) + 1 by omega]
      exact hdet _ _ (by omega) (by omega) ih
  have hall : ∀ k, n₀ ≤ k → y (k + (n₁ - n₀)) = y k := by
    intro k hk
    have := hper (k - n₀)
    rwa [show n₀ + (k - n₀) = k by omega] at this
  intro k hk
  have e1 := hrec (k + (n₁ - n₀))
  have e2 := hrec k
  rw [show k + (n₁ - n₀) + 1 = (k + 1) + (n₁ - n₀) by omega, hall (k + 1) (by omega),
    hall k hk] at e1
  have : ((w (k + (n₁ - n₀)) : ℝ)) = (w k : ℝ) := by linarith
  exact_mod_cast this

/-- The **hold set** of `U` at the base `p/q`: the points of `U` that carry an infinite orbit of
the carry relation `q·y_{n+1} = p·yₙ − sₙ` inside `U`.

It is the model-level survivor set — a certificate's funnel pushes it into the blocks, and a real
orbit confined to `U` runs inside it — and it is what decides whether a certificate can exist. -/
def holdSet (p q : ℕ) (U : Set ℝ) : Set ℝ :=
  {z | ∃ (y : ℕ → ℝ) (w : ℕ → ℤ), y 0 = z ∧ (∀ n, y n ∈ U) ∧
    ∀ n, (q : ℝ) * y (n + 1) = p * y n - w n}

/-- **T5(i): completeness on the finite-hold-set class.**  If the hold set of `U` is finite then
no `ξ ≠ 0` keeps its orbit in `U`: the verdict is *empty*, with no certificate in sight.

This is the converse half of `Z32.BlockCert.Cert.not_confined`: soundness says a certificate
forces the verdict, completeness says the class on which a certificate can exist — finitely many
held points — already forces it.  The hypothesis is exactly the plan's "hold set is finitely many
periodic orbits plus transients", with no condition on how they are arranged: `step_unique` makes
the branching hypothesis of plan §5.2 automatic. -/
theorem holdSet_finite_imp (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {U : Set ℝ} (hfin : (holdSet p q U).Finite)
    {ξ : ℝ} (hξ : ξ ≠ 0) : ∃ n, yFract p q ξ 0 n ∉ U := by
  by_contra hcon
  push Not at hcon
  have hq0 : 0 < q := by omega
  have hrec : ∀ n, (q : ℝ) * yFract p q ξ 0 (n + 1) = p * yFract p q ξ 0 n - carry p q ξ 0 n := by
    intro n
    have h := carry_eq (p := p) (q := q) (ξ := ξ) (ν := 0) hq0 n
    simp only [mul_zero, sub_zero] at h
    linarith
  have hsub : Set.range (yFract p q ξ 0) ⊆ holdSet p q U := by
    rintro z ⟨n, rfl⟩
    exact ⟨fun k => yFract p q ξ 0 (n + k), fun k => carry p q ξ 0 (n + k), rfl,
      fun k => hcon (n + k), fun k => hrec (n + k)⟩
  exact not_isEventuallyPeriodic_carry (p := p) (q := q) (ξ := ξ) (ν := 0) hq hqp hcop hξ
    (isEventuallyPeriodic_of_finite_range hqp hcop (fun n => yFract_nonneg n)
      (fun n => yFract_lt_one n) hrec (hfin.subset hsub))


namespace BlockCert

variable {c : Cert}

/-! ## The obstruction: what an unranked certificate cannot see (T5(iii), C‑5)

`funcOk` with `strata = []` asks the block graph to be a genuine partial function.  That is a
statement about *blocks*, but it has an exact consequence for *points*: distinct confined orbits
must live in distinct blocks, so a set with more held points than blocks admits no unranked
certificate.  Since the number of blocks is finite whatever the depth, an **infinite hold set**
refutes the unranked scheme at every depth — which is precisely the situation an endpoint cycle
creates, and precisely what rank strata were introduced to survive. -/

private theorem eq_of_mem_of_length_le_one'' {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h with
  | [x], _ => simp only [List.mem_singleton] at ha hb; rw [ha, hb]

/-- With no rank strata, every block has at most one outgoing edge. -/
theorem outEdges_length_le_one (hc : c.ok = true) (hst : c.strata = []) {I : Ivl}
    (hI : I ∈ c.blocks) : (outEdges c.D c.p c.q c.closed c.blocks I).length ≤ 1 := by
  obtain ⟨-, -, -, -, -, hfunc⟩ := Cert.parts hc
  simp only [funcOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfunc
  have h := (hfunc I hI).2
  rwa [hst, show ((outEdges c.D c.p c.q c.closed c.blocks I).filter fun e =>
    decide (rank [] e.2 = rank [] I)) = outEdges c.D c.p c.q c.closed c.blocks I by
      simp [rank]] at h

/-- **Distinct confined orbits occupy distinct blocks.**  For an unranked certificate the block
itinerary and the carry word are determined by the starting block, so two confined orbits that
share a block have the same carry word — and two orbits with the same carry word separate at the
rate `(p/q)ⁿ`, which `[0,1)` cannot hold. -/
theorem Cert.eq_of_memI_block (hc : c.ok = true) (hst : c.strata = [])
    {y y' : ℕ → ℝ} {w w' : ℕ → ℤ}
    (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n < 1) (hmem : ∀ n, memL c.D c.closed c.U (y n))
    (hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ))
    (hy0' : ∀ n, 0 ≤ y' n) (hy1' : ∀ n, y' n < 1) (hmem' : ∀ n, memL c.D c.closed c.U (y' n))
    (hrec' : ∀ n, (c.q : ℝ) * y' (n + 1) = (c.p : ℝ) * y' n - (w' n : ℝ))
    {I : Ivl} (hI : I ∈ c.blocks)
    (h0 : memI c.D c.closed I (y 0)) (h0' : memI c.D c.closed I (y' 0)) : y 0 = y' 0 := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  have hq0 : 0 < c.q := by omega
  have hp0 : 0 < c.p := by omega
  -- the two block paths, both started at `I`
  have hH : ∀ n, memL c.D c.closed c.blocks (y n) := fun n =>
    Cert.memL_blocks_of_le hc hy0 hy1 hrec (N := n + c.levels.length) (fun m _ => hmem m) le_rfl
  have hH' : ∀ n, memL c.D c.closed c.blocks (y' n) := fun n =>
    Cert.memL_blocks_of_le hc hy0' hy1' hrec' (N := n + c.levels.length) (fun m _ => hmem' m) le_rfl
  choose Bl hBmem hBm using hH
  choose Bl' hBmem' hBm' using hH'
  set B : ℕ → Ivl := fun n => if n = 0 then I else Bl n with hBdef
  set B' : ℕ → Ivl := fun n => if n = 0 then I else Bl' n with hB'def
  have hBb : ∀ n, B n ∈ c.blocks := by
    intro n; simp only [hBdef]; split
    · exact hI
    · exact hBmem n
  have hBb' : ∀ n, B' n ∈ c.blocks := by
    intro n; simp only [hB'def]; split
    · exact hI
    · exact hBmem' n
  have hBi : ∀ n, memI c.D c.closed (B n) (y n) := by
    intro n; simp only [hBdef]; split
    · rename_i he; rw [he]; exact h0
    · exact hBm n
  have hBi' : ∀ n, memI c.D c.closed (B' n) (y' n) := by
    intro n; simp only [hB'def]; split
    · rename_i he; rw [he]; exact h0'
    · exact hBm' n
  have hedge : ∀ n, (w n, B (n + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (B n) := fun n =>
    Cert.mem_outEdges_of_memI hc hy0 hy1 hrec (hBb (n + 1)) (hBi n) (hBi (n + 1))
  have hedge' : ∀ n, (w' n, B' (n + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (B' n) := fun n =>
    Cert.mem_outEdges_of_memI hc hy0' hy1' hrec' (hBb' (n + 1)) (hBi' n) (hBi' (n + 1))
  -- the itineraries, hence the carry words, coincide
  have hsame : ∀ n, B n = B' n ∧ w n = w' n := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [hBdef, hB'def], ?_⟩
      have h1 := hedge 0
      have h2 := hedge' 0
      have hB0 : B' 0 = B 0 := by simp [hBdef, hB'def]
      rw [hB0] at h2
      exact congrArg Prod.fst (eq_of_mem_of_length_le_one''
        (outEdges_length_le_one hc hst (hBb 0)) h1 h2)
    | succ n ih =>
      have h1 := hedge n
      have h2 := hedge' n
      rw [← ih.1] at h2
      have heq := eq_of_mem_of_length_le_one'' (outEdges_length_le_one hc hst (hBb n)) h1 h2
      have hBeq : B (n + 1) = B' (n + 1) := congrArg Prod.snd heq
      refine ⟨hBeq, ?_⟩
      have h3 := hedge (n + 1)
      have h4 := hedge' (n + 1)
      rw [← hBeq] at h4
      exact congrArg Prod.fst (eq_of_mem_of_length_le_one''
        (outEdges_length_le_one hc hst (hBb (n + 1))) h3 h4)
  -- equal carry words separate the two orbits at the rate `(p/q)ⁿ`
  have hgap : ∀ n, (c.q : ℝ) ^ n * (y n - y' n) = (c.p : ℝ) ^ n * (y 0 - y' 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 := hrec n
      have e2 := hrec' n
      rw [(hsame n).2] at e1
      have : (c.q : ℝ) ^ (n + 1) * (y (n + 1) - y' (n + 1))
          = (c.q : ℝ) ^ n * ((c.q : ℝ) * y (n + 1) - (c.q : ℝ) * y' (n + 1)) := by ring
      rw [this, e1, e2]
      have hpow : (c.p : ℝ) ^ (n + 1) = (c.p : ℝ) * (c.p : ℝ) ^ n := by ring
      rw [hpow]
      linear_combination (c.p : ℝ) * ih
  by_contra hne
  have hd0 : 0 < |y 0 - y' 0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hqR : (0 : ℝ) < c.q := by exact_mod_cast hq0
  have hpR : (0 : ℝ) < c.p := by exact_mod_cast hp0
  have hratio : (c.q : ℝ) / c.p < 1 := by
    rw [div_lt_one hpR]; exact_mod_cast hqp
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd0 hratio
  have h1 : |(c.q : ℝ) ^ n * (y n - y' n)| < (c.q : ℝ) ^ n := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.q : ℝ) ^ n)]
    have : |y n - y' n| < 1 := by
      rw [abs_lt]; constructor <;> [linarith [hy0 n, hy1' n]; linarith [hy0' n, hy1 n]]
    nlinarith [pow_pos hqR n]
  rw [hgap n, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.p : ℝ) ^ n)] at h1
  have h2 : |y 0 - y' 0| < ((c.q : ℝ) / c.p) ^ n := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **The unranked scheme cannot decide a set with infinitely many held points.**  Given an
injective family of hold points, no certificate with `strata = []` is valid — at any depth,
however deep the funnel.  This turns a bounded search ("`gencert.py` finds nothing to depth 60")
into a theorem. -/
theorem Cert.ok_eq_false_of_infinite_hold (hst : c.strata = [])
    {z : ℕ → ℝ} (hz : Function.Injective z)
    (hhold : ∀ j, ∃ (y : ℕ → ℝ) (w : ℕ → ℤ), y 0 = z j ∧ (∀ n, 0 ≤ y n) ∧ (∀ n, y n < 1) ∧
      (∀ n, memL c.D c.closed c.U (y n)) ∧
      (∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ))) :
    c.ok = false := by
  rcases Bool.eq_false_or_eq_true c.ok with hc | h
  swap
  · exact h
  exfalso
  choose Y W hY0 hYnn hY1 hYmem hYrec using hhold
  -- each hold point sits in a block
  have hblk : ∀ j, ∃ I ∈ c.blocks, memI c.D c.closed I (z j) := by
    intro j
    have := Cert.memL_blocks_of_le hc (hYnn j) (hY1 j) (hYrec j)
      (N := c.levels.length) (fun m _ => hYmem j m) (n := 0) (by omega)
    rw [hY0 j] at this
    exact this
  choose F hFmem hFi using hblk
  have hFinj : Function.Injective F := by
    intro i j hij
    refine hz ?_
    rw [← hY0 i, ← hY0 j]
    refine Cert.eq_of_memI_block hc hst (hYnn i) (hY1 i) (hYmem i) (hYrec i)
      (hYnn j) (hY1 j) (hYmem j) (hYrec j) (hFmem i) ?_ ?_
    · rw [hY0 i]; exact hFi i
    · rw [hY0 j, hij]; exact hFi j
  have hinf : (Set.range F).Infinite := Set.infinite_range_of_injective hFinj
  have hsub : Set.range F ⊆ {x | x ∈ c.blocks} := by
    rintro x ⟨j, rfl⟩; exact hFmem j
  exact hinf ((c.blocks.finite_toSet).subset hsub)

/-! ### The two-cell arc with closed endpoints

`Z32.BlockCert.certTwoCellFifth` certifies the **half-open** `[0,1/5) ∪ [4/5,1)`, and the file's
note records that the engine's search "finds no certificate to depth 60" once the endpoints are
closed.  Both halves of that story are now theorems, and they say different things:

* no **unranked** certificate exists, at any depth — because closing `1/5` admits the whole chain
  `(1/5)(2/3)^k` into the hold set, which is therefore infinite
  (`Cert.ok_eq_false_of_two_cell_chain`);
* a **ranked** certificate does exist, at depth `1` (`certTwoCellFifthClosed`).

So the engine's refusal was a refusal of the unranked search, not of the set; `--ranked` was never
tried here.  The theory of this file predicted the second bullet from the first. -/

/-- The backward chain `(1/5)(2/3)^k` of the branch `y ↦ (3y)/2` at `3/2`, running down to `0`
from the cycle point `1/5`. -/
noncomputable def twoCellPt (k : ℕ) : ℝ := (1 / 5 : ℝ) * (2 / 3) ^ k

theorem twoCellPt_injective : Function.Injective twoCellPt := by
  have hanti : StrictAnti twoCellPt := by
    refine strictAnti_nat_of_succ_lt fun n => ?_
    simp only [twoCellPt, pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2 / 3) n]
  exact hanti.injective

theorem twoCellPt_pos (k : ℕ) : 0 < twoCellPt k := by
  have : (0:ℝ) < (2 / 3 : ℝ) ^ k := pow_pos (by norm_num) k
  simp only [twoCellPt]; linarith

theorem twoCellPt_le (k : ℕ) : twoCellPt k ≤ 1 / 5 := by
  have : ((2 : ℝ) / 3) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [twoCellPt]; linarith

/-- The orbit that holds `twoCellPt j`: down the chain to `1/5`, then round the `2`-cycle
`1/5 ↔ 4/5` for ever. -/
noncomputable def twoCellOrbit (j n : ℕ) : ℝ :=
  if n ≤ j then twoCellPt (j - n) else if (n - j) % 2 = 1 then 4 / 5 else 1 / 5

/-- Its carry word: `0` down the chain, then `−1, 2` alternating around the cycle. -/
def twoCellCarry (j n : ℕ) : ℤ :=
  if n < j then 0 else if (n - j) % 2 = 0 then -1 else 2

theorem twoCellOrbit_zero (j : ℕ) : twoCellOrbit j 0 = twoCellPt j := by
  simp [twoCellOrbit]

theorem twoCellOrbit_rec (j n : ℕ) :
    (2 : ℝ) * twoCellOrbit j (n + 1) = 3 * twoCellOrbit j n - (twoCellCarry j n : ℝ) := by
  rcases lt_trichotomy n j with h | h | h
  · have h1 : n ≤ j := by omega
    have h2 : n + 1 ≤ j := by omega
    simp only [twoCellOrbit, twoCellCarry, h1, h2, h, ite_true]
    rw [show j - n = (j - (n + 1)) + 1 by omega]
    simp only [twoCellPt, pow_succ]
    push_cast
    ring
  · subst h
    have h2 : ¬ (n + 1 ≤ n) := by omega
    have h3 : ¬ (n < n) := by omega
    have hle : n ≤ n := le_refl n
    simp only [twoCellOrbit, twoCellCarry, hle, h2, h3, ite_true, ite_false,
      show n + 1 - n = 1 by omega, show n - n = 0 by omega]
    norm_num [twoCellPt]
  · have h1 : ¬ (n ≤ j) := by omega
    have h2 : ¬ (n + 1 ≤ j) := by omega
    have h3 : ¬ (n < j) := by omega
    simp only [twoCellOrbit, twoCellCarry, h1, h2, h3, ite_false,
      show n + 1 - j = (n - j) + 1 by omega]
    rcases Nat.even_or_odd (n - j) with he | he
    · have e1 : (n - j) % 2 = 0 := Nat.even_iff.mp he
      rw [e1, show (n - j + 1) % 2 = 1 by omega]
      norm_num
    · have e1 : (n - j) % 2 = 1 := Nat.odd_iff.mp he
      rw [e1, show (n - j + 1) % 2 = 0 by omega]
      norm_num

theorem twoCellOrbit_nonneg (j n : ℕ) : 0 ≤ twoCellOrbit j n := by
  simp only [twoCellOrbit]
  split
  · exact (twoCellPt_pos _).le
  · split <;> norm_num

theorem twoCellOrbit_lt_one (j n : ℕ) : twoCellOrbit j n < 1 := by
  simp only [twoCellOrbit]
  split
  · linarith [twoCellPt_le (j - n)]
  · split <;> norm_num

/-- **T5(iii) as a theorem.**  At `3/2`, a set that contains the whole chain `(1/5)(2/3)^k`
together with `4/5` has an infinite hold set, so **no unranked certificate for it exists at any
depth**.  The point `1/5 = twoCellPt 0` is the hinge: including it (the closed convention) admits
the chain, excluding it (the half-open convention) kills the chain at its first step, and
`Z32.BlockCert.certTwoCellFifth` then certifies at depth `1`. -/
theorem Cert.ok_eq_false_of_two_cell_chain {c : Cert} (hp : c.p = 3) (hq : c.q = 2)
    (hst : c.strata = []) (hchain : ∀ k : ℕ, memL c.D c.closed c.U (twoCellPt k))
    (h45 : memL c.D c.closed c.U (4 / 5)) : c.ok = false := by
  refine Cert.ok_eq_false_of_infinite_hold hst (z := twoCellPt) twoCellPt_injective fun j => ?_
  refine ⟨twoCellOrbit j, twoCellCarry j, twoCellOrbit_zero j, twoCellOrbit_nonneg j,
    twoCellOrbit_lt_one j, fun n => ?_, fun n => ?_⟩
  · simp only [twoCellOrbit]
    split
    · exact hchain _
    · split
      · exact h45
      · have h0 : twoCellPt 0 = (1 / 5 : ℝ) := by norm_num [twoCellPt]
        rw [← h0]; exact hchain 0
  · rw [hp, hq]
    push_cast
    exact twoCellOrbit_rec j n

/-- Certificate for the **closed** `[0/5,1/5] ∪ [4/5,5/5]`, total length `2/5`; funnel depth 1,
4 blocks in 2 rank strata.  The blocks are the `2`-cycle `{1/5, 4/5}` at rank `0` and the two
fat cells at rank `1`; the chain `(1/5)(2/3)^k` lives in the rank-`1` block at `0`, which is
exactly the configuration `Cert.ok_eq_false_of_two_cell_chain` shows an unranked certificate
cannot have. -/
def certTwoCellFifthClosed : Cert where
  D := 15
  closed := true
  U := [(0, 3), (12, 15)]
  levels := [[(0, 2), (3, 3), (12, 12), (13, 15)]]
  strata := [[(3, 3), (12, 12)], [(0, 2), (13, 15)]]

theorem certTwoCellFifthClosed_ok : certTwoCellFifthClosed.ok = true := by decide

/-- **The closed two-cell arc.**  For every `ξ ≠ 0` some `{ξ(3/2)ⁿ}` lies outside
`[0,1/5] ∪ [4/5,1]` — that is, `‖ξ(3/2)ⁿ‖ > 1/5` for some `n`, with the endpoints *included*.

**Subsumed, and kept for the certificate rather than the statement.**  `Z32.two_cell_238_empty`
(`Z32/XG0Certs.lean`, experiment X-238) already proves the stronger `‖ξ(3/2)ⁿ‖ < 0.238` impossible,
and `[0,1/5] ∪ [4/5,1] ⊆ [0, 119/500) ∪ [381/500, 1)`.  What is new here is the *certificate*: the
set `Z32/BlockCert.lean` recorded as refused by `gencert.py --closed` to depth 60 is certified at
funnel depth **1**, which is the prediction of `Cert.ok_eq_false_of_covers_two_cell` — the refusal
is of the unranked search only, because the closed arc's hold set is infinite. -/
theorem two_cell_fifth_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (0 : ℝ) (1 / 5) ∪ Set.Icc (4 / 5 : ℝ) 1 := by
  intro h
  refine not_confined_base certTwoCellFifthClosed_ok (3 / 2)
    (by norm_num [certTwoCellFifthClosed]) hξ fun n => ?_
  rcases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(0, 3), by simp [certTwoCellFifthClosed], ?_, ?_⟩ <;>
      simp only [certTwoCellFifthClosed, rleR] <;> push_cast <;> linarith
  · refine ⟨(12, 15), by simp [certTwoCellFifthClosed], ?_, ?_⟩ <;>
      simp only [certTwoCellFifthClosed, rleR] <;> push_cast <;> linarith


/-- **Every unranked certificate covering the closed two-cell arc is invalid**, at every depth and
every denominator: the hold set of `[0,1/5] ∪ [4/5,1]` at `3/2` contains the whole chain
`(1/5)(2/3)^k`. -/
theorem Cert.ok_eq_false_of_covers_two_cell {c : Cert} (hp : c.p = 3) (hq : c.q = 2)
    (hst : c.strata = [])
    (hcov : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) (1 / 5) ∪ Set.Icc (4 / 5 : ℝ) 1 →
      memL c.D c.closed c.U y) : c.ok = false :=
  Cert.ok_eq_false_of_two_cell_chain hp hq hst
    (fun k => hcov _ (Or.inl ⟨(twoCellPt_pos k).le, twoCellPt_le k⟩))
    (hcov _ (Or.inr ⟨by norm_num, by norm_num⟩))

/-! ### Three more closed-convention entries

The same theory says the *ranked* scheme is not obstructed by an endpoint cycle, so every
half-open entry of `Z32/BlockCert.lean` should have a closed companion.  Three of them do, and are
checked here; the two union entries `7/12`, `2/3`, `25/36` do not (their exact funnels still branch
inside one rank class at depth 22, experiment X‑C of the M4 note). -/

/-- Certificate for the **closed** `[4/24,13/24]`, total length `3/8`; funnel depth 8, 9 blocks
in 7 rank strata.  The half-open entry `Z32.BlockCert.certWindow38` merges its funnel into 3
blocks and needs no ranks; closing the right endpoint `13/24` adds transients that only a rank
stratification separates. -/
def certWindow38Closed : Cert where
  D := 157464
  closed := true
  U := [(26244, 85293)]
  levels := [
    [(26244, 56862), (69984, 85293)],
    [(26244, 37908), (46656, 56862), (69984, 85293)],
    [(31104, 37908), (46656, 56862), (69984, 77760), (83592, 85293)],
    [(31104, 37908), (46656, 51840), (55728, 56862), (73224, 77760), (83592, 85293)],
    [(31104, 34560), (37152, 37908), (48816, 51840), (55728, 56862), (73224, 77760), (83592, 85293)],
    [(32544, 34560), (37152, 37908), (48816, 51840), (55728, 56862), (73224, 75528), (77256, 77760), (85032, 85293)],
    [(32544, 34560), (37152, 37908), (48816, 50352), (51504, 51840), (56688, 56862), (74184, 75528), (77256, 77760), (85032, 85293)],
    [(32544, 33568), (34336, 34560), (37792, 37908), (49456, 50352), (51504, 51840), (56688, 56862), (74184, 75528), (77256, 77760), (85032, 85293)]
  ]
  strata := [
    [(85032, 85293)],
    [(56688, 56862)],
    [(37792, 37908)],
    [(77256, 77760)],
    [(51504, 51840)],
    [(34336, 34560)],
    [(32544, 33568), (49456, 50352), (74184, 75528)]
  ]

theorem certWindow38Closed_ok : certWindow38Closed.ok = true := by decide

/-- Certificate for the **closed** `[8/24,15/24]` at `4/3`, total length `7/24`; funnel depth 5,
12 blocks in 6 rank strata. -/
def certFourThreeClosed : Cert where
  D := 24576
  p := 4
  q := 3
  closed := true
  U := [(8192, 15360)]
  levels := [
    [(8192, 11520), (12288, 15360)],
    [(8192, 8640), (9216, 11520), (12288, 14784), (15360, 15360)],
    [(8192, 8640), (9216, 11088), (11520, 11520), (12288, 12624), (13056, 14784), (15360, 15360)],
    [(8192, 8316), (8640, 8640), (9216, 9468), (9792, 11088), (11520, 11520), (12288, 12624), (13056, 14460), (14784, 14784), (15360, 15360)],
    [(8192, 8316), (8640, 8640), (9216, 9468), (9792, 10845), (11088, 11088), (11520, 11520), (12288, 12381), (12624, 12624), (13056, 13245), (13488, 14460), (14784, 14784), (15360, 15360)]
  ]
  strata := [
    [(8192, 8316), (11088, 11088), (11520, 11520), (12288, 12381), (14784, 14784), (15360, 15360)],
    [(8640, 8640)],
    [(12624, 12624)],
    [(9216, 9468)],
    [(13056, 13245)],
    [(9792, 10845), (13488, 14460)]
  ]

theorem certFourThreeClosed_ok : certFourThreeClosed.ok = true := by decide

/-- Certificate for the **closed** `[1/5,2/5]` at `5/2`, in the regime `p > q²`; funnel depth 0
— the certified set is already its own block, with one outgoing edge. -/
def certFiveTwoClosed : Cert where
  D := 5
  p := 5
  closed := true
  U := [(1, 2)]
  levels := []

theorem certFiveTwoClosed_ok : certFiveTwoClosed.ok = true := by decide

/-- **The flagship window, with both endpoints.**  `Z_{3/2}` of the **closed** `[1/6, 13/24]` is
empty: a window of length `3/8 > 1/3` past the [FLP95] line, now including its right endpoint. -/
theorem sixth_3_8_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈ Set.Icc (1 / 6 : ℝ) (13 / 24) := by
  intro h
  refine not_confined_base certWindow38Closed_ok (3 / 2)
    (by norm_num [certWindow38Closed]) hξ fun n => ?_
  obtain ⟨h1, h2⟩ := h n
  refine ⟨(26244, 85293), by simp [certWindow38Closed], ?_, ?_⟩ <;>
    simp only [certWindow38Closed, rleR] <;> push_cast <;> linarith

/-- Certificate for the **closed** `[961/3600, 2427/3600]`, total length `1466/3600 = 0.40722…`
— the engine frontier; funnel depth 13, 14 blocks in 13 rank strata. -/
def certFrontierClosed : Cert where
  D := 5739562800
  closed := true
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
    [(1532144403, 1533830976), (1956411468, 1958983776), (2144974608, 2147940576), (2228780448, 2231921376), (2266027488, 2269246176), (2282581728, 2285834976), (2289939168, 2298012384), (2934617202, 2935741584), (3217461912, 3219176784), (3343170672, 3345147984), (3399041232, 3401135184), (3423872592, 3426018384), (3434908752, 3437077584), (3439813712, 3447018576)]
  ]
  strata := [
    [(1532144403, 1533830976)],
    [(2934617202, 2935741584)],
    [(1956411468, 1958983776)],
    [(3217461912, 3219176784)],
    [(2144974608, 2147940576)],
    [(3343170672, 3345147984)],
    [(2228780448, 2231921376)],
    [(3399041232, 3401135184)],
    [(2266027488, 2269246176)],
    [(3423872592, 3426018384)],
    [(2282581728, 2285834976)],
    [(3434908752, 3437077584)],
    [(2289939168, 2298012384), (3439813712, 3447018576)]
  ]

theorem certFrontierClosed_ok : certFrontierClosed.ok = true := by decide

/-- **The engine frontier, with both endpoints**: `Z_{3/2}` of the **closed**
`[961/3600, 2427/3600]` is empty — the longest single window the M2 sweep certifies, now closed. -/
theorem frontier_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((3 : ℝ) / 2) ^ n) ∈
      Set.Icc (961 / 3600 : ℝ) (2427 / 3600) := by
  intro h
  refine not_confined_base certFrontierClosed_ok (3 / 2)
    (by norm_num [certFrontierClosed]) hξ fun n => ?_
  obtain ⟨h1, h2⟩ := h n
  refine ⟨(1532144403, 3869421921), by simp [certFrontierClosed], ?_, ?_⟩ <;>
    simp only [certFrontierClosed, rleR] <;> push_cast <;> linarith

/-- **The `4/3` entry, with both endpoints**: `Z_{4/3}` of the closed `[1/3, 5/8]` is empty. -/
theorem four_three_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((4 : ℝ) / 3) ^ n) ∈ Set.Icc (1 / 3 : ℝ) (5 / 8) := by
  intro h
  refine not_confined_base certFourThreeClosed_ok (4 / 3)
    (by norm_num [certFourThreeClosed]) hξ fun n => ?_
  obtain ⟨h1, h2⟩ := h n
  refine ⟨(8192, 15360), by simp [certFourThreeClosed], ?_, ?_⟩ <;>
    simp only [certFourThreeClosed, rleR] <;> push_cast <;> linarith

/-- **The `5/2` entry, with both endpoints**: `Z_{5/2}` of the closed `[1/5, 2/5]` is empty, in the
regime `p > q²` that [Dub09AA] §4 leaves open. -/
theorem five_two_fifth_closed {ξ : ℝ} (hξ : ξ ≠ 0) :
    ¬ ∀ n : ℕ, Int.fract (ξ * ((5 : ℝ) / 2) ^ n) ∈ Set.Icc (1 / 5 : ℝ) (2 / 5) := by
  intro h
  refine not_confined_base certFiveTwoClosed_ok (5 / 2)
    (by norm_num [certFiveTwoClosed]) hξ fun n => ?_
  obtain ⟨h1, h2⟩ := h n
  refine ⟨(1, 2), by simp [certFiveTwoClosed], ?_, ?_⟩ <;>
    simp only [certFiveTwoClosed, rleR] <;> push_cast <;> linarith

end BlockCert

end Z32
