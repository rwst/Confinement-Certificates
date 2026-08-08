/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.InfiniteComplexity
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# The carry word of a rational-base orbit, and its aperiodicity (milestone M1-bis)

The arithmetic layer of [Dub09AA].  Fix coprime integers `p > q > 1`, a real `ξ ≠ 0` and a real
shift `ν`, and split the orbit of `ξ` under multiplication by `p/q` into its integer and
fractional parts,

`xₙ = ⌊ξ(p/q)ⁿ + ν⌋`,  `yₙ = {ξ(p/q)ⁿ + ν}`.

The **carry word** is `sₙ = q·x_{n+1} − p·xₙ` ([Dub09AA] (2)).  It is an integer word, it records
exactly how the ceiling/floor of the multiplication behaves, and the whole of [Dub09AA] is an
analysis of it.

## Main results

* `Z32.carry_eq` — the fractional-part form `sₙ = p·yₙ − q·y_{n+1} − (p−q)ν` ([Dub09AA] (3)); it
  is what confines the alphabet once the orbit is confined.
* `Z32.xInt_add` — the summation identity [Dub09AA] (4),
  `x_{n+m} = (p/q)^m xₙ + (Σ_{r<m} (p/q)^{m−1−r} s_{n+r})/q`, written with the accumulator
  `Z32.geomAcc`.
* `Z32.abs_xInt_le` — the growth bound `|xₙ| ≤ (|x₀| + C)(p/q)ⁿ` whenever the carries are bounded
  by `C`; the source's `c = |x₀| + 2p`.
* `Z32.not_isEventuallyPeriodic_carry` — **[Dub09AA] Lemma 2**: the carry word is aperiodic.

## Lemma 2 is proved here, not cited

[Dub09AA] quotes its Lemma 2 from [DN05].  The proof below is self-contained and short, so the
corpus takes it as a theorem rather than as a cited axiom.  The argument: eventual periodicity of
`s` makes `eₙ := xₙ − ξ(p/q)ⁿ = ν − yₙ` satisfy an *expanding* affine recursion `e_{n+P} = β^P eₙ +
D` along each residue class mod `P`, with `β = p/q > 1`; a bounded orbit of an expanding affine map
is its fixed point, so `e` — and hence `y` — is `P`-periodic from some point on.  Then
`x_{n+P} − xₙ = ξ(p/q)ⁿ(β^P − 1)` is an integer for every `n ≥ N`, so `M := x_{N+P} − x_N` is
divisible by `q^k` for every `k` (coprimality), forcing `M = 0` and therefore `ξ = 0`.

Consequently the *only* cited axiom of milestone M1-bis is the Lothaire criterion in
`Z32.Sturmian`.

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — §2, equations (2)–(5) and Lemma 2.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2, the source of the aperiodicity statement reproved here.
-/

namespace Z32

open ForMathlib.SubwordComplexity

/-! ## The orbit and its carry word -/

section Defs

variable (p q : ℕ) (ξ ν : ℝ)

/-- The shifted orbit `ξ(p/q)ⁿ + ν` of [Dub09AA] §2. -/
noncomputable def orb (n : ℕ) : ℝ := ξ * ((p : ℝ) / q) ^ n + ν

/-- The integer part `xₙ = ⌊ξ(p/q)ⁿ + ν⌋`. -/
noncomputable def xInt (n : ℕ) : ℤ := ⌊orb p q ξ ν n⌋

/-- The fractional part `yₙ = {ξ(p/q)ⁿ + ν}`. -/
noncomputable def yFract (n : ℕ) : ℝ := Int.fract (orb p q ξ ν n)

/-- The **carry word** `sₙ = q·x_{n+1} − p·xₙ` of [Dub09AA] (2). -/
noncomputable def carry (n : ℕ) : ℤ := q * xInt p q ξ ν (n + 1) - p * xInt p q ξ ν n

end Defs

variable {p q : ℕ} {ξ ν : ℝ}

/-- `xₙ + yₙ = ξ(p/q)ⁿ + ν`. -/
theorem xInt_add_yFract (n : ℕ) :
    (xInt p q ξ ν n : ℝ) + yFract p q ξ ν n = ξ * ((p : ℝ) / q) ^ n + ν :=
  Int.floor_add_fract _

theorem yFract_nonneg (n : ℕ) : 0 ≤ yFract p q ξ ν n := Int.fract_nonneg _

theorem yFract_lt_one (n : ℕ) : yFract p q ξ ν n < 1 := Int.fract_lt_one _

/-- **[Dub09AA] (3)** in fractional-part form: `sₙ = p·yₙ − q·y_{n+1} − (p−q)ν`.  The powers of
`ξ` cancel, so the carry is entirely controlled by two consecutive fractional parts. -/
theorem carry_eq (hq : 0 < q) (n : ℕ) :
    (carry p q ξ ν n : ℝ)
      = p * yFract p q ξ ν n - q * yFract p q ξ ν (n + 1) - ((p : ℝ) - q) * ν := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have h1 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := ν) n
  have h2 := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := ν) (n + 1)
  have hpow : ((p : ℝ) / q) ^ (n + 1) = ((p : ℝ) / q) ^ n * ((p : ℝ) / q) := pow_succ _ _
  rw [hpow] at h2
  simp only [carry, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  field_simp at h1 h2 ⊢
  nlinarith [h1, h2]

/-! ## The accumulator and the summation identity (4) -/

/-- The **geometric accumulator** `Σ_{r<m} β^{m−1−r} · w r`, defined by the recursion
`geomAcc β w 0 = 0`, `geomAcc β w (m+1) = β · geomAcc β w m + w m`.

Recursion rather than a `Finset.sum` on purpose: every use below is an induction on `m`, and the
`m − 1 − r` exponent is exactly the kind of truncated subtraction that makes sums painful. -/
noncomputable def geomAcc (β : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => β * geomAcc β w m + w m

@[simp] theorem geomAcc_zero (β : ℝ) (w : ℕ → ℝ) : geomAcc β w 0 = 0 := rfl

@[simp] theorem geomAcc_succ (β : ℝ) (w : ℕ → ℝ) (m : ℕ) :
    geomAcc β w (m + 1) = β * geomAcc β w m + w m := rfl

/-- The accumulator only reads the first `m` letters. -/
theorem geomAcc_congr {β : ℝ} {w₁ w₂ : ℕ → ℝ} {m : ℕ} (h : ∀ r, r < m → w₁ r = w₂ r) :
    geomAcc β w₁ m = geomAcc β w₂ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [geomAcc_succ, geomAcc_succ, ih fun r hr => h r (by omega), h m (by omega)]

/-- The accumulator is additive in the word. -/
theorem geomAcc_sub (β : ℝ) (w₁ w₂ : ℕ → ℝ) (m : ℕ) :
    geomAcc β (fun r => w₁ r - w₂ r) m = geomAcc β w₁ m - geomAcc β w₂ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [geomAcc_succ, geomAcc_succ, geomAcc_succ, ih]; ring

/-- **A spike at the two ends.**  If `w` vanishes except at `0`, the accumulator over `m + 1`
letters is `β^m · w 0`.  This is the shape produced by a bispecial pair, where the two words differ
in exactly their first and last letters. -/
theorem geomAcc_spike {β c : ℝ} {w : ℕ → ℝ} {m : ℕ} (h0 : w 0 = c)
    (hz : ∀ r, 1 ≤ r → r ≤ m → w r = 0) : geomAcc β w (m + 1) = β ^ m * c := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [geomAcc_succ, ih fun r h1 h2 => hz r h1 (by omega), hz (m + 1) (by omega) (by omega)]
    ring

/-- **[Dub09AA] (4)**: `x_{n+m} = (p/q)^m xₙ + (Σ_{r<m} (p/q)^{m−1−r} s_{n+r})/q`. -/
theorem xInt_add (hq : 0 < q) (n m : ℕ) :
    (xInt p q ξ ν (n + m) : ℝ)
      = ((p : ℝ) / q) ^ m * (xInt p q ξ ν n)
        + geomAcc ((p : ℝ) / q) (fun r => (carry p q ξ ν (n + r) : ℝ)) m / q := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (q : ℝ) * (xInt p q ξ ν (n + m + 1) : ℝ)
        = p * (xInt p q ξ ν (n + m) : ℝ) + (carry p q ξ ν (n + m) : ℝ) := by
      simp only [carry, Int.cast_sub, Int.cast_mul, Int.cast_natCast]; ring
    have hidx : n + (m + 1) = n + m + 1 := by omega
    have hx : (xInt p q ξ ν (n + m + 1) : ℝ)
        = ((p : ℝ) / q) * (xInt p q ξ ν (n + m) : ℝ) + (carry p q ξ ν (n + m) : ℝ) / q := by
      field_simp
      linarith [hstep]
    rw [hidx, geomAcc_succ, hx, ih, pow_succ]
    ring

/-- **Growth of the integer parts.**  If every carry is bounded by `C`, then
`|xₙ| + C ≤ (|x₀| + C)(p/q)ⁿ`; in particular `|xₙ| ≤ (|x₀| + C)(p/q)ⁿ`.  ([Dub09AA] uses this with
`C = 2p`, giving his constant `c = |x₀| + 2p`.) -/
theorem abs_xInt_le {C : ℝ} (hq : 0 < q) (hpq : q < p) (hC : 0 ≤ C)
    (hcar : ∀ n, |(carry p q ξ ν n : ℝ)| ≤ C) (n : ℕ) :
    |(xInt p q ξ ν n : ℝ)| + C ≤ (|(xInt p q ξ ν 0 : ℝ)| + C) * ((p : ℝ) / q) ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) < p := lt_trans hq0 hpq'
  have hβ0 : (0 : ℝ) < (p : ℝ) / q := div_pos hp0 hq0
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (q : ℝ) * (xInt p q ξ ν (n + 1) : ℝ)
        = p * (xInt p q ξ ν n : ℝ) + (carry p q ξ ν n : ℝ) := by
      simp only [carry, Int.cast_sub, Int.cast_mul, Int.cast_natCast]; ring
    have habs : |(q : ℝ) * (xInt p q ξ ν (n + 1) : ℝ)|
        ≤ (p : ℝ) * |(xInt p q ξ ν n : ℝ)| + C := by
      rw [hstep]
      calc |(p : ℝ) * (xInt p q ξ ν n : ℝ) + (carry p q ξ ν n : ℝ)|
          ≤ |(p : ℝ) * (xInt p q ξ ν n : ℝ)| + |(carry p q ξ ν n : ℝ)| := abs_add_le _ _
        _ ≤ (p : ℝ) * |(xInt p q ξ ν n : ℝ)| + C := by
            rw [abs_mul, abs_of_pos hp0]
            gcongr
            exact hcar n
    have hb : (q : ℝ) * |(xInt p q ξ ν (n + 1) : ℝ)|
        ≤ (p : ℝ) * |(xInt p q ξ ν n : ℝ)| + C := by
      rwa [abs_mul, abs_of_pos hq0] at habs
    -- `q·(|x_{n+1}| + C) ≤ p·(|xₙ| + C)` because `q + 1 ≤ p`.
    have hqp : (q : ℝ) + 1 ≤ p := by exact_mod_cast hpq
    have hkey : (q : ℝ) * (|(xInt p q ξ ν (n + 1) : ℝ)| + C)
        ≤ (p : ℝ) * (|(xInt p q ξ ν n : ℝ)| + C) := by nlinarith [hb, hC, hq0]
    have h1 : |(xInt p q ξ ν (n + 1) : ℝ)| + C
        ≤ ((p : ℝ) / q) * (|(xInt p q ξ ν n : ℝ)| + C) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
      linarith
    calc |(xInt p q ξ ν (n + 1) : ℝ)| + C
        ≤ ((p : ℝ) / q) * (|(xInt p q ξ ν n : ℝ)| + C) := h1
      _ ≤ ((p : ℝ) / q) * ((|(xInt p q ξ ν 0 : ℝ)| + C) * ((p : ℝ) / q) ^ n) :=
          mul_le_mul_of_nonneg_left ih hβ0.le
      _ = (|(xInt p q ξ ν 0 : ℝ)| + C) * ((p : ℝ) / q) ^ (n + 1) := by rw [pow_succ]; ring

/-! ## Lemma 2: the carry word is aperiodic -/

/-- A bounded orbit of an expanding affine map is constant. -/
private theorem const_of_bounded_affine {β c B : ℝ} (hβ : 1 < β) {g : ℕ → ℝ}
    (hrec : ∀ k, g (k + 1) = β * g k + c) (hb : ∀ k, |g k| ≤ B) : g 1 = g 0 := by
  -- the successive differences are the pure geometric sequence `β^k (g 1 − g 0)`
  have hd : ∀ k, g (k + 1) - g k = β ^ k * (g 1 - g 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : g (k + 1 + 1) - g (k + 1) = β * (g (k + 1) - g k) := by
        rw [hrec (k + 1), hrec k]; ring
      rw [hstep, ih, pow_succ]; ring
  by_contra hne
  have hpos : 0 < |g 1 - g 0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((2 * B) / |g 1 - g 0|) hβ
  have h1 : |g (k + 1) - g k| ≤ 2 * B := by
    have h2 := abs_sub (g (k + 1)) (g k)
    have h3 := hb (k + 1)
    have h4 := hb k
    linarith
  rw [hd k, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ k)] at h1
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- **[Dub09AA] Lemma 2** (= [DN05] Lemma 2), proved rather than cited: for coprime `p > q > 1`,
any `ξ ≠ 0` and any shift `ν`, the carry word `sₙ = q·x_{n+1} − p·xₙ` is **aperiodic**. -/
theorem not_isEventuallyPeriodic_carry (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) : ¬ IsEventuallyPeriodic (carry p q ξ ν) := by
  rintro ⟨N, P, hP, hper⟩
  have hq0' : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq0'
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  set β : ℝ := (p : ℝ) / q with hβdef
  have hβ1 : 1 < β := by rw [hβdef, lt_div_iff₀ hq0]; linarith
  have hβ0 : (0 : ℝ) < β := by linarith
  have hβP : 1 < β ^ P := one_lt_pow₀ hβ1 hP.ne'
  -- The "error" `eₙ = xₙ − ξβⁿ = ν − yₙ` is bounded.
  set e : ℕ → ℝ := fun n => (xInt p q ξ ν n : ℝ) - ξ * β ^ n with hedef
  have he : ∀ n, e n = ν - yFract p q ξ ν n := by
    intro n
    have h := xInt_add_yFract (p := p) (q := q) (ξ := ξ) (ν := ν) n
    rw [← hβdef] at h
    simp only [hedef]
    linarith
  have heb : ∀ n, |e n| ≤ |ν| + 1 := by
    intro n
    rw [he n, abs_le]
    have h1 := yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := ν) n
    have h2 := yFract_lt_one (p := p) (q := q) (ξ := ξ) (ν := ν) n
    have h3 : -|ν| ≤ ν := neg_abs_le ν
    have h4 : ν ≤ |ν| := le_abs_self ν
    constructor <;> linarith
  -- One period of accumulated carry.
  set D : ℕ → ℝ := fun n => geomAcc β (fun r => (carry p q ξ ν (n + r) : ℝ)) P / q with hDdef
  have hrec : ∀ n, e (n + P) = β ^ P * e n + D n := by
    intro n
    have h := xInt_add (p := p) (q := q) (ξ := ξ) (ν := ν) hq0' n P
    rw [← hβdef] at h
    have hpa : β ^ (n + P) = β ^ n * β ^ P := pow_add β n P
    simp only [hedef, hDdef]
    rw [h, hpa]
    ring
  have hDper : ∀ n, N ≤ n → D (n + P) = D n := by
    intro n hn
    simp only [hDdef]
    congr 1
    refine geomAcc_congr ?_
    intro r _
    have h := hper (n + r) (by omega)
    have hidx : n + P + r = n + r + P := by omega
    rw [hidx, h]
  -- A bounded orbit of the expanding affine map `t ↦ β^P t + D n` is constant.
  have hconst : ∀ n, N ≤ n → e (n + P) = e n := by
    intro n hn
    have hDconst : ∀ k, D (n + k * P) = D n := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h2 : n + (k + 1) * P = n + k * P + P := by ring
        rw [h2, hDper _ (by omega), ih]
    have hg : ∀ k : ℕ, (fun k => e (n + k * P)) (k + 1)
        = β ^ P * (fun k => e (n + k * P)) k + D n := by
      intro k
      have h1 : n + (k + 1) * P = n + k * P + P := by ring
      simp only
      rw [h1, hrec (n + k * P), hDconst k]
    have h := const_of_bounded_affine (β := β ^ P) (c := D n) (B := |ν| + 1)
      (g := fun k => e (n + k * P)) hβP hg (fun k => heb (n + k * P))
    simpa using h
  -- Hence `y` is `P`-periodic from `N` on, so `x_{n+P} − xₙ = ξβⁿ(β^P − 1)` is an integer.
  have hdiff : ∀ n, N ≤ n →
      ((xInt p q ξ ν (n + P) - xInt p q ξ ν n : ℤ) : ℝ) = ξ * β ^ n * (β ^ P - 1) := by
    intro n hn
    have h := hconst n hn
    simp only [hedef] at h
    have hpa : β ^ (n + P) = β ^ n * β ^ P := pow_add β n P
    rw [hpa] at h
    push_cast
    linarith
  set M : ℤ := xInt p q ξ ν (N + P) - xInt p q ξ ν N with hM
  have hMval : (M : ℝ) = ξ * β ^ N * (β ^ P - 1) := by rw [hM]; exact hdiff N le_rfl
  have hMk : ∀ k : ℕ,
      ((xInt p q ξ ν (N + k + P) - xInt p q ξ ν (N + k) : ℤ) : ℝ) = β ^ k * M := by
    intro k
    rw [hdiff (N + k) (by omega), hMval]
    have hpa : β ^ (N + k) = β ^ k * β ^ N := by rw [pow_add]; ring
    rw [hpa]; ring
  -- Every power of `q` divides `M`, because `p` and `q` are coprime.
  have hdvd : ∀ k : ℕ, (q : ℤ) ^ k ∣ M := by
    intro k
    have hreal : ((xInt p q ξ ν (N + k + P) - xInt p q ξ ν (N + k) : ℤ) : ℝ) * (q : ℝ) ^ k
        = (p : ℝ) ^ k * (M : ℝ) := by
      rw [hMk k, hβdef, div_pow]
      field_simp
    have hint : (xInt p q ξ ν (N + k + P) - xInt p q ξ ν (N + k)) * (q : ℤ) ^ k
        = (p : ℤ) ^ k * M := by exact_mod_cast hreal
    have hdd : (q : ℤ) ^ k ∣ (p : ℤ) ^ k * M :=
      ⟨xInt p q ξ ν (N + k + P) - xInt p q ξ ν (N + k), by rw [← hint]; ring⟩
    have hcopz : IsCoprime ((q : ℤ) ^ k) ((p : ℤ) ^ k) :=
      (Nat.isCoprime_iff_coprime.mpr hcop.symm).pow
    exact hcopz.dvd_of_dvd_mul_left hdd
  have hM0 : M = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|M| : ℤ) (by exact_mod_cast hq : (1 : ℤ) < (q : ℤ))
    have hle : (q : ℤ) ^ k ≤ |M| :=
      Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr (hdvd k))
    omega
  -- `M = 0` forces `ξ = 0`.
  rw [hM0] at hMval
  have hβN : β ^ N ≠ 0 := (pow_pos hβ0 N).ne'
  have hβPne : β ^ P - 1 ≠ 0 := by intro h; linarith
  refine hξ ?_
  have h0 : ξ * β ^ N * (β ^ P - 1) = 0 := by push_cast at hMval; linarith
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hβN
  · exact absurd h hβPne

end Z32
