/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

/-!
# The Flatto–Lagarias–Pollington ⅓-spread theorem: core objects (FLP95)

Stage 0 of the FLP program (`plan-FLT.html`): the arithmetic and dynamical objects that
underlie Flatto–Lagarias–Pollington's theorem that for coprime `p > q ≥ 2` the orbit
`{ξ(p/q)ⁿ}` has range spread `≥ 1/p` for *every* `ξ > 0` (their Theorem 1.4; the `3/2`
case is milestone **M3** of the `report2-weyl` §5 ladder).

The proof (see `plan-FLT.html` §2–4) decouples the real orbit into an integer part driven by
the **`T`-map** `T(g) = ⌈(pg+a)/q⌉` and a fractional part driven by the **linear mod-one
transformation** `f_{β,α}(x) = {βx + α}`.  This file fixes those two objects and the sets they
act on, and proves the elementary structural facts everything downstream consumes:

* the fractional map `lmo β α` lands in `[0,1)` and, restricted to `J = [0,1/β)`, is a pair of
  increasing affine branches split at `c = (1-α)/β` (its images are `[α,1)` and `[0,α)`);
* the ceiling map `TMap` has the exact linearization `q·T(g) = pg + a + i_g` with the symbol
  `i_g := iSym ∈ [0,q)` (`TMap_mul`, `iSym_lt`), the congruence `i_g ≡ -(pg+a) (mod q)`
  (`iSym_add_modEq`), and the key shift identity `T(g + qi) = T(g) + pi` (`TMap_add_qmul`)
  that powers the `T`-expansion injectivity of `FLP.TExpansion`.

Everything here is fractional-part / `ℕ`-division bookkeeping — no measure theory, no
transcendence input.  The target footprint of the whole `FLP/` root is the standard three
axioms.

## Contents

* `FLP.lmo` — the linear mod-one map `f_{β,α}`; `lmo_mem_Ico`, `lmo_iterate_succ_mem_Ico`,
  branch lemmas `lmo_of_lt`/`lmo_of_ge`, `lmo_zero`.
* `FLP.survivors` — the survivor set `S_{β,α} = {x ∈ [0,1/β) : fⁿx < 1/β ∀n}`.
* `FLP.ZSet` — the `Z`-set `Z_{p/q}(s,s+t) = {ξ>0 : {ξ(p/q)ⁿ} ∈ [s,s+t) ∀n}`.
* `FLP.TMap`, `FLP.iSym` — the integer dynamics and its symbol; `TMap_mul`, `iSym_lt`,
  `iSym_add_modEq`, `TMap_add_qmul`.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arithmetica **70.2** (1995), 125–147.  (`aa7023.pdf`; §2 for the
  decoupling, §3 for the `Z`-set / survivor machinery.)
-/

namespace FLP

open Set

/-! ## The linear mod-one transformation `f_{β,α}` -/

/-- The **linear mod-one transformation** `f_{β,α}(x) = {βx + α}` (FLP §2), the fractional-part
dynamics that drives the `θ`-coordinate of a trapped orbit. -/
noncomputable def lmo (β α x : ℝ) : ℝ := Int.fract (β * x + α)

/-- The split point `c = (1-α)/β` of `f_{β,α}` on `J = [0,1/β)`: below `c` the map is `βx+α`
(image `[α,1)`), at or above it the map is `βx+α-1` (image `[0,α)`). -/
noncomputable def splitPt (β α : ℝ) : ℝ := (1 - α) / β

theorem lmo_nonneg (β α x : ℝ) : 0 ≤ lmo β α x := Int.fract_nonneg _

theorem lmo_lt_one (β α x : ℝ) : lmo β α x < 1 := Int.fract_lt_one _

theorem lmo_mem_Ico (β α x : ℝ) : lmo β α x ∈ Ico (0 : ℝ) 1 :=
  ⟨lmo_nonneg β α x, lmo_lt_one β α x⟩

/-- Every nonzero iterate of `f_{β,α}` lands in `[0,1)` (it is a fractional part). -/
theorem lmo_iterate_succ_mem_Ico (β α x : ℝ) (n : ℕ) :
    (lmo β α)^[n + 1] x ∈ Ico (0 : ℝ) 1 := by
  rw [Function.iterate_succ']
  exact lmo_mem_Ico β α _

/-- Lower branch of `f_{β,α}`: for `βx+α ∈ [0,1)` the map is the affine `βx+α`. -/
theorem lmo_of_lt {β α x : ℝ} (hlo : 0 ≤ β * x + α) (hhi : β * x + α < 1) :
    lmo β α x = β * x + α :=
  Int.fract_eq_self.mpr ⟨hlo, hhi⟩

/-- Upper branch of `f_{β,α}`: for `βx+α ∈ [1,2)` the map is the affine `βx+α-1`. -/
theorem lmo_of_ge {β α x : ℝ} (hlo : 1 ≤ β * x + α) (hhi : β * x + α < 2) :
    lmo β α x = β * x + α - 1 := by
  have hr : Int.fract (β * x + α - 1) = β * x + α - 1 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold lmo
  rw [← Int.fract_sub_one (β * x + α), hr]

/-- `f_{β,α}(0) = α` (for `α ∈ [0,1)`): the orbit of the origin starts at `α`, the fact that
pins the escape time to the itinerary of `0` in `FLP.SurvivorFinite`. -/
theorem lmo_zero {β α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : lmo β α 0 = α := by
  unfold lmo
  rw [mul_zero, zero_add, Int.fract_eq_self.mpr ⟨hα0, hα1⟩]

/-! ## The survivor and `Z` sets -/

/-- The **survivor set** `S_{β,α} = {x ∈ [0,1/β) : f_{β,α}ⁿ(x) < 1/β for all n}` (FLP §3):
the points of `J = [0,1/β)` whose forward orbit never leaves `J`. -/
def survivors (β α : ℝ) : Set ℝ :=
  {x | x ∈ Ico (0 : ℝ) (1 / β) ∧ ∀ n, (lmo β α)^[n] x < 1 / β}

/-- The **`Z`-set** `Z_{p/q}(s, s+t) = {ξ > 0 : {ξ(p/q)ⁿ} ∈ [s, s+t) for all n}` (FLP §1):
the positive reals whose entire `(p/q)`-power orbit stays in the interval `[s, s+t)`. -/
def ZSet (p q : ℕ) (s t : ℝ) : Set ℝ :=
  {ξ | 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * ((p : ℝ) / q) ^ n) ∈ Ico s (s + t)}

/-! ## The integer dynamics `T` and its symbol `i_g` -/

/-- The **`T`-map** `T(g) = ⌈(pg + a)/q⌉` (FLP §2), realized in `ℕ` as `(pg + a + (q-1)) / q`;
it advances the integer part `gₙ = ⌊ξβⁿ⌋` of a trapped orbit. -/
def TMap (p q a g : ℕ) : ℕ := (p * g + a + (q - 1)) / q

/-- The **symbol** `i_g := q·T(g) - (pg + a) ∈ [0,q)` (FLP eqn (2.7)): the mod-`q` defect of the
ceiling.  Defined as the subtraction so that `q·T(g) = pg + a + i_g` holds by construction
(`TMap_mul`). -/
def iSym (p q a g : ℕ) : ℕ := q * TMap p q a g - (p * g + a)

/-- `pg + a ≤ q·T(g)`: the ceiling times `q` dominates the argument. -/
theorem le_q_mul_TMap {p q a g : ℕ} (hq : 0 < q) : p * g + a ≤ q * TMap p q a g := by
  have hdm := Nat.div_add_mod (p * g + a + (q - 1)) q
  have hmod := Nat.mod_lt (p * g + a + (q - 1)) hq
  -- `q * TMap = (p*g+a+(q-1)) - r` with `r < q`, so it is `≥ p*g+a`.
  unfold TMap
  omega

/-- **Exact linearization of the `T`-map** (FLP eqn (2.7)): `q·T(g) = pg + a + i_g`. -/
theorem TMap_mul {p q a g : ℕ} (hq : 0 < q) :
    q * TMap p q a g = p * g + a + iSym p q a g := by
  unfold iSym
  rw [Nat.add_sub_cancel' (le_q_mul_TMap hq)]

/-- The symbol `i_g` lies in `[0, q)`. -/
theorem iSym_lt {p q a g : ℕ} (hq : 0 < q) : iSym p q a g < q := by
  have hdm := Nat.div_add_mod (p * g + a + (q - 1)) q
  have hmod := Nat.mod_lt (p * g + a + (q - 1)) hq
  unfold iSym TMap
  omega

/-- The symbol congruence `pg + a + i_g ≡ 0 (mod q)`, i.e. `i_g ≡ -(pg+a) (mod q)`
(FLP eqn (2.7)); the mod-`q` shape used by the symbol match of `FLP.Decoupling`. -/
theorem iSym_add_modEq {p q a g : ℕ} (hq : 0 < q) :
    (p * g + a + iSym p q a g) % q = 0 := by
  rw [← TMap_mul hq, Nat.mul_mod_right]

/-- **The shift identity** `T(g + qi) = T(g) + pi` (FLP, used in Lemma 2.2): adding a multiple
of `q` to the argument shifts the ceiling by the corresponding multiple of `p`.  Exact in
`ℕ`-division; the engine of the `T`-expansion injectivity in `FLP.TExpansion`. -/
theorem TMap_add_qmul {p q a g i : ℕ} (hq : 0 < q) :
    TMap p q a (g + q * i) = TMap p q a g + p * i := by
  unfold TMap
  rw [show p * (g + q * i) + a + (q - 1) = (p * g + a + (q - 1)) + (p * i) * q by ring,
    Nat.add_mul_div_right _ _ hq]

/-! ## Sanity checks -/

/-- Sanity: `f_{3/2, 1/3}(0) = 1/3` — the origin of the `p/q = 3/2`, `s = 1/3` orbit. -/
example : lmo (3 / 2) (1 / 3) 0 = 1 / 3 := lmo_zero (by norm_num) (by norm_num)

/-- Sanity: for `p=3, q=2, a=0`, `T(1) = ⌈3/2⌉ = 2` and the symbol is `i₁ = 4 - 3 = 1`. -/
example : TMap 3 2 0 1 = 2 ∧ iSym 3 2 0 1 = 1 := by decide

end FLP
