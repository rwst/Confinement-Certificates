/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.BlockCert
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# `φ_model`: the entropy ledger of the carry model (plan-M5A9, milestone N2(a))

`plans/plan-M5A9.html` §2 refutes, at the level of the model, the external report's hoped-for
"every hole drops the entropy" theorem, and replaces it by a **quantitative ledger**: the entropy
`φ_model(U)` of the carry language of the hold set of `U`, which is `0` exactly where the atlas
certifies and *positive* on the band and at the small central holes.  This file defines that
quantity and proves both sides of the ledger.

## The object

With `xₙ = ⌊ξ(p/q)ⁿ⌋`, `yₙ = {ξ(p/q)ⁿ}` and the carry `sₙ = q·x_{n+1} − p·xₙ` the orbit obeys
`q·y_{n+1} = p·yₙ − sₙ` (`Z32.carry_eq`).  A **model orbit** (`Z32.IsModelOrbit`) is any sequence
in `[0,1)` obeying that relation and staying in `U` — the *hold set* of the interval map, which is
a strictly larger object than the set of genuine `ξ`-orbits.  Its **language**
(`Z32.modelLang`) is the set of carry words its orbits realise, and

`Z32.phiModel p q U := limsup (log #{words of length n}) / n`.

This is the plan's `φ_model(H) = log λ(H)`: on a certified entry the block graph is functional and
the two agree (both `0`); relating them in general is the transfer lemma of N2(c), which is *not*
in this file.

## The two sides

* **Zero on the certified entries.**  `Z32.phiModel_eq_zero_of_cert`: if a block certificate of
  `Z32/BlockCert.lean` has a functional block graph (`strata = []`), the whole carry word of a
  confined model orbit is determined by the block its orbit starts in
  (`Z32.card_modelLang_le_of_cert`, via the new `Z32.BlockCert.Cert.exists_block_path`), so the
  language has at most `#blocks` words of *every* length.  Read back as sets:
  `Z32.phiModel_eq_zero_window38` (`[1/6, 13/24)`) and `Z32.phiModel_eq_zero_frontier`
  (the `0.40722` frontier).
* **Positive on the band and at the two-cell hole.**  A `Z32.Horse` certificate is the mirror
  image of a funnel: a closed interval `K = [A/D, B/D]` and `N` distinct carry words of a common
  length `L`, each mapping `K` into itself under the *contracting inverse* branches
  `h_s(x) = (qx+s)/p` while visiting only points of `U`.  Then every concatenation of those words
  is realised — by the periodic orbit of its own fixed point, which lies in `K` by the intermediate
  value theorem (`Z32.Horse.exists_fixed`, `Z32.Horse.flatten_mem_modelLang`) — so the language has
  at least `N^k` words of length `kL` and `Z32.Horse.le_phiModel` gives `φ_model ≥ log N / L`.

`Z32.not_cert_and_horse` closes the ledger: no set carries both kinds of certificate.

## The entries

| set | certificate | `φ_model` |
| --- | --- | --- |
| `[1/6, 13/24)`, length `0.375` | `certWindow38` | `= 0` (`Z32.phiModel_eq_zero_window38`) |
| `[961/3600, 2427/3600)`, length `0.40722` | `certFrontier` | `= 0` (`Z32.phiModel_eq_zero_frontier`) |
| the other five `strata = []` entries | `certUnion712`, `certUnion23`, `certUnion2536`, `certFourThree`, `certFiveTwo` | `= 0` by `Z32.phiModel_eq_zero_of_cert` |
| band `[0, 5/12)`, past the frontier | `Z32.horseBand` (4 words, `L = 6`) | `≥ (log 2)/3 = 0.2310…` |
| band `[0, 5/12)` | `Z32.horseBandRecord` (14 words, `L = 10`) | `≥ (log 14)/10 = 0.2639…` |
| two-cell hole `[0,1/3) ∪ [2/3,1)` | `Z32.horseTwoCellSmall` (4 words, `L = 3`) | `≥ (log 4)/3 = 0.4621…` |
| two-cell hole `[0,1/3) ∪ [2/3,1)` | `Z32.horseTwoCell` (16 words, `L = 5`) | `≥ (4/5)·log 2 = 0.5545…` |

The band value `(log 2)/3` is exactly the figure plan-M5A9 §2 attributes to the cycle counts
`4/8/16` at periods `≤ 6/9/12`; the certificate turns that count — which by itself proves nothing
about growth — into a theorem, and `horseBandRecord` then passes it.  At the two-cell hole the
census of `Z32/README.md` measures a *full* `2`-shift (`2^L − 1` points of period dividing `L`);
`(4/5)·log 2` is what a certificate of length `5` proves of it.  The family
`N = 2^{L−1}`, `K = [0, (3^{L−1}−2^{L−1})/(3^L−2^L)]` continues at every `L`, so the certified
bound tends to `log 2`; no single certificate of this shape reaches it (at `L = 1` invariance would
force `K = [0,1]`), which is the honest form of the landmine in N2(d).

## What is *not* claimed

`φ_model` is a statement about the **model** — the hold set of the two-branch interval map — and
never about the actual sets of real `ξ` (plan risk R-B).  A positive `φ_model` says that *this
family of certificates* cannot decide the entry, and that the obstruction is exponential rather
than accidental; it says nothing about whether the underlying `Z`-set is empty.  At the two-cell
hole the underlying set is in fact known nonempty ([Dub10]), and at the band entry nothing is
known either way.

The zero side covers certificates with `strata = []`, which is seven of the eight entries.  The
rank-stratified `certDub08` also has `φ_model = 0` — a rank-`r` graph has polynomially many paths
— but that count is not formalized here; only the functional case is.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.  Every certificate is `decide`-checked from its literal data over one common
denominator, exactly as in `Z32/BlockCert.lean`; the search that produced the data
(`Z32/horseshoe.py`, exact `Fraction` arithmetic) is not trusted by anything here.

## Claim level

Formalization and measurement.  The horseshoe construction is the standard covering/IFS argument;
what is new is that the entries are kernel-checked, that the ledger's two colours are proved
disjoint, and that the plan's heuristic `(log 2)/3` is replaced by a theorem (and beaten).

## References

* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
* [Dub08] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. **281**
  (2008), 951–958.
* [Dub10] A. Dubickas, *On the limit points of the fractional parts of powers of Pisot numbers*
  — the trap `‖ξ(3/2)ⁿ‖ < 1/3` is nonempty.
* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, Acta Arith. **70.2** (1995), 125–147.
* `plans/plan-M5A9.html` §2 (correction C4, the `φ_model` replacement for R2/R3), §5 (N2).
* `plans/plan-cert32.html` §4.4 (the atlas and its band), §11 (milestones M2, M3, M7);
  `Z32/README.md` (the λ tables, the cycle counts, the M7 census).
-/

namespace Z32

open Filter Topology BlockCert

/-! ## The model and its language -/

/-- A **model orbit** confined to `U`: a forward orbit of the `(p+q−1)`-branch carry relation
`q·y_{n+1} = p·yₙ − sₙ` that stays inside `U`.  The fractional-part window `[0,1)` is part of the
definition, because that is the space the model lives on. -/
def IsModelOrbit (p q : ℕ) (U : Set ℝ) (y : ℕ → ℝ) (s : ℕ → ℤ) : Prop :=
  (∀ n, y n ∈ U) ∧ (∀ n, y n ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ n, (q : ℝ) * y (n + 1) = (p : ℝ) * y n - (s n : ℝ)

/-- The **language of the hold set**: the carry words of length `n` realised by some model orbit
confined to `U`. -/
def modelLang (p q : ℕ) (U : Set ℝ) (n : ℕ) : Set (Fin n → ℤ) :=
  {v | ∃ y s, IsModelOrbit p q U y s ∧ ∀ i : Fin n, s i = v i}

/-- `φ_model(U)`, the exponential growth rate of the language of the hold set. -/
noncomputable def phiModel (p q : ℕ) (U : Set ℝ) : ℝ :=
  limsup (fun n : ℕ => Real.log (Nat.card (modelLang p q U n)) / n) atTop

/-! ### The alphabet is finite, hence so is every `modelLang` -/

/-- The carries of a model orbit lie in the alphabet `{−q+1, …, p−1}`, exactly as for a genuine
orbit (`Z32.BlockCert.mem_carries`). -/
theorem mem_carries_of_isModelOrbit {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ} {y s}
    (h : IsModelOrbit p q U y s) (n : ℕ) : s n ∈ carries p q := by
  obtain ⟨-, hIco, hrec⟩ := h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 : (p : ℝ) * y n < (p : ℝ) * 1 := mul_lt_mul_of_pos_left (hIco n).2 hpR
  have e2 : (q : ℝ) * y (n + 1) < (q : ℝ) * 1 := mul_lt_mul_of_pos_left (hIco (n + 1)).2 hqR
  have e3 : 0 ≤ (p : ℝ) * y n := mul_nonneg hpR.le (hIco n).1
  have e4 : 0 ≤ (q : ℝ) * y (n + 1) := mul_nonneg hqR.le (hIco (n + 1)).1
  have hn := hrec n
  refine mem_carries ?_ ?_
  · have h' : -((q : ℕ) : ℝ) < (s n : ℝ) := by linarith
    exact_mod_cast h'
  · have h' : (s n : ℝ) < ((p : ℕ) : ℝ) := by linarith
    exact_mod_cast h'

/-- Every letter of a word of the language is a carry. -/
theorem mem_carries_of_mem_modelLang {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {U : Set ℝ} {n : ℕ}
    {v : Fin n → ℤ} (hv : v ∈ modelLang p q U n) (i : Fin n) : v i ∈ carries p q := by
  obtain ⟨y, s, horb, hval⟩ := hv
  exact hval i ▸ mem_carries_of_isModelOrbit hp hq horb i

/-- Every `modelLang` is finite: the alphabet is. -/
theorem modelLang_finite {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (U : Set ℝ) (n : ℕ) :
    (modelLang p q U n).Finite := by
  have hpi : (Set.pi Set.univ fun _ : Fin n => {x : ℤ | x ∈ carries p q}).Finite :=
    Set.Finite.pi fun _ => (carries p q).finite_toSet
  refine hpi.subset fun v hv => Set.mem_univ_pi.mpr fun i => ?_
  exact mem_carries_of_mem_modelLang hp hq hv i

/-- The crude count: at most `(p+q−1)ⁿ` words of length `n`.  This is what makes `φ_model` a
*bounded* quantity, hence a limsup with the expected properties. -/
theorem card_modelLang_le_pow {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (U : Set ℝ) (n : ℕ) :
    Nat.card (modelLang p q U n) ≤ (carries p q).length ^ n := by
  classical
  have hinj : Function.Injective fun v : modelLang p q U n =>
      (fun i => ⟨v.1 i, List.mem_toFinset.mpr (mem_carries_of_mem_modelLang hp hq v.2 i)⟩ :
        Fin n → {x : ℤ // x ∈ (carries p q).toFinset}) := by
    intro v v' h
    refine Subtype.ext (funext fun i => ?_)
    exact congrArg Subtype.val (congrFun h i)
  calc Nat.card (modelLang p q U n)
      ≤ Nat.card (Fin n → {x : ℤ // x ∈ (carries p q).toFinset}) :=
        Nat.card_le_card_of_injective _ hinj
    _ = (carries p q).toFinset.card ^ n := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    _ ≤ (carries p q).length ^ n := Nat.pow_le_pow_left (carries p q).toFinset_card_le n

/-- `φ_model` is a limsup of a bounded sequence — the side condition of the limsup API. -/
theorem isBoundedUnder_phiModel {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (U : Set ℝ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => Real.log (Nat.card (modelLang p q U n)) / n) := by
  refine ⟨Real.log (carries p q).length, ?_⟩
  simp only [eventually_map, eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard := card_modelLang_le_pow hp hq U n
  have hlog : Real.log (Nat.card (modelLang p q U n)) ≤ (n : ℝ) * Real.log (carries p q).length := by
    have h1 : ((Nat.card (modelLang p q U n) : ℕ) : ℝ) ≤ (((carries p q).length ^ n : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rcases Nat.eq_zero_or_pos (Nat.card (modelLang p q U n)) with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact mul_nonneg hn'.le (Real.log_natCast_nonneg _)
    · calc Real.log (Nat.card (modelLang p q U n))
          ≤ Real.log (((carries p q).length ^ n : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast h0) h1
        _ = (n : ℝ) * Real.log (carries p q).length := by
            push_cast
            rw [Real.log_pow]
  rw [div_le_iff₀ hn']
  linarith [hlog]

/-! ## `φ_model = 0`: the certified entries

A block certificate whose block graph is outright functional (`strata = []`, which is what seven of
the eight entries of `Z32/BlockCert.lean` use) forces the whole carry word of a confined model
orbit to be determined by its **initial block**.  So the language has at most `#blocks` words of
each length, and the growth rate is `0`. -/

/-- The set a certificate speaks about, as a subset of `ℝ`. -/
def certSet (c : Cert) : Set ℝ := {y | memL c.D c.closed c.U y}

private theorem eq_of_mem_of_length_le_one' {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l with
  | [] => exact absurd ha (by simp)
  | [_] => rw [List.mem_singleton] at ha hb; rw [ha, hb]
  | _ :: _ :: _ => simp at h

/-- With `strata = []` the block graph is a partial function: a block has at most one outgoing
edge, carry included. -/
theorem outEdge_unique {c : Cert} (hc : c.ok = true) (hstrata : c.strata = []) {I : Ivl}
    (hI : I ∈ c.blocks) {e e' : ℤ × Ivl}
    (he : e ∈ outEdges c.D c.p c.q c.closed c.blocks I)
    (he' : e' ∈ outEdges c.D c.p c.q c.closed c.blocks I) : e = e' := by
  simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hfunc := hc.2
  simp only [funcOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfunc
  have hone := (hfunc I hI).2
  rw [hstrata] at hone
  simp only [rank, decide_true, List.filter_true] at hone
  exact eq_of_mem_of_length_le_one' hone he he'

/-- **The count on a certified entry**: at most one word of each length per block. -/
theorem card_modelLang_le_of_cert {c : Cert} (hc : c.ok = true) (hstrata : c.strata = []) (n : ℕ) :
    Nat.card (modelLang c.p c.q (certSet c) n) ≤ c.blocks.length := by
  classical
  have hex : ∀ v : modelLang c.p c.q (certSet c) n,
      ∃ (s : ℕ → ℤ) (B : ℕ → Ivl), (∀ i : Fin n, s i = v.1 i) ∧ (∀ m, B m ∈ c.blocks) ∧
        ∀ m, (s m, B (m + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (B m) := by
    rintro ⟨v, y, s, horb, hval⟩
    obtain ⟨B, hB, -, hedge⟩ :=
      Cert.exists_block_path hc (fun m => (horb.2.1 m).1) (fun m => (horb.2.1 m).2) horb.1 horb.2.2
    exact ⟨s, B, hval, hB, hedge⟩
  choose sf Bf hval hBmem hBedge using hex
  -- the initial block determines the whole word
  have hdet : ∀ v v' : modelLang c.p c.q (certSet c) n, Bf v 0 = Bf v' 0 → v = v' := by
    intro v v' h0
    have hB : ∀ m, Bf v m = Bf v' m := by
      intro m
      induction m with
      | zero => exact h0
      | succ m ih =>
        have h2 : (sf v' m, Bf v' (m + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (Bf v m) := by
          rw [ih]; exact hBedge v' m
        exact congrArg Prod.snd (outEdge_unique hc hstrata (hBmem v m) (hBedge v m) h2)
    have hs : ∀ m, sf v m = sf v' m := by
      intro m
      have h2 : (sf v' m, Bf v' (m + 1)) ∈ outEdges c.D c.p c.q c.closed c.blocks (Bf v m) := by
        rw [hB m]; exact hBedge v' m
      exact congrArg Prod.fst (outEdge_unique hc hstrata (hBmem v m) (hBedge v m) h2)
    refine Subtype.ext (funext fun i => ?_)
    rw [← hval v i, ← hval v' i, hs i]
  have hinj : Function.Injective fun v : modelLang c.p c.q (certSet c) n =>
      (⟨Bf v 0, List.mem_toFinset.mpr (hBmem v 0)⟩ : {I // I ∈ c.blocks.toFinset}) :=
    fun v v' h => hdet v v' (congrArg Subtype.val h)
  calc Nat.card (modelLang c.p c.q (certSet c) n)
      ≤ Nat.card {I // I ∈ c.blocks.toFinset} := Nat.card_le_card_of_injective _ hinj
    _ = c.blocks.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ c.blocks.length := c.blocks.toFinset_card_le

/-- A language with boundedly many words of each length has growth rate `0`. -/
theorem phiModel_eq_zero_of_card_le {p q : ℕ} {U : Set ℝ} {B : ℕ} (hB : 0 < B)
    (h : ∀ n, Nat.card (modelLang p q U n) ≤ B) : phiModel p q U = 0 := by
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlim : Tendsto (fun n : ℕ => Real.log (Nat.card (modelLang p q U n)) / n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log B))
    · exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg n)
    · have hlog : Real.log (Nat.card (modelLang p q U n)) ≤ Real.log B := by
        rcases Nat.eq_zero_or_pos (Nat.card (modelLang p q U n)) with h0 | h0
        · rw [h0]
          simpa using Real.log_natCast_nonneg B
        · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h n)
      have hd : 0 ≤ (Real.log B - Real.log (Nat.card (modelLang p q U n))) / n :=
        div_nonneg (by linarith) (Nat.cast_nonneg n)
      rw [sub_div] at hd
      linarith
  exact hlim.limsup_eq

/-- **The certified entries carry no model entropy.**  Seven of the eight entries of
`Z32/BlockCert.lean` (all but the rank-stratified `certDub08`) satisfy `strata = []`. -/
theorem phiModel_eq_zero_of_cert {c : Cert} (hc : c.ok = true) (hstrata : c.strata = []) :
    phiModel c.p c.q (certSet c) = 0 := by
  rcases Nat.eq_zero_or_pos c.blocks.length with h0 | h0
  · refine phiModel_eq_zero_of_card_le (B := 1) one_pos fun n => ?_
    exact le_trans (card_modelLang_le_of_cert hc hstrata n) (by omega)
  · exact phiModel_eq_zero_of_card_le h0 (card_modelLang_le_of_cert hc hstrata)

/-! ## Positive `φ_model`: horseshoe certificates

The lower bound needs the opposite of a funnel: a closed interval `K = [A/D, B/D]` and a list of
distinct carry words of a common length `L`, each of which maps `K` back **into** `K` under the
contracting inverse branches `h_s(x) = (qx+s)/p`, visiting only points of `U` on the way.  Then
every concatenation of those words is itself such a word, its (unique) periodic point lies in `K`
by the intermediate value theorem, and its whole orbit lies in `U` — so the language has at least
`Nʲ` words of length `jL` and `φ_model ≥ log N / L`. -/

/-- The **backward branch** applied along a word: `back p q z w` is the point that follows the
carry word `w` and arrives at `z`.  One step is `h_s(x) = (q·x + s)/p`, the inverse of the forward
branch `f_s(y) = (p·y − s)/q`. -/
noncomputable def back (p q : ℕ) (z : ℝ) : List ℤ → ℝ
  | [] => z
  | s :: t => ((q : ℝ) * back p q z t + (s : ℝ)) / p

@[simp] theorem back_nil (p q : ℕ) (z : ℝ) : back p q z [] = z := rfl

theorem back_cons (p q : ℕ) (z : ℝ) (s : ℤ) (t : List ℤ) :
    back p q z (s :: t) = ((q : ℝ) * back p q z t + (s : ℝ)) / p := rfl

/-- Consecutive points of `back` obey the model relation: this is why a `back`-chain *is* an
orbit. -/
theorem back_step {p q : ℕ} (hp : 0 < p) (z : ℝ) (s : ℤ) (t : List ℤ) :
    (q : ℝ) * back p q z t = (p : ℝ) * back p q z (s :: t) - (s : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [back_cons]
  field_simp
  ring

theorem back_append (p q : ℕ) (z : ℝ) (u v : List ℤ) :
    back p q z (u ++ v) = back p q (back p q z v) u := by
  induction u with
  | nil => rfl
  | cons s t ih => rw [List.cons_append, back_cons, back_cons, ih]

theorem back_mono {p q : ℕ} (hp : 0 < p) {z z' : ℝ} (h : z ≤ z') (w : List ℤ) :
    back p q z w ≤ back p q z' w := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  induction w with
  | nil => exact h
  | cons s t ih =>
      rw [back_cons, back_cons]
      have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      have key : 0 ≤ (((q : ℝ) * back p q z' t + (s : ℝ)) - ((q : ℝ) * back p q z t + (s : ℝ))) / p :=
        div_nonneg (by nlinarith) hpR.le
      rw [sub_div] at key
      linarith

theorem continuous_back (p q : ℕ) (w : List ℤ) : Continuous fun z : ℝ => back p q z w := by
  induction w with
  | nil => exact continuous_id
  | cons s t ih =>
      simp only [back_cons]
      exact ((continuous_const.mul ih).add continuous_const).div_const _

/-- The scaled numerator of `back p q (A/D) w`, over the denominator `D · p^|w|`. -/
def backNum (D : ℤ) (p q : ℕ) (A : ℤ) : List ℤ → ℤ
  | [] => A
  | s :: t => (q : ℤ) * backNum D p q A t + s * (D * (p : ℤ) ^ t.length)

/-- The bridge: the endpoints of the backward images are exactly the integers the kernel
computes. -/
theorem back_eq_backNum {D : ℤ} {p q : ℕ} (hD : 0 < D) (hp : 0 < p) (A : ℤ) (w : List ℤ) :
    back p q ((A : ℝ) / (D : ℝ)) w
      = (backNum D p q A w : ℝ) / ((D : ℝ) * (p : ℝ) ^ w.length) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  induction w with
  | nil => simp [backNum]
  | cons s t ih =>
      rw [back_cons, ih, backNum]
      simp only [List.length_cons]
      have hpow : (0 : ℝ) < (p : ℝ) ^ t.length := pow_pos hpR _
      push_cast
      field_simp
      ring

/-! ### The certificate -/

/-- `[X/(D·k), Y/(D·k)] ⊆ U`, as an integer test (`k = p^j`, `U` over `D`). -/
def subU (cl : Bool) (U : List Ivl) (k X Y : ℤ) : Bool :=
  U.any fun I => decide (I.1 * k ≤ X) && rle cl Y (I.2 * k)

/-- Every point visited along `w` — the image of the base interval under each nonempty suffix of
`w` — lies inside `U`. -/
def suffixOk (D : ℤ) (p q : ℕ) (cl : Bool) (U : List Ivl) (A B : ℤ) : List ℤ → Bool
  | [] => true
  | s :: t =>
      subU cl U ((p : ℤ) ^ (t.length + 1)) (backNum D p q A (s :: t)) (backNum D p q B (s :: t)) &&
        suffixOk D p q cl U A B t

/-- A **horseshoe certificate** for the set `⋃ U` at the base `p/q`: a closed base interval
`K = [A/D, B/D]` and a list of distinct carry words of a common length, each mapping `K` into `K`
backwards while visiting only points of `U`. -/
structure Horse where
  /-- The common denominator of `U` and of the base interval. -/
  D : ℤ
  /-- The numerator of the base `p/q`. -/
  p : ℕ := 3
  /-- The denominator of the base `p/q`. -/
  q : ℕ := 2
  /-- Are the intervals of `U` closed on the right? -/
  closed : Bool := false
  /-- The set, as a list of intervals `[a/D, b/D⟩`. -/
  U : List Ivl
  /-- Left endpoint of the base interval `K`. -/
  A : ℤ
  /-- Right endpoint of the base interval `K`. -/
  B : ℤ
  /-- The words of the horseshoe, all of the same length. -/
  words : List (List ℤ)

namespace Horse

/-- The common length of the words. -/
def len (h : Horse) : ℕ := (h.words.headD []).length

/-- The base interval `K = [A/D, B/D]`, closed. -/
def K (h : Horse) : Set ℝ := Set.Icc ((h.A : ℝ) / (h.D : ℝ)) ((h.B : ℝ) / (h.D : ℝ))

/-- The set the certificate speaks about, as a subset of `ℝ`. -/
def uSet (h : Horse) : Set ℝ := {y | memL h.D h.closed h.U y}

/-- The certificate is valid.  Decidable by kernel evaluation. -/
def ok (h : Horse) : Bool :=
  decide (0 < h.D) && decide (0 < h.q) && decide (h.q < h.p) && decide (h.A ≤ h.B) &&
    h.U.all (fun I => decide (0 ≤ I.1) && rle (!h.closed) I.2 h.D) &&
    decide (2 ≤ h.words.length) && decide h.words.Nodup && decide (0 < h.len) &&
    h.words.all fun w =>
      decide (w.length = h.len) && suffixOk h.D h.p h.q h.closed h.U h.A h.B w &&
        decide (h.A * (h.p : ℤ) ^ h.len ≤ backNum h.D h.p h.q h.A w) &&
        decide (backNum h.D h.p h.q h.B w ≤ h.B * (h.p : ℤ) ^ h.len)

end Horse

/-! ### Soundness -/

private theorem rle_iff' (cl : Bool) (x y : ℤ) : rle cl x y = true ↔ rleR cl (x : ℝ) (y : ℝ) := by
  cases cl <;> simp [rle, rleR]

private theorem rleR_of_div {cl : Bool} {x N k I2 : ℝ} (hk : 0 < k) (hx : x ≤ N / k)
    (h : rleR cl N (I2 * k)) : rleR cl x I2 := by
  cases cl <;> simp only [rleR] at h ⊢
  · have : N / k < I2 := by rw [div_lt_iff₀ hk]; linarith
    linarith
  · have : N / k ≤ I2 := by rw [div_le_iff₀ hk]; linarith
    linarith

namespace Horse

variable {h : Horse}

private theorem ok_parts (hok : h.ok = true) :
    0 < h.D ∧ 0 < h.q ∧ h.q < h.p ∧ h.A ≤ h.B ∧
      (∀ I ∈ h.U, 0 ≤ I.1 ∧ rle (!h.closed) I.2 h.D = true) ∧
      2 ≤ h.words.length ∧ h.words.Nodup ∧ 0 < h.len ∧
      ∀ w ∈ h.words, w.length = h.len ∧
        suffixOk h.D h.p h.q h.closed h.U h.A h.B w = true ∧
        h.A * (h.p : ℤ) ^ h.len ≤ backNum h.D h.p h.q h.A w ∧
        backNum h.D h.p h.q h.B w ≤ h.B * (h.p : ℤ) ^ h.len := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hU⟩, h5⟩, h6⟩, h7⟩, hw⟩ := hok
  refine ⟨h1, h2, h3, h4, fun I hI => ?_, h5, h6, h7, fun w hw' => ?_⟩
  · simpa only [Bool.and_eq_true, decide_eq_true_eq] using hU I hI
  · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hw w hw'
    exact ⟨a, b, c, d⟩

/-- Points of `U` are points of `[0,1)`: the certificate checks the endpoints. -/
theorem mem_Ico_of_mem_uSet (hok : h.ok = true) {y : ℝ} (hy : y ∈ h.uSet) :
    y ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨hD, -, -, -, hU, -⟩ := ok_parts hok
  have hDR : (0 : ℝ) < h.D := by exact_mod_cast hD
  obtain ⟨I, hI, hlo, hhi⟩ := hy
  obtain ⟨h1, h2⟩ := hU I hI
  have h1R : (0 : ℝ) ≤ (I.1 : ℝ) := by exact_mod_cast h1
  have h2R : rleR (!h.closed) ((I.2 : ℤ) : ℝ) ((h.D : ℤ) : ℝ) := (rle_iff' _ _ _).mp h2
  constructor
  · nlinarith
  · refine lt_of_mul_lt_mul_left (a := (h.D : ℝ)) ?_ hDR.le
    rw [mul_one]
    cases hcl : h.closed
    · simp only [hcl, rleR, Bool.not_false] at hhi h2R
      linarith
    · simp only [hcl, rleR, Bool.not_true] at hhi h2R
      linarith

/-- Along a word of the certificate, every visited point lies in `U`. -/
theorem mem_uSet_of_suffixOk (hok : h.ok = true) {z : ℝ} (hz : z ∈ h.K) :
    ∀ (w : List ℤ), suffixOk h.D h.p h.q h.closed h.U h.A h.B w = true →
      ∀ i, i < w.length → back h.p h.q z (w.drop i) ∈ h.uSet := by
  obtain ⟨hD, hq, hqp, hAB, -, -⟩ := ok_parts hok
  have hp : 0 < h.p := by omega
  have hDR : (0 : ℝ) < h.D := by exact_mod_cast hD
  have hpR : (0 : ℝ) < h.p := by exact_mod_cast hp
  intro w
  induction w with
  | nil => intro _ i hi; simp at hi
  | cons s t ih =>
      intro hs i hi
      simp only [suffixOk, Bool.and_eq_true, subU, List.any_eq_true, decide_eq_true_eq] at hs
      match i with
      | Nat.succ j =>
          simp only [List.drop_succ_cons]
          exact ih hs.2 j (by simpa using hi)
      | 0 =>
          simp only [List.drop_zero]
          obtain ⟨I, hI, hlo, hhi⟩ := hs.1
          set k : ℝ := (h.p : ℝ) ^ (t.length + 1) with hk
          have hkpos : (0 : ℝ) < k := pow_pos hpR _
          have hlen : (s :: t).length = t.length + 1 := rfl
          -- the two endpoint identities
          have eA : back h.p h.q ((h.A : ℝ) / (h.D : ℝ)) (s :: t)
              = (backNum h.D h.p h.q h.A (s :: t) : ℝ) / ((h.D : ℝ) * k) := by
            rw [back_eq_backNum hD hp, hlen]
          have eB : back h.p h.q ((h.B : ℝ) / (h.D : ℝ)) (s :: t)
              = (backNum h.D h.p h.q h.B (s :: t) : ℝ) / ((h.D : ℝ) * k) := by
            rw [back_eq_backNum hD hp, hlen]
          have hmono1 := back_mono (q := h.q) hp hz.1 (s :: t)
          have hmono2 := back_mono (q := h.q) hp hz.2 (s :: t)
          rw [eA] at hmono1
          rw [eB] at hmono2
          refine ⟨I, hI, ?_, ?_⟩
          · have hI1 : ((I.1 * (h.p : ℤ) ^ (t.length + 1) : ℤ) : ℝ)
                ≤ ((backNum h.D h.p h.q h.A (s :: t) : ℤ) : ℝ) := by exact_mod_cast hlo
            push_cast at hI1
            rw [← hk] at hI1
            have : (I.1 : ℝ) ≤ (backNum h.D h.p h.q h.A (s :: t) : ℝ) / k := by
              rw [le_div_iff₀ hkpos]; linarith
            have hDb : (backNum h.D h.p h.q h.A (s :: t) : ℝ) / k
                ≤ (h.D : ℝ) * back h.p h.q z (s :: t) := by
              have : (backNum h.D h.p h.q h.A (s :: t) : ℝ) / ((h.D : ℝ) * k) * (h.D : ℝ)
                  = (backNum h.D h.p h.q h.A (s :: t) : ℝ) / k := by
                field_simp
              nlinarith [hmono1]
            linarith
          · have hI2 : rleR h.closed ((backNum h.D h.p h.q h.B (s :: t) : ℤ) : ℝ)
                (((I.2 * (h.p : ℤ) ^ (t.length + 1)) : ℤ) : ℝ) := (rle_iff' _ _ _).mp hhi
            push_cast at hI2
            rw [← hk] at hI2
            refine rleR_of_div hkpos ?_ hI2
            have : (backNum h.D h.p h.q h.B (s :: t) : ℝ) / ((h.D : ℝ) * k) * (h.D : ℝ)
                = (backNum h.D h.p h.q h.B (s :: t) : ℝ) / k := by
              field_simp
            nlinarith [hmono2]

/-- A word of the certificate maps the base interval into itself. -/
theorem back_mem_K (hok : h.ok = true) {z : ℝ} (hz : z ∈ h.K) {w : List ℤ} (hw : w ∈ h.words) :
    back h.p h.q z w ∈ h.K := by
  obtain ⟨hD, hq, hqp, hAB, -, -, -, -, hwords⟩ := ok_parts hok
  have hp : 0 < h.p := by omega
  have hDR : (0 : ℝ) < h.D := by exact_mod_cast hD
  have hpR : (0 : ℝ) < h.p := by exact_mod_cast hp
  obtain ⟨hlen, -, hA, hB⟩ := hwords w hw
  set k : ℝ := (h.p : ℝ) ^ h.len with hk
  have hkpos : (0 : ℝ) < k := pow_pos hpR _
  have eA : back h.p h.q ((h.A : ℝ) / (h.D : ℝ)) w
      = (backNum h.D h.p h.q h.A w : ℝ) / ((h.D : ℝ) * k) := by
    rw [back_eq_backNum hD hp, hlen]
  have eB : back h.p h.q ((h.B : ℝ) / (h.D : ℝ)) w
      = (backNum h.D h.p h.q h.B w : ℝ) / ((h.D : ℝ) * k) := by
    rw [back_eq_backNum hD hp, hlen]
  have hmono1 := back_mono (q := h.q) hp hz.1 w
  have hmono2 := back_mono (q := h.q) hp hz.2 w
  rw [eA] at hmono1
  rw [eB] at hmono2
  have hAR : ((h.A * (h.p : ℤ) ^ h.len : ℤ) : ℝ) ≤ ((backNum h.D h.p h.q h.A w : ℤ) : ℝ) := by
    exact_mod_cast hA
  have hBR : ((backNum h.D h.p h.q h.B w : ℤ) : ℝ) ≤ ((h.B * (h.p : ℤ) ^ h.len : ℤ) : ℝ) := by
    exact_mod_cast hB
  push_cast at hAR hBR
  rw [← hk] at hAR hBR
  constructor
  · refine le_trans ?_ hmono1
    rw [div_le_div_iff₀ hDR (by positivity)]
    nlinarith
  · refine le_trans hmono2 ?_
    rw [div_le_div_iff₀ (by positivity) hDR]
    nlinarith

/-- A concatenation of certificate words maps the base interval into itself. -/
theorem back_flatten_mem_K (hok : h.ok = true) {z : ℝ} (hz : z ∈ h.K) :
    ∀ cs : List (List ℤ), (∀ w ∈ cs, w ∈ h.words) → back h.p h.q z cs.flatten ∈ h.K := by
  intro cs
  induction cs with
  | nil => intro _; simpa using hz
  | cons w rest ih =>
      intro hall
      rw [List.flatten_cons, back_append]
      exact back_mem_K hok (ih fun w' hw' => hall w' (by simp [hw'])) (hall w (by simp))

/-- Every point visited along a concatenation lies in `U`. -/
theorem mem_uSet_flatten (hok : h.ok = true) {z : ℝ} (hz : z ∈ h.K) :
    ∀ cs : List (List ℤ), (∀ w ∈ cs, w ∈ h.words) →
      ∀ i, i < cs.flatten.length → back h.p h.q z (cs.flatten.drop i) ∈ h.uSet := by
  intro cs
  induction cs with
  | nil => intro _ i hi; simp at hi
  | cons w rest ih =>
      intro hall i hi
      have hw : w ∈ h.words := hall w (by simp)
      have hrest : ∀ w' ∈ rest, w' ∈ h.words := fun w' hw' => hall w' (by simp [hw'])
      have hzr : back h.p h.q z rest.flatten ∈ h.K := back_flatten_mem_K hok hz rest hrest
      simp only [List.flatten_cons, List.length_append] at hi ⊢
      rcases lt_or_ge i w.length with hlt | hge
      · rw [List.drop_append_of_le_length hlt.le, back_append]
        obtain ⟨-, -, -, -, -, -, -, -, hwords⟩ := ok_parts hok
        exact mem_uSet_of_suffixOk hok hzr w (hwords w hw).2.1 i hlt
      · rw [List.drop_append, List.drop_eq_nil_of_le hge, List.nil_append]
        exact ih hrest (i - w.length) (by omega)

/-- **The periodic point.**  A concatenation of certificate words has a fixed point in the base
interval — the intermediate value theorem applied to the contraction `H_W`. -/
theorem exists_fixed (hok : h.ok = true) (cs : List (List ℤ)) (hcs : ∀ w ∈ cs, w ∈ h.words) :
    ∃ z ∈ h.K, back h.p h.q z cs.flatten = z := by
  obtain ⟨hD, -, -, hAB, -⟩ := ok_parts hok
  have hDR : (0 : ℝ) < h.D := by exact_mod_cast hD
  have hle : (h.A : ℝ) / (h.D : ℝ) ≤ (h.B : ℝ) / (h.D : ℝ) := by
    have hABR : (h.A : ℝ) ≤ (h.B : ℝ) := by exact_mod_cast hAB
    have h1 : (0 : ℝ) ≤ ((h.B : ℝ) - (h.A : ℝ)) / (h.D : ℝ) :=
      div_nonneg (by linarith) hDR.le
    rw [sub_div] at h1
    linarith
  have hcont : ContinuousOn (fun x => back h.p h.q x cs.flatten - x)
      (Set.Icc ((h.A : ℝ) / (h.D : ℝ)) ((h.B : ℝ) / (h.D : ℝ))) :=
    ((continuous_back h.p h.q cs.flatten).sub continuous_id).continuousOn
  have hAmem : ((h.A : ℝ) / (h.D : ℝ)) ∈ h.K := Set.left_mem_Icc.mpr hle
  have hBmem : ((h.B : ℝ) / (h.D : ℝ)) ∈ h.K := Set.right_mem_Icc.mpr hle
  have hA0 : 0 ≤ back h.p h.q ((h.A : ℝ) / (h.D : ℝ)) cs.flatten - (h.A : ℝ) / (h.D : ℝ) := by
    have := (back_flatten_mem_K hok hAmem cs hcs).1
    linarith
  have hB0 : back h.p h.q ((h.B : ℝ) / (h.D : ℝ)) cs.flatten - (h.B : ℝ) / (h.D : ℝ) ≤ 0 := by
    have := (back_flatten_mem_K hok hBmem cs hcs).2
    linarith
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hle hcont (Set.mem_Icc.mpr ⟨hB0, hA0⟩)
  exact ⟨z, hz, by linarith [hfz]⟩

private theorem mod_succ_of_lt {n N : ℕ} (h : n % N + 1 < N) : (n + 1) % N = n % N + 1 := by
  conv_lhs => rw [← Nat.div_add_mod n N]
  rw [add_assoc, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt h

private theorem mod_succ_of_eq {n N : ℕ} (h : n % N + 1 = N) : (n + 1) % N = 0 := by
  conv_lhs => rw [← Nat.div_add_mod n N]
  rw [add_assoc, h, Nat.mul_add_mod, Nat.mod_self]

/-- **The horseshoe realises every concatenation**: the carry word of any concatenation of
certificate words belongs to the language of the hold set, realised by the periodic orbit of its
own fixed point. -/
theorem flatten_mem_modelLang (hok : h.ok = true) {cs : List (List ℤ)}
    (hcs : ∀ w ∈ cs, w ∈ h.words) {n : ℕ} (hn : cs.flatten.length = n) (hn0 : 0 < n) :
    (fun i : Fin n => cs.flatten.getD (i : ℕ) 0) ∈ modelLang h.p h.q h.uSet n := by
  subst hn
  obtain ⟨hD, hq, hqp, -⟩ := ok_parts hok
  have hp : 0 < h.p := by omega
  obtain ⟨z, hz, hfix⟩ := exists_fixed hok cs hcs
  set W := cs.flatten with hW
  set N := W.length with hN
  refine ⟨fun n => back h.p h.q z (W.drop (n % N)), fun n => W.getD (n % N) 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun n => mem_uSet_flatten hok hz cs hcs (n % N) (Nat.mod_lt _ hn0)
  · exact fun n =>
      mem_Ico_of_mem_uSet hok (mem_uSet_flatten hok hz cs hcs (n % N) (Nat.mod_lt _ hn0))
  · intro n
    show (h.q : ℝ) * back h.p h.q z (W.drop ((n + 1) % N))
      = (h.p : ℝ) * back h.p h.q z (W.drop (n % N)) - ((W.getD (n % N) 0 : ℤ) : ℝ)
    have hlt : n % N < N := Nat.mod_lt _ hn0
    have hdrop : W.drop (n % N) = W[n % N] :: W.drop (n % N + 1) := List.drop_eq_getElem_cons hlt
    have hget : W.getD (n % N) 0 = W[n % N] := (List.getElem_eq_getD (h := hlt) 0).symm
    have hnext : back h.p h.q z (W.drop ((n + 1) % N)) = back h.p h.q z (W.drop (n % N + 1)) := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt2
      · have heq' : n % N + 1 = N := heq
        rw [mod_succ_of_eq heq', List.drop_zero, heq', List.drop_eq_nil_of_le (le_of_eq hN.symm),
          back_nil, hfix]
      · have hlt2' : n % N + 1 < N := hlt2
        rw [mod_succ_of_lt hlt2']
    rw [hget, hnext, hdrop]
    exact back_step hp z (W[n % N]) (W.drop (n % N + 1))
  · intro i
    show W.getD ((i : ℕ) % N) 0 = W.getD (i : ℕ) 0
    rw [Nat.mod_eq_of_lt i.isLt]

private theorem flatten_inj {m : ℕ} : ∀ {l l' : List (List ℤ)}, (∀ w ∈ l, w.length = m) →
    (∀ w ∈ l', w.length = m) → l.length = l'.length → l.flatten = l'.flatten → l = l' := by
  intro l
  induction l with
  | nil => intro l' _ _ hlen _; exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons w t ih =>
      intro l' hl hl' hlen hflat
      match l' with
      | [] => simp at hlen
      | w' :: t' =>
          simp only [List.flatten_cons] at hflat
          have hlw : w.length = w'.length := by rw [hl w (by simp), hl' w' (by simp)]
          obtain ⟨h1, h2⟩ := List.append_inj hflat hlw
          subst h1
          rw [ih (fun x hx => hl x (by simp [hx])) (fun x hx => hl' x (by simp [hx]))
            (by simpa using hlen) h2]

/-- **The count.**  With `N` words of length `L`, the language has at least `N^k` words of
length `kL`. -/
theorem card_modelLang_ge (hok : h.ok = true) {k : ℕ} (hk : 0 < k) :
    h.words.length ^ k ≤ Nat.card (modelLang h.p h.q h.uSet (k * h.len)) := by
  classical
  obtain ⟨hD, hq, hqp, -, -, hN2, hnodup, hlen0, hwords⟩ := ok_parts hok
  have hp : 0 < h.p := by omega
  -- the concatenation attached to a choice vector
  set F : (Fin k → Fin h.words.length) → List (List ℤ) :=
    fun c => List.ofFn fun j => h.words.get (c j) with hF
  have hFmem : ∀ c, ∀ w ∈ F c, w ∈ h.words := by
    intro c w hw
    simp only [hF, List.mem_ofFn] at hw
    obtain ⟨j, rfl⟩ := hw
    exact List.get_mem _ _
  have hFlen : ∀ c, (F c).flatten.length = k * h.len := by
    intro c
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    have : ∀ j : Fin k, ((List.length ∘ fun j => h.words.get (c j)) j) = h.len :=
      fun j => (hwords _ (List.get_mem _ _)).1
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hkl : 0 < k * h.len := Nat.mul_pos hk hlen0
  have : Finite (modelLang h.p h.q h.uSet (k * h.len)) :=
    (modelLang_finite hp hq _ _).to_subtype
  have hmem : ∀ c, (fun i : Fin (k * h.len) => (F c).flatten.getD (i : ℕ) 0) ∈
      modelLang h.p h.q h.uSet (k * h.len) :=
    fun c => flatten_mem_modelLang hok (hFmem c) (hFlen c) hkl
  have hinj : Function.Injective fun c : Fin k → Fin h.words.length =>
      (⟨fun i : Fin (k * h.len) => (F c).flatten.getD (i : ℕ) 0, hmem c⟩ :
        modelLang h.p h.q h.uSet (k * h.len)) := by
    intro c c' hcc
    have hval : ∀ i : Fin (k * h.len), (F c).flatten.getD (i : ℕ) 0
        = (F c').flatten.getD (i : ℕ) 0 := fun i => congrFun (congrArg Subtype.val hcc) i
    have hflat : (F c).flatten = (F c').flatten := by
      refine List.ext_getElem (by rw [hFlen, hFlen]) fun i h1 h2 => ?_
      have hi : i < k * h.len := by rwa [hFlen] at h1
      have hv := hval ⟨i, hi⟩
      rwa [← List.getElem_eq_getD (h := h1) 0, ← List.getElem_eq_getD (h := h2) 0] at hv
    have hFeq : F c = F c' :=
      flatten_inj (m := h.len) (fun w hw => (hwords w (hFmem c w hw)).1)
        (fun w hw => (hwords w (hFmem c' w hw)).1) (by simp [hF]) hflat
    have hget : (fun j => h.words.get (c j)) = fun j => h.words.get (c' j) :=
      List.ofFn_injective hFeq
    funext j
    exact List.nodup_iff_injective_get.mp hnodup (congrFun hget j)
  calc h.words.length ^ k
      = Nat.card (Fin k → Fin h.words.length) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ ≤ Nat.card (modelLang h.p h.q h.uSet (k * h.len)) := Nat.card_le_card_of_injective _ hinj

/-- **A horseshoe certificate is a lower bound for `φ_model`**: `N` words of length `L` give
`φ_model ≥ log N / L`. -/
theorem le_phiModel (hok : h.ok = true) :
    Real.log h.words.length / h.len ≤ phiModel h.p h.q h.uSet := by
  obtain ⟨hD, hq, hqp, -, -, hN2, -, hlen0, -⟩ := ok_parts hok
  have hp : 0 < h.p := by omega
  have hlenR : (0 : ℝ) < h.len := by exact_mod_cast hlen0
  have hNR : (1 : ℝ) ≤ (h.words.length : ℝ) := by exact_mod_cast (by omega : 1 ≤ h.words.length)
  refine le_limsup_of_frequently_le ?_ (isBoundedUnder_phiModel hp hq _)
  rw [frequently_atTop]
  intro m
  refine ⟨(m + 1) * h.len, le_trans (by omega) (Nat.le_mul_of_pos_right _ hlen0), ?_⟩
  have hge := card_modelLang_ge hok (k := m + 1) (by omega)
  have hposN : 0 < h.words.length ^ (m + 1) := by positivity
  have hposC : 0 < Nat.card (modelLang h.p h.q h.uSet ((m + 1) * h.len)) := lt_of_lt_of_le hposN hge
  have hlog : ((m + 1 : ℕ) : ℝ) * Real.log (h.words.length)
      ≤ Real.log (Nat.card (modelLang h.p h.q h.uSet ((m + 1) * h.len))) := by
    have h1 : Real.log ((h.words.length ^ (m + 1) : ℕ) : ℝ)
        ≤ Real.log ((Nat.card (modelLang h.p h.q h.uSet ((m + 1) * h.len)) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hposN) (by exact_mod_cast hge)
    rw [Nat.cast_pow, Real.log_pow] at h1
    exact_mod_cast h1
  have hkR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hlenR (by push_cast; positivity)]
  have hlogN : 0 ≤ Real.log (h.words.length) := Real.log_nonneg hNR
  push_cast
  push_cast at hlog
  nlinarith [hlog, hlenR, hlogN]

end Horse

/-! ## The two colours never meet -/

/-- **The ledger is consistent.**  No set carries both a block certificate (with a functional block
graph) and a horseshoe certificate: the first forces `φ_model = 0`, the second forces it
positive. -/
theorem not_cert_and_horse {c : Cert} {h : Horse} (hc : c.ok = true) (hstrata : c.strata = [])
    (hok : h.ok = true) (hp : h.p = c.p) (hq : h.q = c.q) (hU : h.uSet = certSet c) : False := by
  obtain ⟨-, -, -, -, -, hN2, -, hlen0, -⟩ := Horse.ok_parts hok
  have h1 := Horse.le_phiModel hok
  rw [hU, hp, hq, phiModel_eq_zero_of_cert hc hstrata] at h1
  have hlenR : (0 : ℝ) < h.len := by exact_mod_cast hlen0
  have hNR : (2 : ℝ) ≤ (h.words.length : ℝ) := by exact_mod_cast hN2
  have hlogpos : 0 < Real.log (h.words.length) :=
    Real.log_pos (by linarith)
  have : 0 < Real.log (h.words.length) / (h.len : ℝ) := div_pos hlogpos hlenR
  linarith

/-! ## The entries

Four horseshoe certificates, each `decide`-checked, generated and cross-validated by the exact
`Fraction` search of `Z32/horseshoe.py`.  Two live on the **band** entry `[0, 5/12)` — a window
just past the certified frontier `L* = 0.40722`, where the atlas decides nothing — and two on the
**two-cell hole** `‖·‖ < 1/3`, the [Dub10] trap, which is *known nonempty*. -/

/-- Horseshoe for the band window `[0, 5/12)`: four words of length `6` on `K = [0, 1/9]`, so
`φ_model ≥ (log 2)/3`. -/
def horseBand : Horse where
  D := 108
  U := [(0, 45)]
  A := 0
  B := 12
  words := [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0]]

theorem horseBand_ok : horseBand.ok = true := by decide

/-- Horseshoe for the band window `[0, 5/12)`, the record: fourteen words of length `10` on
`K = [0, 11/90]`, so `φ_model ≥ (log 14)/10 = 0.2639…`. -/
def horseBandRecord : Horse where
  D := 180
  U := [(0, 75)]
  A := 0
  B := 22
  words := [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 1, 0, 0]]

theorem horseBandRecord_ok : horseBandRecord.ok = true := by decide

/-- Horseshoe for the two-cell hole `[0,1/3) ∪ [2/3,1)`: four words of length `3` on
`K = [0, 5/19]`, small enough to check by hand. -/
def horseTwoCellSmall : Horse where
  D := 57
  U := [(0, 19), (38, 57)]
  A := 0
  B := 15
  words := [[-1, 1, 2], [-1, 2, 0], [0, -1, 2], [0, 0, 0]]

theorem horseTwoCellSmall_ok : horseTwoCellSmall.ok = true := by decide

/-- Horseshoe for the two-cell hole `[0,1/3) ∪ [2/3,1)`: sixteen words of length `5` on
`K = [0, 65/211]`, so `φ_model ≥ (4/5)·log 2` — four fifths of the full shift entropy the census
of `Z32/README.md` measures there. -/
def horseTwoCell : Horse where
  D := 633
  U := [(0, 211), (422, 633)]
  A := 0
  B := 195
  words := [
    [-1, 1, 1, 1, 2], [-1, 1, 1, 2, 0], [-1, 1, 2, -1, 2], [-1, 1, 2, 0, 0],
    [-1, 2, -1, 1, 2], [-1, 2, -1, 2, 0], [-1, 2, 0, -1, 2], [-1, 2, 0, 0, 0],
    [0, -1, 1, 1, 2], [0, -1, 1, 2, 0], [0, -1, 2, -1, 2], [0, -1, 2, 0, 0],
    [0, 0, -1, 1, 2], [0, 0, -1, 2, 0], [0, 0, 0, -1, 2], [0, 0, 0, 0, 0]]

theorem horseTwoCell_ok : horseTwoCell.ok = true := by decide

/-! ### The sets, read back -/

private theorem log_two_pow (k : ℕ) (x : ℝ) (hx : x = 2 ^ k) : Real.log x = k * Real.log 2 := by
  rw [hx, Real.log_pow]

theorem horseBand_uSet : horseBand.uSet = Set.Ico (0 : ℝ) (5 / 12) := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [horseBand, List.mem_singleton] at hI
    subst hI
    simp only [horseBand, rleR] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(0, 45), by simp [horseBand], ?_, ?_⟩
    · simp only [horseBand]; push_cast; linarith
    · simp only [horseBand, rleR]; push_cast; linarith

theorem horseBandRecord_uSet : horseBandRecord.uSet = Set.Ico (0 : ℝ) (5 / 12) := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [horseBandRecord, List.mem_singleton] at hI
    subst hI
    simp only [horseBandRecord, rleR] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(0, 75), by simp [horseBandRecord], ?_, ?_⟩
    · simp only [horseBandRecord]; push_cast; linarith
    · simp only [horseBandRecord, rleR]; push_cast; linarith

theorem horseTwoCellSmall_uSet :
    horseTwoCellSmall.uSet = Set.Ico (0 : ℝ) (1 / 3) ∪ Set.Ico (2 / 3) 1 := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [horseTwoCellSmall, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · simp only [horseTwoCellSmall, rleR] at h1 h2
      push_cast at h1 h2
      exact Or.inl ⟨by linarith, by linarith⟩
    · simp only [horseTwoCellSmall, rleR] at h1 h2
      push_cast at h1 h2
      exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨(0, 19), by simp [horseTwoCellSmall], ?_, ?_⟩
      · simp only [horseTwoCellSmall]; push_cast; linarith
      · simp only [horseTwoCellSmall, rleR]; push_cast; linarith
    · refine ⟨(38, 57), by simp [horseTwoCellSmall], ?_, ?_⟩
      · simp only [horseTwoCellSmall]; push_cast; linarith
      · simp only [horseTwoCellSmall, rleR]; push_cast; linarith

theorem horseTwoCell_uSet :
    horseTwoCell.uSet = Set.Ico (0 : ℝ) (1 / 3) ∪ Set.Ico (2 / 3) 1 := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [horseTwoCell, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · simp only [horseTwoCell, rleR] at h1 h2
      push_cast at h1 h2
      exact Or.inl ⟨by linarith, by linarith⟩
    · simp only [horseTwoCell, rleR] at h1 h2
      push_cast at h1 h2
      exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨(0, 211), by simp [horseTwoCell], ?_, ?_⟩
      · simp only [horseTwoCell]; push_cast; linarith
      · simp only [horseTwoCell, rleR]; push_cast; linarith
    · refine ⟨(422, 633), by simp [horseTwoCell], ?_, ?_⟩
      · simp only [horseTwoCell]; push_cast; linarith
      · simp only [horseTwoCell, rleR]; push_cast; linarith

/-! ### The zero rows: certified entries

Two of the eight entries of `Z32/BlockCert.lean`, read back as sets.  The other five with
`strata = []` go through `Z32.phiModel_eq_zero_of_cert` verbatim; only the rank-stratified
`certDub08` is out of scope (see the header). -/

theorem certSet_window38 : certSet certWindow38 = Set.Ico (1 / 6 : ℝ) (13 / 24) := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [certWindow38, List.mem_singleton] at hI
    subst hI
    simp only [certWindow38, rleR] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(26244, 85293), by simp [certWindow38], ?_, ?_⟩
    · simp only [certWindow38]; push_cast; linarith
    · simp only [certWindow38, rleR]; push_cast; linarith

theorem certSet_frontier :
    certSet certFrontier = Set.Ico (961 / 3600 : ℝ) (2427 / 3600) := by
  ext y
  constructor
  · rintro ⟨I, hI, h1, h2⟩
    simp only [certFrontier, List.mem_singleton] at hI
    subst hI
    simp only [certFrontier, rleR] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(1532144403, 3869421921), by simp [certFrontier], ?_, ?_⟩
    · simp only [certFrontier]; push_cast; linarith
    · simp only [certFrontier, rleR]; push_cast; linarith

/-- **A certified window carries no model entropy**, at the first entry past the [FLP95] line. -/
theorem phiModel_eq_zero_window38 : phiModel 3 2 (Set.Ico (1 / 6 : ℝ) (13 / 24)) = 0 := by
  have h := phiModel_eq_zero_of_cert certWindow38_ok rfl
  rwa [certSet_window38] at h

/-- **The engine frontier carries no model entropy either.**  Length `0.40722…`. -/
theorem phiModel_eq_zero_frontier :
    phiModel 3 2 (Set.Ico (961 / 3600 : ℝ) (2427 / 3600)) = 0 := by
  have h := phiModel_eq_zero_of_cert certFrontier_ok rfl
  rwa [certSet_frontier] at h

/-! ### The ledger entries -/

/-- **A band entry carries model entropy at least `(log 2)/3`.**  The window `[0, 5/12)` lies past
the certified frontier `L* = 0.40722…` of `Z32/README.md`, so no block certificate reaches it; the
horseshoe shows that none ever will (`Z32.not_cert_and_horse`), and quantifies the obstruction. -/
theorem log_two_div_three_le_phiModel_band :
    Real.log 2 / 3 ≤ phiModel 3 2 (Set.Ico (0 : ℝ) (5 / 12)) := by
  have h := Horse.le_phiModel horseBand_ok
  rw [horseBand_uSet] at h
  refine le_trans (le_of_eq ?_) h
  have hw : ((horseBand.words.length : ℕ) : ℝ) = 4 := by norm_num [horseBand]
  have hl : ((horseBand.len : ℕ) : ℝ) = 6 := by norm_num [horseBand, Horse.len]
  rw [hw, hl, log_two_pow 2 4 (by norm_num)]
  push_cast
  ring

/-- **The record lower bound on the band entry**: `φ_model ≥ (log 14)/10 = 0.26392…`, past the
`(log 2)/3 = 0.23105…` that the cycle counts of `Z32/README.md` suggest. -/
theorem log_fourteen_div_ten_le_phiModel_band :
    Real.log 14 / 10 ≤ phiModel 3 2 (Set.Ico (0 : ℝ) (5 / 12)) := by
  have h := Horse.le_phiModel horseBandRecord_ok
  rw [horseBandRecord_uSet] at h
  refine le_trans (le_of_eq ?_) h
  have hw : ((horseBandRecord.words.length : ℕ) : ℝ) = 14 := by norm_num [horseBandRecord]
  have hl : ((horseBandRecord.len : ℕ) : ℝ) = 10 := by norm_num [horseBandRecord, Horse.len]
  rw [hw, hl]

/-- **The two-cell hole carries model entropy at least `(log 4)/3`** — the certificate small
enough to check by hand: four words of length three on `K = [0, 5/19]`. -/
theorem log_four_div_three_le_phiModel_two_cell :
    Real.log 4 / 3 ≤ phiModel 3 2 (Set.Ico (0 : ℝ) (1 / 3) ∪ Set.Ico (2 / 3) 1) := by
  have h := Horse.le_phiModel horseTwoCellSmall_ok
  rw [horseTwoCellSmall_uSet] at h
  refine le_trans (le_of_eq ?_) h
  have hw : ((horseTwoCellSmall.words.length : ℕ) : ℝ) = 4 := by norm_num [horseTwoCellSmall]
  have hl : ((horseTwoCellSmall.len : ℕ) : ℝ) = 3 := by
    norm_num [horseTwoCellSmall, Horse.len]
  rw [hw, hl]

/-- **The two-cell hole carries almost the full shift entropy.**  `U = [0,1/3) ∪ [2/3,1)` is the
trap `‖ξ(3/2)ⁿ‖ < 1/3`, which [Dub10] proves *nonempty*; the census of `Z32/README.md` measures a
full `2`-shift there, and the certificate proves `φ_model ≥ (4/5)·log 2`, i.e. at least `80 %` of
it. -/
theorem four_fifths_log_two_le_phiModel_two_cell :
    4 * Real.log 2 / 5 ≤ phiModel 3 2 (Set.Ico (0 : ℝ) (1 / 3) ∪ Set.Ico (2 / 3) 1) := by
  have h := Horse.le_phiModel horseTwoCell_ok
  rw [horseTwoCell_uSet] at h
  refine le_trans (le_of_eq ?_) h
  have hw : ((horseTwoCell.words.length : ℕ) : ℝ) = 16 := by norm_num [horseTwoCell]
  have hl : ((horseTwoCell.len : ℕ) : ℝ) = 5 := by norm_num [horseTwoCell, Horse.len]
  rw [hw, hl, log_two_pow 4 16 (by norm_num)]
  push_cast
  ring

end Z32
