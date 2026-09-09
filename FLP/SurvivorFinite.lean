/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Mathlib.Tactic

/-!
# Escape of the origin ⟹ the survivor set is finite (FLP95, Theorem 3.4, weakened)

For the theorem of Flatto–Lagarias–Pollington only *finiteness* of the survivor set
`S_{β,α} = {x ∈ [0,1/β) : f^n(x) < 1/β for all n}` is needed, not the sharp count.  This file
proves it, for an arbitrary real base `β > 1` and offset `α ∈ [0,1)`, under the single hypothesis
that the **origin escapes**: some iterate `f^N(0) ≥ 1/β`.

The proof is the measure-free redesign of `plan-FLT.html` §4 (numerically verified 120/120 there):

* **Cylinders.** For a branch word `w`, `cyl w` is the set of points whose first `|w|` branches
  follow `w`.  Each `cyl w` is order-connected (`cyl_ordConnected`), and the two branches of `f`
  restrict to increasing affine bijections `[0,c) → [α,1)` and `[c,1/β) → [0,α)` (`c = (1-α)/β`),
  so a nonempty cylinder has **two** nonempty children iff it *straddles* `α` — meets both `[0,α)`
  and `[α,1)` — and **one** otherwise.
* **The count is bounded by `N`.** A straddling cylinder contains `α` (order-connectedness), and
  distinct cylinders are disjoint, so at most one cylinder straddles per depth
  (`straddle_filter_card_le_one`).  Since `f(0) = α`, a straddle at depth `m` forces `0`'s orbit
  `f, f², …, f^m` to stay in `J`, impossible once `m ≥ N`.  Hence the number of nonempty depth-`m`
  cylinders never exceeds `N + 1` (`alive_card_le`).
* **Expansivity + separation.** Two survivors sharing their first `m` branches differ by
  `< (1/β)^m` (the branch maps have slope `β`, `iter_sub_eq`), so distinct survivors eventually
  get distinct depth-`m` words.  A set of `> N+1` survivors would therefore realize `> N+1`
  nonempty cylinders at some depth — a contradiction.  Thus `survivors` is finite.

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Theorem 3.4 (only the
  finiteness of `S_{β,α}` is used; the measure-theoretic argument there is replaced by the
  cylinder split-count above).
-/

set_option linter.unusedSectionVars false

namespace FLP

open Set

open scoped Classical

/-- The **survivor cylinder** of a branch word `w` (prepend recursion): `cyl (j :: w)` is the set
of points landing in branch `J_j` and whose image under `f` lies in `cyl w`.  So `x ∈ cyl w` iff
the first `|w|` branches of `x` follow `w`. -/
def cyl (β α : ℝ) : List Bool → Set ℝ
  | [] => Ico 0 (1 / β)
  | j :: w => {x | x ∈ (if j then Ico (splitPt β α) (1 / β) else Ico 0 (splitPt β α))
                    ∧ lmo β α x ∈ cyl β α w}

/-- A cylinder **straddles** `α` if it meets both `[0,α)` and `[α,1)` — equivalently (for an
order-connected cylinder) if it contains `α`.  Exactly the condition for two nonempty children. -/
def straddle (β α : ℝ) (w : List Bool) : Prop :=
  (cyl β α w ∩ Ico 0 α).Nonempty ∧ (cyl β α w ∩ Ico α 1).Nonempty

/-- The nonempty children of `cyl w`: the words `j :: w` with `cyl (j :: w)` nonempty. -/
noncomputable def children (β α : ℝ) (w : List Bool) : Finset (List Bool) :=
  (Finset.univ.filter (fun j : Bool => (cyl β α (j :: w)).Nonempty)).image (fun j => j :: w)

/-- The nonempty cylinders at depth `m`, as a `Finset` of branch words. -/
noncomputable def alive (β α : ℝ) : ℕ → Finset (List Bool)
  | 0 => {[]}
  | m + 1 => (alive β α m).biUnion (children β α)

/-- The length-`m` branch word (itinerary) of `x`: entry `k` is `true` iff the `k`-th iterate is
in the upper branch `[c, 1/β)`. -/
noncomputable def word (β α : ℝ) (x : ℝ) (m : ℕ) : List Bool :=
  (List.range m).map (fun k => decide (splitPt β α ≤ (lmo β α)^[k] x))

variable {β α : ℝ}

/-! ## Word combinatorics (hypothesis-free) -/

theorem word_length (x : ℝ) (m : ℕ) : (word β α x m).length = m := by simp [word]

theorem word_succ_eq (x : ℝ) (m : ℕ) :
    word β α x (m + 1) = word β α x m ++ [decide (splitPt β α ≤ (lmo β α)^[m] x)] := by
  simp only [word, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem word_succ_cons (x : ℝ) (m : ℕ) :
    word β α x (m + 1) = decide (splitPt β α ≤ x) :: word β α (lmo β α x) m := by
  simp only [word, List.range_succ_eq_map, List.map_cons, List.map_map, Function.iterate_zero, id]
  rfl

theorem word_take {m m' : ℕ} (h : m ≤ m') (x : ℝ) :
    (word β α x m').take m = word β α x m := by
  simp only [word]
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem word_ne_mono {x y : ℝ} {m m' : ℕ} (h : m ≤ m')
    (hne : word β α x m ≠ word β α y m) : word β α x m' ≠ word β α y m' := by
  intro heq
  exact hne (by rw [← word_take h x, ← word_take h y, heq])

/-! ## Survivors keep their iterates in `J` -/

theorem survivors_iterate_mem {x : ℝ} (hx : x ∈ survivors β α) (n : ℕ) :
    (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β) := by
  refine ⟨?_, hx.2 n⟩
  cases n with
  | zero => exact hx.1.1
  | succ k => rw [Function.iterate_succ_apply']; exact lmo_nonneg β α _

theorem lmo_mem_survivors {x : ℝ} (hx : x ∈ survivors β α) : lmo β α x ∈ survivors β α := by
  refine ⟨⟨lmo_nonneg β α x, ?_⟩, ?_⟩
  · have := hx.2 1; rwa [Function.iterate_one] at this
  · intro n; have := hx.2 (n + 1); rwa [Function.iterate_succ_apply] at this

section
variable (hβ : 1 < β) (hα0 : 0 ≤ α) (hα1 : α < 1)
include hβ hα0 hα1

/-! ## Geometry of the split point and branches -/

theorem splitPt_pos : 0 < splitPt β α := by unfold splitPt; positivity

theorem splitPt_le : splitPt β α ≤ 1 / β := by
  rw [splitPt, div_le_div_iff_of_pos_right (by linarith)]; linarith

/-- Lower branch: `f(x) = βx + α` on `[0, c)`. -/
theorem lmo_lower {x : ℝ} (hx0 : 0 ≤ x) (hxc : x < splitPt β α) : lmo β α x = β * x + α := by
  apply lmo_of_lt (by positivity)
  have h : β * x < β * splitPt β α := mul_lt_mul_of_pos_left hxc (by linarith)
  rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at h; linarith

/-- Upper branch: `f(x) = βx + α - 1` on `[c, 1/β)`. -/
theorem lmo_upper {x : ℝ} (hxc : splitPt β α ≤ x) (hx1 : x < 1 / β) : lmo β α x = β * x + α - 1 := by
  apply lmo_of_ge
  · have h : β * splitPt β α ≤ β * x := mul_le_mul_of_nonneg_left hxc (by linarith)
    rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at h; linarith
  · have h : β * x < β * (1 / β) := mul_lt_mul_of_pos_left hx1 (by linarith)
    rw [mul_one_div, div_self (by linarith : β ≠ 0)] at h; linarith

/-- `f` is monotone on each branch `J_j`. -/
theorem lmo_mono_branch (j : Bool) {u v : ℝ}
    (hu : u ∈ (if j then Ico (splitPt β α) (1 / β) else Ico 0 (splitPt β α)))
    (hv : v ∈ (if j then Ico (splitPt β α) (1 / β) else Ico 0 (splitPt β α)))
    (huv : u ≤ v) : lmo β α u ≤ lmo β α v := by
  cases j with
  | false =>
      simp only [ite_eq_right (by decide : ¬ (false = true))] at hu hv
      rw [lmo_lower hβ hα0 hα1 hu.1 hu.2, lmo_lower hβ hα0 hα1 hv.1 hv.2]; nlinarith [huv, hβ]
  | true =>
      rw [lmo_upper hβ hα0 hα1 hu.1 hu.2, lmo_upper hβ hα0 hα1 hv.1 hv.2]; nlinarith [huv, hβ]

/-! ## Cylinder structure -/

theorem cyl_subset_J : ∀ w, cyl β α w ⊆ Ico 0 (1 / β)
  | [] => by rw [cyl]
  | j :: w => by
      rw [cyl]
      rintro x ⟨hxJ, _⟩
      cases j with
      | false => simp only [ite_eq_right (by decide : ¬ (false = true))] at hxJ
                 exact ⟨hxJ.1, lt_of_lt_of_le hxJ.2 (splitPt_le hβ hα0 hα1)⟩
      | true => exact ⟨le_trans (le_of_lt (splitPt_pos hβ hα0 hα1)) hxJ.1, hxJ.2⟩

theorem cyl_ordConnected : ∀ w, (cyl β α w).OrdConnected
  | [] => by rw [cyl]; exact ordConnected_Ico
  | j :: w => by
      rw [cyl]
      constructor
      rintro x hx y hy z ⟨hxz, hzy⟩
      obtain ⟨hxJ, hxc⟩ := hx
      obtain ⟨hyJ, hyc⟩ := hy
      have hzJ : z ∈ (if j then Ico (splitPt β α) (1 / β) else Ico 0 (splitPt β α)) := by
        have : (if j then Ico (splitPt β α) (1 / β) else Ico 0 (splitPt β α)).OrdConnected := by
          cases j <;> simp <;> exact ordConnected_Ico
        exact this.out hxJ hyJ ⟨hxz, hzy⟩
      exact ⟨hzJ, (cyl_ordConnected w).out hxc hyc
        ⟨lmo_mono_branch hβ hα0 hα1 j hxJ hzJ hxz, lmo_mono_branch hβ hα0 hα1 j hzJ hyJ hzy⟩⟩

/-- Every point of `cyl w` keeps its first `|w|` iterates inside `J`. -/
theorem cyl_stays : ∀ (w : List Bool) {x : ℝ}, x ∈ cyl β α w →
    ∀ k < w.length, (lmo β α)^[k] x ∈ Ico 0 (1 / β)
  | [], x, _, k, hk => by simp at hk
  | j :: w, x, hx, k, hk => by
      rw [cyl] at hx
      obtain ⟨hxJ, hxc⟩ := hx
      have hxJ' : x ∈ Ico 0 (1 / β) := cyl_subset_J hβ hα0 hα1 (j :: w) (by rw [cyl]; exact ⟨hxJ, hxc⟩)
      match k with
      | 0 => simpa using hxJ'
      | k + 1 =>
          rw [Function.iterate_succ_apply]
          exact cyl_stays w hxc k (by simpa using Nat.lt_of_succ_lt_succ hk)

/-! ## Child criteria -/

theorem false_child_nonempty (w : List Bool) :
    (cyl β α (false :: w)).Nonempty ↔ (cyl β α w ∩ Ico α 1).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [cyl] at hx
    obtain ⟨hxJ, hxc⟩ := hx
    simp only [ite_eq_right (by decide : ¬ (false = true))] at hxJ
    refine ⟨lmo β α x, hxc, ?_⟩
    rw [lmo_lower hβ hα0 hα1 hxJ.1 hxJ.2]
    refine ⟨by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β) hxJ.1], ?_⟩
    have : β * x < β * splitPt β α := mul_lt_mul_of_pos_left hxJ.2 (by linarith)
    rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at this; linarith
  · rintro ⟨y, hyc, hy1, hy2⟩
    refine ⟨(y - α) / β, ?_⟩
    have hx0 : 0 ≤ (y - α) / β := by rw [le_div_iff₀ (by linarith)]; nlinarith [hy1]
    have hxc : (y - α) / β < splitPt β α := by
      rw [div_lt_iff₀ (by linarith), splitPt, div_mul_cancel₀ _ (by linarith : β ≠ 0)]; linarith
    rw [cyl]
    refine ⟨by simp only [ite_eq_right (by decide : ¬ (false = true))]; exact ⟨hx0, hxc⟩, ?_⟩
    rw [lmo_lower hβ hα0 hα1 hx0 hxc, mul_div_cancel₀ _ (by linarith : β ≠ 0)]
    simpa using hyc

theorem true_child_nonempty (w : List Bool) :
    (cyl β α (true :: w)).Nonempty ↔ (cyl β α w ∩ Ico 0 α).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [cyl] at hx
    obtain ⟨hxJ, hxc⟩ := hx
    refine ⟨lmo β α x, hxc, ?_⟩
    rw [lmo_upper hβ hα0 hα1 hxJ.1 hxJ.2]
    have hge : β * splitPt β α ≤ β * x := mul_le_mul_of_nonneg_left hxJ.1 (by linarith)
    rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at hge
    have hlt : β * x < β * (1 / β) := mul_lt_mul_of_pos_left hxJ.2 (by linarith)
    rw [mul_one_div, div_self (by linarith : β ≠ 0)] at hlt
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨y, hyc, hy1, hy2⟩
    refine ⟨(y + 1 - α) / β, ?_⟩
    have hx0 : splitPt β α ≤ (y + 1 - α) / β := by
      rw [splitPt, div_le_div_iff_of_pos_right (by linarith)]; linarith
    have hxc : (y + 1 - α) / β < 1 / β := by
      rw [div_lt_div_iff_of_pos_right (by linarith)]; linarith
    rw [cyl]
    refine ⟨⟨hx0, hxc⟩, ?_⟩
    rw [lmo_upper hβ hα0 hα1 hx0 hxc]
    have hcan : β * ((y + 1 - α) / β) = y + 1 - α := by field_simp
    rw [hcan, show y + 1 - α + α - 1 = y by ring]; exact hyc

/-- A straddling cylinder contains `α` (order-connectedness). -/
theorem straddle_mem (w : List Bool) (h : straddle β α w) : α ∈ cyl β α w := by
  obtain ⟨⟨p, hp, hp0, hpα⟩, ⟨q, hq, hqα, hq1⟩⟩ := h
  exact (cyl_ordConnected hβ hα0 hα1 w).out hp hq ⟨le_of_lt hpα, hqα⟩

/-- `straddle` is having two nonempty children. -/
theorem straddle_iff (w : List Bool) :
    straddle β α w ↔ (cyl β α (false :: w)).Nonempty ∧ (cyl β α (true :: w)).Nonempty := by
  rw [false_child_nonempty hβ hα0 hα1, true_child_nonempty hβ hα0 hα1, straddle]; tauto

/-- Distinct cylinders of the same depth are disjoint: a common point forces equality. -/
theorem cyl_eq_of_mem : ∀ (w w' : List Bool) {z : ℝ},
    z ∈ cyl β α w → z ∈ cyl β α w' → w.length = w'.length → w = w'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, hlen => by simp at hlen
  | j :: w, j' :: w', z, hz, hz', hlen => by
      rw [cyl] at hz hz'
      obtain ⟨hzJ, hzc⟩ := hz
      obtain ⟨hzJ', hzc'⟩ := hz'
      have hj : j = j' := by
        cases j <;> cases j'
        · rfl
        · exact absurd (lt_of_lt_of_le hzJ.2 hzJ'.1) (by simp)
        · exact absurd (lt_of_lt_of_le hzJ'.2 hzJ.1) (by simp)
        · rfl
      subst hj
      rw [cyl_eq_of_mem w w' hzc hzc' (by simpa using hlen)]

/-! ## Counting: at most `N + 1` nonempty cylinders at any depth -/

theorem children_card_le (w : List Bool) :
    (children β α w).card ≤ 1 + (if straddle β α w then 1 else 0) := by
  unfold children
  rw [Finset.card_image_of_injective _ (fun a b h => (List.cons.inj h).1)]
  by_cases hs : straddle β α w
  · rw [ite_eq_left hs]
    calc (Finset.univ.filter fun j : Bool => (cyl β α (j :: w)).Nonempty).card
        ≤ (Finset.univ : Finset Bool).card := Finset.card_filter_le _ _
      _ = 2 := by decide
      _ = 1 + 1 := by norm_num
  · rw [ite_eq_right hs, add_zero, Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact hs ((straddle_iff hβ hα0 hα1 w).mpr (by cases a <;> cases b <;> simp_all))

theorem alive_mem_length : ∀ (m : ℕ) (w : List Bool),
    w ∈ alive β α m ↔ w.length = m ∧ (cyl β α w).Nonempty
  | 0, w => by
      simp only [alive, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨rfl, ⟨0, by rw [cyl]; exact ⟨le_refl 0, one_div_pos.mpr (by linarith)⟩⟩⟩
      · rintro ⟨hlen, _⟩; exact List.length_eq_zero_iff.mp hlen
  | m + 1, w => by
      simp only [alive, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hwv⟩
        simp only [children, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hwv
        obtain ⟨j, hjne, rfl⟩ := hwv
        exact ⟨by simp [((alive_mem_length m v).mp hv).1], hjne⟩
      · rintro ⟨hlen, hne⟩
        cases w with
        | nil => simp at hlen
        | cons j v =>
            have hvlen : v.length = m := by simpa using hlen
            have hvne : (cyl β α v).Nonempty := by
              obtain ⟨y, hy⟩ := hne; rw [cyl] at hy; exact ⟨lmo β α y, hy.2⟩
            refine ⟨v, (alive_mem_length m v).mpr ⟨hvlen, hvne⟩, ?_⟩
            simp only [children, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hne, rfl⟩

/-- At most one cylinder straddles `α` per depth (disjointness + `straddle_mem`). -/
theorem straddle_filter_card_le_one (m : ℕ) :
    ((alive β α m).filter (straddle β α)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro w hw w' hw'
  simp only [Finset.mem_filter] at hw hw'
  exact cyl_eq_of_mem hβ hα0 hα1 w w' (straddle_mem hβ hα0 hα1 w hw.2)
    (straddle_mem hβ hα0 hα1 w' hw'.2)
    (by rw [((alive_mem_length hβ hα0 hα1 m w).mp hw.1).1,
      ((alive_mem_length hβ hα0 hα1 m w').mp hw'.1).1])

/-- `f^k(α) = f^{k+1}(0)`: the orbit of `α` is that of `0` shifted (since `f(0) = α`). -/
theorem iterate_alpha (k : ℕ) : (lmo β α)^[k] α = (lmo β α)^[k + 1] 0 := by
  rw [Function.iterate_succ_apply, lmo_zero hα0 hα1]

/-- A straddle at depth `m` forces `m < N`: it makes `α` (hence `0`'s orbit `f,…,f^m`) stay in
`J`, impossible once `m ≥ N` by the escape hypothesis. -/
theorem straddle_lt_N {N : ℕ} (hesc : 1 / β ≤ (lmo β α)^[N] 0) {m : ℕ} {w : List Bool}
    (hw : w ∈ alive β α m) (hstr : straddle β α w) : m < N := by
  have hlen : w.length = m := ((alive_mem_length hβ hα0 hα1 m w).mp hw).1
  have hmem : α ∈ cyl β α w := straddle_mem hβ hα0 hα1 w hstr
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp only [Function.iterate_zero, id] at hesc
      have : (0 : ℝ) < 1 / β := one_div_pos.mpr (by linarith)
      linarith
    · exact h
  by_contra hle
  push Not at hle
  have hk : N - 1 < w.length := by rw [hlen]; omega
  have hstay := cyl_stays hβ hα0 hα1 w hmem (N - 1) hk
  rw [iterate_alpha hβ hα0 hα1 (N - 1), show N - 1 + 1 = N by omega] at hstay
  exact absurd hstay.2 (not_lt.mpr hesc)

theorem splitCount_le {N : ℕ} (hesc : 1 / β ≤ (lmo β α)^[N] 0) (m : ℕ) :
    ((alive β α m).filter (straddle β α)).card ≤ (if m < N then 1 else 0) := by
  by_cases hm : m < N
  · rw [ite_eq_left hm]; exact straddle_filter_card_le_one hβ hα0 hα1 m
  · rw [ite_eq_right hm, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun w hw hstr => hm (straddle_lt_N hβ hα0 hα1 hesc hw hstr)

theorem alive_step {N : ℕ} (hesc : 1 / β ≤ (lmo β α)^[N] 0) (m : ℕ) :
    (alive β α (m + 1)).card ≤ (alive β α m).card + (if m < N then 1 else 0) := by
  rw [alive]
  calc ((alive β α m).biUnion (children β α)).card
      ≤ ∑ w ∈ alive β α m, (children β α w).card := Finset.card_biUnion_le
    _ ≤ ∑ w ∈ alive β α m, (1 + if straddle β α w then 1 else 0) :=
        Finset.sum_le_sum (fun w _ => children_card_le hβ hα0 hα1 w)
    _ = (alive β α m).card + ((alive β α m).filter (straddle β α)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole,
          Nat.cast_id]
    _ ≤ (alive β α m).card + (if m < N then 1 else 0) := by
        have := splitCount_le hβ hα0 hα1 hesc m; omega

theorem alive_card_le {N : ℕ} (hesc : 1 / β ≤ (lmo β α)^[N] 0) (m : ℕ) :
    (alive β α m).card ≤ N + 1 := by
  have hbound : ∀ m, (alive β α m).card ≤ 1 + min m N := by
    intro m
    induction m with
    | zero => simp [alive]
    | succ k ih =>
        have hstep := alive_step hβ hα0 hα1 hesc k
        rcases Nat.lt_or_ge k N with hk | hk
        · rw [ite_eq_left hk] at hstep; omega
        · rw [ite_eq_right (not_lt.mpr hk)] at hstep; omega
  have := hbound m; omega

/-! ## Expansivity -/

/-- The two branch maps have slope `β`: same branch ⟹ difference scales by `β`. -/
theorem lmo_diff {u v : ℝ} (hu : u ∈ Ico (0 : ℝ) (1 / β)) (hv : v ∈ Ico (0 : ℝ) (1 / β))
    (hb : decide (splitPt β α ≤ u) = decide (splitPt β α ≤ v)) :
    lmo β α u - lmo β α v = β * (u - v) := by
  have hiff : (splitPt β α ≤ u) ↔ (splitPt β α ≤ v) := decide_eq_decide.mp hb
  by_cases hcu : splitPt β α ≤ u
  · rw [lmo_upper hβ hα0 hα1 hcu hu.2, lmo_upper hβ hα0 hα1 (hiff.mp hcu) hv.2]; ring
  · have hcv : ¬ splitPt β α ≤ v := fun h => hcu (hiff.mpr h)
    push Not at hcu hcv
    rw [lmo_lower hβ hα0 hα1 hu.1 hcu, lmo_lower hβ hα0 hα1 hv.1 hcv]; ring

/-- Same first `m` branches ⟹ the two points differ by exactly `β^m·(x−y)`. -/
theorem iter_sub_eq {x y : ℝ} (hx : ∀ n, (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β))
    (hy : ∀ n, (lmo β α)^[n] y ∈ Ico (0 : ℝ) (1 / β)) :
    ∀ m, word β α x m = word β α y m →
      (lmo β α)^[m] x - (lmo β α)^[m] y = β ^ m * (x - y) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hw
      rw [word_succ_eq, word_succ_eq] at hw
      obtain ⟨hpre, htail⟩ := List.append_inj hw (by rw [word_length, word_length])
      have hlast : decide (splitPt β α ≤ (lmo β α)^[m] x)
          = decide (splitPt β α ≤ (lmo β α)^[m] y) := by simpa using htail
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        lmo_diff hβ hα0 hα1 (hx m) (hy m) hlast, ih hpre, pow_succ]
      ring

/-- Distinct survivors have distinct itineraries (expansivity). -/
theorem eq_of_word_eq {x y : ℝ} (hx : ∀ n, (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β))
    (hy : ∀ n, (lmo β α)^[n] y ∈ Ico (0 : ℝ) (1 / β))
    (h : ∀ m, word β α x m = word β α y m) : x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt1 : (1 : ℝ) / β < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos hlt1
  have hsub := iter_sub_eq hβ hα0 hα1 hx hy m (h m)
  have hb : |(lmo β α)^[m] x - (lmo β α)^[m] y| < 1 / β := by
    obtain ⟨a1, a2⟩ := hx m; obtain ⟨b1, b2⟩ := hy m
    rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
  rw [hsub, abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < β) m)] at hb
  have h2 : |x - y| < (1 / β) ^ (m + 1) := by
    rw [div_pow, one_pow, lt_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < β) (m + 1)), pow_succ]
    have hmul := mul_lt_mul_of_pos_left hb (show (0 : ℝ) < β by linarith)
    rw [mul_one_div, div_self (by linarith : β ≠ 0)] at hmul
    nlinarith [hmul]
  have h3 : (1 / β) ^ (m + 1) ≤ (1 / β) ^ m := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (le_of_lt (one_div_pos.mpr (by linarith))) m)
      (le_of_lt hlt1)
  linarith

/-! ## The survivor set is finite -/

/-- Every survivor lies in the cylinder of its own itinerary. -/
theorem mem_cyl_word : ∀ (m : ℕ) {x : ℝ}, x ∈ survivors β α → x ∈ cyl β α (word β α x m) := by
  intro m
  induction m with
  | zero =>
      intro x hx
      have hw : word β α x 0 = [] := by simp [word]
      rw [hw, cyl]; exact hx.1
  | succ m ih =>
      intro x hx
      rw [word_succ_cons, cyl]
      refine ⟨?_, ih (lmo_mem_survivors hx)⟩
      by_cases hc : splitPt β α ≤ x
      · rw [decide_eq_true_eq.mpr hc]; exact ⟨hc, hx.1.2⟩
      · rw [decide_eq_false (by simpa using hc)]; exact ⟨hx.1.1, not_le.mp hc⟩

theorem word_mem_alive {x : ℝ} (hx : x ∈ survivors β α) (m : ℕ) :
    word β α x m ∈ alive β α m :=
  (alive_mem_length hβ hα0 hα1 m (word β α x m)).mpr
    ⟨word_length x m, ⟨x, mem_cyl_word hβ hα0 hα1 m hx⟩⟩

/-- **FLP95 Theorem 3.4 (finiteness):** if the origin escapes (`1/β ≤ f^N(0)`), then the survivor
set is finite. -/
theorem survivors_finite {N : ℕ} (hesc : 1 / β ≤ (lmo β α)^[N] 0) :
    (survivors β α).Finite := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (N + 2)
  have hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ m, word β α x m ≠ word β α y m := by
    intro x hx y hy hxy
    by_contra h; push Not at h
    exact hxy (eq_of_word_eq hβ hα0 hα1 (survivors_iterate_mem (hTsub hx))
      (survivors_iterate_mem (hTsub hy)) h)
  set sepIdx : ℝ × ℝ → ℕ := fun p =>
    if h : ∃ m, word β α p.1 m ≠ word β α p.2 m then Nat.find h else 0 with hsepIdx
  set M := T.offDiag.sup sepIdx with hMdef
  have hM : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → word β α x M ≠ word β α y M := by
    intro x hx y hy hxy
    have hex : ∃ m, word β α x m ≠ word β α y m := hsep x hx y hy hxy
    have hsi : word β α x (sepIdx (x, y)) ≠ word β α y (sepIdx (x, y)) := by
      rw [hsepIdx]; simp only [dite_eq_left hex]; exact Nat.find_spec hex
    exact word_ne_mono (Finset.le_sup (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)) hsi
  have hinj : Set.InjOn (fun x => word β α x M) T := by
    intro x hx y hy heq
    by_contra hxy
    exact hM x hx y hy hxy heq
  have hsub : (T.image (fun x => word β α x M)) ⊆ alive β α M := by
    intro w hw
    simp only [Finset.mem_image] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact word_mem_alive hβ hα0 hα1 (hTsub hx) M
  have hcard : T.card ≤ N + 1 :=
    calc T.card = (T.image (fun x => word β α x M)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (alive β α M).card := Finset.card_le_card hsub
      _ ≤ N + 1 := alive_card_le hβ hα0 hα1 hesc M
  omega

end

end FLP
