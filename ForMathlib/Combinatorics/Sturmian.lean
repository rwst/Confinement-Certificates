/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.InfiniteComplexity

/-!
# Sturmian words and the bispecial criterion

A binary word is **Sturmian** when its subword complexity is exactly `m + 1` at every length `m` —
by Morse–Hedlund the minimum compatible with aperiodicity.  This file proves the criterion used in
symbolic-dynamics arguments about `⌊ξ (p/q)ⁿ⌋`:

> an aperiodic binary word in which no finite word `u` has **both** `0u0` and `1u1` as factors is
> Sturmian.

## Main results

* `IsSturmian` — `p_W(m) = m + 1` for every `m`.
* `HasBispecialPair` — some finite word `u` occurs flanked by `0`s and (elsewhere) by `1`s.
* `isSturmian_of_not_hasBispecialPair` — the criterion above.
* `exists_factor_eq_of_isSturmian` — the pigeonhole consequence: in a Sturmian word two of the
  `m + 2` factors read at positions `0, …, m + 1` coincide.

## Proof

The classical route (Lothaire, Proposition 2.1.3 and Theorem 2.1.5) goes through *balance*: a word
is unbalanced iff some palindrome `u` has `0u0` and `1u1` as factors, and aperiodic + balanced is
equivalent to complexity `m + 1`.  The route taken here is shorter, because a bispecial pair is
*exactly* the obstruction to uniqueness of the right-special factor:

1. `hasBispecialPair_of_flank` — two positions whose letters agree strictly between offsets `t₀`
   and `m`, disagree at `t₀`, and repeat their `t₀`-letter at offset `m`, form a bispecial pair
   (read the two occurrences starting at offset `t₀`).
2. `factor_eq_of_not_hasBispecialPair` — hence at most one length-`m` factor is right-special: if
   two were, take the **longest common suffix** `z` of the two, of length `d`; the letters
   preceding the two copies of `z` differ, and each factor may be continued by whichever letter
   matches its own preceding one, producing `0z0` and `1z1`.
3. `pComplexity_succ_le_of_not_hasBispecialPair` — truncating the last letter maps the length-`m+1`
   factors onto the length-`m` factors, injectively away from the single exceptional factor
   `u₀ ⌢ 1`; so `p_W(m + 1) ≤ p_W(m) + 1` and inductively `p_W(m) ≤ m + 1`.
4. The matching floor `p_W(m) ≥ m + 1` is
   `pComplexity_lt_succ_of_not_isEventuallyPeriodic` from
   `ForMathlib.Combinatorics.InfiniteComplexity`.

## References

* [Lot02] M. Lothaire, *Algebraic Combinatorics on Words*, Encyclopedia of Mathematics and its
  Applications **90**, Cambridge Univ. Press, 2002 — Proposition 2.1.3 and Theorem 2.1.5 (the
  balance route to the same criterion).
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics II: Sturmian trajectories*, Amer. J. Math.
  **62** (1940), 1–42.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — §2 uses exactly the statement proved here: "an aperiodic
  word on the alphabet `A = {U, V}` is Sturmian if and only if for any finite word `u` on `A`
  either `UuU` or `VuV` is not a factor of `w`".
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Definitions -/

/-- A word over a finite alphabet is **Sturmian** when it has exactly `m + 1` distinct factors of
each length `m`.

This is the standard definition; by Morse–Hedlund it is the least complexity compatible with not
being eventually periodic. -/
def IsSturmian [Finite α] (W : ℕ → α) : Prop :=
  ∀ m : ℕ, pComplexity W m = m + 1

/-- `W` has a **bispecial pair**: a common factor `u` of length `m`, occurring at `i + 1` and at
`j + 1`, whose two occurrences are flanked by `false` on both sides in the first case and by `true`
on both sides in the second — i.e. `0u0` and `1u1` are both factors of `W`. -/
def HasBispecialPair (W : ℕ → Bool) : Prop :=
  ∃ m i j : ℕ,
    W i = false ∧ W (i + 1 + m) = false ∧ W j = true ∧ W (j + 1 + m) = true ∧
      ∀ t, t < m → W (i + 1 + t) = W (j + 1 + t)

/-! ## The complexity floor -/

/-- There is exactly one factor of length `0`, the empty word. -/
@[simp]
lemma pComplexity_zero [Finite α] (u : ℕ → α) : pComplexity u 0 = 1 := by
  rw [pComplexity, Set.ncard_eq_one]
  exact ⟨factor u 0 0, Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨0, rfl⟩, fun x _ => funext fun s => s.elim0⟩⟩

/-- **Morse–Hedlund's floor.**  A word that is not eventually periodic has at least `m + 1`
factors of each length `m`. -/
lemma succ_le_pComplexity [Finite α] {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (m : ℕ) :
    m + 1 ≤ pComplexity u m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have := pComplexity_lt_succ_of_not_isEventuallyPeriodic hu k
    omega

/-! ## At most one right-special factor -/

/-- **The flank construction.**  Suppose two positions `A`, `B` carry the same letters at every
offset strictly between `t₀` and `m`, carry `false` resp. `true` at offset `t₀`, and repeat that
letter at offset `m`.  Reading both occurrences from offset `t₀` exhibits a bispecial pair: the
common middle block of length `m - 1 - t₀` is flanked by `0`s at `A` and by `1`s at `B`. -/
private lemma hasBispecialPair_of_flank {W : ℕ → Bool} {m t₀ A B : ℕ} (ht₀ : t₀ < m)
    (hA0 : W (A + t₀) = false) (hAm : W (A + m) = false)
    (hB0 : W (B + t₀) = true) (hBm : W (B + m) = true)
    (hmid : ∀ s, t₀ < s → s < m → W (A + s) = W (B + s)) :
    HasBispecialPair W := by
  refine ⟨m - 1 - t₀, A + t₀, B + t₀, hA0, ?_, hB0, ?_, ?_⟩
  · have e : A + t₀ + 1 + (m - 1 - t₀) = A + m := by omega
    rw [e]; exact hAm
  · have e : B + t₀ + 1 + (m - 1 - t₀) = B + m := by omega
    rw [e]; exact hBm
  · intro s hs
    have e1 : A + t₀ + 1 + s = A + (t₀ + 1 + s) := by omega
    have e2 : B + t₀ + 1 + s = B + (t₀ + 1 + s) := by omega
    rw [e1, e2]
    exact hmid (t₀ + 1 + s) (by omega) (by omega)

/-- **Uniqueness of the right-special factor.**  In a word with no bispecial pair, a length-`m`
factor admitting both continuations is unique: if the factor at `a` continues with `false` (at `b`
with `true`) and likewise the factor at `a'` continues with `false` (at `b'` with `true`), then the
factors at `a` and `a'` coincide.

The proof takes the longest common suffix `z` of the two candidate factors — say of length
`m - 1 - t₀`, so that they first differ at offset `t₀`.  Whichever of the two carries `false` at
offset `t₀` may be continued by `false`, the other by `true`, and `0z0`, `1z1` are both factors. -/
lemma factor_eq_of_not_hasBispecialPair {W : ℕ → Bool} (h : ¬ HasBispecialPair W)
    {m a b a' b' : ℕ}
    (hab : ∀ t, t < m → W (a + t) = W (b + t)) (ha : W (a + m) = false) (hb : W (b + m) = true)
    (hab' : ∀ t, t < m → W (a' + t) = W (b' + t)) (ha' : W (a' + m) = false)
    (hb' : W (b' + m) = true) :
    ∀ t, t < m → W (a + t) = W (a' + t) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨t, htm, htne⟩ := hcon
  -- the largest offset at which the two candidate factors differ
  set D : Finset ℕ := (Finset.range m).filter (fun s => W (a + s) ≠ W (a' + s)) with hD
  have hmemD : ∀ s, s ∈ D ↔ s < m ∧ W (a + s) ≠ W (a' + s) := by
    intro s; rw [hD, Finset.mem_filter, Finset.mem_range]
  have hDne : D.Nonempty := ⟨t, (hmemD t).mpr ⟨htm, htne⟩⟩
  obtain ⟨t₀, ht₀D, ht₀max⟩ : ∃ t₀, t₀ ∈ D ∧ ∀ s ∈ D, s ≤ t₀ :=
    ⟨D.max' hDne, D.max'_mem hDne, fun s hs => D.le_max' s hs⟩
  obtain ⟨ht₀m, ht₀ne⟩ := (hmemD t₀).mp ht₀D
  -- beyond `t₀` the two factors agree: that common suffix is the middle block
  have hmid : ∀ s, t₀ < s → s < m → W (a + s) = W (a' + s) := by
    intro s hs hsm
    by_contra hne
    exact absurd (ht₀max s ((hmemD s).mpr ⟨hsm, hne⟩)) (by omega)
  cases hv : W (a + t₀) with
  | false =>
    have h' : W (a' + t₀) = true := by
      cases e : W (a' + t₀)
      · exact absurd (hv.trans e.symm) ht₀ne
      · rfl
    refine h (hasBispecialPair_of_flank ht₀m hv ha ?_ hb' ?_)
    · rw [← hab' t₀ ht₀m]; exact h'
    · intro s hs hsm
      rw [hmid s hs hsm]; exact hab' s hsm
  | true =>
    have h' : W (a' + t₀) = false := by
      cases e : W (a' + t₀)
      · rfl
      · exact absurd (hv.trans e.symm) ht₀ne
    refine h (hasBispecialPair_of_flank ht₀m h' ha' ?_ hb ?_)
    · rw [← hab t₀ ht₀m]; exact hv
    · intro s hs hsm
      rw [← hmid s hs hsm]; exact hab s hsm

/-! ## The complexity ceiling -/

/-- **One extra factor per length.**  Truncating the last letter maps the length-`(m + 1)` factors
onto the length-`m` factors, and — no bispecial pair — injectively except above the single
right-special factor.  Hence `p_W(m + 1) ≤ p_W(m) + 1`. -/
lemma pComplexity_succ_le_of_not_hasBispecialPair {W : ℕ → Bool} (h : ¬ HasBispecialPair W)
    (m : ℕ) : pComplexity W (m + 1) ≤ pComplexity W m + 1 := by
  classical
  -- a length-`m` word `u₀` containing every right-special factor
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin m → Bool, ∀ a b : ℕ, (∀ t, t < m → W (a + t) = W (b + t)) →
      W (a + m) = false → W (b + m) = true → factor W m a = u₀ := by
    by_cases hrs : ∃ i j : ℕ, (∀ t, t < m → W (i + t) = W (j + t)) ∧
        W (i + m) = false ∧ W (j + m) = true
    · obtain ⟨i, j, hij, hi, hj⟩ := hrs
      exact ⟨factor W m i, fun a b hab ha hb => (factor_eq_iff W m a i).mpr
        (factor_eq_of_not_hasBispecialPair h hab ha hb hij hi hj)⟩
    · exact ⟨fun _ => false, fun a b hab ha hb => absurd ⟨a, b, hab, ha, hb⟩ hrs⟩
  -- a length-`(m + 1)` word is determined by its truncation and its last letter
  have hrec : ∀ v w : Fin (m + 1) → Bool, v ∘ Fin.castSucc = w ∘ Fin.castSucc →
      v (Fin.last m) = w (Fin.last m) → v = w := by
    intro v w h1 h2
    funext s
    refine Fin.lastCases ?_ ?_ s
    · exact h2
    · intro r
      simpa using congrFun h1 r
  have hkey : ∀ a b : ℕ, factor W (m + 1) a ∘ Fin.castSucc = factor W (m + 1) b ∘ Fin.castSucc →
      W (a + m) = false → W (b + m) = true → factor W (m + 1) a ∘ Fin.castSucc = u₀ := by
    intro a b hcs ha hb
    have h1 : factor W m a = factor W m b := by
      rw [factor_castSucc W m a, factor_castSucc W m b]; exact hcs
    rw [← factor_castSucc]
    exact hu₀ a b ((factor_eq_iff W m a b).mp h1) ha hb
  -- the exceptional factor: `u₀` continued by `true`
  set e : Fin (m + 1) → Bool := Fin.snoc u₀ true with he
  have hecs : e ∘ Fin.castSucc = u₀ := by rw [he]; exact Fin.snoc_comp_castSucc
  have helast : e (Fin.last m) = true := by rw [he]; exact Fin.snoc_last _ _
  set S : Set (Fin (m + 1) → Bool) := factorSet W (m + 1) with hS
  set S' : Set (Fin (m + 1) → Bool) := S \ {e} with hS'
  -- truncation is injective away from `e`
  have hstep : ∀ v ∈ S', ∀ w ∈ S', v ∘ Fin.castSucc = w ∘ Fin.castSucc →
      v (Fin.last m) = false → w (Fin.last m) = true → False := by
    intro v hv w hw hcs hvl hwl
    obtain ⟨a, rfl⟩ := hv.1
    obtain ⟨b, hb⟩ := hw.1
    have hwe : w ≠ e := hw.2
    subst hb
    have h1 : factor W (m + 1) a ∘ Fin.castSucc = u₀ :=
      hkey a b hcs (by simpa [factor] using hvl) (by simpa [factor] using hwl)
    have h2 : factor W (m + 1) b ∘ Fin.castSucc = u₀ := hcs.symm.trans h1
    exact hwe (hrec _ _ (by rw [hecs]; exact h2) (by rw [helast]; exact hwl))
  have hinj : Set.InjOn (fun v : Fin (m + 1) → Bool => v ∘ Fin.castSucc) S' := by
    intro v hv w hw hcs
    by_contra hne
    have hlast : v (Fin.last m) ≠ w (Fin.last m) := fun hl => hne (hrec v w hcs hl)
    cases hvl : v (Fin.last m) with
    | false =>
      have hwl : w (Fin.last m) = true := by
        cases ew : w (Fin.last m)
        · exact absurd (hvl.trans ew.symm) hlast
        · rfl
      exact hstep v hv w hw hcs hvl hwl
    | true =>
      have hwl : w (Fin.last m) = false := by
        cases ew : w (Fin.last m)
        · rfl
        · exact absurd (hvl.trans ew.symm) hlast
      exact hstep w hw v hv hcs.symm hwl hvl
  -- count
  have hsub : S ⊆ insert e S' := by
    intro v hv
    by_cases hve : v = e
    · exact Or.inl hve
    · exact Or.inr ⟨hv, hve⟩
  have himg : (fun v : Fin (m + 1) → Bool => v ∘ Fin.castSucc) '' S' ⊆ factorSet W m := by
    rw [← image_factorSet_castSucc W m]
    exact Set.image_mono Set.sdiff_subset
  calc pComplexity W (m + 1) = S.ncard := rfl
    _ ≤ (insert e S').ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ S'.ncard + 1 := Set.ncard_insert_le e S'
    _ = ((fun v : Fin (m + 1) → Bool => v ∘ Fin.castSucc) '' S').ncard + 1 := by
        rw [hinj.ncard_image]
    _ ≤ pComplexity W m + 1 := by
        have h3 : ((fun v : Fin (m + 1) → Bool => v ∘ Fin.castSucc) '' S').ncard
            ≤ pComplexity W m := Set.ncard_le_ncard himg (finite_factorSet W m)
        omega

/-- The complexity ceiling: a binary word with no bispecial pair has at most `m + 1` factors of
each length `m`. -/
lemma pComplexity_le_succ_of_not_hasBispecialPair {W : ℕ → Bool} (h : ¬ HasBispecialPair W)
    (m : ℕ) : pComplexity W m ≤ m + 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have := pComplexity_succ_le_of_not_hasBispecialPair h k
    omega

/-! ## The criterion -/

/-- **The bispecial criterion for Sturmian words.**  An aperiodic binary word in which no finite
word `u` has both `0u0` and `1u1` as factors has complexity exactly `m + 1` at every length, i.e.
is Sturmian.

This is the direction of [Lot02, Prop. 2.1.3 + Thm. 2.1.5] used in Diophantine arguments; the
converse (a Sturmian word has no bispecial pair) is the easy one and is not needed here. -/
theorem isSturmian_of_not_hasBispecialPair {W : ℕ → Bool}
    (haper : ¬ IsEventuallyPeriodic W) (hbal : ¬ HasBispecialPair W) : IsSturmian W := fun m =>
  le_antisymm (pComplexity_le_succ_of_not_hasBispecialPair hbal m) (succ_le_pComplexity haper m)

/-! ## The pigeonhole consequence

With only `m + 1` factors of length `m` available, the `m + 2` factors read at positions
`0, 1, …, m + 1` cannot be pairwise distinct. -/

/-- **Two early occurrences of one factor.**  In a Sturmian word, for every `m` there are positions
`i < j ≤ m + 1` carrying the same length-`m` factor.

The bound `j ≤ m + 1` is what makes [Dub09AA]'s endgame work: the repetition happens *within* the
first `m + 2` letters. -/
theorem exists_factor_eq_of_isSturmian {α : Type*} [Finite α] {W : ℕ → α} (hW : IsSturmian W)
    (m : ℕ) : ∃ i j : ℕ, i < j ∧ j ≤ m + 1 ∧ ∀ t, t < m → W (i + t) = W (j + t) := by
  classical
  have hcard : ((↑(Finset.range (m + 2)) : Set ℕ)).ncard = m + 2 := by
    rw [Set.ncard_coe_finset, Finset.card_range]
  have hlt : (factorSet W m).ncard < ((↑(Finset.range (m + 2)) : Set ℕ)).ncard := by
    rw [hcard, ← pComplexity, hW m]; omega
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt
      (fun n _ => (⟨n, rfl⟩ : factor W m n ∈ factorSet W m)) (finite_factorSet W m)
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, by omega, (factor_eq_iff W m a b).mp heq⟩
  · exact ⟨b, a, h, by omega, (factor_eq_iff W m b a).mp heq.symm⟩

end ForMathlib.SubwordComplexity
