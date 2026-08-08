/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Mathlib.Tactic

/-!
# Forward decoupling of a trapped orbit (FLP95, Lemma 2.1 / Prop 2.1, forward half)

For a `Z`-number `ξ ∈ Z_{p/q}(s, s + 1/p)` — a positive real whose whole `(p/q)`-power orbit
stays in the window `[s, s + 1/p)` — the paper decouples the orbit into

* an **integer part** `gₙ = ⌊ξ(p/q)ⁿ⌋` obeying `g_{n+1} = T(gₙ)`  (`T` = `FLP.TMap`), and
* a **fractional part** `θₙ = q({ξ(p/q)ⁿ} − s) ∈ [0, q/p)` obeying `θ_{n+1} = f(θₙ)`,
  where `f = f_{p/q, α}` is the linear mod-one map (`FLP.lmo`) with `α = {(p−q)s}`,

together with the **symbol match** `i_{gₙ} = ⌊(p/q)θₙ + α⌋` linking the two dynamics.

`plan-FLT.html` §3.1–3.2 records the two simplifications used here:

* **`t = 1/p`** makes conditions (C1),(C2) automatic (`{·} < 1 ≤ q − 1` for `q ≥ 2`) and the
  `f`-symbol binary, so no general-`t` bookkeeping is needed; and
* **only the forward direction** is proved (the sufficiency half of Lemma 2.1 is never used).

The entire step is one real identity (`decouple_step`),
`q(g_{n+1} − T(gₙ)) + (θ_{n+1} − f(θₙ)) = ⌊βθₙ+α⌋ − i_{gₙ}`, closed by "an integer that lies in
`(−1,1)` is `0`" (forcing `θ_{n+1} = f(θₙ)`) and "a multiple of `q` with `|·| < q` is `0`"
(forcing `g_{n+1} = T(gₙ)` and `i_{gₙ} = ⌊βθₙ+α⌋` simultaneously).

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, §2 (Lemma 2.1,
  Prop 2.1) at the specialization `t = 1/p`.
-/

namespace FLP

open Set

/-! ## The abstract single step -/

/-- **The decoupling single step** (FLP §2, `t = 1/p`), stated abstractly over the reals.

Given the ceiling linearization `q·T = pg + a + i` (`FLP.TMap_mul`), the orbit relation
`q(g' + s + θ'/q) = p(g + s + θ/q)` (i.e. `q·ξβ^{n+1} = p·ξβⁿ`), the trap bounds
`θ, θ' ∈ [0, q/p)`, and the parameter identity `a + α = (p−q)s` with `α ∈ [0,1)`, the next
integer part is `T(g)`, the next fractional part is `f_{p/q,α}(θ) = {(p/q)θ + α}`, and the
symbol `i` equals `⌊(p/q)θ + α⌋`. -/
theorem decouple_step {p q a g g' T i : ℕ} {s θ θ' α : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hiq : i < q)
    (hig : (q : ℝ) * T = p * g + a + i)
    (hβ : (q : ℝ) * ((g' : ℝ) + s + θ' / q) = p * ((g : ℝ) + s + θ / q))
    (hθlo : 0 ≤ θ) (hθhi : θ < (q : ℝ) / p)
    (hθ'lo : 0 ≤ θ') (hθ'hi : θ' < (q : ℝ) / p)
    (haα : (a : ℝ) + α = ((p : ℝ) - q) * s) (hαlo : 0 ≤ α) (hαhi : α < 1) :
    g' = T ∧ θ' = lmo ((p : ℝ) / q) α θ ∧ (⌊(p : ℝ) / q * θ + α⌋ : ℤ) = i := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
  set F : ℝ := Int.fract ((p : ℝ) / q * θ + α) with hF
  set L : ℤ := ⌊(p : ℝ) / q * θ + α⌋ with hL
  have hyLF : (L : ℝ) + F = (p : ℝ) / q * θ + α := by rw [hF, hL]; exact Int.floor_add_fract _
  have hmaster : (q : ℝ) * g' + θ' + i = (q : ℝ) * T + L + F := by
    linear_combination (norm := (field_simp; ring)) hβ - hig - haα - hyLF
  have hFlo : (0 : ℝ) ≤ F := Int.fract_nonneg _
  have hFhi : F < 1 := Int.fract_lt_one _
  have hθ'1 : θ' < 1 := lt_trans hθ'hi (by rw [div_lt_one hp0]; exact hqp')
  have hy0 : (0 : ℝ) ≤ (p : ℝ) / q * θ + α := add_nonneg (mul_nonneg (by positivity) hθlo) hαlo
  have hpqθ : (p : ℝ) / q * θ < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hq0]; linarith [(lt_div_iff₀ hp0).mp hθhi]
  have hL0 : 0 ≤ L := Int.floor_nonneg.mpr hy0
  have hL1 : L ≤ 1 := by
    have hle := Int.floor_le ((p : ℝ) / q * θ + α)
    rw [← hL] at hle
    have hlt2 : (L : ℝ) < 2 := by linarith
    have : L < 2 := by exact_mod_cast hlt2
    omega
  have hiZ : (i : ℤ) < q := by exact_mod_cast hiq
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  have hc : θ' - F = (((L : ℤ) - i - q * ((g' : ℤ) - T)) : ℝ) := by push_cast; linarith [hmaster]
  have hkeyR : ((L : ℤ) - i - q * ((g' : ℤ) - T)) = 0 := by
    have h1 : (((L : ℤ) - i - q * ((g' : ℤ) - T)) : ℝ) < 1 := by rw [← hc]; linarith
    have h2 : (-1 : ℝ) < (((L : ℤ) - i - q * ((g' : ℤ) - T)) : ℝ) := by rw [← hc]; linarith
    have h1' : ((L : ℤ) - i - q * ((g' : ℤ) - T)) < 1 := by exact_mod_cast h1
    have h2' : (-1 : ℤ) < ((L : ℤ) - i - q * ((g' : ℤ) - T)) := by exact_mod_cast h2
    omega
  have key : (L : ℤ) - i = q * ((g' : ℤ) - T) := by omega
  have hgT : (g' : ℤ) - T = 0 := by
    have hqpos : (0 : ℤ) < q := by omega
    have hb1 : q * ((g' : ℤ) - T) < q * 1 := by rw [← key]; omega
    have hb2 : q * (-1) < q * ((g' : ℤ) - T) := by rw [← key]; omega
    have h1 : (g' : ℤ) - T < 1 := _root_.lt_of_mul_lt_mul_left hb1 (le_of_lt hqpos)
    have h2 : (-1 : ℤ) < (g' : ℤ) - T := _root_.lt_of_mul_lt_mul_left hb2 (le_of_lt hqpos)
    omega
  have hgTeq : g' = T := by omega
  have hLi : (L : ℤ) = i := by rw [hgT, mul_zero] at key; omega
  refine ⟨hgTeq, ?_, ?_⟩
  · have hLiR : (L : ℝ) = i := by exact_mod_cast hLi
    show θ' = Int.fract ((p : ℝ) / q * θ + α)
    rw [← hF]; rw [hgTeq] at hmaster; linarith [hmaster, hLiR]
  · exact hLi

/-! ## The orbit coordinates -/

variable (p q : ℕ) (s ξ : ℝ)

/-- The orbit value `ξ(p/q)ⁿ`. -/
noncomputable def orbitVal (n : ℕ) : ℝ := ξ * ((p : ℝ) / q) ^ n

/-- The integer part `gₙ = ⌊ξ(p/q)ⁿ⌋`. -/
noncomputable def gPart (n : ℕ) : ℕ := ⌊orbitVal p q ξ n⌋₊

/-- The fractional coordinate `θₙ = q({ξ(p/q)ⁿ} − s)`. -/
noncomputable def thetaPart (n : ℕ) : ℝ := q * (Int.fract (orbitVal p q ξ n) - s)

/-- The offset `a = ⌊(p−q)s⌋` of the `T`-map. -/
noncomputable def aSym : ℕ := ⌊((p : ℝ) - q) * s⌋₊

/-- The offset `α = {(p−q)s}` of the linear mod-one map. -/
noncomputable def alphaSym : ℝ := Int.fract (((p : ℝ) - q) * s)

variable {p q s ξ}

/-- `a + α = (p−q)s` (for `s ≥ 0`, `q ≤ p`, so the argument is nonnegative). -/
theorem aSym_add_alphaSym (hqp : q ≤ p) (hs : 0 ≤ s) :
    (aSym p q s : ℝ) + alphaSym p q s = ((p : ℝ) - q) * s := by
  have hnn : 0 ≤ ((p : ℝ) - q) * s := mul_nonneg (by
    have : (q : ℝ) ≤ p := by exact_mod_cast hqp
    linarith) hs
  have hg : (aSym p q s : ℝ) = (⌊((p : ℝ) - q) * s⌋ : ℝ) := by
    rw [aSym]; exact_mod_cast Int.natCast_floor_eq_floor hnn
  rw [hg, alphaSym, Int.floor_add_fract]

/-- `α ∈ [0,1)`. -/
theorem alphaSym_mem : alphaSym p q s ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The **orbit decomposition** `ξ(p/q)ⁿ = gₙ + s + θₙ/q`. -/
theorem orbit_decomp (hp : 0 < p) (hq : 0 < q) (hξ : 0 < ξ) (n : ℕ) :
    orbitVal p q ξ n = (gPart p q ξ n : ℝ) + s + thetaPart p q s ξ n / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hnn : 0 ≤ orbitVal p q ξ n :=
    mul_nonneg (le_of_lt hξ) (by positivity)
  have hg : (gPart p q ξ n : ℝ) = (⌊orbitVal p q ξ n⌋ : ℝ) := by
    rw [gPart]; exact_mod_cast Int.natCast_floor_eq_floor hnn
  rw [thetaPart, hg]
  field_simp
  linarith [Int.floor_add_fract (orbitVal p q ξ n)]

/-- `θₙ ∈ [0, q/p)` for a `Z`-number `ξ ∈ Z_{p/q}(s, s+1/p)`. -/
theorem thetaPart_mem (hp : 0 < p) (hq : 0 < q)
    (hmem : ξ ∈ ZSet p q s (1 / p)) (n : ℕ) :
    thetaPart p q s ξ n ∈ Ico (0 : ℝ) ((q : ℝ) / p) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨_, hfr⟩ := hmem
  have h := hfr n
  rw [mem_Ico] at h
  obtain ⟨hlo, hhi⟩ := h
  -- `orbitVal` is literally the argument of `Int.fract` in `ZSet`
  have hcast : Int.fract (orbitVal p q ξ n) = Int.fract (ξ * ((p : ℝ) / q) ^ n) := rfl
  rw [thetaPart, hcast]
  rw [mem_Ico]
  constructor
  · exact mul_nonneg (le_of_lt hq0) (by linarith)
  · -- q*(fract - s) < q/p  ⟺  fract - s < 1/p
    rw [show (q : ℝ) / p = q * (1 / p) by ring]
    exact mul_lt_mul_of_pos_left (by linarith) hq0

/-! ## The forward decoupling recurrence -/

/-- **Forward decoupling** (FLP95 Lemma 2.1 / Prop 2.1, forward half, at `t = 1/p`): for a
`Z`-number `ξ ∈ Z_{p/q}(s, s+1/p)`, the integer part advances by `T`, the fractional part by
`f_{p/q, α}`, and the symbols match, at every step. -/
theorem decouple (hq2 : 2 ≤ q) (hqp : q < p) (hs : 0 ≤ s) (hξ : 0 < ξ)
    (hmem : ξ ∈ ZSet p q s (1 / p)) (n : ℕ) :
    gPart p q ξ (n + 1) = TMap p q (aSym p q s) (gPart p q ξ n) ∧
      thetaPart p q s ξ (n + 1) = lmo ((p : ℝ) / q) (alphaSym p q s) (thetaPart p q s ξ n) ∧
      (⌊(p : ℝ) / q * thetaPart p q s ξ n + alphaSym p q s⌋ : ℤ)
        = iSym p q (aSym p q s) (gPart p q ξ n) := by
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- the ceiling linearization, cast
  have hig : (q : ℝ) * (TMap p q (aSym p q s) (gPart p q ξ n) : ℝ)
      = p * (gPart p q ξ n) + (aSym p q s) + (iSym p q (aSym p q s) (gPart p q ξ n)) := by
    have := TMap_mul (p := p) (q := q) (a := aSym p q s) (g := gPart p q ξ n) hq
    exact_mod_cast this
  -- the orbit relation `q·ξβ^{n+1} = p·ξβⁿ`
  have hβ : (q : ℝ) * ((gPart p q ξ (n + 1) : ℝ) + s + thetaPart p q s ξ (n + 1) / q)
      = p * ((gPart p q ξ n : ℝ) + s + thetaPart p q s ξ n / q) := by
    rw [← orbit_decomp hp hq hξ, ← orbit_decomp hp hq hξ]
    have hstep : orbitVal p q ξ (n + 1) = (p : ℝ) / q * orbitVal p q ξ n := by
      rw [orbitVal, orbitVal, pow_succ]; ring
    rw [hstep]; field_simp
  have hθ := thetaPart_mem hp hq hmem n
  have hθ' := thetaPart_mem hp hq hmem (n + 1)
  rw [mem_Ico] at hθ hθ'
  exact decouple_step hq2 hqp (iSym_lt hq) hig hβ hθ.1 hθ.2 hθ'.1 hθ'.2
    (aSym_add_alphaSym (le_of_lt hqp) hs) (alphaSym_mem).1 (alphaSym_mem).2

end FLP
