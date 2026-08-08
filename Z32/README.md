<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 (public domain).
-->

# Z32 — the confinement atlas for {ξ(3/2)ⁿ}

Milestones **M2**, **M3**, **M6** and **M7** of `plans/plan-cert32.html`: the C prototypes, the
X1/X2/X3 sweeps, the **two-colored atlas draft** — which (position, length)
pairs are certified <span>**empty**</span>, which are certified
<span>**nonempty**</span> in the literature, and what is left in the
<span>**band**</span> between them — and the **Lean bridge** that turns an
engine verdict into a kernel-checked theorem.

The Lean side of the same root (`Dictionary`, `EscapeCert`, `ResidueCapture`,
`DubickasWord`, `SmallInterval`, `BlockCert`, and — for `plans/plan-M5A9.html` —
`EscapeLadder`, `ModelEntropy`) builds with `lake build Z32`, std3, zero cited
axioms, no `native_decide`.

Status of the *numbers* below: **computationally established, pending
independent replication** (plan R-5/R-7, the M2′ precondition inherited from
plan-dubC1); reproducible in a few minutes with `sh reproduce.sh` (except the M6 controls,
which take about an hour). Status of the eight entries listed under
**M3 — the Lean bridge**: *proved*, and no longer resting on any engine — see
that section for what changed.

---

## The model

With `xₙ = ⌊ξ(3/2)ⁿ⌋` and `yₙ = {ξ(3/2)ⁿ}`, the identity `3(xₙ+yₙ) = 2(xₙ₊₁+yₙ₊₁)`
gives the **carry coding** (plan §1.1)

```
  y_{n+1} = (3 yₙ + eₙ)/2 ,   eₙ = 3xₙ − 2xₙ₊₁ ∈ {−2,−1,0,1} ,   eₙ ≡ xₙ (mod 2).
```

Confinement of the orbit to a set `U ⊆ [0,1)` is survival of `y` under this
2-branch interval dynamics. The engines compute, **exactly** (all arithmetic is
integer arithmetic over the denominator `Gden·3^k`, no floating point in any
decision path),

```
  S₀ = U ,   S_{k+1} = U ∩ f⁻¹(S_k) ,   f⁻¹(A) = ⋃_e (2A − e)/3 ,
```

so `S_k` = the points of `U` with an admissible continuation staying in `U` for
`k` more steps. `Z(U) ⊆ ⋂ₖ S_k`, always.

For a single window `[s, s+L)` with `L ≤ 1/2` this is affinely conjugate to the
FLP95 picture that `FLP/` formalizes: `θₙ = q({ξ(3/2)ⁿ} − s)` (`FLP.thetaPart`)
satisfies `θₙ₊₁ = f_{β,α}(θₙ)` with `β = 3/2`, `α = {(p−q)s} = s`
(`FLP.alphaSym`), and the survival threshold is `qL = 2L` — at `L = 1/3` exactly
`FLP.survivors (3/2) s`. `hold.c` runs that coordinate, `atlas.c` runs the
`y`-coordinate directly; they are independent implementations of the same
question and agree everywhere they overlap.

### The two certificates

**KILL n** — `S_n = ∅`. Unconditional: no `ξ > 0` has its whole orbit in `U`.
Needs no theory at all.

**CYCLE** — `S_k` is covered by disjoint rational intervals `H₁…H_m` such that
the transition relation

> `i → j` iff `(3·H_i + e)/2` meets `H_j`, for some carry `e`

is a **partial function** (out-degree ≤ 1, so the carry is determined by the
block). Then a confined orbit walks a functional graph, hence its block
itinerary — and therefore its **carry word** — is eventually periodic. But the
carry word of *every* `ξ ≠ 0` is aperiodic:

> `Z32.not_isEventuallyPeriodic_carry` (= [DN05] Lemma 2), **proved** in
> `Z32/DubickasWord.lean`, std3, no cited axiom, no hypothesis beyond `ξ ≠ 0`
> and `p, q` coprime with `p > q > 1`.

So `Z(U) = ∅`. This is DubC's `C(𝒫)` certificate ("no branching SCC ⇒ every
path eventually periodic ⇒ the avoiding ξ are rational ⇒ contradiction")
transplanted to the fractional side, and it is the reason the engine covers the
FLP positions, whose survivor set is a nonempty finite cycle. **It also removes
the plan's R-8 risk**: FLP95's Thm 3.2 (finite survivors ⇒ `Z` empty) is stated
at window length `1/p`, and §4.1(b) flagged its generalization as the plan's own
analytic work. The CYCLE certificate needs no such generalization — it needs no
decoupling, no threshold hypothesis, and it works for unions.

**FAT** — the component count keeps growing: the survivor set is infinite and
the engine decides nothing. `λ` = growth rate of the component count;
`dim_box ≤ log λ / log(3/2)` is the T5 dimension datum. Reported, never hidden.

---

## Results

### X1 — the FLP control, and the length-1/3 line

The five FLP95 Cor 1.4a positions regenerate digit for digit, with the paper's
own escape witnesses:

| s | orbit of 0 under `f_{3/2,s}` | escape N |
|---|---|---|
| 1/6 | 0 → 1/6 → 5/12 → 19/24 | **3** |
| 1/3 | 0 → 1/3 → 5/6 | **2** |
| 1/2 | 0 → 1/2 → 1/4 → 7/8 | **3** |
| 2/3 | 0 → 2/3 | **1** |
| 0 | fixed point, no escape | — |

The exact pruning then reproduces **FLP95 Thm 3.4's trichotomy** as a
measurement: the survivor set has *exactly* `N` components, `N` = the escape
depth (1, 3, 2, 3, 1 at s = 0, 1/6, 1/3, 1/2, 2/3), in both coordinate systems.
The certificates are the exact rational cycles — e.g. at `s = 1/6` the survivor
set is `{4/19, 6/19, 9/19}` with carry word `(0,0,−1)`, denominator `3³−2³ = 19`.

Sweeping every rational position `s = i/G` at `L = 1/3`:

| G | 6 | 12 | 24 | 48 | 96 | 192 | 384 | 768 | 1536 | 3072 | 3888 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| positions | 5 | 9 | 17 | 33 | 65 | 129 | 257 | 513 | 1025 | 2049 | 2593 |
| certified | **all** | all | all | all | all | all | all | all | all | all | **all** |
| max escape depth | 3 | 7 | 11 | 11 | 13 | 13 | 14 | 21 | 21 | 23 | 25 |

**X1's open half is answered, negatively and informatively**: there are *no*
stubborn positions at any rational `s` with denominator ≤ 3888. That is exactly
what [Bug04]/[Kwon15] predict — the exceptional set `E_{3/2}` is
Sturmian-parametrized and of Hausdorff dimension 0, so **no rational sweep can
ever meet it**. The stubborn positions are invisible to this experiment by
nature, not by budget; the length-1/3 line is closed in Lean anyway
(`Z32.ZSet_three_two_third_empty`, all real `s`).

### X2 — the (position, length) map, and the frontier

Full sweep at `G = 360`, all positions, `L = 1/3 … 1/2`, depth 30
(`data/x2_G360.txt`). Fraction of positions certified:

| L | 1/3 | .3361 | .3444 | .3556 | .3667 | .375 | .3833 | .3944 | .4028 | .4056 | ≥ .4083 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| certified | **100 %** | 79.2 % | 55.3 % | 37.3 % | 26.6 % | 22.1 % | 13.0 % | 10.0 % | 6.5 % | 3.7 % | **0 %** |

Refined at `G = 3600`: the last certified length is

> **L\* = 1466/3600 = 0.407222…**, at 14 positions
> (i/3600 ∈ {961, 965, 971, 985, 986, 1018, 1026, 1108, 1116, 1148, 1149, 1163, 1169, 1173}),

and a full-range scan at `j = 1467…1500` certifies **nothing**, anywhere. The
surviving positions concentrate in `s ∈ [0.267, 0.326]`.

Three consequences.

1. **M4's decision point (a) is dead.** The certified fraction falls off 100 %
   *immediately* above `L = 1/3` (79 % at `L = 1/3 + 1/360`). There is no
   uniform `δ > 0` reachable this way, so a strengthening of
   `FLP.three_halves_spread` to `1/3 + δ` is not what this engine can deliver.
   The M4 lane is **(b): the two-colored atlas**.
2. **New atlas entries above the 1995 line.** Emptiness of a *longer* window is
   strictly stronger than emptiness of a shorter one, so every certified entry
   with `L > 1/3` is beyond both FLP95 (which certifies only at `t = 1/p`) and
   [Dub09AA] (all `s`, but only at `1/3`). The best is length **0.40722**.
3. **The band below `L*` is provably a band for this model class.** The
   `horse` mode enumerates all cycles of period ≤ P exactly (a period-P cycle is
   the rational `−(Σ 3^{P−1−i}2^i w_i)/(3^P − 2^P)`), giving a *rigorous* lower
   bound on the survivor set:

   | entry | cycles P≤6 | P≤9 | P≤12 |
   |---|---|---|---|
   | certified, e.g. `[1/3,2/3)` or `[4/24,13/24)` | 1 | 1 | 1 |
   | band, e.g. `[0,10/24)` or `[0,150/360)` | 4 | 8 | **16** |

   The count doubles: the hold set of a band entry contains exponentially many
   distinct confined orbits, so **no argument that looks only at the archimedean
   hold set can settle it** — those entries need the dyadic product refinement
   (plan §4.3, experiment X4). The band is a theorem about the method, not a
   budget shortfall.

T5 dimension data comes free from the same run (`dim_box ≤ log λ / log(3/2)`):

| L | .3361 | .3528 | .3694 | .3861 | .4028 | .4194 | .4361 |
|---|---|---|---|---|---|---|---|
| λ (max over positions) | 1.165 | 1.229 | 1.285 | 1.325 | 1.345 | 1.370 | 1.359 |
| dim bound | 0.378 | 0.509 | 0.618 | 0.694 | 0.730 | 0.776 | 0.756 |

(These bound the *hold set*, not `Z_ev(U)`; the T5 target needs the covering
argument of plan §7, which is M5 work. Reported here as calibration.)

### X3 — unions

**Literature controls (positive).**

| set | \|U\| | engine verdict |
|---|---|---|
| [Dub08] Cor 1.2: `[8/39,18/39) ∪ [21/39,31/39)` | 20/39 = .5128 | **CYCLE**, 4 blocks — cycle `{2/5,3/5}`, transients `{4/15,11/15}` |
| [Dub06] complement: `[0,0.238117) ∪ [0.761883,1)` | .476234 | **FAT** — components 394 → 2212 → 9836 → 29472 at depth 12/20/30/40, λ ≈ 1.15 |

So the engine independently reproduces the **half-open shadow** of [Dub08]
Cor 1.2 — the strongest published *explicit* union-emptiness result. `atlas.c`
is half-open throughout, so this row is the shadow and not the corollary; the
printed statement closes both intervals and is strictly stronger. The closed
form is reached instead by `gencert.py --closed --ranked` and proved in Lean —
see the M3 section, which is where the difference turns out to have real
content. It does **not** reach
[Dub06]: there the hold set grows steadily, so that theorem uses more than the
archimedean hold set, and the entry stays in the band. Both engines agree on
both verdicts (394 components at depth 12 for [Dub06], independently).

**Literature controls (negative) — the soundness test that matters.** Every set
the literature proves *nonempty* must come back undecided, and does:

| set | \|U\| | source | verdict |
|---|---|---|---|
| `[0,1/6) ∪ [1/3,2/3) ∪ [5/6,1)` | 2/3 | [KK18] Cor 4.8 (nonempty) | FAT ✓ |
| `‖·‖ < 1/3` | 2/3 | [Dub10] (1.1) (nonempty) | FAT ✓ |
| `[4/65,61/65)` | .8769 | [Pol81] (positive dim.) | FAT ✓ |
| `(5/48,43/48)` | 19/24 | [Dub08] Thm 1.3 (nonempty) | FAT ✓ |
| `[1/19,18/19)` | 17/19 | [Cho80] (nonempty) | FAT ✓ |

**The largeness record (T2(c)).** Goodness is downward closed, so maximal
certified unions can be searched exhaustively at coarse resolution and then
refined (a certified union is the same *set* at any finer grid, so refining can
only help):

| cells N₀ | 12 | 16 | 18 | 20 | 24 | 30 | 36 | 48 | 60 | 120 | 240 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| method | exh | exh | exh | exh | rnd | rnd | rnd | rnd | rnd | climb | climb |
| best \|U\| | .5833 | .6250 | .6667 | .6000 | .6667 | .6667 | .6944 | .7083 | .7167 | .7250 | **.74167** |

The record union (178 of 240 cells, total length 89/120):

```
[0,1/30) [1/20,2/15) [3/20,1/5) [13/60,11/30) [5/12,13/30) [9/20,8/15)
[11/20,19/30) [161/240,23/30) [19/24,191/240) [4/5,13/15) [9/10,14/15)
[19/20,79/80) [119/120,239/240)
```

certified CYCLE at depth 30 with 3783 components merging into 2512 blocks, all
of out-degree 1. **This is 0.7417 against [Dub08] Cor 1.2's 20/39 = 0.5128**,
the best explicit certified-empty union in the twenty-eight sources read at
M0 — i.e. a record on the curve that [KK18] **Problem 6.1** asks about (make
Thm 5.9's non-constructive total-length-`1−ε` union explicit). The curve is
still climbing under refinement, which is the expected shape if Thm 5.9 is the
limit. *Claim the record on the curve, never the problem* (plan R-1).

Note the two colors genuinely interleave: [KK18]'s **nonempty** union has total
length 2/3 < 0.7417. Total length alone decides nothing — which is precisely why
the atlas is a table and not an inequality.

---

## M3 — the Lean bridge

The engines decide; the kernel now checks. `Z32/BlockCert.lean` formalizes the
CYCLE certificate and re-verifies six of the entries above from scratch, with
`decide` — **no `native_decide`, no floating point, no cited axiom**, footprint
`[propext, Classical.choice, Quot.sound]` on every exported declaration.

Since M6 the file is stated for an arbitrary base `p/q`; the `(3,2)` reading
below is the special case its first six entries use. See
[M6 — a second base](#m6--a-second-base).

### What is checked

A certificate for a set `U` is a *funnel* of interval lists

```
  T₀ = U ⊇ T₁ ⊇ … ⊇ T_K =: H   (the blocks),
```

all endpoints integers over one common denominator `D = G·p^K`, subject to two
conditions that are pure integer arithmetic:

| check | statement | consequence |
|---|---|---|
| `funnelOk` | for every `I ∈ T_k`, carry `s`, `J ∈ U`: the piece `{y ∈ J : (py−s)/q ∈ I}` lies in a **single** interval of `T_{k+1}` | a confined orbit lies in every `T_k`, hence in `H` |
| `funcOk` | with the blocks stratified by rank: no successor of larger rank, at most one of equal rank | the rank along an orbit is a non-increasing `ℕ`, hence eventually constant; from there the itinerary is deterministic ⇒ eventually periodic ⇒ so is the carry word |

`strata := []` gives every block rank `0`, and `funcOk` is then the plain "at
most one outgoing edge" condition — which is what five of the six entries use.
The certificate also carries a `closed` flag: with `closed := true` every
interval it mentions is `[a/D, b/D]` rather than `[a/D, b/D)`, and every
comparison flips (a piece is empty iff `hi < lo`, two intervals meet iff they
touch). Both fields default to the old behaviour.

and the carry word of every `ξ ≠ 0` is aperiodic
(`Z32.not_isEventuallyPeriodic_carry`, proved at M1-bis). Hence `Z(U) = ∅`.

`min`/`max` are expanded by hand into disjunctions, and everything is scaled by
`pD`, so the kernel only ever compares integers — which is why the whole file
elaborates in about 16 s (eight certificates).

`Z32/gencert.py` re-runs the exact pruning and emits the funnel; `reproduce.sh`
regenerates all eight and `diff`s them against the file. **The Lean file trusts
no engine**: the conditions are rechecked by the kernel from the literal data.

### The eight entries

| entry | \|U\| | Lean name | funnel |
|---|---|---|---|
| `[1/6, 13/24)` | .375 | `Z32.ZSet_three_two_sixth_3_8` | depth 8, 3 blocks |
| `[961/3600, 2427/3600)` | .40722 | `Z32.ZSet_three_two_frontier` | depth 13, 2 blocks |
| `[8/39,18/39] ∪ [21/39,31/39]` **closed** | 20/39 | `Z32.dubickas_2008_cor_1_2` | depth 3, 12 blocks, 4 rank strata |
| 4-interval union | 7/12 | `Z32.union_seven_twelfths_empty` | depth 7, 1 block |
| 5-interval union | 2/3 | `Z32.union_two_thirds_empty` | depth 9, 12 blocks |
| 6-interval union | **25/36** | `Z32.union_record_empty` | depth 11, 17 blocks |
| `[1/3, 5/8)` at **4/3** | 7/24 | `Z32.ZSet_four_three_beyond_line` | depth 5, 2 blocks |
| `[1/5, 2/5)` at **5/2** | 1/5 | `Z32.ZSet_five_two_fifth` | depth 1, 1 block |

`Z32.not_eventually_mem_sixth_3_8` is the *eventual* form of the first entry
(shift trick, `Z32.mem_ZSet_of_eventually`), and the soundness theorem
`Z32.BlockCert.Cert.not_confined` covers every `ξ ≠ 0` — the certificate never
uses the sign, so these are slightly stronger than the `FLP.ZSet` statements.

Three of these are worth separating out.

1. **`[1/6, 13/24)` is past the 1995 line.** [FLP95] Corollary 1.4a certifies
   emptiness only at length `1/p = 1/3`, and [Dub09AA] Theorem 1 covers every
   position but again only at `1/3`. This window has length `3/8 = 0.375`.
2. **[Dub08] Corollary 1.2 as printed, closed** — the strongest *explicit*
   union-emptiness statement in the twenty-eight sources read at M0, and the
   only entry needing both general features of the certificate (M4′ item P1,
   landed 2026-07-27). The closed/half-open gap has content: the closed set
   contains the 4-cycle `6/13 → 9/13 → 7/13 → 4/13`, which runs through the
   right endpoint `18/39 = 6/13`.

   The prediction attached to P1 in the plan — "expected to succeed, since
   tolerating cycles is what this method does" — was **half right, and the
   wrong half is the interesting one**. Closing the endpoints does not merely
   admit one more cycle: the hold set acquires an infinite backward tree of
   transients feeding *two* disjoint cycles (the 4-cycle and `{2/5, 3/5}`), and
   with it four components per level forever. Measured to depth 40, **no
   partition into blocks of out-degree 1 exists at any depth** — the greedy
   hull merge collapses to a single block with out-degree 2 every time, and
   fattening the half-open set instead of closing it behaves identically. What
   does exist, at depth 3, is a *rank stratification* of the twelve raw
   components: rank 0 is the 4-cycle, rank 2 the two fat blocks holding
   `{2/5, 3/5}` (which also escape downward), ranks 1 and 3 transients. So P1
   cost a genuine weakening of `funcOk`, not just a flag.
3. **`25/36 = 0.6944…` is the formalized union-largeness record**, against
   `20/39 = 0.5128…` in print. Note again that [KK18] Corollary 4.8's
   **nonempty** union has total length `2/3`, and `Z32.union_two_thirds_empty`
   is an **empty** one of exactly the same total length.

### Why not the 0.7417 record

The engine's best union (240 cells, §X3) has 3783 surviving components at depth
30. The funnel for it is thousands of intervals wide, and `decide` cost grows
like `Σ_k |T_k|·|T_{k+1}|·4·|U|`. The 48-cell record (`0.7083`) already
projects to ~4 minutes of kernel time; `25/36` costs about 6 s. Narrowing the
funnel — coarsening the intermediate levels outward, which is sound and only
needs the *containment* to survive — is the obvious next engineering step and is
not on the M3 critical path.

### Negative controls, again

The generator refuses all five sets known nonempty in print
(`[4/65,61/65)`, `[1/19,18/19)`, `[5/48,43/48)`, `‖·‖<1/3`, `X_{3,2}`): no
certificate within depth 60, in the default mode and in the stronger
`--closed --ranked` mode alike. Three Lean lemmas record that the checks have
teeth: `ok_eq_false_of_full` (`[0,1)` fails, its single block has all four
carries outgoing), `ok_eq_false_of_full_closed` (nor does `[0,1]` with a rank of
its own), and `ok_eq_false_of_not_coprime` (a non-coprime base is refused — at
`4/2 = 2` the point `ξ = 1/3` has the periodic orbit `1/3 → 2/3`, so a
certificate there would prove a falsehood).

A certified window is **not** one whose interval-map hold set is empty: at
`[1/6, 13/24)` the hold set is exactly the 3-cycle `4/19 → 6/19 → 9/19` with
carries `(0,0,1)`, and the C engine's `e = (0,0,−1)` is its negative, as the
conventions demand. What the certificate rules out is a *real number* whose
fractional parts follow that cycle.

---

## M6 — a second base

Every engine here, and the Lean bridge, were hardwired to `3/2`: the four
carries `{−1,0,1,2}` and the literals `2` and `3` in the piece arithmetic. **The
mathematics never was.** `Z32.not_isEventuallyPeriodic_carry` — the sole
analytic input — is proved for every coprime `p > q > 1` and every `ξ ≠ 0`, and
`Z32.carry_eq` is stated for general `p, q`. So M6 is a parameterization, not a
research step, and `Cert.not_confined` generalizes with the same proof.

What changes, and nothing else does:

| | at `3/2` | at `p/q` |
|---|---|---|
| carry alphabet | `{−1,0,1,2}` | `{−q+1, …, p−1}`, i.e. `p+q−1` letters |
| branch-`s` preimage of `[a,b)` | `[(2a+s)/3, (2b+s)/3)` | `[(qa+s)/p, (qb+s)/p)` |
| common denominator | `G·3^K` | `G·p^K` |
| `hits` | `3·I₁` vs `2·J₂+sD` | `p·I₁` vs `q·J₂+sD` |

`Cert` gained two fields, `p := 3` and `q := 2`, so **no `(3,2)` certificate
mentions the base**, and `Cert.ok` gained three decidable side conditions —
`1 < q`, `q < p`, `gcd p q = 1` — which are exactly the hypotheses of the
aperiodicity lemma. That is why `Cert.not_confined` still takes no hypothesis
but `ok` itself. `gencert.py --pq p q` emits the base only when it is not
`3/2`; all eight certificates in `BlockCert.lean` regenerate byte-identically,
and `--pq 3 2` reproduces the default path exactly.

**Scope.** The *certificate* path — `gencert.py` → `BlockCert.lean` — is
parametric. The three C *search* engines (`atlas.c`, `hold.c`, `gridcert.c`)
are not, and remain `3/2`-only; the `(4,3)` and `(5,2)` sweeps quoted below ran
on the Python pipeline. Parameterizing the C engines is what a full second
atlas *column* (an X2-scale `(p,q)` map) would need, not what entries need.

### The controls are the point

A second base gives soundness tests the `(3,2)` engine could not run. Run by
`pqcontrols.py`, exact `Fraction` arithmetic, output in `data/m6_controls.txt`:

| | what the literature says | what the engine does |
|---|---|---|
| **(A)** windows of length `1/p`, `1 < q < p < q²` | [Dub09AA] Thm 1: **empty**, every real `s` | **8/8 certified** at each of `(4,3)`, `(5,3)`, `(5,4)`, `(7,5)`. Funnel depth up to 26 at `(4,3)` — the two windows at `1/4` and `1/2` need 26 levels, and a scan cut off at depth 25 wrongly reports them unresolved |
| **(B)** two-cell sets at `p > q²` | [Aki08] Thms 2.4/2.5: **nonempty** Cantor sets of dimension `log q / log(p/q)` | FAT (>1000 components by depth 9) at `(5,2)`, `(7,2)`, `(9,2)` — refused, as it must be |

(A) is a genuine cross-check rather than a new result: the general statement is
`Z32.ZSet_eq_empty_of_lt_sq` in `Z32/SmallInterval.lean`, proved by the Sturmian
route of [Dub09AA]. The block certificate reaches the same conclusion by a
completely different argument. It is not formalized a second time.

### Past the line at `4/3`, and the `p > q²` regime

The `(4,3)` sweep gives a **lower bound** on the frontier for a single
non-wrapping window, not the frontier: length `70/240 = 0.29167` still certifies
at 10 positions (denominator `240`, funnel depth `≤ 20`). A scan of
`72/240 … 94/240` found nothing, **but only to depth 14** — and `(4,3)` is
precisely the base whose length-`1/4` windows need depth **26**, so that scan
proves nothing and the frontier above `0.2917` is open. Against `1/p = 0.25` in
print, that is an overshoot of at least `1.17×`, against `1.22×` (`0.40722` over
`1/3`) at `(3,2)`. `Z32.ZSet_four_three_beyond_line` formalizes
`Z_{4/3}(1/3, 5/8) = ∅`, length `7/24 = 0.2917`.

For `p > q²`, [Dub09AA] §4 says Theorem 1 is **open** — his counting step needs
`p < q²`. The block certificate has no such step, and it certifies *every*
length-`1/p` window tested at `(5,2)`, `(7,2)`, `(9,2)`, `(10,3)`, `(11,3)`,
mostly at depth 1. `Z32.ZSet_five_two_fifth` formalizes one of them,
`Z_{5/2}(1/5, 2/5) = ∅`; its certificate is small enough to check by hand.

**That is not the open theorem, and the gap does not close.** Theorem 1
quantifies over all real `s`; a certificate handles one rational window. The
natural upgrade is a cover — certify the `N` windows `[i/N, i/N + 1/N + 1/p)`
mod 1, and every real window of length `1/p` sits inside one of them, so
`Z32.ZSet_mono` would give the general statement. Measured, it fails:

| base | `N` | element length | certified |
|---|---|---|---|
| `(5,2)` | 5 / 10 / 20 | .4000 / .3000 / .2500 | 0/5, 2/10, **8/20** |
| `(7,2)` | 7 / 14 / 28 | .2857 / .2143 / .1786 | 0/7, 4/14, **14/28** |
| `(9,2)` | 9 / 18 / 36 | .2222 / .1667 / .1389 | 0/9, 6/18, **20/36** |
| `(10,3)` | 10 | .2000 | 0/10 |

The failures are FAT, and the first one is always `i = 0`: the fattened window
contains `0`, which is the fixed point of the `s = 0` branch — the degenerate
position the plan warns about, and the one `FLP.ZSet_empty_zero` handles
separately at `(3,2)`. But they are not *only* degenerate: at `(5,2)` with
`N = 20`, twelve of the twenty fail. So the `p > q²` column is a finite list of
rational windows, **not** the open theorem, and there is no tension with
[Aki08]'s nonempty Cantor sets — the fattened windows are exactly large enough
to hold them. Whether the block certificate can be pushed to a uniform argument
is open; this measurement says the cheap route does not.

---

## M7 — [Aki08] Conjecture 1.4, and the end of the product refinement

**The conjecture** ([Aki08] pp. 92–93): there is no `x > 0` with
`{x(4/3)ⁿ} ∈ [0,¼) ∪ [¾,1)` for every `n ≥ 0`, equivalently `‖x(4/3)ⁿ‖ < ¼`
for all `n`. Akiyama works half-open throughout, so this is verbatim a question
about `U = [0,¼) ∪ [¾,1)` at the base `4/3`.

The archimedean engine cannot touch it: `U` is **exactly forward-invariant**
(`S₁ = U`, hence `S_k = U` for all `k`), so there is no KILL, and the block
graph is `U`'s own two intervals with a nowhere-functional transition relation.
The plan therefore routed M7 through §4.3's **product refinement**: a state
becomes a pair `(cell, xₙ mod qʲ)`, and the two coordinates constrain each
other, because `q x_{n+1} = p xₙ + sₙ` forces

    sₙ ≡ −p xₙ  (mod q),

so the branch is *determined* by the residue — one carry out of `q` instead of
`q`. `prodcert.py` implements it, and the answer is that the machine is empty.

### Theorem A — the residue coordinate is free

> Let `S_k` be the archimedean hold set at depth `k` and `S_k⁽ʲ⁾[r]` the product
> one at level `j`. Then for every `k` and every `j`, `⋃_r S_k⁽ʲ⁾[r] = S_k`.

*Proof.* `⊆` is the projection. For `⊇`, take an archimedean chain
`y₀,…,y_k ∈ U` with carries `s₀,…,s_{k−1}`. Since `gcd(p,q) = 1`, `p` is
invertible mod `qʲ`, so choose **any** `r_k ∈ ℤ/qʲ` and run the residues
*backward*, `r_i := p⁻¹(q r_{i+1} − s_i)`. That is a legal product chain lying
over `y`. ∎

The whole content of the refinement is `q | p x + s`, and it costs exactly what
it buys: forcing the carry divides the branching by `q`, and the `q` lifts of
`x_{n+1} mod qʲ` — which `q x_{n+1} = p xₙ + sₙ` pins only mod `q^{j−1}` —
multiply it straight back. **So the product engine reports KILL at exactly the
archimedean depth, never one step earlier, at any level, any base, any `U`.**
The dyadic ladder cannot empty a set the archimedean engine could not.

### Theorem B — cycle counting lifts, so certificates are capped

> If the hold set of `U` carries `N` distinct periodic orbits, every product
> certificate for `U` — at every level `j` — needs at least `N` blocks. In
> particular, a hold set with infinitely many periodic orbits admits **no**
> product certificate at any level.

*Proof.* Each periodic orbit lifts: run the residues backward as above; over one
period the return map on `ℤ/qʲ` has linear part `p^{−P} q^P`, which vanishes
once `P ≥ j` (replace `P` by a multiple if not), so it is constant and has a
fixed point — a periodic path in the product graph. Conversely a functional
block graph determines, from a block, the entire forward path *and its carry
labels*; and the carries determine the point, since
`yₙ = Σ_{i≥0} qⁱ s_{n+i} / p^{i+1}`. So `orbit ↦ block containing y₀` is
injective. (For the rank-stratified variant, take the block at which the rank
stabilizes: an infinite path has eventually constant rank and is deterministic
from there.) ∎

Theorem B is §4.4's archimedean no-go, lifted verbatim to every level. It is
also the reason a functional certificate means what it means: a hold set with a
CYCLE certificate has **at most one point per block**.

### The measurement

`prodcert.py`, exact `Fraction` arithmetic, output in `data/m7_controls.txt`:

| | | |
|---|---|---|
| **(A0)** Theorem A itself, 5 sets at 3 bases, `j = 1,2,3` | `⋃_r S_k⁽ʲ⁾[r] = S_k` **at every depth**, no mismatch anywhere | the theorem tested as an identity, not through its consequences |
| **(A)** its consequence, 8 sets at `(3,2)`, `j = 1,2,3` | no level ever KILLs earlier than `j = 0` | and on the three entries that certify, the product needs a **deeper** funnel: `certWindow38` 8 → 8, 8, 9; `certUnion712` 7 → 8, 9, 10; `certFrontier` 13 → 13, 14, 15 |
| **(B)** the five sets known nonempty in print | STABLE at every level, never certified | as it must be |
| **(D)** `(4,3)`, Akiyama's `U`, `j = 1…5` | nonempty, exactly invariant, out-degree 2 at every level | `2^{j+1}` components of length `(¾)ʲ/4` over `2^{j+1}−2` residues mod `3ʲ`; mass `3ʲ/2^{j+1}` |
| **(E)** the periodic-orbit census | **`2^L − 1`** points of period dividing `L`, `L ≤ 13`, at `(4,3)` | a full 2-shift ⇒ Theorem B ⇒ no certificate at any level |

The `2^L − 1` is not a coincidence and does not need the machine. On `U` the two
inverse branches

    h_A(y) = ¾y  on [0,¼),  (3y−2)/4 on [¾,1)   → image [0,¼)
    h_B(y) = (3y+3)/4       , (3y+1)/4          → image [¾,1)

both map `U` into `U` with disjoint images and ratio `¾`, so `{h_A, h_B}` is a
horseshoe: every word in `{A,B}^L` has a fixed point, giving `2^L` periodic
points minus the one at `y = 1` that the half-open convention excludes.

**So M7 exits negatively, and rigorously: no block certificate — archimedean or
product, at any level `j` — can prove [Aki08] Conjecture 1.4.** This is exit
(β) of the plan, and it is stronger than the plan asked for: the no-go covers
all levels at once, and Theorems A/B cover all `U` and all bases.

### It is not evidence about the conjecture

Run the identical census at `(3,2)` on `‖ξ(3/2)ⁿ‖ < ¼`'s analogue
`U = [0,⅓) ∪ [⅔,1)` and the counts are **the same `2^L − 1`** — and there
[Dub10] *proves* the set nonempty. The two cases are indistinguishable to this
entire certificate family, so the obstruction says nothing about whether
Akiyama is right.

### X4 answered, and one caveat

X4 asked for the crossover curve of the dyadic ladder near `L = ½`. It is flat.
Theorem A rules out a KILL gain outright; measured at the frontier
`L* = 1466/3600`, `j = 0…3`, funnel depth 30:

| length | `j=0` | `j=1` | `j=2` | `j=3` |
|---|---|---|---|---|
| `1466` (certified) | CYCLE @13 | CYCLE @13 | CYCLE @14 | CYCLE @15 |
| `1467` (band) | — | — | — | — |
| `1470` (band) | — | — | — | — |

(`—` = undecided to depth 30, with the CYCLE test actually run at every level:
the component count stayed under the 400 cap where the cubic block merge would
have been skipped.)

**Caveat, and it matters: the band is not proven out of reach.** Theorem B
bounds a certificate below by the periodic-orbit count, and at these band
entries that count is *small* — 1, 2 and 3 orbits respectively out to period 20
(`[0,2,0,2,…]` with one extra orbit appearing at period 14, and at 12 for
`1470`). So the theorem does not bite there. The correct statement is that this
engine fails on the band, not that every engine must. `L*` remains the frontier
of what is *certified*, not a proved wall.

---

## The `φ_model` ledger (plan-M5A9 milestone N2(a))

The M7 census says the band and the two-cell holes are *fat*, but a count of
periodic orbits is not a growth rate. `Z32/ModelEntropy.lean` replaces the
count by the quantity plan-M5A9 §2 asks for — the entropy of the carry language
of the hold set,

```
  phi_model(U) := limsup (1/n) log #{ carry words of length n realised
                                      by a model orbit confined to U } ,
```

and proves both colors of the ledger. **Neither side is a statement about real
`ξ`**: `phi_model` is a property of the interval-map model, i.e. of what this
family of certificates can and cannot decide (plan risk R-B).

| set | `\|U\|` | certificate | `phi_model` | Lean name |
|---|---|---|---|---|
| `[1/6, 13/24)` | .375 | `certWindow38` | **0** | `Z32.phiModel_eq_zero_window38` |
| `[961/3600, 2427/3600)` | .40722 | `certFrontier` | **0** | `Z32.phiModel_eq_zero_frontier` |
| the five other `strata = []` entries | — | `certUnion712`, `certUnion23`, `certUnion2536`, `certFourThree`, `certFiveTwo` | **0** | `Z32.phiModel_eq_zero_of_cert` |
| `[8/39,18/39] ∪ [21/39,31/39]` closed | 20/39 | `certDub08` (rank-stratified) | 0 (polynomial path count; **not formalized**) | — |
| band `[0, 5/12)` | .41667 | `Z32.horseBand` — 4 words, `L = 6`, `K = [0,1/9]` | **≥ (log 2)/3 = .2310** | `Z32.log_two_div_three_le_phiModel_band` |
| band `[0, 5/12)` | .41667 | `Z32.horseBandRecord` — 14 words, `L = 10`, `K = [0,11/90]` | **≥ (log 14)/10 = .2639** | `Z32.log_fourteen_div_ten_le_phiModel_band` |
| two-cell `[0,1/3) ∪ [2/3,1)` | 2/3 | `Z32.horseTwoCellSmall` — 4 words, `L = 3`, `K = [0,5/19]` | **≥ (log 4)/3 = .4621** | `Z32.log_four_div_three_le_phiModel_two_cell` |
| two-cell `[0,1/3) ∪ [2/3,1)` | 2/3 | `Z32.horseTwoCell` — 16 words, `L = 5`, `K = [0,65/211]` | **≥ (4/5)·log 2 = .5545** | `Z32.four_fifths_log_two_le_phiModel_two_cell` |
| [Dub06] complement | .476 | none found to `L = 7` | engine `λ ≈ 1.15` only | — |

### The certificate

A **horseshoe certificate** is the mirror image of a funnel. Where `BlockCert`
pushes an orbit *forward* into blocks with the expanding branches, this one
carries a closed interval *backwards* with the contracting inverse branches
`h_s(x) = (qx+s)/p`: a base interval `K = [A/D, B/D]` and `N` distinct words of
a common length `L` with

```
  H_{(s_i..s_{L-1})}(K) ⊆ U  for every i < L,     H_w(K) ⊆ K ,
```

all endpoint tests being integer comparisons over `D·p^j`, so the kernel
re-checks the whole thing with `decide`. Every concatenation of the `N` words
then fixes a point of `K` — by the intermediate value theorem, no compactness
and no limits — whose entire orbit stays in `U`, so the language holds at least
`N^k` words of length `kL` and `phi_model ≥ log N / L`.

Two things the search settles. First, **the branching is not at a point**: no
point of any of these hold sets carries two distinct return words of the same
length (checked exhaustively to `L = 6`), so a "two loops at one point"
certificate does not exist and the interval form is necessary. Second, the
minimal candidate for `K` is forced — any invariant `K` contains the fixed point
of each `H_w`, so the hull of those fixed points is optimal and the search over
hulls is exhaustive at each length.

### What the numbers mean

`(log 2)/3` on the band entry is exactly the figure plan-M5A9 §2 reads off the
cycle counts `4/8/16` at periods `≤ 6/9/12`; the certificate turns that reading
into a theorem, and the 14-word entry then passes it. At the two-cell hole the
census measures a **full** 2-shift, and the family `N = 2^{L−1}` on
`K = [0, (3^{L−1}−2^{L−1})/(3^L−2^L)]` certifies `((L−1)/L)·log 2` at every `L`,
so the certified bound tends to `log 2` without ever reaching it: at `L = 1`
invariance would force `K = [0,1]` and hence `U = [0,1]`. That is the precise,
non-negotiable form of the landmine plan-M5A9 flags in N2(d) — the `(4,3)`
disjoint-images horseshoe has no `(3,2)` analogue at length one.

Finally, `Z32.not_cert_and_horse` proves the ledger's two colors **disjoint**:
no set carries both a functional block certificate and a horseshoe. The searches
confirm it from the other side — neither certified window admits a horseshoe at
any length tested (`sh reproduce.sh`, section N2(a)).

---

## The atlas draft (two colors and the band)

Single intervals `[s, s+L)`:

| L | positions | color | certificate |
|---|---|---|---|
| ≤ 1/3 | **every** `s` | **EMPTY** | [Dub09AA]; formalized: `Z32.ZSet_three_two_third_empty` |
| 1/3 | 0, 1/6, 1/3, 1/2, 2/3 | **EMPTY** | escape N = 3,2,3,1; formalized: `Z32.FLP_cor_one_four_a` |
| 1/6 | e.g. `[1/12,3/12)` | **EMPTY** | KILL, depth 3 — unconditional |
| (1/3, 0.40722] | a shrinking set, 79 % → 0 % | **EMPTY** where certified | CYCLE (engine); `[1/6,13/24)` and the frontier now **proved**: `Z32.ZSet_three_two_sixth_3_8`, `Z32.ZSet_three_two_frontier` |
| (1/3, 0.40722] | the rest | **BAND** | §4.3 tried and refuted (M7): the product refinement gains nothing (Thm A), and here the cycle count is too small for Thm B to close it either — genuinely open |
| (0.40722, 19/24) | all | **BAND** | nothing certified either way |
| 19/24 = .7917 | (5/48, 43/48) | **NONEMPTY** | [Dub08] Thm 1.3 (≥1 per unit interval) |
| 57/65 = .8769 | [4/65, 61/65] | **NONEMPTY**, positive `dim_H` | [Pol81]; trap formalized in `Bugeaud/Chapter3/PollingtonConstruction.lean` |
| 17/19 = .8947 | [1/19, 18/19] | **NONEMPTY** | [Cho80] |

Unions:

| \|U\| | set | color | certificate |
|---|---|---|---|
| → 0 | [KK18] Cor 4.11 family | **NONEMPTY** | literature (constructive in principle) |
| 2/3 | `X_{3,2}`, and `‖·‖<1/3` | **NONEMPTY** | [KK18] Cor 4.8, [Dub10] |
| .476 | [Dub06] complement | **EMPTY** in print; **BAND** for this engine | [Dub06]; engine says FAT, λ ≈ 1.15 |
| 20/39 | [Dub08] Cor 1.2, **closed** | **EMPTY** | CYCLE, 12 blocks in 4 rank strata; **proved as printed**: `Z32.dubickas_2008_cor_1_2` |
| 25/36 | the 36-cell union | **EMPTY** | **proved**: `Z32.union_record_empty` (formalized record) |
| **.7417** | the 240-cell union above | **EMPTY** | CYCLE, 2512 blocks (engine record) |
| 1−ε | non-constructive | **EMPTY** | [KK18] Thm 5.9 |

---

## Verification depth (why to trust the verdicts)

Four implementations, two of them genuinely independent on the load-bearing
path:

1. `hold.c` — θ-coordinates (the FLP coordinate the Lean chain uses), single
   windows, exact `__int128` over `G·3^k`, plus the kneading-orbit escape test
   over `G·2^n`.
2. `atlas.c` — `y`-coordinates, arbitrary unions, exact, block-merge certificate.
3. `gridcert.c` — a uniform cell SFT with peeling, Tarjan SCCs and a
   branching-SCC test: a completely different algorithm.
4. `verify_atlas.py` — Python `Fraction` re-implementation, deliberately naive
   (generate every preimage, sort, merge), written to be slow and obviously
   correct.
5. **the Lean kernel** (M3) — for the six entries of `BlockCert.lean` there is a
   fifth checker that shares no code with any of the above: `gencert.py` emits a
   funnel, and the kernel rechecks both certificate conditions from the literal
   integer data. A wrong verdict from every engine at once would still have to
   survive this.

Checks actually run:

- **(1) vs (2)**: identical component counts at all five FLP positions
  (1, 3, 2, 3, 1) and identical certified/undecided verdicts across the `G = 24`
  length sweep.
- **(2) vs (4)**: identical component counts at **every level 15…30** on the
  record union (…1509, 1867, 2252, 2699… and …691, 688, 675…), and identical
  block structure and verdict on the smaller records, on [Dub08], and on the
  FLP positions.
- **Negative controls**: five sets known nonempty in print, all returned FAT.
  A false certificate here would be visible immediately.
- **Falsification test**: `atlas horse` searches for a *horseshoe* — two
  distinct cycles through one point, which implies uncountably many confined
  orbits and would **contradict** any CYCLE certificate. Run on every certified
  record: none found. Run on the X2 band entries at large `L`: the cycle count
  grows exponentially, as it must. **But not on the band entries at the
  frontier** — corrected at M7: `[961/3600, 2428/3600)` has exactly **one**
  cycle (2 orbit points) at `P ≤ 12`, the same as the certified entry beside it,
  and only a second at `P = 14`. Both `atlas horse` and `prodcert.py cycles`
  agree on this, independently.
- **A real bug was found this way.** The first `atlas.c` merged preimages
  against only the previous interval. For a single window of length ≤ 1/2 the
  preimages under different carries are disjoint, so that was correct — but for
  unions they overlap (the preimage of `[0,1)` under `e` is `[−e/3,(2−e)/3)`,
  width 2/3, while consecutive `e` are 1/3 apart), and the naive merge silently
  dropped intervals, producing a bogus "certified" union of total length 11/12.
  The Python cross-check caught it; the fix is a 4-way merge. All single-window
  results (X1, X2) were verified bit-identical before and after. Recorded here
  because plan R-5 says correlated single-author error is the dominant risk, and
  this is exactly what it looks like. Its blast radius was two verdicts, both
  now corrected: the bogus 11/12 union, and a [Dub06] "reproduction" that the
  fixed engine reports as FAT. Every number in this file was regenerated by
  `reproduce.sh` **after** the fix.

**Known limitation, stated up front.** `gridcert.c` cannot certify any `U` whose
hold set contains a cycle: the image of a cell is 1.5 cells wide, so a genuine
periodic point always looks branching, at every resolution. It is kept as an
independent implementation and for the empty-core certificate, not as an
oracle — its `λ` values are grid artifacts and are **not** dimension data.

**Convention.** `U` is half-open, `[lo,hi)` — the corpus `Ico` standard
(`FLP.ZSet`). Closed windows are *not* decided by the C engines: inflating the
right endpoint by a positive amount is too lossy (for [Dub08]'s set the inflated
version already fails at 1/(39·10⁶) — and the M4′ P1 work explains why, since
the closed hold set is genuinely richer, not marginally so). Closed intervals
*are* decided by `gencert.py --closed`, and proved by `BlockCert.lean`;
upgrading `atlas.c`/`gridcert.c` in the same way is still open (plan R-3).

---

## What this does and does not establish

**Does.** (i) The FLP95 chain reproduces exactly, including Thm 3.4's exact-`N`
trichotomy. (ii) The length-1/3 line holds at every rational position tested and
the stubborn set is provably invisible to rational sweeps. (iii) There is a
sharp engine frontier at `L* ≈ 0.40722` for single windows, and no uniform
`δ > 0` — M4 goes to lane (b). (iv) Explicit certified-empty unions exist with
total length up to **0.7417**, past the best published explicit value.
(v) The X2 band entries at large `L` are provably out of reach of hold-set-only
methods — but **not** the ones at the frontier (corrected at M7; see the
falsification test below). (vii) No block certificate of this family, at any
product level, can prove [Aki08] Conjecture 1.4 — M7, Theorems A and B.

(vi) Six of these entries are now **Lean theorems**, kernel-checked, std3, no
`native_decide` — including a window of length `0.375` and one of `0.40722`,
both past the 1995 line, and a certified-empty union of total length `25/36`.

**Does not.** The atlas *as a whole* is not formalized: the sweeps, the
frontier's sharpness (`nothing is certified above 1467/3600`), the λ / dimension
columns and the 0.7417 record remain engine output, and the six Lean entries are
individual points on the map, not the map. Nothing here touches the twin
ceilings `[0,1/2)` and `[1/2,1)` — at `L = 1/2` the engine returns the whole
interval, exactly as plan §1.3(ii) predicts. And no *numerical* claim is
announced before the M2′-style precondition (independent re-run + artifact +
referee read) is met; the six proved entries no longer need it.

---

## The M6 grid (plan-A6+ milestone WP0)

`plans/plan-A6+.html` §3.2 replaces the linear milestone ladder between M5 (every arc is visited
infinitely often) and M7 (uniform distribution) by a **grid**: how *many* visits an arc receives,
resolved per arc.  Three files ship the vocabulary and the exact arithmetic it runs on; all three
are `std3`, no cited axiom, no `native_decide`.

| rung (per arc) | predicate | state |
|---|---|---|
| V0 visits i.o. | `Z32.VisitsIO` | shipped, all `ξ ≠ 0` — see the ladder above |
| V1 `≥ c log N` visits | `Z32.V1` | **open**; WP2 target (sojourn dichotomy) |
| V2 `≥ c N^θ` visits | `Z32.V2` | open |
| V3 positive upper density | `Z32.V3` | open |
| V4 positive lower density | `Z32.V4` | open — **M6 at that arc** |
| V4S syndetic | `Z32.V4S` | open ⟺ bounded sojourns ⟺ `σ(p) = 0` |
| V5 frequency `= |I|` | `Z32.V5` | open — M7 at that arc |

Proved between the rungs: `V5 → V4 → V2 → V1 → V0`, `V4 → V3 → V0`, `V4S → V4`; and
`Z32.M6_iff_dyadic`, which reduces M6 to the countable family of dyadic windows.  The ceiling the
grid records: nothing above V0 can hold *uniformly in `ξ`* —
`Bugeaud.Pollington.exists_forall_dist_ge_of_cert` exhibits a `ξ > 0` avoiding the length-`8/65`
arc at `0` for ever.  Everything above V0 is `ξ = 1` territory.

The exact arithmetic at `ξ = 1` (`Z32/DyadicOrbit.lean`): `xₙ = rₙ/2ⁿ` with `rₙ = 3ⁿ mod 2ⁿ` odd,
so the points are pairwise distinct, separate by `2^{-max(m,n)}`, and — the floor WP2 runs on —
stay `≥ 1/(D·2ⁿ)` away from every rational with odd denominator `D`, i.e. from every cycle point of
`×3/2`.  Its negative companion: `3` has order exactly `2^{k-2}` mod `2ᵏ`, so the low `k` bits of
`rₙ` are purely periodic — the annealed baseline every census statistic is to be compared against.

The statistics (`Z32/PairStatistics.lean`): the lag identity `x_{m+d} - x_m ≡ ((3/2)^d - 1)(3/2)^m`,
the lag decomposition `P_N(s) = Σ_d C_N(s,d)`, the window energy `E_N(w) = Σ_b A_N(w,b)²` with its
exact L² defect identity (an empty window costs `N²/4ʷ`), and the **Weyl collapse**
`|S_N(2h) - S_N(3h)| ≤ 2` for every `h` — an exact consequence of `2(3/2)^{n+1} = 3(3/2)^n`, which
is why testing frequencies is only informative on the skeleton `gcd(m,6) = 1`.

## Balance vectors, and what finite resolution cannot do (plan-A6+ milestone WP1)

`Z32/BalanceVectors.lean` builds C6's measure-free enemy layer: instead of weak-\* limits of
empirical measures on the solenoid (risk R-G), level-`w` frequency vectors and the
flow-conservation equations of the **level-`w` carry graph**.  `std3`, no cited axiom, no
`native_decide`.  (R-G's compactness half has since closed upstream — Mathlib now has Prokhorov,
tightness, Lévy–Prokhorov and portmanteau — so the measure formulation is scheduled, in
`TH/Solenoid/LimitMeasures.lean` of plan-A1+, rather than blocked.  It would not rescue this layer:
the vacuity theorem's witnesses are invariant measures upstairs too.  Details in the file's module
doc.)

*The graph.*  At `ξ = 1` consecutive orbit points obey `2x_{n+1} = 3xₙ - sₙ` with an integer carry
`sₙ ∈ {-1,0,1,2}` (`Z32.exists_carry`, the four letters of `BlockCert.carries 3 2`).  `edgeOk w b b'`
asks whether *some* point of the level-`w` window `b` is carried into the window `b'` by one branch;
scaled by `2ʷ` that is the meeting of two integer intervals, so the graph is a kernel-evaluable
`Bool`.  It is sparse for `w ≥ 3` (at most the four carries per cell, `4·2ʷ` of the `4ʷ` pairs) and
**complete** at `w = 2` (`Z32.edgeOk_complete_two`).  The orbit walks in it: `Z32.edgeOk_orbit`.

*The balance lemma* (`Z32.exists_balanceVec`).  Along any horizon sequence `N k → ∞` the empirical
flow vectors `#{n < N : cellₙ = b, cell_{n+1} = b'}/N` have a convergent subsequence
(Bolzano–Weierstrass on `[0,1]^{cells²}`), and every limit is a `Z32.BalanceVec`: a probability
vector `μ` on the cells with a nonnegative flow `ν` on the graph whose two marginals are both `μ`.
The out-marginal identity is exact; the in-marginal costs only the two boundary dates (`≤ 1/N`).

*The enemy statement* (`Z32.exists_balanceVec_zero_of_not_V4`, `Z32.exists_trap_of_not_V4`).  If a
level-`w` window `b` has zero lower density — M6 fails there — then the graph carries a stationary
vector with **zero mass at `b`**, whose support is a `Z32.IsTrap`: a nonempty set of cells avoiding
`b` in which every cell has a successor and a predecessor, i.e. a subgraph carrying a cycle that
never visits `b`.  Contrapositive criterion: `Z32.V4_of_forall_trap_mem`.

*And the criterion is vacuous* (`Z32.exists_balanceVec_zero`, `Z32.exists_trap_not_mem`).  For every
`w ≥ 2` and every window `b` such a trap exists, so the criterion never fires and **no level-`w`
balance argument can prove M6 at any window, at any resolution**.  The witnesses are exactly C6's
atomic enemies: the fixed point `0` (a self-loop at the zero cell) and the rational 2-cycle
`{2/5, 3/5}` of denominator `5 = 3² - 2²`.  This is the honest WP1 deliverable — the flow layer
handles Front E bookkeeping and provably cannot touch Front D, which is why Front D is Diophantine.

*The cycle-point classification* (`Z32.cycle_point_eq`, `Z32.dist_cycle_point`).  A `p`-periodic
point of the carry relation is `A/(3^p - 2^p)` with `3^p - 2^p` **odd** — the [L90] rational-cycle
shape — so `Z32.dist_odd_denom` applies and the `ξ = 1` orbit stays `≥ 1/((3^p-2^p)2ⁿ)` away from
every `p`-cycle.  That is the quantitative floor C7/WP2 runs on.

## Files

| file | what it does |
|---|---|
| `VisitDensity.lean` | WP0: visit counts, lower/upper density, the V-rungs and their implications, `M6_iff_dyadic` |
| `DyadicOrbit.lean` | WP0: `xₙ = rₙ/2ⁿ` with `rₙ` odd — distinctness, separation, the 2-adic floor, the annealed baseline, the AP rung |
| `PairStatistics.lean` | WP0: lag identity and decomposition, window energy and its defect identity, Weyl sums and the collapse, `𝓔_N(H)` |
| `BalanceVectors.lean` | WP1: the level-`w` carry graph, empirical frequency/flow vectors, the balance lemma, the trap form of the M6 enemy, its proved vacuity at every level, the [L90] cycle-point classification |
| `hold.c` | engine A: θ-model, single windows; `orbit` (kneading escape), `prune`, `x1`, `x2` |
| `atlas.c` | engine C: exact `y`-model for arbitrary unions; `cert`, `win`, `x2`, `x3`, `x3exh`, `horse` |
| `gridcert.c` | engine B: uniform cell SFT, peel + Tarjan + branching-SCC test; `cert`, `ladder`, `search` |
| `verify_atlas.py` | independent Python/`Fraction` re-implementation (the cross-check) |
| `gencert.py` | M3/M6: emits the kernel-checkable funnel for `BlockCert.lean`; refuses the negative controls; `--pq p q`, `--closed`, `--ranked` |
| `pqcontrols.py` | M6: the second-base controls — [Dub09AA]'s length-`1/p` line, [Aki08]'s nonempty sets, and the cover test |
| `prodcert.py` | M7/X4: the §4.3 product refinement `(cell, x mod qʲ)`, the periodic-orbit census, and the two no-go theorems it measures; `cycles`/`hold` subcommands |
| `BlockCert.lean` | M3/M6: the soundness theorem for any coprime `p > q > 1`, and the eight `decide`-checked entries |
| `x3climb.py` | refinement hill-climb for the union record, driving `atlas` as a black box |
| `reproduce.sh` | regenerates every number above into `data/`, with checksums |
| `data/*.txt` | the sweep outputs quoted above |

Build: `gcc -O2 -o atlas atlas.c -lm` (likewise `hold`, `gridcert`).

## References

- **[FLP95]** Flatto, Lagarias, Pollington, *On the range of fractional parts
  ξ(p/q)ⁿ*, Acta Arith. **70** (1995) 125–147. Formalized: `FLP/`.
- **[Dub09AA]** Dubickas, *Powers of a rational number modulo 1 cannot lie in a
  small interval*, Acta Arith. **137** (2009) 233–239. Formalized:
  `Z32/SmallInterval.lean`.
- **[DN05]** Dubickas, Novikas — the aperiodicity lemma. Proved:
  `Z32/DubickasWord.lean`; it is the sole analytic input of the M3 certificate.
- **[Dub06]** Dubickas, J. Number Theory **117** (2006). **[Dub08]** Dubickas,
  Math. Nachr. **281** (2008). **[Dub10]** Dubickas (2010).
- **[Pol81]** Pollington, C. R. Acad. Sci. **292** (1981) 383–384.
  **[Cho80]** Choquet. **[Bug04]** Bugeaud. **[Kwon15]** Kwon.
- **[KK18]** Kari, Kopra — automata and `Z_{p/q}(S)`; Problem 6.1.
- **[AFS08]** Akiyama, Frougny, Sakarovitch. **[Aki08]** Akiyama.
- Plan: `plans/plan-cert32.html`. Engine ancestor: `plans/plan-dubC1.html`,
  `DubC/README.md`.
