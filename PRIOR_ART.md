# Prior-art search

*Confinement schemas and the reach of block certificates for powers of rational numbers
modulo one* (`paper2.pdf`; statements in `Challenge2.lean`, proofs in `Solution2`)

This file records the literature search behind the novelty statements and the comparisons with
print in the paper and in `formalization.yaml`. It is compiled from the dated working notes of
the research plan that produced the paper, *z32-transform*: the memo of its gate G-0
(2026-09-01), the note of milestone M3 (2026-09-02), and the notes of milestones M2 and M4–M6
(2026-09-02 and 2026-09-03). Those notes are not part of this repository; their names are given
so that each entry can be traced. Citation keys are the paper's.

**In short.** The search was targeted, not exhaustive: sources chosen for relevance, extended by
forward-citation sweeps on three papers. It found the whole of §3 in print — Theorems 3.5 and 3.6
are a machine-checked fragment of [Bug04, Thm. 1] — and it supplies the comparisons with print
in §§1, 3 and 7. It records no search aimed at Theorems C and D, and no keyword search of a
database. Novelty is therefore recorded as unknown.

## 1. Gate G-0: scoop check, 2026-09-01

Run before any novelty wording was fixed (memo `note-z32transform-G0`), on three questions:
(a) what [Dub19] settles of the window problem for p > q², and what Lu and Zheng prove for
negative bases; (b) whether the literature on expanding maps with holes already treats ×p/q;
(c) whether [Dub09AA, §4] has been resolved since 2009.

| Source | Read |
| --- | --- |
| [Dub19] | in full |
| [Dub09AA] | §4, verbatim |
| P. Glendinning, N. Sidorov, *The doubling map with asymmetrical holes*, ETDS (2015), arXiv:1302.2486 | in full |
| Q. Lu, W. Zheng, *Fractional parts of powers of negative rationals*, arXiv:2603.16794 | in full |
| [KK17] | §6; Problem 6.1 verbatim |
| [Bug12] | §3.5–3.6 |
| O. Kurganskyy, I. Potapov, *De Bruijn graphs and powers of 3/2*, arXiv:1811.02254 | the same day (memo §4.4) |
| J. Kopra, *On the trace subshifts of fractional multiplication automata*, Theoret. Comput. Sci. 851 (2021) | the same day, reached from [KK17] |
| B. Farhi, arXiv:math/0611622; N. Sidorov, arXiv:1204.1920; arXiv:2311.02465 | abstracts only |

Forward-citation sweeps were run on [Dub09AA], [Dub19] and [KK17]. The sweep on [Dub19] returned
Lu–Zheng and one unrelated paper; the one on [Dub09AA] found no progress on the question its §4
leaves open; the one on [KK17] led to Kopra.

Found:

- [Dub19, Thm. 1.1] settles p > q² at every position for algebraic ξ ≠ 0. The paper's statements
  in that regime are accordingly made with no assumption on the arithmetic nature of ξ, and
  compared with it.
- [Dub19, Thm. 1.2], the window [8/57, 805/1539] of length 31/81 at the base 3/2: the
  single-window record in print that Theorem E is compared with.
- [Dub06, Cor. 1], read here as [Bug12, Thm. 3.14]: the constants 0.238117… and 0.285647… of
  §7.1. It superseded a theorem in the abstract of the first paper [Ste26], which was corrected
  the same day.
- Kurganskyy–Potapov and Kopra: prior art for automaton approaches to the same sets, with no
  unconditional emptiness result.

Not found: any result after 2019 on p > q² for transcendental ξ; any explicit answer to
[KK17, Prob. 6.1]; any treatment of ×p/q in the literature on maps with holes — the last a miss,
corrected at M3 (§2).

## 2. Milestone M3: the objects of §3, 2026-09-02

Before any novelty wording for the depth-K schema, its objects were searched for (note
`note-z32transform-M3`, §3). All of them are in print, in a paper that the plan's own
bibliography had cited from its first draft and that G-0 had not read:

| Object | In print |
| --- | --- |
| Definition 3.3, escaping case | [FLP95, Thm. 3.4] |
| Definition 3.3, returning case, and its exactness | [Bug04, Lems. 1, 2] |
| Proposition 3.4, the rank rotation | [FLP95, Thm. 3.4]; [Bug04, Prop. 1], after [Bug93], [BC99] |
| Theorem 3.6's band (4) | [Bug04, Lem. 3], the interval J¹_{K+1}(q/p) |
| the positions settled, assembled over all K (§3.3) | [Bug04, Thm. 1]: full Lebesgue measure |
| the positions left over (§3.3 and its footnote) | [Bug04, Thm. 3]: null, uncountable, not closed; transcendental by [BKLN21] |

Read at this step: [Bug04] in full, and [FLP95] Theorems 3.4–3.5. Consulted: [BKLN21];
M. Laurent, A. Nogueira, *Rotation number of contracted rotations*, J. Mod. Dyn. 12 (2018);
J. P. Gaivão, Qual. Theory Dyn. Syst. (2025). [Bug93] and [BC99] are cited through
[Bug04, Prop. 1].

The match was checked independently: [Bug04, Lem. 3]'s intervals J^a_b(q/p), computed from the
Sturmian sequence with no reference to the development's derivation, agree with the development's
criterion at 840 points over every a/b with b ≤ 9, and J¹_{K+1} coincides with `Z32.LowBand` at
every base tested, up to K = 11.

Consequence: §3.3 of the paper ("The mathematics of this section is not new"), and the
formalization claims only the machine-checked form of §3. The miss is recorded as a lesson of the
plan: search the plan's own reference list for the target's key words before searching outward.

## 3. Later milestones, 2026-09-02 and 2026-09-03

- [Dub06] was read in full at M6 (Cor. 1, p. 225); its two constants are the ceilings §7.1
  identifies. [Pol81] is quoted there, on p. 225, and [AFS08] is cited for the matching bound on
  the other side; neither is recorded as read.
- [Koh08] was read for the plan; it is the methodological source of §4.
- Theorem 6.3 is framed against [KK17, Prob. 6.1], read verbatim at G-0.

No search aimed specifically at Theorem C (§4), Theorem D (§§5–6) or the closed-endpoint entries
of Theorem 5.10 is recorded.

## 4. What rests on it

| Statement | Where | Basis |
| --- | --- | --- |
| §3 is not new; Theorems 3.5 and 3.6 are a fragment of [Bug04, Thm. 1] | §3.3; `formalization.yaml` | M3 |
| p > q² is settled in print only for algebraic ξ, and open for arbitrary real ξ | §1; Corollary 3.11 | G-0: [Dub19, Thm. 1.1]; sweeps on [Dub19] and [Dub09AA] |
| 31/81 is the longest single window excluded in print | §1; §7 | G-0: [Dub19, Thm. 1.2]; sweep on [Dub19] |
| the ceilings of §7.1 are the constants of [Dub06, Cor. 1] | §7.1 | G-0, through [Bug12]; [Dub06] itself at M6 |
| [KK17, Prob. 6.1] has no explicit answer in print | §1; §6 | G-0 |

## 5. Limits

- The search was targeted. No keyword search of MathSciNet, zbMATH or arXiv is recorded, and
  forward-citation sweeps were run on three papers only.
- It has missed once already: G-0 skipped [Bug04], and M3 caught it before the paper's wording
  was fixed.
- Some items were read by abstract only (§1).
- Nothing is recorded after 2026-09-03; the paper is dated 2026-09-08.

So `formalization.yaml` records novelty as unknown, and the comparisons with print in §4 are as
strong as the reading behind them.
