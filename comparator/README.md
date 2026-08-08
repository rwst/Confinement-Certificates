<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 (public domain).
-->

# Certifying this repository with `comparator`

[`leanprover/comparator`](https://github.com/leanprover/comparator) is a trustworthy judge
for Lean proofs. Here it is used as a **self-audit**: it checks that the development really
proves the statements this repository claims, using only the axioms this repository admits.

Given the challenge (`Challenge.lean`: the statements, importing *Mathlib only*, proofs
`sorry`) and `Solution.lean` / `SolutionRecord.lean` (bare re-exports of the development),
comparator independently verifies:

1. **Statement match** — every constant in the transitive closure of the certified
   statements is *identical* in both environments. The `Z`-set `FLP.ZSet` is the only
   definition the certified statements mention, and a version that had drifted from the one
   in `Challenge.lean` — a half-open `[s,s+t)` quietly turned closed, the membership condition
   `0 < ξ` swapped for another, an endpoint moved — is caught here.
2. **Axiom discipline** — the proofs reach for no axiom outside the config's
   `permitted_axioms`, and a permitted axiom's *type* is compared across both environments
   too (so a permitted axiom cannot be quietly restated as `False`).
3. **Kernel replay** — the exported solution environment is re-accepted from scratch by the
   Lean kernel: `lean4export` writes it out, and comparator replays it into a fresh
   environment, without loading any `.olean` at all. For this
   repository that is the load-bearing step: every block certificate is proved by
   `theorem cert…_ok : cert….ok = true := by decide`, so the replay makes the kernel
   *re-evaluate the integer arithmetic of every certificate from the raw data*, on a fresh
   environment, with no appeal to the C engines that discovered them.

Auditing the headline claims therefore reduces to **reading one file**, `Challenge.lean`.

## The seven configs

The paper's claim about its own trust base is uniform and negative: no `sorry`, no cited
literature admitted as an axiom, no natively compiled decision procedure — every statement is
proved at "std3", the classical core of Lean (`propext`, `Quot.sound`, `Classical.choice`).
Accordingly **every config below permits exactly those three axioms**. That is not a formality:
were any proof to start leaning on a cited result, comparator would report `Illegal axiom
detected` for the config that covers it — which is how a regression in the trust base would be
caught, rather than by inspection of the prose.

The split into seven follows the paper's own grouping of results, so that a failure names the
section it belongs to.

| Config | Paper | Theorems |
| --- | --- | --- |
| `classical.json` | §4, §6 | `Z32.FLP_cor_one_four_a` ([FLP95] Cor. 1.4a); `Z32.dubickas_theorem_1`, `Z32.ZSet_eq_empty_of_lt_sq`, `Z32.ZSet_three_two_third_empty` ([Dub09AA] Thm. 1) |
| `residue.json` | §5, Thm. C | `Z32.residue_not_eventually_constant`, `Z32.exists_residue_change`, `Z32.residue_not_eventually_constant_one` |
| `windows.json` | §7, Thm. A | `Z32.ZSet_three_two_sixth_3_8`, `Z32.ZSet_three_two_frontier`, `Z32.not_eventually_mem_sixth_3_8`, `Z32.ZSet_four_three_beyond_line` |
| `unions.json` | §7, Thm. B | `Z32.dubickas_2008_cor_1_2`, `Z32.union_seven_twelfths_empty`, `Z32.union_two_thirds_empty`, `Z32.union_record_empty` |
| `nearest.json` | §7, Thm. D | `Z32.two_cell_fifth_empty`, `Z32.not_forall_abs_sub_round_lt_fifth` |
| `pastsquare.json` | §7 | `Z32.ZSet_five_two_fifth` and the five grid theorems — the thirty windows in the regime `p > q²` |
| `record.json` | §7, Thm. B | `Z32.union_record_7083_empty` — the union record, total length `17/24` |

So the two classical pillars, the residue corollary, Theorems A, B and D, and the whole
`p > q²` table are certified — and none of them borrows anything.

### What the challenge deliberately does *not* restate

`Challenge.lean` re-declares one definition, `FLP.ZSet`, and nothing else. The block-certificate
apparatus — `Z32.BlockCert.Cert`, `Cert.ok`, `funnelOk`, `funcOk`, the carry alphabet — does not
appear there, and neither does the soundness theorem `Cert.not_confined` or its sole analytic
input, the aperiodicity lemma `Z32.not_isEventuallyPeriodic_carry`.

That is not an omission but the shape of the result. Every certified statement above is phrased
in Mathlib vocabulary alone — `Int.fract`, `Set.Ico`, `Set.Icc`, `round`, `⌊·⌋` — so the whole
apparatus is *quantified away* before comparator ever sees a statement. A reader auditing
`Challenge.lean` therefore does not have to read the checker, the funnel conditions, or the
notion of a rank stratum in order to know what is being claimed. Their correctness is nowhere
assumed either: `Cert.not_confined` and the aperiodicity lemma are ordinary Lean theorems, and
step 3 re-checks them in the kernel along with everything else in the transitive closure of the
certified statements.

### Why `record.json` has a solution module of its own

The certificate behind `Z32.union_record_7083_empty` has denominator `48·3¹⁷` and a funnel of
17 levels and 100 blocks; kernel-checking `certUnion7083_ok` alone costs about **100 seconds
and 12 gigabytes** when the module is built. The development isolates it in
`Z32/UnionRecord.lean` precisely so that no other file pays that, and nothing imports that
module. Comparator then re-does the work: its replay of the exported environment took 51
seconds and peaked at 8.6 GB here, on top of an already-built `Z32.UnionRecord`.

`Solution.lean` preserves the isolation — it re-exports the development *without*
`Z32.UnionRecord` — and `SolutionRecord.lean` adds it. Only `record.json` names the latter, so
the other six configs never build the expensive module at all. On a machine with less than
about 16 GB of memory, run those six and leave the record out:

```sh
lake test -- comparator/classical.json comparator/residue.json comparator/windows.json \
             comparator/unions.json comparator/nearest.json comparator/pastsquare.json
```

## Install

Comparator is a Lake dependency (`lakefile.lean`), so Lake builds it and `lean4export` at this
project's toolchain — nothing to install by hand:

```sh
lake build comparator lean4export
```

`landrun` is the one exception: it has no pinned release, so build it from source. It uses
**Landlock**, so this is **Linux-only** (check with `grep LANDLOCK /boot/config-$(uname -r)`);
building it needs [Go](https://go.dev/dl/).

```sh
git clone https://github.com/Zouuup/landrun && cd landrun
go build -o ~/.local/bin/landrun cmd/landrun/main.go   # ensure ~/.local/bin is on PATH
```

## Run

```sh
lake build Challenge Solution                 # prebuild: the sandbox has no network
lake build SolutionRecord                     # only for `record.json` — ~100 s, ~12 GB
lake test                                     # runs comparator on all seven configs
```

A successful run prints `Your solution is okay!` once per config. To run a single config:

```sh
lake test -- comparator/windows.json
```

Each binary can be overridden by environment variable — `COMPARATOR_BIN`,
`COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN` — which is also how to substitute
comparator's `scripts/fake-landrun.sh` shim on a machine without Landlock. That shim does
**not** sandbox anything; it still exercises the statement match, the axiom check and the
kernel replay, which are the three properties that matter for a self-audit.

## A note on the sandbox

Comparator's threat model targets an *adversarial* solution: it sandboxes every build with
`landrun` and, for full hardening against a known landrun escape (fixed in Linux 7.1), asks
to be wrapped in

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- bash -c 'lake test'
```

Here the solution is our own code, so the sandbox is belt-and-braces; the load-bearing
guarantees are the statement match, the axiom check, and the independent kernel replay.
