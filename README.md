See https://www.researchgate.net/publication/411967777_Confinement_certificates_for_powers_of_rational_numbers_modulo_one

## Verification

Every statement of the paper is a theorem of Lean 4, machine-checked down to the kernel, with
no `sorry`, no cited axiom, and no natively compiled arithmetic: the block certificates are
verified by the kernel's own evaluator on integer data.

```sh
lake build              # the development
lake test               # re-certify it with `leanprover/comparator`
```

`lake test` runs [`leanprover/comparator`](https://github.com/leanprover/comparator) on
`comparator.json` and `comparator2.json` — one config per paper. Each checks, independently of
this repository's build, that the development proves the statements of its challenge file — the
paper's claims restated against Mathlib alone — using only the three axioms of classical Lean, and
that the resulting environment is re-accepted by the Lean kernel from a fresh export.
`comparator.json` checks every statement of `Challenge.lean`; `comparator2.json` checks the
schemas paper's lettered results — the eleven entries of `Challenge2.lean` that carry a Theorem
A–E label, which is all of them except Theorem D(ii):

| Paper | Numbered statements | `Challenge2.lean` |
| --- | --- | --- |
| Theorem A | Thms. 3.5, 3.6 | `ZSet_eq_empty_of_certifiedK`, `ZSet_eq_empty_of_lowBand` |
| Theorem B | Cors. 3.7, 3.8 | `ZSet_eq_empty_of_certified` (Cor. 3.8 is arithmetic from it) |
| Theorem C | Thm. 4.4 | `exists_fract_notMem_le_of_certifiedK` |
| Theorem D(i) | Thm. 5.5 | `holdSet_finite_imp` |
| Theorem D(ii) | Thm. 5.7 | — (quantifies over `Z32.BlockCert.Cert`; not restated) |
| Theorem D(iii) | Thm. 6.3, Cor. 6.4 | `depth_size`, `depth_size_logb` |
| Theorem E | Thm. 7.1 | `ZSet_three_two_two_seven`, `two_seven_empty`, `not_eventually_two_seven`, `not_forall_two_seven_le_abs_sub_round` |

The remaining thirty statements of `Challenge2.lean` — the §3 corollaries, the Table 1 escape
rows, the closed entries of Thm. 5.10 — are still stated and still proved by the development; they
are simply not part of what this config certifies.

| Config | Challenge | Solution | Statements | Paper |
| --- | --- | --- | --- | --- |
| `comparator.json` | `Challenge.lean` | `SolutionRecord` | 24 | *Confinement certificates …* |
| `comparator2.json` | `Challenge2.lean` | `Solution2` | 11 | *Confinement schemas …* |

Run one at a time with `lake test -- comparator2.json`. `comparator.json`'s solution module carries
`Z32/UnionRecord.lean`, whose certificate's kernel check alone costs about 100 seconds and 12
gigabytes, so that config wants a machine with about 16 GB of memory.  `comparator2.json` no
longer names `Z32.escape_union_7083` (Table 1 row 6), so it runs against `Solution2` and does not
pay that cost.

`Challenge2.lean` states the schemas paper's Theorems A–E and their corollaries; the statements it
leaves out are those quantified over the certificate format `Z32.BlockCert.Cert` itself
(Thm. 4.2, 5.6–5.8, Cor. 5.9, Cor. 6.4, Ex. 6.5), whose challenge would have to re-declare the
whole `Bool`-valued validity checker. Its docstring says so, entry by entry.

`comparator` and `lean4export` are Lake dependencies (`lake build comparator lean4export`);
`landrun`, which comparator uses to sandbox every build, has no pinned release and must be built
once by hand (Go, and Linux-only — it uses Landlock), or supplied via `COMPARATOR_LANDRUN`.

Please cite:
```
@misc{stephan2026confinementcertificates,
      title={Confinement certificates for powers of rational numbers modulo one}, 
      author={Ralf Stephan},
      abstract="Let $p>q>1$ be coprime integers and let $\Zset_{p/q}(s,s+t)$ denote the set of
positive real $\xi$ whose fractional parts $\fp{\xi(p/q)^{n}}$ lie in $[s,s+t)$
for every $n\ge0$. We describe a machine-verified development, in the Lean~4
proof assistant, of the emptiness theory of these sets at and beyond the window
length $1/p$. Corollary~1.4a of Flatto, Lagarias and Pollington is regenerated
as a kernel-checked finite computation, and the theorem of Dubickas --- for
$1<q<p<q^{2}$ the parts $\fp{\xi(p/q)^{n}}$ cannot all lie in a closed interval
of length $1/p$ --- is formalized in full, including proofs of its
combinatorial inputs (the aperiodicity lemma of Dubickas and Novikas and the
bispecial criterion for Sturmian words).
    We then introduce \emph{block certificates} --- finite integer
witnesses, rechecked from scratch by the Lean proof kernel, whose soundness rests on
the aperiodicity lemma alone --- and use them to pass the length-$1/p$ line:
$\Zset_{3/2}(1/6,13/24)=\emptyset$ (window length $3/8>1/3$),
$\Zset_{3/2}(961/3600,2427/3600)=\emptyset$ (length $733/1800$), and explicit
unions of total length up to $17/24$, against $20/39$ in print. The
closed-interval union statement of Dubickas is replicated exactly as printed;
no $\xi\ne0$ keeps $\|\xi(3/2)^{n}\|<1/5$ for every $n$, with $\|\cdot\|$ the
distance to the nearest integer; and thirty windows of length $1/p$ are
certified at five bases in the regime $p>q^{2}$ that Dubickas leaves open. The
development is free of unproved assumptions beyond the classical core of Lean.",
      year={2026},
      url={https://www.researchgate.net/publication/411967777_Confinement_certificates_for_powers_of_rational_numbers_modulo_one}, 
}
```
