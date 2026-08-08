See https://www.researchgate.net/publication/411967777_Confinement_certificates_for_powers_of_rational_numbers_modulo_one

## Verification

Every statement of the paper is a theorem of Lean 4, machine-checked down to the kernel, with
no `sorry`, no cited axiom, and no natively compiled arithmetic: the block certificates are
verified by the kernel's own evaluator on integer data.

```sh
lake build Z32          # the development
lake test               # re-certify it with `leanprover/comparator`
```

`lake test` runs [`leanprover/comparator`](https://github.com/leanprover/comparator) on the
seven configs in `comparator/`. It checks, independently of this repository's build, that the
development proves exactly the statements of `Challenge.lean` — the paper's claims restated
against Mathlib alone — using only the three axioms of classical Lean, and that the resulting
environment is re-accepted by the Lean kernel from a fresh export. Setup, the config table, and
the memory cost of the union record are in [`comparator/README.md`](comparator/README.md).
