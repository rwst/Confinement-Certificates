/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Solution2
import Z32.UnionRecord

/-!
# The second comparator solution, expensive half: the union record

`Solution2.lean` re-exports the development the schemas paper rests on; this module adds the one
theorem of that paper which carries a real price, `Z32.escape_union_7083` — Table 1 row 6, the
effective form of the union record of total length `17/24`.  Its certificate
`Z32.BlockCert.certUnion7083` has denominator `48·3¹⁷` and a funnel of 17 levels and 100 blocks;
kernel-checking `certUnion7083_ok` alone costs about 100 seconds and 12 gigabytes.

The development keeps that cost in a module of its own so that no other file pays it.
`comparator2.json` certifies the paper's lettered results, Theorems A to E, and Table 1 row 6 is
not among them — so the config names `Solution2` and a `lake test` run does not pay this cost.
This module exists for anyone who wants `Z32.escape_union_7083` compared too: add it to
`comparator2.json`'s `theorem_names` and point `solution_module` here.

As with `Solution2.lean`, there is deliberately no content here.
-/
