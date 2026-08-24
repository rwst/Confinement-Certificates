/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Solution
import Z32.UnionRecord

/-!
# The comparator solution, expensive half: the union record

`Solution.lean` re-exports the development; this module adds the one theorem that carries a real
price, `Z32.union_record_7083_empty` (Theorem C's record, total length `17/24`).  Its certificate
`Z32.BlockCert.certUnion7083` has denominator `48·3¹⁷` and a funnel of 17 levels and 100 blocks;
kernel-checking `certUnion7083_ok` alone costs about 100 seconds and 12 gigabytes.

The development keeps that cost in a module of its own so that no other file pays it.  This
module is what `comparator.json` names, so a `lake test` run pays it once; certifying any subset
of the other statements against `Solution` does not pay it at all.

As with `Solution.lean`, there is deliberately no content here.
-/
