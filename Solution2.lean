/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.SymbolicCert
import Z32.DepthKSchema
import Z32.EscapeBound
import Z32.CertComplete
import Z32.DepthSize
import Z32.RankedFrontier

/-!
# The second comparator solution: the real development

The counterpart of `Challenge2.lean`.  Where the challenge *states* the theorems of the schemas
paper (against Mathlib alone, with `sorry` proofs), this file simply **imports the actual
proofs**, so that the constants comparator is asked about are present in this module's environment
with their genuine proofs and their genuine definitional dependencies:

* `Z32.ZSet_eq_empty_of_certified` and the §3 corollaries — `Z32.SymbolicCert`
* `Z32.ZSet_eq_empty_of_certifiedK`, `Z32.ZSet_eq_empty_of_lowBand` and the depth-`K` instances —
  `Z32.DepthKSchema`
* `Z32.exists_fract_notMem_le_of_certifiedK` and the `Z32.BlockCert.escape_*` table —
  `Z32.EscapeBound`
* `Z32.step_unique`, `Z32.holdSet_finite_imp` and the five closed entries — `Z32.CertComplete`
* `Z32.depth_size`, `Z32.depth_size_logb` — `Z32.DepthSize`
* `Z32.ZSet_three_two_two_seven` and its three companions — `Z32.RankedFrontier`

`Z32.CycleTransversal` is not imported: none of the statements `comparator2.json` certifies is
proved there (Proposition 5.4 and Theorems 5.8, 5.10's transversal half quantify over
`Z32.BlockCert.Cert`, which `Challenge2.lean` deliberately does not restate — see its docstring).

Table 1 row 6 of the paper is deliberately **not** here: `Z32.escape_union_7083` rests on the
certificate `Z32.BlockCert.certUnion7083`, whose kernel check alone costs about 100 seconds and 12
gigabytes, and `Z32/UnionRecord.lean` exists so that nothing else pays that.  `SolutionRecord2.lean`
adds it, for anyone who wants that row compared.  Since `comparator2.json` certifies the paper's
lettered results and that row is not among them, the config names **this** module, and a
`comparator2.json` run does not pay the union record's cost at all.

There is deliberately no content here.  Anything proved *in this file* would be outside the scope
of what comparator checks against the challenge, so the file must stay a pure re-export of the
development.
-/
