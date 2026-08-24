/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.EscapeCert
import Z32.ResidueCapture
import Z32.SmallInterval
import Z32.BlockCert

/-!
# The comparator solution: the real development

The counterpart of `Challenge.lean`.  Where the challenge *states* the certified theorems
(against Mathlib alone, with `sorry` proofs), this file simply **imports the actual proofs**, so
that the constants comparator is asked about are present in this module's environment with their
genuine proofs and their genuine definitional dependencies:

* `Z32.FLP_cor_one_four_a` — [FLP95] Cor. 1.4a (`Z32.EscapeCert`)
* `Z32.dubickas_theorem_1`, `Z32.ZSet_eq_empty_of_lt_sq`, `Z32.ZSet_three_two_third_empty` —
  [Dub09AA] Thm. 1 and its `Z`-set forms (`Z32.SmallInterval`)
* `Z32.residue_not_eventually_constant` and its two variants — Theorem A (`Z32.ResidueCapture`)
* every block-certificate entry — Theorems B, C, D and the `p > q²` table (`Z32.BlockCert`)

The union record of Theorem C is deliberately **not** here: its certificate alone costs about 100
seconds and 12 gigabytes to check, and `Z32/UnionRecord.lean` exists so that nothing else pays
that.  `SolutionRecord.lean` adds it, and `comparator.json` names *that* module — so this one
stays the cheap re-export, for anyone certifying a subset of the statements against it.

There is deliberately no content here.  Anything proved *in this file* would be outside the scope
of what comparator checks against the challenge, so the file must stay a pure re-export of the
development.
-/
