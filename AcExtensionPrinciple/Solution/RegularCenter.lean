module

public import AcExtensionPrinciple.Frozen.RegularCenterLocalACBV
public import AcExtensionPrinciple.Solution.LocalBV

/-!
# Regular-center local AC/BV class (minimal)

Paper commit `e1a0fd5`, `equations.tex`
lines 114–119 and 220–275. Joint r, m, λ, φ continuity and outgoing λ AC are derived in
`Minimal/Restore.lean`; ν continuity
is retained (line 222: "The incoming expansion ν is continuous"). By author ruling Q1, incoming AC
of ν is omitted: the proof of Theorem 1
uses only incoming continuity and BV of ν, supplied by the remaining fields.
Scalar axis traces (author ruling Q10): one-sided limits along the
two characteristics through each regular axis point, `eq:regular-axis-one-sided-traces`
(lines 247–256). The two-dimensional limits within the off-axis triangle (lines 263–273) are
derived in `Minimal/OneSidedTraces.lean`.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

end AcExtensionPrinciple

end
