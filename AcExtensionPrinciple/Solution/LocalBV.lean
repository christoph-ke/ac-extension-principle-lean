module

public import AcExtensionPrinciple.Frozen.AxisVanishingVariation
public import AcExtensionPrinciple.Frozen.LocalBVSolution
public import AcExtensionPrinciple.Solution.Fields

/-!
# Local BV solution class (minimal)

Paper commit `e1a0fd5`, `equations.tex`
lines 66–84, 220–275; Luk–Oh Definition 2.1. Rulings: Q5 (Def. 2.1(5) included), Q6 (all
compact subsets, incl. those reaching v = 0), Q8 (characteristic integral equations). The four axis
oscillation conditions retain exactly the four families in Definition 2.1(5),
intersected with the given domain. Scalar AC and four right-continuity conventions are recovered for
standing solutions in `Minimal/Restore.lean`. The two uniform scalar TV bounds remain
(field `scalar_variation`).
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

end AcExtensionPrinciple

end
