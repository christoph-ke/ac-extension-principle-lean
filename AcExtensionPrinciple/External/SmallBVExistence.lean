module

public import AcExtensionPrinciple.External.ChristodoulouBV
public import AcExtensionPrinciple.Frozen.SmallBVDomain
public import AcExtensionPrinciple.Frozen.SmallBVExistence
public import AcExtensionPrinciple.Frozen.SmallBVGeometry
public import AcExtensionPrinciple.Frozen.SmallBVIncomingTV
public import AcExtensionPrinciple.Frozen.SmallBVOutgoingTV
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Small-BV existence input E1

Paper `e1a0fd5`, `equations.tex`
`lem:small-bv-existence`, lines 1364–1388. Source: Luk–Oh, Anal. PDE 8
(2015), Theorem 5.12, (5-29)–(5-31), Remark 5.13 and footnote 13,
p. 1633; provenance: Christodoulou, CPAM 46 (1993), Theorem 6.2,
p. 1183 and its proof. This is a proposition to assume explicitly,
not an assertion that the external theorem has been proved in Lean.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

end AcExtensionPrinciple

end
