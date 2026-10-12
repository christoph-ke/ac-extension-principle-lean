module

public import AcExtensionPrinciple.Frozen.BlueshiftSup
public import AcExtensionPrinciple.Frozen.StandingAssumptions
public import AcExtensionPrinciple.Solution.RegularCenter
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Standing hypotheses and incoming blueshift

Paper commit `e1a0fd5`, `equations.tex`
lines 114–132. No conclusion of Lemma 1.1
is a field of the hypotheses.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Real incoming blueshift constant, used under finiteness of the supremum.
Paper `e1a0fd5`, `eq:uniform-blueshift`. -/
@[expose] noncomputable def Bstar (ui : ℝ) (S : SSFields) : ℝ :=
  (blueshiftSup ui S).toReal

end AcExtensionPrinciple

end
