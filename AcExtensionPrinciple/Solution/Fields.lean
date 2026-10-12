module

public import AcExtensionPrinciple.Frozen.Axis
public import AcExtensionPrinciple.Frozen.InSeg
public import AcExtensionPrinciple.Frozen.IntervalPrimitive
public import AcExtensionPrinciple.Frozen.OffAxis
public import AcExtensionPrinciple.Frozen.OutSeg
public import AcExtensionPrinciple.Frozen.PastTriangle
public import AcExtensionPrinciple.Frozen.SSFields
public import AcExtensionPrinciple.Frozen.SSFieldsGamma
public import AcExtensionPrinciple.Frozen.SSFieldsMassU
public import AcExtensionPrinciple.Frozen.SSFieldsMassV
public import AcExtensionPrinciple.Frozen.SSFieldsMu
public import AcExtensionPrinciple.Frozen.SSFieldsRadiusCoeff
public import AcExtensionPrinciple.Frozen.SSFieldsTheta
public import AcExtensionPrinciple.Frozen.SSFieldsVarkappa
public import AcExtensionPrinciple.Frozen.SSFieldsZeta
public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Fields and characteristic segments

Rulings Q1, Q6, Q8. Paper commit
`e1a0fd5`, `equations.tex` lines 49–106 and `eq:past-triangle` (lines 114–119).
Derivative fields acquire their meaning from characteristic integral identities,
not from differentiation in a definition.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

namespace SSFields

/-- Normalized outgoing expansion. Paper `e1a0fd5`, `eq:normalized-expansions`. -/
@[expose] noncomputable def kappa (S : SSFields) (u v : ℝ) : ℝ :=
  kappaOf (S.lam u v) (S.mu u v)

/-- Outgoing scalar derivative away from the axis. Paper `e1a0fd5`, lines 94–99. -/
@[expose] noncomputable def dvphi (S : SSFields) (u v : ℝ) : ℝ :=
  S.theta u v / S.r u v

/-- Incoming scalar derivative away from the axis. Paper `e1a0fd5`, lines 94–99. -/
@[expose] noncomputable def duphi (S : SSFields) (u v : ℝ) : ℝ :=
  S.zeta u v / S.r u v

end SSFields

open Set

end AcExtensionPrinciple

end
