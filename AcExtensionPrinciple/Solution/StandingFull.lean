module

public import AcExtensionPrinciple.Solution.Standing
public import AcExtensionPrinciple.Solution.RegularCenterFull

/-!
# Internal full standing bundle
Paper `e1a0fd5`, `equations.tex` lines 66–84 and 220–275.
This preserves the former full interface for downstream proofs.
The source class is minimal; this bundle is derived for standing solutions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Internal full standing bundle, restored from the minimal source hypotheses.
Paper `e1a0fd5`,
`thm:main`, lines 114–132. External continuation inputs are outside this bundle. -/
structure StandingFull (ui : ℝ) (S : SSFields) : Prop where
  initial_negative : ui < 0
  regularCenter : RegularCenterFull ui S
  signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
    0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1
  initial_gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1
  initial_ac_data : AbsolutelyContinuousOnInterval (S.dvpsi ui) ui 0
  blueshift_finite : blueshiftSup ui S < ⊤


end AcExtensionPrinciple

end
