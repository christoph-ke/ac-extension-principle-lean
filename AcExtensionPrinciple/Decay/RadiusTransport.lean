module

public import AcExtensionPrinciple.Solution.Fields
public import Mathlib.Tactic

/-!
# Radius separation along an incoming segment

Paper `e1a0fd5`, `equations.tex` line 814. The radius
equation `∂ᵤr=ν` is used in the characteristic integral form `IntervalPrimitive`,
already defined by the shared solution interface.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Integrating `-ν≥K⁻¹` from the earlier cone to the cylinder gives the
radius lower bound. The integral relation is the shared encoding of `∂ᵤr=ν`,
not a new geometric bound. Paper `e1a0fd5`, `equations.tex` line 814,
using `eq:radius` and `eq:outward-nu-monotonicity`. -/
theorem radius_lower_bound_of_incoming_transport {R nu : ℝ → ℝ} {u0 u b K : ℝ}
    (hu : u0 ≤ u) (htransport : IntervalPrimitive R nu u0 u)
    (hb : R u = b) (hnu : ∀ s ∈ Icc u0 u, K⁻¹ ≤ -nu s) :
    b + K⁻¹ * (u - u0) ≤ R u0 := by
  have hmono : (∫ s in u0..u, nu s) ≤ ∫ _s in u0..u, -(K⁻¹) := by
    apply intervalIntegral.integral_mono_on hu htransport.1 intervalIntegrable_const
    intro s hs
    linarith [hnu s hs]
  rw [intervalIntegral.integral_const] at hmono
  have heq := htransport.2
  rw [hb] at heq
  simp only [smul_eq_mul] at hmono
  linarith

end AcExtensionPrinciple

end
