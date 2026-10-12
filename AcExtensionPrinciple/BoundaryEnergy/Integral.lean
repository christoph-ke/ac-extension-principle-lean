module

public import AcExtensionPrinciple.BoundaryEnergy.Pointwise
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integrated boundary energy balance

Source: paper commit `e1a0fd5`, `equations.tex` lines 690–697,
729–738 (`eq:boundary-energy-balance`). This is the calculus step for AC traces.
-/

public section

namespace AcExtensionPrinciple

open MeasureTheory Set

/-- Integrated balance B; paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697,
729–738. Only AC of the energy and integrability of dissipation are needed:
AC of `P` and the sign of `D` are unnecessary for this equality. The balance itself gives
integrability of its right-hand side, even without a separate regularity assumption on `A`. -/
theorem boundary_energy_integral_balance {a0 a1 b : ℝ} {E P A D : ℝ → ℝ}
    (hE : AbsolutelyContinuousOnInterval E a0 a1)
    (hD : IntervalIntegrable D volume a0 a1)
    (hbalance : ∀ᵐ x ∂volume, x ∈ uIoc a0 a1 →
      deriv E x + D x = b * A x * deriv P x) :
    E a1 - E a0 + (∫ x in a0..a1, D x) =
      ∫ x in a0..a1, b * A x * deriv P x := by
  rw [← hE.integral_deriv_eq_sub,
    ← intervalIntegral.integral_add hE.intervalIntegrable_deriv hD]
  apply intervalIntegral.integral_congr_ae
  exact hbalance

end AcExtensionPrinciple

end
