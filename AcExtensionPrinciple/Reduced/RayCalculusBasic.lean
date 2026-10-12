module

public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Pointwise calculus shared by the two characteristic directions

Source: paper commit `e1a0fd5`, `equations.tex` lines 66–106,
1049–1067. No regularity away from the point of differentiation is assumed.
-/

public section

namespace AcExtensionPrinciple

/-- The two radius coefficients agree. Paper `e1a0fd5`, `eq:radius`, lines 70–73. -/
theorem radius_coefficient_eq (lam nu mu r : ℝ) :
    kappaOf lam mu * varkappaOf r mu * nu =
      lam * (gammaOf nu mu * varkappaOf r mu) := by
  unfold kappaOf gammaOf varkappaOf
  ring

/-- Normalize a scalar derivative. Paper `e1a0fd5`,
`eq:normalized-scalar-derivatives`, lines 94–99. -/
theorem normalized_scalar_eq {b : ℝ} (r phi q : ℝ) (hb : b ≠ 0) :
    (b * phi + r * q) / b = phi + (r / b) * q := by
  field_simp

variable {r b phi q : ℝ → ℝ} {x a p c : ℝ}

/-- Product form of the scalar transport equation. Paper `e1a0fd5`,
`eq:scalar-bound-first-derivative-transport` (also `eq:wave-phi`, lines 78–80). -/
theorem ray_scalar_product (hr : HasDerivAt r a x)
    (hq : HasDerivAt q (-(a / r x) * q x - (b x / r x) * p) x)
    (hr0 : r x ≠ 0) :
    HasDerivAt (fun s => r s * q s) (-b x * p) x := by
  convert hr.mul hq using 1
  field_simp
  ring

/-- Wave equation for the unnormalized scalar derivative. Paper `e1a0fd5`,
`eq:wave-psi`, lines 81–84. -/
theorem ray_wave_product (hr : HasDerivAt r a x) (hphi : HasDerivAt phi p x)
    (hb : HasDerivAt b (b x * c) x)
    (hq : HasDerivAt q (-(a / r x) * q x - (b x / r x) * p) x)
    (hr0 : r x ≠ 0) :
    HasDerivAt (fun s => b s * phi s + r s * q s) (b x * c * phi x) x := by
  convert (hb.mul hphi).add (ray_scalar_product hr hq hr0) using 1
  ring

/-- Damping form of normalized scalar transport. Paper `e1a0fd5`,
`eq:normalized-scalar-transport`, lines 100–104. -/
theorem ray_normalized_scalar (hr : HasDerivAt r a x) (hphi : HasDerivAt phi p x)
    (hb : HasDerivAt b (b x * c) x)
    (hq : HasDerivAt q (-(a / r x) * q x - (b x / r x) * p) x)
    (hr0 : r x ≠ 0) (hb0 : b x ≠ 0) :
    HasDerivAt (fun s => (b s * phi s + r s * q s) / b s)
      (-c * ((b x * phi x + r x * q x) / b x - phi x)) x := by
  convert (ray_wave_product hr hphi hb hq hr0).div hb hb0 using 1
  field_simp
  ring

/-- Transport of the radial scalar amplitude. Paper `e1a0fd5`,
`equations.tex` lines 1051–1052 and 1066–1067. -/
theorem ray_scalar_amplitude (hr : HasDerivAt r a x)
    (hb : HasDerivAt b (b x * c) x)
    (hq : HasDerivAt q (-(a / r x) * q x - (b x / r x) * p) x)
    (hr0 : r x ≠ 0) (hb0 : b x ≠ 0) :
    HasDerivAt (fun s => (r s / b s) * q s)
      (-p - c * (r x / b x) * q x) x := by
  have h := (ray_scalar_product hr hq hr0).fun_div hb hb0
  convert h using 1
  · funext s
    ring
  · field_simp

/-- Differentiate the mass ratio using the mass equation. Paper `e1a0fd5`,
`eq:mass`, lines 74–77; `equations.tex` lines 1049–1050 and 1062–1063. -/
theorem ray_massRatio {m : ℝ → ℝ} (hr : HasDerivAt r a x)
    (hm : HasDerivAt m (r x ^ 2 / (2 * gammaOf a (massRatio (r x) (m x))) * p ^ 2) x)
    (hr0 : r x ≠ 0) (ha : a ≠ 0) :
    HasDerivAt (fun s => massRatio (r s) (m s))
      (r x * (1 - massRatio (r x) (m x)) / a * p ^ 2 -
        massRatio (r x) (m x) * a / r x) x := by
  unfold massRatio gammaOf at *
  convert (hm.const_mul 2).div hr hr0 using 1
  field_simp

/-- Differentiate a normalized expansion before taking its logarithm. Paper `e1a0fd5`,
`eq:raychaudhuri`, lines 90–92. -/
theorem ray_normalized_expansion {mu : ℝ → ℝ}
    (hb : HasDerivAt b (b x * (a / (1 - mu x) * (mu x / r x))) x)
    (hmu : HasDerivAt mu
      (r x * (1 - mu x) / a * p ^ 2 - mu x * a / r x) x)
    (hr0 : r x ≠ 0) (ha : a ≠ 0) (hmu0 : 1 - mu x ≠ 0) :
    HasDerivAt (fun s => b s / (1 - mu s))
      ((b x / (1 - mu x)) * (r x / a * p ^ 2)) x := by
  convert hb.fun_div (hmu.const_sub 1) hmu0 using 1
  field_simp
  ring

end AcExtensionPrinciple

end
