module

public import AcExtensionPrinciple.Reduced.RayCalculusBasic

/-!
# Reduced equations along an incoming characteristic

Source: paper commit `e1a0fd5`, `equations.tex` lines 66–106,
416, 1049–1052. The parameter is `u`; all equations are assumed only at that point.
-/

public section

namespace AcExtensionPrinciple.IncomingRay

variable {r lam nu m phi phiU phiV : ℝ → ℝ} {u : ℝ}

local notation "μ" => (fun s => massRatio (r s) (m s))
local notation "κ" => (fun s => kappaOf (lam s) (μ s))
local notation "γ" => (fun s => gammaOf (nu s) (μ s))
local notation "ϰ" => (fun s => varkappaOf (r s) (μ s))

/-- Incoming logarithmic expansion. Paper `e1a0fd5`,
`eq:logarithmic-expansions` (first), lines 87–89. -/
theorem log_lam
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u) (hlam0 : 0 < lam u) :
    HasDerivAt (fun s => Real.log (lam s)) (γ u * ϰ u) u := by
  have h := (hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))).log
    (ne_of_gt hlam0)
  convert h using 1
  field_simp

/-- Derivative of the incoming mass ratio. Paper `e1a0fd5`,
`eq:mass`, lines 74–77, and `equations.tex` lines 1049–1050. -/
theorem mass_ratio (hr : HasDerivAt r (nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hr0 : 0 < r u) (hnu0 : nu u < 0) :
    HasDerivAt μ
      (r u * (1 - μ u) / nu u * phiU u ^ 2 - μ u * nu u / r u) u :=
  ray_massRatio hr hm (ne_of_gt hr0) (ne_of_lt hnu0)

/-- Incoming logarithmic mass factor. Paper `e1a0fd5`, `equations.tex` lines 1049–1050. -/
theorem log_one_sub_mass_ratio (hr : HasDerivAt r (nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hr0 : 0 < r u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => Real.log (1 - μ s))
      (r u / (-nu u) * phiU u ^ 2 + γ u * ϰ u) u := by
  have h := ((mass_ratio hr hm hr0 hnu0).const_sub 1).log (ne_of_gt (sub_pos.mpr hmu))
  convert h using 1
  unfold gammaOf varkappaOf
  field_simp [ne_of_gt hr0, ne_of_lt hnu0, ne_of_gt (sub_pos.mpr hmu)]
  ring

/-- Incoming Raychaudhuri equation. Paper `e1a0fd5`,
`eq:raychaudhuri` (first), lines 90–92. -/
theorem log_kappa (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => Real.log (kappaOf (lam s) (μ s)))
      (-(r u / (-nu u)) * phiU u ^ 2) u := by
  have hmu0 : 1 - μ u ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  have hb := hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))
  have hk := ray_normalized_expansion hb (mass_ratio hr hm hr0 hnu0)
    (ne_of_gt hr0) (ne_of_lt hnu0) hmu0
  have h := hk.log (div_ne_zero (ne_of_gt hlam0) hmu0)
  change HasDerivAt (fun s => Real.log (lam s / (1 - μ s))) _ u
  convert h using 1
  field_simp

/-- Algebraic normalized outgoing scalar derivative on an incoming ray. Paper `e1a0fd5`,
`eq:normalized-scalar-derivatives` (first), lines 94–99. -/
theorem normalized_scalar (hlam0 : lam u ≠ 0) :
    (lam u * phi u + r u * phiV u) / lam u = phi u + (r u / lam u) * phiV u :=
  normalized_scalar_eq (r u) (phi u) (phiV u) hlam0

/-- Incoming transport of the first outgoing scalar derivative. Paper `e1a0fd5`,
`eq:scalar-bound-first-derivative-transport` (second). -/
theorem scalar_product (hr : HasDerivAt r (nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) :
    HasDerivAt (fun s => r s * phiV s) (-lam u * phiU u) u :=
  ray_scalar_product hr hphiV (ne_of_gt hr0)

/-- Incoming wave equation for `∂ᵥψ`, in the mass form. Paper `e1a0fd5`,
`eq:wave-psi`, lines 81–84. -/
theorem wave_psi (hr : HasDerivAt r (nu u) u) (hphi : HasDerivAt phi (phiU u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) :
    HasDerivAt (fun s => lam s * phi s + r s * phiV s)
      (κ u * ϰ u * nu u / r u * (r u * phi u)) u := by
  have hb := hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))
  have h := ray_wave_product hr hphi hb hphiV (ne_of_gt hr0)
  convert h using 1
  rw [radius_coefficient_eq]
  field_simp

/-- Incoming wave equation for `∂ᵥψ`, in the expansion form. Paper `e1a0fd5`,
`eq:wave-psi`, lines 81–84. -/
theorem wave_psi_expansion (hr : HasDerivAt r (nu u) u)
    (hphi : HasDerivAt phi (phiU u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) :
    HasDerivAt (fun s => lam s * phi s + r s * phiV s)
      (lam u * ϰ u * γ u / r u * (r u * phi u)) u := by
  convert wave_psi hr hphi hlam hphiV hr0 using 1
  rw [radius_coefficient_eq]
  ring

/-- Incoming linear damping equation for the normalized scalar derivative. Paper `e1a0fd5`,
`eq:scalar-bound-linear-transport`, line 416. -/
theorem normalized_scalar_damping (hr : HasDerivAt r (nu u) u)
    (hphi : HasDerivAt phi (phiU u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) :
    HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (-(γ u * ϰ u) * ((lam u * phi u + r u * phiV u) / lam u - phi u)) u := by
  have hb := hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))
  exact ray_normalized_scalar hr hphi hb hphiV (ne_of_gt hr0) (ne_of_gt hlam0)

/-- Incoming normalized scalar transport. Paper `e1a0fd5`,
`eq:normalized-scalar-transport` (first), lines 100–104. -/
theorem normalized_scalar_transport (hr : HasDerivAt r (nu u) u)
    (hphi : HasDerivAt phi (phiU u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) :
    HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (-(μ u * γ u / lam u) * phiV u) u := by
  have h := normalized_scalar_damping hr hphi hlam hphiV hr0 hlam0
  convert h using 1
  rw [normalized_scalar (ne_of_gt hlam0)]
  unfold varkappaOf
  field_simp
  ring

/-- Incoming transport of `r ∂ᵥφ / λ`. Paper `e1a0fd5`, `equations.tex` lines 1051–1052. -/
theorem scalar_amplitude (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) :
    HasDerivAt (fun s => (r s / lam s) * phiV s)
      (-phiU u - γ u * ϰ u * (r u / lam u) * phiV u) u := by
  have hb := hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))
  exact ray_scalar_amplitude hr hb hphiV (ne_of_gt hr0) (ne_of_gt hlam0)

end AcExtensionPrinciple.IncomingRay

end
