module

public import AcExtensionPrinciple.Reduced.RayCalculusBasic

/-!
# Reduced equations along an outgoing characteristic

Source: paper commit `e1a0fd5`, `equations.tex` lines 66–106,
648, 976, 1063–1067. The parameter is `v`; all equations are assumed only at that point.
-/

public section

namespace AcExtensionPrinciple.OutgoingRay

variable {r lam nu m phi phiU phiV : ℝ → ℝ} {v : ℝ}

local notation "μ" => (fun s => massRatio (r s) (m s))
local notation "κ" => (fun s => kappaOf (lam s) (μ s))
local notation "γ" => (fun s => gammaOf (nu s) (μ s))
local notation "ϰ" => (fun s => varkappaOf (r s) (μ s))

/-- Outgoing logarithmic expansion. Paper `e1a0fd5`,
`eq:logarithmic-expansions` (second), lines 87–89. -/
theorem log_neg_nu
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v) (hnu0 : nu v < 0) :
    HasDerivAt (fun s => Real.log (-nu s)) (κ v * ϰ v) v := by
  have h := hnu.neg.log (neg_ne_zero.mpr (ne_of_lt hnu0))
  convert h using 1
  simp only [Pi.neg_apply]
  field_simp [ne_of_lt hnu0]

/-- Outgoing mass-ratio derivative in its direct quotient form. Paper `e1a0fd5`,
`eq:mass`, lines 74–77, and `equations.tex` lines 1062–1063. -/
theorem mass_ratio (hr : HasDerivAt r (lam v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hr0 : 0 < r v) (hlam0 : 0 < lam v) :
    HasDerivAt μ
      (r v * (1 - μ v) / lam v * phiV v ^ 2 - μ v * lam v / r v) v :=
  ray_massRatio hr hm (ne_of_gt hr0) (ne_of_gt hlam0)

/-- Outgoing Raychaudhuri equation. Paper `e1a0fd5`,
`eq:raychaudhuri` (second), lines 90–92. -/
theorem log_neg_gamma (hr : HasDerivAt r (lam v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hr0 : 0 < r v) (hlam0 : 0 < lam v) (hnu0 : nu v < 0) (hmu : μ v < 1) :
    HasDerivAt (fun s => Real.log (-gammaOf (nu s) (μ s)))
      (r v / lam v * phiV v ^ 2) v := by
  have hmu0 : 1 - μ v ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  have hb : HasDerivAt nu (nu v * (lam v / (1 - μ v) * (μ v / r v))) v := by
    convert hnu using 1
    unfold kappaOf varkappaOf
    ring
  have hg := ray_normalized_expansion hb (mass_ratio hr hm hr0 hlam0)
    (ne_of_gt hr0) (ne_of_gt hlam0) hmu0
  have h := hg.neg.log (neg_ne_zero.mpr (div_ne_zero (ne_of_lt hnu0) hmu0))
  change HasDerivAt (fun s => Real.log (-(nu s / (1 - μ s)))) _ v
  convert h using 1
  simp only [Pi.neg_apply]
  field_simp [ne_of_lt hnu0]

/-- Algebraic normalized incoming scalar derivative on an outgoing ray. Paper `e1a0fd5`,
`eq:normalized-scalar-derivatives` (second), lines 94–99. -/
theorem normalized_scalar (hnu0 : nu v ≠ 0) :
    (nu v * phi v + r v * phiU v) / nu v = phi v + (r v / nu v) * phiU v :=
  normalized_scalar_eq (r v) (phi v) (phiU v) hnu0

/-- Outgoing transport of the first incoming scalar derivative. Paper `e1a0fd5`,
`eq:scalar-bound-first-derivative-transport` (first). -/
theorem scalar_product (hr : HasDerivAt r (lam v) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hr0 : 0 < r v) :
    HasDerivAt (fun s => r s * phiU s) (-nu v * phiV v) v := by
  have hq : HasDerivAt phiU (-(lam v / r v) * phiU v - (nu v / r v) * phiV v) v := by
    convert hphiU using 1
    ring
  exact ray_scalar_product hr hq (ne_of_gt hr0)

/-- Outgoing linear damping of the normalized scalar derivative. Paper `e1a0fd5`,
`eq:incoming-normalized-damping`, line 976. -/
theorem normalized_scalar_damping (hr : HasDerivAt r (lam v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hr0 : 0 < r v) (hnu0 : nu v < 0) :
    HasDerivAt (fun s => (nu s * phi s + r s * phiU s) / nu s)
      (-(κ v * ϰ v) * ((nu v * phi v + r v * phiU v) / nu v - phi v)) v := by
  have hb : HasDerivAt nu (nu v * (κ v * ϰ v)) v := by
    convert hnu using 1
    ring
  have hq : HasDerivAt phiU (-(lam v / r v) * phiU v - (nu v / r v) * phiV v) v := by
    convert hphiU using 1
    ring
  exact ray_normalized_scalar hr hphi hb hq (ne_of_gt hr0) (ne_of_lt hnu0)

/-- Outgoing normalized scalar transport. Paper `e1a0fd5`,
`eq:normalized-scalar-transport` (second), lines 100–104. -/
theorem normalized_scalar_transport (hr : HasDerivAt r (lam v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hr0 : 0 < r v) (hnu0 : nu v < 0) :
    HasDerivAt (fun s => (nu s * phi s + r s * phiU s) / nu s)
      (-(μ v * κ v / nu v) * phiU v) v := by
  have h := normalized_scalar_damping hr hphi hnu hphiU hr0 hnu0
  convert h using 1
  rw [normalized_scalar (ne_of_lt hnu0)]
  unfold varkappaOf
  field_simp
  ring

/-- Outgoing transport of `r ∂ᵤφ / ν`. Paper `e1a0fd5`, `equations.tex` lines 1066–1067. -/
theorem scalar_amplitude (hr : HasDerivAt r (lam v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hr0 : 0 < r v) (hnu0 : nu v < 0) :
    HasDerivAt (fun s => (r s / nu s) * phiU s)
      (-phiV v - κ v * ϰ v * (r v / nu v) * phiU v) v := by
  have hb : HasDerivAt nu (nu v * (κ v * ϰ v)) v := by
    convert hnu using 1
    ring
  have hq : HasDerivAt phiU (-(lam v / r v) * phiU v - (nu v / r v) * phiV v) v := by
    convert hphiU using 1
    ring
  exact ray_scalar_amplitude hr hb hq (ne_of_gt hr0) (ne_of_lt hnu0)

/-- The radial mass equation in terms of the radial scalar amplitude. Paper `e1a0fd5`,
`eq:radial-mass`, line 648. -/
theorem radial_mass
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hlam0 : 0 < lam v) :
    HasDerivAt m ((1 - μ v) / 2 * ((r v / lam v) * phiV v) ^ 2 * lam v) v := by
  convert hm using 1
  unfold kappaOf
  field_simp

/-- The radial mass-ratio equation in terms of the radial scalar amplitude. Paper `e1a0fd5`,
`equations.tex` lines 1062–1063. -/
theorem radial_mass_ratio (hr : HasDerivAt r (lam v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hr0 : 0 < r v) (hlam0 : 0 < lam v) :
    HasDerivAt μ
      (lam v / r v * ((1 - μ v) * ((r v / lam v) * phiV v) ^ 2 - μ v)) v := by
  convert mass_ratio hr hm hr0 hlam0 using 1
  field_simp

end AcExtensionPrinciple.OutgoingRay

end
