module

public import AcExtensionPrinciple.Reduced.IncomingRay
public import AcExtensionPrinciple.Renormalized.OutgoingIdentities

/-!
# Renormalized identities along incoming rays

Paper commit `e1a0fd5`, `equations.tex` lines 1030, 1094,
1243–1248 and 1262. The reduced equations are assumed at one point on an
incoming ray. The differentiated datum transport is supplied as the content
of `eq:radial-datum-transport` (line 564), rather than reproved here.
-/

public section

namespace AcExtensionPrinciple.Renormalized.Incoming

open Filter Topology

variable {r lam nu m phiU phiV q J : ℝ → ℝ} {u : ℝ}

local notation "μ" => (fun s => massRatio (r s) (m s))
local notation "κ" => (fun s => kappaOf (lam s) (μ s))
local notation "γ" => (fun s => gammaOf (nu s) (μ s))
local notation "ϰ" => (fun s => varkappaOf (r s) (μ s))
local notation "A" => (fun s => r s / lam s * phiV s)
local notation "B" => (fun s => r s / nu s * phiU s)
local notation "𝒞" => (fun s => interactionOf (r s) (lam s) (nu s) (m s) (phiU s) (phiV s))
local notation "j" => (fun s => renormalizedDerivativeOf (r s) (lam s) (m s) (phiV s) (q s))
local notation "w" => (fun s => r s / ((1 - μ s) ^ 2 * lam s))

/-- The cubic correction cancels the cubic incoming source. Paper `e1a0fd5`,
`eq:renormalized-incoming-transport`, line 1030, using
`eq:radial-datum-transport`, line 564. -/
theorem renormalized_transport (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hphiV : HasDerivAt phiV (-(nu u / r u) * phiV u - (lam u / r u) * phiU u) u)
    (hq : HasDerivAt q (-2 * γ u * ϰ u * q u -
      (γ u / r u ^ 2) * A u * (A u ^ 2 - 3 * μ u)) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt j ((r u / (-nu u)) * phiU u ^ 2 * j u +
      (3 * nu u / r u) * phiV u * 𝒞 u) u := by
  have hmu' := IncomingRay.mass_ratio hr hm hr0 hnu0
  have hA := IncomingRay.scalar_amplitude hr hlam hphiV hr0 hlam0
  have hcubic := (hA.pow 3).div hr (ne_of_gt hr0)
  convert (((hmu'.const_sub 1).mul hlam).mul (hq.sub hcubic)) using 1
  · funext s
    rfl
  · dsimp [renormalizedDerivativeOf, interactionOf, gammaOf, kappaOf, varkappaOf]
    field_simp [ne_of_gt hr0, ne_of_gt hlam0, ne_of_lt hnu0,
      ne_of_gt (sub_pos.mpr hmu)]
    ring

/-- Logarithmic derivative of the incoming energy weight. Paper `e1a0fd5`,
`equations.tex` line 1243, proof of `eq:renormalized-energy-identity`. -/
theorem log_energy_weight (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => Real.log (w s))
      ((-nu u / r u) * (-1 - 2 * B u ^ 2 + 3 * μ u / (1 - μ u))) u := by
  have hmu' := IncomingRay.mass_ratio hr hm hr0 hnu0
  have hlogmu := IncomingRay.log_one_sub_mass_ratio hr hm hr0 hnu0 hmu
  have hloglam := IncomingRay.log_lam hlam hlam0
  have h := ((hr.log (ne_of_gt hr0)).sub (hlogmu.const_mul 2)).sub hloglam
  have heq : (fun s => Real.log (w s)) =ᶠ[𝓝 u]
      (fun s => Real.log (r s) - 2 * Real.log (1 - μ s) - Real.log (lam s)) := by
    filter_upwards [hr.continuousAt.eventually_ne (ne_of_gt hr0),
      (hmu'.const_sub 1).continuousAt.eventually_ne (ne_of_gt (sub_pos.mpr hmu)),
      hlam.continuousAt.eventually_ne (ne_of_gt hlam0)] with s hrs hms hls
    rw [Real.log_div hrs (mul_ne_zero (pow_ne_zero 2 hms) hls),
      Real.log_mul (pow_ne_zero 2 hms) hls, Real.log_pow]
    ring
  convert h.congr_of_eventuallyEq heq using 1
  dsimp [gammaOf, varkappaOf]
  field_simp [ne_of_gt hr0, ne_of_lt hnu0, ne_of_gt (sub_pos.mpr hmu)]
  ring

/-- Ordinary derivative of the incoming energy weight. Paper `e1a0fd5`,
`equations.tex` line 1243. This is the multiplicative form of its log derivative. -/
theorem energy_weight_derivative (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt w (w u * ((-nu u / r u) *
      (-1 - 2 * B u ^ 2 + 3 * μ u / (1 - μ u)))) u := by
  have hmu' := IncomingRay.mass_ratio hr hm hr0 hnu0
  have hw := hr.div (((hmu'.const_sub 1).pow 2).mul hlam)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hmu))) (ne_of_gt hlam0))
  have hw0 : w u ≠ 0 := div_ne_zero (ne_of_gt hr0)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hmu))) (ne_of_gt hlam0))
  have he := (hw.log hw0).unique (log_energy_weight hr hlam hm hr0 hlam0 hnu0 hmu)
  apply hw.congr_deriv
  exact (div_eq_iff hw0).mp he |>.trans (mul_comm _ _)

/-- Energy identity for an arbitrary frozen source. Paper `e1a0fd5`,
`eq:frozen-linear-transport`, line 1262, and
`eq:renormalized-energy-identity`, line 1248. -/
theorem frozen_energy_identity {F : ℝ → ℝ} (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hJ : HasDerivAt J ((r u / (-nu u)) * phiU u ^ 2 * J u +
      3 * nu u * phiV u * F u) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => r s * J s ^ 2 / ((1 - μ s) ^ 2 * lam s))
      (-(-nu u) / ((1 - μ u) ^ 2 * lam u) *
        (1 - 3 * μ u / (1 - μ u)) * J u ^ 2 +
        (6 * nu u / (1 - μ u) ^ 2) * A u * F u * J u) u := by
  have hw := energy_weight_derivative hr hlam hm hr0 hlam0 hnu0 hmu
  convert hw.mul (hJ.pow 2) using 1
  · funext s
    dsimp
    ring
  · dsimp
    field_simp [ne_of_gt hr0, ne_of_gt hlam0, ne_of_lt hnu0,
      ne_of_gt (sub_pos.mpr hmu)]
    ring

/-- Energy identity for any solution of the renormalized remainder equation.
Paper `e1a0fd5`, `eq:renormalized-energy-identity`, line 1248, and
`eq:renormalized-remainder-transport`, line 1104. -/
theorem renormalized_energy_identity (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hJ : HasDerivAt J ((r u / (-nu u)) * phiU u ^ 2 * J u +
      (3 * nu u / r u) * phiV u * 𝒞 u) u)
    (hr0 : 0 < r u) (hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => r s * J s ^ 2 / ((1 - μ s) ^ 2 * lam s))
      (-(-nu u) / ((1 - μ u) ^ 2 * lam u) *
        (1 - 3 * μ u / (1 - μ u)) * J u ^ 2 +
        (6 * nu u / (1 - μ u) ^ 2) * A u * (𝒞 u / r u) * J u) u := by
  have hJ' : HasDerivAt J ((r u / (-nu u)) * phiU u ^ 2 * J u +
      3 * nu u * phiV u * (𝒞 u / r u)) u := by
    convert hJ using 1
    ring
  exact frozen_energy_identity (F := fun s => 𝒞 s / r s)
    hr hlam hm hJ' hr0 hlam0 hnu0 hmu

/-- The integrating factor `κ J` is constant to first order for the homogeneous
incoming equation. Paper `e1a0fd5`, `equations.tex` line 1094 and
`eq:renormalized-initial-transport`, line 1086. -/
theorem homogeneous_integrating_factor (hr : HasDerivAt r (nu u) u)
    (hlam : HasDerivAt lam (κ u * ϰ u * nu u) u)
    (hm : HasDerivAt m (r u ^ 2 / (2 * γ u) * phiU u ^ 2) u)
    (hJ : HasDerivAt J ((r u / (-nu u)) * phiU u ^ 2 * J u) u)
    (hr0 : 0 < r u) (_hlam0 : 0 < lam u) (hnu0 : nu u < 0) (hmu : μ u < 1) :
    HasDerivAt (fun s => κ s * J s) 0 u := by
  have hb := hlam.congr_deriv (radius_coefficient_eq (lam u) (nu u) (μ u) (r u))
  have hk := ray_normalized_expansion hb (IncomingRay.mass_ratio hr hm hr0 hnu0)
    (ne_of_gt hr0) (ne_of_lt hnu0) (ne_of_gt (sub_pos.mpr hmu))
  convert hk.mul hJ using 1
  · funext s
    rfl
  · field_simp [ne_of_lt hnu0]
    ring

end AcExtensionPrinciple.Renormalized.Incoming

end
