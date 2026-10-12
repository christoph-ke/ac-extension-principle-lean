module

public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-energy cone estimates

Real-integral consequences of weighted Cauchy–Schwarz;
paper commit `e1a0fd5`, `equations.tex` lines 1346–1350.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Weighted Cauchy–Schwarz for finite real integrals; paper `e1a0fd5`,
`equations.tex` lines 1346–1350 (`prop:small-outgoing-bv-cones`). -/
theorem weighted_integral_cauchySchwarz {ω j : ℝ → ℝ} {u : ℝ}
    (hω : Measurable ω) (hj : Measurable j)
    (hpos : ∀ v ∈ Ioc u 0, 0 < ω v)
    (hJ : IntegrableOn (fun v ↦ |j v|) (Ioc u 0))
    (hInv : IntegrableOn (fun v ↦ 1 / ω v) (Ioc u 0))
    (hEnergy : IntegrableOn (fun v ↦ ω v * |j v| ^ 2) (Ioc u 0)) :
    (∫ v in Ioc u 0, |j v|) ^ 2 ≤
      (∫ v in Ioc u 0, 1 / ω v) * ∫ v in Ioc u 0, ω v * |j v| ^ 2 := by
  have h := weighted_lintegral_cauchySchwarz hω hj hpos
  have hInvpos : 0 ≤ᵐ[volume.restrict (Ioc u 0)] (fun v ↦ 1 / ω v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (one_div_pos.mpr (hpos v hv)).le
  have hEpos : 0 ≤ᵐ[volume.restrict (Ioc u 0)] (fun v ↦ ω v * |j v| ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (hpos v hv).le (sq_nonneg _)
  have hJpos : 0 ≤ ∫ v in Ioc u 0, |j v| := integral_nonneg (fun v ↦ abs_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hJ (ae_of_all _ (fun v ↦ abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hInv hInvpos,
    ← ofReal_integral_eq_lintegral_ofReal hEnergy hEpos,
    ← ENNReal.ofReal_pow hJpos,
    ← ENNReal.ofReal_mul (integral_nonneg_of_ae hInvpos)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (integral_nonneg_of_ae hInvpos) (integral_nonneg_of_ae hEpos))).mp h

/-- A uniformly positive weight controls the normalized cone L¹ integral;
paper `e1a0fd5`, `equations.tex` lines 1346–1350. -/
theorem weighted_integral_cone_length_bound {ω j : ℝ → ℝ} {u c : ℝ}
    (hu : u < 0) (hc : 0 < c) (hω : Measurable ω) (hj : Measurable j)
    (hlower : ∀ v ∈ Ioc u 0, c ≤ ω v)
    (hJ : IntegrableOn (fun v ↦ |j v|) (Ioc u 0))
    (hEnergy : IntegrableOn (fun v ↦ ω v * |j v| ^ 2) (Ioc u 0)) :
    (∫ v in u..0, |j v|) ^ 2 / (-u) ≤
      c⁻¹ * ∫ v in u..0, ω v * |j v| ^ 2 := by
  have h := weighted_lintegral_cone_length_bound hu hc hω hj hlower
  have hEpos : 0 ≤ᵐ[volume.restrict (Ioc u 0)] (fun v ↦ ω v * |j v| ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (hc.le.trans (hlower v hv)) (sq_nonneg _)
  have hJpos : 0 ≤ ∫ v in Ioc u 0, |j v| := integral_nonneg (fun v ↦ abs_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hJ (ae_of_all _ (fun v ↦ abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hEnergy hEpos,
    ← ENNReal.ofReal_pow hJpos,
    ← ENNReal.ofReal_mul (div_nonneg (neg_pos.mpr hu).le hc.le)] at h
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (div_nonneg (neg_pos.mpr hu).le hc.le) (integral_nonneg_of_ae hEpos))).mp h
  rw [intervalIntegral.integral_of_le hu.le, intervalIntegral.integral_of_le hu.le]
  apply (div_le_iff₀ (neg_pos.mpr hu)).mpr
  convert hreal using 1
  ring

end AcExtensionPrinciple

end
