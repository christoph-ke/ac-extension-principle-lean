module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# Weighted Cauchy–Schwarz on a proper cone

Helpers for paper commit `e1a0fd5`, `equations.tex` lines 1346–1350.
The lintegral formulation also covers infinite integrals.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Squared Cauchy–Schwarz for nonnegative integrands; paper `e1a0fd5`,
`equations.tex` lines 1346–1350. -/
theorem lintegral_sqrt_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) :
    (∫⁻ x, F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) ∂μ) ^ 2 ≤
      (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
  have h := ENNReal.lintegral_mul_norm_pow_le hF hG
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  have hsq := pow_le_pow_left' h 2
  simpa only [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, ENNReal.rpow_one] using hsq

/-- Weighted Cauchy–Schwarz, without finiteness restrictions; paper `e1a0fd5`,
`equations.tex` lines 1346–1350 (`prop:small-outgoing-bv-cones`). -/
theorem weighted_lintegral_cauchySchwarz {ω j : ℝ → ℝ} {u : ℝ}
    (hω : Measurable ω) (hj : Measurable j)
    (hpos : ∀ v ∈ Ioc u 0, 0 < ω v) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal |j v|) ^ 2 ≤
      (∫⁻ v in Ioc u 0, ENNReal.ofReal (1 / ω v)) *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j v| ^ 2) := by
  have hF : Measurable (fun v ↦ ENNReal.ofReal (1 / ω v)) :=
    (measurable_const.div hω).ennreal_ofReal
  have hG : Measurable (fun v ↦ ENNReal.ofReal (ω v * |j v| ^ 2)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using
      (hω.mul (hj.norm.pow_const 2)).ennreal_ofReal
  have h := lintegral_sqrt_mul_sq_le (μ := volume.restrict (Ioc u 0))
    hF.aemeasurable hG.aemeasurable
  convert h using 2
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro v hv
  change ENNReal.ofReal |j v| =
    ENNReal.ofReal (1 / ω v) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (ω v * |j v| ^ 2) ^ (1 / 2 : ℝ)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.ofReal_mul (one_div_nonneg.mpr (hpos v hv).le)]
  have heq : 1 / ω v * (ω v * |j v| ^ 2) = |j v| ^ 2 := by
    field_simp [(hpos v hv).ne']
  rw [heq, ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- A lower bound on the weight gives the cone-length version of
Cauchy–Schwarz; paper `e1a0fd5`, `equations.tex` lines 1346–1350. -/
theorem weighted_lintegral_cone_length_bound {ω j : ℝ → ℝ} {u c : ℝ}
    (_hu : u < 0) (hc : 0 < c) (hω : Measurable ω) (hj : Measurable j)
    (hlower : ∀ v ∈ Ioc u 0, c ≤ ω v) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal |j v|) ^ 2 ≤
      ENNReal.ofReal ((-u) / c) *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j v| ^ 2) := by
  apply (weighted_lintegral_cauchySchwarz hω hj
    (fun v hv ↦ hc.trans_le (hlower v hv))).trans
  apply mul_le_mul ?_ le_rfl zero_le zero_le
  calc
    _ ≤ ∫⁻ _v in Ioc u 0, ENNReal.ofReal (1 / c) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro v hv
      apply ENNReal.ofReal_le_ofReal
      exact one_div_le_one_div_of_le hc (hlower v hv)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, zero_sub,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end AcExtensionPrinciple

end
