module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-!
# Radial expansion comparison

One-cone helper for paper commit `e1a0fd5`, `equations.tex`
lines 1130–1141 (`eq:late-radial-expansion-comparison`).
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

/-- An a.e. bound for the logarithmic derivative gives the radial weight
comparison; paper `e1a0fd5`, `equations.tex` lines 1130–1141
(`eq:late-radial-expansion-comparison`). -/
theorem radial_weight_comparison_of_log_deriv {w : ℝ → ℝ} {y x δ : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hwy : 0 < w y) (hwx : 0 < w x)
    (hAC : AbsolutelyContinuousOnInterval (fun r ↦ Real.log (w r)) y x)
    (hd : ∀ᵐ r ∂volume, r ∈ Icc y x →
      0 ≤ deriv (fun t ↦ Real.log (w t)) r ∧
        deriv (fun t ↦ Real.log (w t)) r ≤ δ / r) :
    w y ≤ w x ∧ w x ≤ w y * (x / y) ^ δ := by
  have hx : 0 < x := hy.trans_le hyx
  have hi : IntervalIntegrable (fun r ↦ δ / r) volume y x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro r hr
    rw [uIcc_of_le hyx] at hr
    exact (hy.trans_le hr.1).ne'
  have hlow : 0 ≤ Real.log (w x) - Real.log (w y) := by
    rw [← hAC.integral_deriv_eq_sub]
    apply intervalIntegral.integral_nonneg_of_ae_restrict hyx
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc]
      with r hrd hr
    exact (hrd hr).1
  have hupp : Real.log (w x) - Real.log (w y) ≤ δ * Real.log (x / y) := by
    rw [← hAC.integral_deriv_eq_sub]
    calc
      _ ≤ ∫ r in y..x, δ / r :=
        intervalIntegral.integral_mono_ae_restrict hyx hAC.intervalIntegrable_deriv hi (by
          filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc]
            with r hrd hr
          exact (hrd hr).2)
      _ = _ := by
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hy hx]
        simp [div_eq_mul_inv]
  constructor
  · exact (Real.log_le_log_iff hwy hwx).mp (by linarith)
  · have he := Real.exp_le_exp.mpr hupp
    rw [Real.exp_sub, Real.exp_log hwx, Real.exp_log hwy,
      mul_comm δ, ← Real.rpow_def_of_pos (div_pos hx hy)] at he
    simpa [mul_comm] using (div_le_iff₀ hwy).mp he

end AcExtensionPrinciple

end
