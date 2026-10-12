module

public import AcExtensionPrinciple.Analysis.HardyPrimitive
public import AcExtensionPrinciple.BoundaryEnergy.Stability

/-!
# Radial Hardy estimate in terms of total variation

Internal helper for paper commit `e1a0fd5`, `equations.tex`
lines 1006–1015 (`eq:scalar-radial-hardy`). This combines the Hardy estimate
with the existing bound of the integral of the absolute derivative by variation.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The radial Hardy bound by total variation of an absolutely continuous
profile; paper `e1a0fd5`, `equations.tex` lines 1006–1015
(`eq:scalar-radial-hardy`). -/
theorem radial_hardy_le_eVariationOn {P : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hP : AbsolutelyContinuousOnInterval P 0 R) :
    (∫⁻ r in Ioc 0 R,
      ENNReal.ofReal (|P r - (1 / r) * (∫ s in 0..r, P s)| / r)) ≤
        eVariationOn P (Icc 0 R) := by
  have hBV : BoundedVariationOn P (Icc 0 R) := by
    simpa only [uIcc_of_le hR.le] using hP.boundedVariationOn
  calc
    _ ≤ ENNReal.ofReal (∫ s in 0..R, |deriv P s|) :=
      radial_hardy_le_integral_abs_deriv hR hP
    _ ≤ ENNReal.ofReal (eVariationOn P (Icc 0 R)).toReal :=
      ENNReal.ofReal_le_ofReal (integral_abs_deriv_le_variation hR.le hBV)
    _ = _ := ENNReal.ofReal_toReal hBV

end AcExtensionPrinciple

end
