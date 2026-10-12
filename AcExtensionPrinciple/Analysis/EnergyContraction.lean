module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Absorbing the work term in the energy balance

Internal helper for paper commit `e1a0fd5`, `equations.tex`
lines 771–787 (`eq:contraction-from-dissipation`).
-/

public section

namespace AcExtensionPrinciple

/-- Young's inequality with an explicit constant, used in paper `e1a0fd5`,
`equations.tex` lines 771–787 (`eq:contraction-from-dissipation`). -/
theorem sqrt_work_le {b E V sigma : ℝ} (hb : 0 < b) (hE : 0 ≤ E)
    (_hV : 0 ≤ V) (hsigma : 0 < sigma) :
    Real.sqrt (2 * b * E) * V ≤ sigma / 4 * E + 2 / sigma * b * V ^ 2 := by
  have hroot : Real.sqrt (2 * b * E) = Real.sqrt (2 * b) * Real.sqrt E :=
    Real.sqrt_mul (by positivity) E
  have hsE := Real.sq_sqrt hE
  have hsb := Real.sq_sqrt (show 0 ≤ 2 * b by positivity)
  have hsq := sq_nonneg (sigma * Real.sqrt E - 2 * Real.sqrt (2 * b) * V)
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * sigma by positivity)).mp
  have heq : (4 * sigma) * (sigma / 4 * E + 2 / sigma * b * V ^ 2) =
      sigma ^ 2 * E + 8 * b * V ^ 2 := by field_simp; ring
  rw [heq, hroot]
  nlinarith

/-- Energy contraction with `C = 1 + H/2 + 2/σ`; paper `e1a0fd5`,
`equations.tex` lines 771–787 (`eq:contraction-from-dissipation`). -/
theorem energy_contraction_of_dissipation {E0 E1 Dis W V b H sigma : ℝ}
    (hb : 0 < b) (_hH : 0 < H) (hsigma : 0 < sigma) (_hsigma1 : sigma ≤ 1)
    (hE0 : 0 ≤ E0) (hV : 0 ≤ V) (hbalance : E1 - E0 + Dis = W)
    (hdiss : sigma / 2 * E0 - H * b / 2 * V ^ 2 ≤ Dis)
    (hwork : W ≤ Real.sqrt (2 * b * E0) * V + b * V ^ 2) :
    E1 ≤ (1 - sigma / 4) * E0 + (1 + H / 2 + 2 / sigma) * b * V ^ 2 := by
  have hy := sqrt_work_le hb hE0 hV hsigma
  nlinarith

end AcExtensionPrinciple

end
