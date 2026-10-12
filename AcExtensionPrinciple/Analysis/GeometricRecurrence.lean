module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Iterating an affine contraction

Internal helper for paper commit `e1a0fd5`, `equations.tex`
line 896 (`eq:iterated-boundary-decay`).
-/

public section

namespace AcExtensionPrinciple

/-- Iterated affine contraction without a sign condition on `x`; paper `e1a0fd5`,
`equations.tex` line 896 (`eq:iterated-boundary-decay`). -/
theorem affine_recurrence_le {x : ℕ → ℝ} {rho c : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hc : 0 ≤ c)
    (hx : ∀ k, x (k + 1) ≤ rho * x k + c) (k : ℕ) :
    x k ≤ rho ^ k * x 0 + c / (1 - rho) := by
  have hd : 0 < 1 - rho := sub_pos.mpr hrho1
  have hfix : rho * (c / (1 - rho)) + c = c / (1 - rho) := by
    field_simp
    ring
  induction k with
  | zero => simpa using (le_add_of_nonneg_right (div_nonneg hc hd.le) :
      x 0 ≤ x 0 + c / (1 - rho))
  | succ k ih =>
    calc
      x (k + 1) ≤ rho * x k + c := hx k
      _ ≤ rho * (rho ^ k * x 0 + c / (1 - rho)) + c := by gcongr
      _ = rho ^ (k + 1) * x 0 + c / (1 - rho) := by
        rw [mul_add, add_assoc, hfix, pow_succ]
        ring

end AcExtensionPrinciple

end
