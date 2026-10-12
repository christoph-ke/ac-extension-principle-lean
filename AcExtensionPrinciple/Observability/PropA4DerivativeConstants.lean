module

public import AcExtensionPrinciple.Observability.PropA4Exterior

/-!
# Absorbing the smaller exterior derivative error

Paper `e1a0fd5`, lines 1797–1819. The exterior cutoff gives `P/r ≤ 1/32`,
so the `P²r^(-5/2)` remainder contribution has the required `Pr^(-3/2)` scale.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- Absorb the smaller radial tail using exactly the printed cutoff.
Paper `e1a0fd5`, lines 1797–1819. -/
theorem exterior_derivative_tail_absorb {P r : ℝ} (hP : 0 ≤ P) (hr : 0 < r)
    (hcut : 32 * P ≤ r) :
    P ^ 2 * r ^ (-(5 / 2) : ℝ) ≤ (P / 32) * r ^ (-(3 / 2) : ℝ) := by
  have he : r ^ (-(5 / 2) : ℝ) = r ^ (-(3 / 2) : ℝ) / r := by
    calc
      _ = r ^ ((-(3 / 2) : ℝ) + (-1)) := by congr 1; norm_num
      _ = r ^ (-(3 / 2) : ℝ) * r ^ (-1 : ℝ) := Real.rpow_add hr _ _
      _ = _ := by rw [Real.rpow_neg_one]; exact (div_eq_mul_inv _ _).symm
  have hratio : P / r ≤ 1 / 32 := by
    apply (div_le_iff₀ hr).mpr
    linarith only [hcut]
  calc
    _ = (P * (P / r)) * r ^ (-(3 / 2) : ℝ) := by rw [he]; ring
    _ ≤ (P * (1 / 32)) * r ^ (-(3 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hP)
        (Real.rpow_nonneg hr.le _)
    _ = _ := by ring

/-- The explicit coefficient in the remainder bound, depending only on K.
Paper `e1a0fd5`, lines 1770–1779 and 1813–1819. -/
@[expose] noncomputable def exteriorErrorCoefficient (K : ℝ) : ℝ :=
  (32 / 3) * Real.sqrt K + 4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K))

/-- Factoring out the common `√E` makes the solution-independent constant
explicit. Paper `e1a0fd5`, lines 1770–1779 and 1813–1819. -/
theorem exteriorErrorCoefficient_factor {K E : ℝ} (hK : 0 ≤ K) :
    (32 / 3) * Real.sqrt (K * E) +
      4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * E) =
        exteriorErrorCoefficient K * Real.sqrt E := by
  rw [Real.sqrt_mul hK, Real.sqrt_mul (by positivity : 0 ≤ 3 * (1 + K))]
  unfold exteriorErrorCoefficient
  ring

end PropA4
end AcExtensionPrinciple

end
