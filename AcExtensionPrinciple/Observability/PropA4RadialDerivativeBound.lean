module

public import AcExtensionPrinciple.Observability.PropA4RadialDerivative

/-!
# Uniform radial scalar derivative bound

Paper `e1a0fd5`, `eq:observability-radial-derivative-bound`, lines
1790–1811. Factoring out `√E` and absorbing `P/r` make the constant's
exclusive dependence on K explicit.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- The inverse radius and inverse square root have the required power.
Paper `e1a0fd5`, lines 1790–1811. -/
theorem inverse_radius_sqrt_eq {r : ℝ} (hr : 0 < r) :
    r ^ (-(3 / 2) : ℝ) = r⁻¹ * (Real.sqrt r)⁻¹ := by
  calc
    _ = r ^ ((-1 : ℝ) + (-(1 / 2))) := by congr 1; norm_num
    _ = r ^ (-1 : ℝ) * r ^ (-(1 / 2) : ℝ) := Real.rpow_add hr _ _
    _ = _ := by rw [Real.rpow_neg_one, Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]

/-- The explicit K-dependent radial derivative coefficient.
Paper `e1a0fd5`, lines 1805–1811. -/
@[expose] noncomputable def radialDerivativeErrorConstant (K : ℝ) : ℝ :=
  (32 / 3) * Real.sqrt K + (2 / 5) * exteriorErrorCoefficient K +
    16 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K))

/-- The actual radial derivative error has the paper's uniform decay.
The unit integral is `-W_r` by `exteriorUnitSolution_hasDerivWithinAt_t`.
Paper `e1a0fd5`, `eq:observability-radial-derivative-bound`, lines 1805–1811. -/
theorem radial_derivative_error_bound {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    |S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t +
      amplitude h s * ((∫ σ in t..s, chartPotential S σ t *
        exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t)| ≤
      radialDerivativeErrorConstant K * P * Real.sqrt (chartScalarEnergy S T) *
        S.r s t ^ (-(3 / 2) : ℝ) := by
  have hK : 0 ≤ K := by linarith only [h.K_ge_one]
  have he := radial_derivative_error_tails h hP hT hmass hp
  rw [exteriorErrorCoefficient_factor hK, Real.sqrt_mul hK,
    Real.sqrt_mul (by positivity : 0 ≤ 3 * (1 + K))] at he
  have ht := exterior_derivative_tail_absorb hP.le (exteriorDomain_interior h hP hp).2 hp.2.2
  have hC : 0 ≤ (64 / 5 : ℝ) * exteriorErrorCoefficient K *
      Real.sqrt (chartScalarEnergy S T) := by unfold exteriorErrorCoefficient; positivity
  have htail := mul_le_mul_of_nonneg_left ht hC
  have htime : (16 * P / S.r s t) * (Real.pi * Real.sqrt 2 / Real.sqrt (S.r s t)) *
      (Real.sqrt (3 * (1 + K)) * Real.sqrt (chartScalarEnergy S T)) =
      16 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K)) * P *
        Real.sqrt (chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) := by
    rw [inverse_radius_sqrt_eq (exteriorDomain_interior h hP hp).2]
    ring
  rw [htime] at he
  calc
    _ ≤ _ := he
    _ ≤ (32 / 3) * P * (Real.sqrt K * Real.sqrt (chartScalarEnergy S T)) *
        S.r s t ^ (-(3 / 2) : ℝ) +
        ((64 / 5) * exteriorErrorCoefficient K * Real.sqrt (chartScalarEnergy S T)) *
          ((P / 32) * S.r s t ^ (-(3 / 2) : ℝ)) +
        16 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K)) * P *
          Real.sqrt (chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) := by
      nlinarith only [htail]
    _ = _ := by unfold radialDerivativeErrorConstant; ring

end PropA4
end AcExtensionPrinciple

end
