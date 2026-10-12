module

public import AcExtensionPrinciple.Observability.PropA4RadialDerivativeBound
public import AcExtensionPrinciple.Observability.PropA4UnitRadialWeight

/-!
# The radial scalar decomposition used to control mass

Paper `e1a0fd5`, `eq:observability-radial-scalar-bound`, lines 1820–1829.
Dividing the exact scalar remainder by radius combines with the proved
radial derivative error and produces the coercive unit-solution weight.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- The exact radial scalar error is the radial wave error minus `R/r`.
Paper `e1a0fd5`, lines 1820–1829. -/
theorem radial_scalar_error_identity {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    S.theta s t / S.lam s t + amplitude h s * exteriorUnitRadialWeight h hP hmass s t -
        S.dvpsi t t / S.lam s t + exteriorBoundaryPrimitive h (s, t) / S.r s t =
      (S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t +
        amplitude h s * ((∫ σ in t..s, chartPotential S σ t *
          exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t)) -
        exteriorRemainder h hP hmass (s, t) / S.r s t := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hl := (h.signs s t hp.1).1
  have he : S.r s t * S.phi s t = amplitude h s * exteriorUnitSolution h hP hmass (s, t) +
      exteriorBoundaryPrimitive h (s, t) + exteriorRemainder h hP hmass (s, t) :=
    exterior_scalar_decomposition h hP hmass (s, t)
  unfold SSFields.theta exteriorUnitRadialWeight
  field_simp [hr.ne', hl.ne']
  linear_combination (-S.lam s t) * he

/-- Radial scalar error with exactly the uniform radius decay needed for
both the amplitude and exterior mass estimates. The left side is the
paper's expression for `rφ_r`, with `W/r-W_r` represented by the actual
unit potential integral. Paper `e1a0fd5`, lines 1820–1829. -/
theorem radial_scalar_error_bound {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    |S.theta s t / S.lam s t + amplitude h s * exteriorUnitRadialWeight h hP hmass s t -
      S.dvpsi t t / S.lam s t + exteriorBoundaryPrimitive h (s, t) / S.r s t| ≤
      (radialDerivativeErrorConstant K + 2 * exteriorErrorCoefficient K) * P *
        Real.sqrt (chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hK : 0 ≤ K := by linarith only [h.K_ge_one]
  have hd := radial_derivative_error_bound h hP hT hmass hp
  have hR := exteriorRemainder_bound h hP hT hmass (s, t) hp
  rw [exteriorErrorCoefficient_factor hK] at hR
  have hdiv := div_le_div_of_nonneg_right hR hr.le
  have he : S.r s t ^ (-(1 / 2) : ℝ) / S.r s t = S.r s t ^ (-(3 / 2) : ℝ) := by
    calc
      _ = S.r s t ^ (-(1 / 2) : ℝ) / S.r s t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = S.r s t ^ ((-(1 / 2) : ℝ) - 1) := (Real.rpow_sub hr _ _).symm
      _ = _ := by congr 1; norm_num
  rw [radial_scalar_error_identity h hP hmass hp]
  let D := S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t +
    amplitude h s * ((∫ σ in t..s, chartPotential S σ t *
      exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t)
  change |D - exteriorRemainder h hP hmass (s, t) / S.r s t| ≤ _
  calc
    _ ≤ |D| + |exteriorRemainder h hP hmass (s, t) / S.r s t| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le D 0 (exteriorRemainder h hP hmass (s, t) / S.r s t)
    _ ≤ radialDerivativeErrorConstant K * P * Real.sqrt (chartScalarEnergy S T) *
        S.r s t ^ (-(3 / 2) : ℝ) +
        (2 * P * (exteriorErrorCoefficient K * Real.sqrt (chartScalarEnergy S T)) *
          S.r s t ^ (-(1 / 2) : ℝ)) / S.r s t := by
      rw [abs_div, abs_of_pos hr]
      exact add_le_add hd hdiv
    _ = radialDerivativeErrorConstant K * P * Real.sqrt (chartScalarEnergy S T) *
        S.r s t ^ (-(3 / 2) : ℝ) +
        (2 * P * (exteriorErrorCoefficient K * Real.sqrt (chartScalarEnergy S T))) *
          (S.r s t ^ (-(1 / 2) : ℝ) / S.r s t) := by ring
    _ = _ := by rw [he]; ring

end PropA4
end AcExtensionPrinciple

end
