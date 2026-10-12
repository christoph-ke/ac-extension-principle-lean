module

public import AcExtensionPrinciple.Observability.PropA4IncomingDerivative
public import AcExtensionPrinciple.Observability.PropA4AmplitudeMass

/-!
# Squared derivative errors on a late inner cylinder

Paper `e1a0fd5`, lines 1890–1897. Squaring the two already proved
pointwise derivative estimates and using the amplitude mass bound gives
uniform errors of order `P⁴/a⁴ + P²E/a³`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Squaring a two-term absolute bound costs a factor two.
Paper `e1a0fd5`, lines 1890–1897. -/
theorem square_abs_le_sum {x d e : ℝ} (he : |x| ≤ d + e) :
    x ^ 2 ≤ 2 * (d ^ 2 + e ^ 2) := by
  have hh := pow_le_pow_left₀ (abs_nonneg x) he 2
  rw [sq_abs] at hh
  nlinarith [sq_nonneg (d - e)]

/-- Squared version of a derivative error with its exact mass/radius scales.
The amplitude premise is discharged by `amplitude_sq_mass_bound`.
Paper `e1a0fd5`, lines 1890–1897. -/
theorem derivative_error_square {x P a E A h C α : ℝ}
    (ha : 0 < a) (hE : 0 ≤ E) (hh : h ^ 2 ≤ A * P ^ 2)
    (he : |x| ≤ α * P * |h| / a ^ 2 + C * P * Real.sqrt E * a ^ (-(3 / 2) : ℝ)) :
    x ^ 2 ≤ 2 * α ^ 2 * A * P ^ 4 / a ^ 4 + 2 * C ^ 2 * P ^ 2 * E / a ^ 3 := by
  have hb := square_abs_le_sum he
  have hp3 : (a ^ (-(3 / 2) : ℝ)) ^ 2 = 1 / a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have hterm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 2 * α ^ 2 * P ^ 2 / a ^ 4 by positivity)
  have heq : 2 * ((α * P * |h| / a ^ 2) ^ 2 +
      (C * P * Real.sqrt E * a ^ (-(3 / 2) : ℝ)) ^ 2) =
      (2 * α ^ 2 * P ^ 2 / a ^ 4) * h ^ 2 + 2 * C ^ 2 * P ^ 2 * E / a ^ 3 := by
    rw [div_pow, mul_pow, sq_abs, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE, hp3]
    ring
  rw [heq] at hb
  have heq' : (2 * α ^ 2 * P ^ 2 / a ^ 4) * (A * P ^ 2) =
      2 * α ^ 2 * A * P ^ 4 / a ^ 4 := by ring
  rw [heq'] at hterm
  linarith only [hb, hterm]

/-- K-only coefficient in the incoming derivative error.
Paper `e1a0fd5`, lines 1813–1819 and 1890–1897. -/
@[expose] noncomputable def incomingDerivativeErrorConstant (K : ℝ) : ℝ :=
  (8 / 3) * Real.sqrt K + exteriorErrorCoefficient K / 10

/-- Common squared error at radius `a`, for both scalar derivatives.
Paper `e1a0fd5`, lines 1890–1897. -/
@[expose] noncomputable def innerDerivativeSquareError (K P a E : ℝ) : ℝ :=
  512 * amplitudeMassSquareConstant K * P ^ 4 / a ^ 4 +
    2 * (incomingDerivativeErrorConstant K ^ 2 + radialDerivativeErrorConstant K ^ 2) *
      P ^ 2 * E / a ^ 3

/-- The incoming derivative error has the common uniform squared bound.
Paper `e1a0fd5`, lines 1890–1897. -/
theorem inner_incoming_derivative_square {b T K P s t a : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) (hp : (s, t) ∈ exteriorDomain h P)
    (ha : 0 < a) (hra : S.r s t = a) :
    (S.dupsi s t - S.dupsi s s) ^ 2 ≤ innerDerivativeSquareError K P a (chartScalarEnergy S T) := by
  have hA := amplitude_sq_mass_bound h hP hT hmass hs hlate hfit hE
  have he := incoming_derivative_error_bound h hP hT hmass hp
  rw [hra, Real.rpow_neg ha.le, Real.rpow_two] at he
  have he' : |S.dupsi s t - S.dupsi s s| ≤ 4 * P * |amplitude h s| / a ^ 2 +
      incomingDerivativeErrorConstant K * P * Real.sqrt (chartScalarEnergy S T) *
        a ^ (-(3 / 2) : ℝ) := by
    convert he using 1
    unfold incomingDerivativeErrorConstant
    ring
  have hb := derivative_error_square ha h.scalar_energy_nonneg hA he'
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hA0 : 0 ≤ amplitudeMassSquareConstant K := by
    unfold amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  have hE0 := h.scalar_energy_nonneg
  unfold innerDerivativeSquareError
  norm_num at hb
  have hN₁ : 0 ≤ amplitudeMassSquareConstant K * P ^ 4 / a ^ 4 := by positivity
  have hN₂ : 0 ≤ radialDerivativeErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T / a ^ 3 :=
    by positivity
  ring_nf at hb hN₁ hN₂ ⊢
  linarith only [hb, hN₁, hN₂]

/-- The radial wave derivative differs from the transported outer datum
by the same squared error. Paper `e1a0fd5`, lines 1890–1897. -/
theorem inner_radial_derivative_square {b T K P s t a : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) (hp : (s, t) ∈ exteriorDomain h P)
    (ha : 0 < a) (hra : S.r s t = a) :
    (S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t) ^ 2 ≤
      innerDerivativeSquareError K P a (chartScalarEnergy S T) := by
  let J := (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) /
    S.lam s t
  have hJ := exteriorUnitSolution_radial_integral_bounds h hP hmass hp
  have he := radial_derivative_error_bound h hP hT hmass hp
  change |S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t + amplitude h s * J| ≤ _ at he
  change 0 ≤ J ∧ J ≤ 16 * P * S.r s t ^ (-2 : ℝ) at hJ
  have habs : |amplitude h s * J| ≤ 16 * P * |amplitude h s| / a ^ 2 := by
    rw [abs_mul, abs_of_nonneg hJ.1]
    have hh := mul_le_mul_of_nonneg_left hJ.2 (abs_nonneg (amplitude h s))
    rw [hra, Real.rpow_neg ha.le, Real.rpow_two] at hh
    convert hh using 1; ring
  have he' : |S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t| ≤
      16 * P * |amplitude h s| / a ^ 2 +
        radialDerivativeErrorConstant K * P * Real.sqrt (chartScalarEnergy S T) *
          a ^ (-(3 / 2) : ℝ) := by
    have hh := abs_sub (S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t + amplitude h s * J)
      (amplitude h s * J)
    simp only [add_sub_cancel_right] at hh
    rw [hra] at he
    linarith only [hh, he, habs]
  have hA := amplitude_sq_mass_bound h hP hT hmass hs hlate hfit hE
  have hb := derivative_error_square ha h.scalar_energy_nonneg hA he'
  have hE0 := h.scalar_energy_nonneg
  unfold innerDerivativeSquareError
  norm_num at hb
  have hN : 0 ≤ incomingDerivativeErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T / a ^ 3 :=
    by positivity
  ring_nf at hb hN ⊢
  linarith only [hb, hN]

end PropA4
end AcExtensionPrinciple

end
