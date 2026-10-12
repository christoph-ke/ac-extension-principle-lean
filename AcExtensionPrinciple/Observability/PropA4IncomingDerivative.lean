module

public import AcExtensionPrinciple.Observability.PropA4OutgoingKernel
public import AcExtensionPrinciple.Observability.PropA4UnitDerivatives
public import AcExtensionPrinciple.Observability.PropA4Derivatives
public import AcExtensionPrinciple.Observability.PropA4DerivativeConstants

/-!
# The incoming scalar derivative estimate on the exterior domain

Paper `e1a0fd5`, `eq:observability-incoming-derivative-bound`, lines
1813–1819. The exact scalar decomposition and the single outgoing
potential integrals give explicit constants before absorbing `P/r`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Explicit incoming derivative error with both decaying potential
contributions displayed. The last term is absorbed using `P/r ≤ 1/32`.
Paper `e1a0fd5`, lines 1813–1819. -/
theorem incoming_derivative_error_tails {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    |S.dupsi s t - S.dupsi s s| ≤
      4 * P * |amplitude h s| * S.r s t ^ (-2 : ℝ) +
        (8 / 3) * P * Real.sqrt (K * chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) +
        (16 / 5) * P ^ 2 * ((32 / 3) * Real.sqrt (K * chartScalarEnergy S T) +
          4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * chartScalarEnergy S T)) *
            S.r s t ^ (-(5 / 2) : ℝ) := by
  let V := fun p : ℝ × ℝ => chartPotential S p.1 p.2
  let W := exteriorUnitSolution h hP hmass
  let B := exteriorBoundaryPrimitive h
  let R := exteriorRemainder h hP hmass
  let E := chartScalarEnergy S T
  let C := (32 / 3) * Real.sqrt (K * E) +
    4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * E)
  have hE : 0 ≤ E := h.scalar_energy_nonneg
  have hK : 0 ≤ K := by linarith only [h.K_ge_one]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htri := exteriorDomain_triangle h hP hp
  have hint := exteriorDomain_interior h hP hp
  have ht : 0 ≤ t := (mul_nonneg hK h.b_pos.le).trans hp.2.1
  have hVc : ContinuousOn V (chartTriangle t s) :=
    continuous_potential_on h (fun p hp => exteriorDomain_interior h hP (htri hp))
  have hWc := (exteriorUnitSolution_continuous h hP hmass).mono htri
  have hBc := (exteriorBoundaryPrimitive_continuous h hP hT).mono htri
  have hRc := (exteriorRemainder_continuous h hP hT hmass).mono htri
  have hline : MapsTo (fun z : ℝ => (s, z)) (Icc t s) (chartTriangle t s) :=
    fun z hz => ⟨hz.1, hz.2, le_rfl⟩
  have hwi : IntervalIntegrable (fun z => V (s, z) * W (s, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hWc).comp (f := fun z : ℝ => (s, z)) (by fun_prop) hline
  have hbi : IntervalIntegrable (fun z => V (s, z) * B (s, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hBc).comp (f := fun z : ℝ => (s, z)) (by fun_prop) hline
  have hri : IntervalIntegrable (fun z => V (s, z) * R (s, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hRc).comp (f := fun z : ℝ => (s, z)) (by fun_prop) hline
  have hBbound : ∀ p ∈ chartTriangle t s,
      |B p| ≤ Real.sqrt (K * E) * S.r p.1 p.2 ^ (1 / 2 : ℝ) := by
    intro p hp'
    have hpD := htri hp'
    have hb := boundary_primitive_bound h (hpD.2.1.trans hpD.1.2.2.2) hpD.1
    calc
      _ ≤ Real.sqrt (K * S.r p.1 p.2 * E) := hb
      _ = _ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (mul_nonneg hK hE)]
        congr 1
        ring
  have hRbound : ∀ p ∈ chartTriangle t s, |R p| ≤ (2 * P * C) * S.r p.1 p.2 ^ (-(1 / 2) : ℝ) :=
    fun p hp' => exteriorRemainder_bound h hP hT hmass p (htri hp')
  have hWB := exteriorUnitSolution_s_integral_bounds h hP hmass hp
  have hBB := outgoing_weighted_integral_bound h hP ht hint hp.2.2 hmass
    (by norm_num : (1 / 2 : ℝ) < 2) (Real.sqrt_nonneg (K * E)) hBc hBbound
  have hRB := outgoing_weighted_integral_bound h hP ht hint hp.2.2 hmass
    (by norm_num : (-(1 / 2) : ℝ) < 2) (show 0 ≤ 2 * P * C by positivity) hRc hRbound
  have hsplit : (∫ z in t..s, V (s, z) * chartPsi S s z) =
      amplitude h s * (∫ z in t..s, V (s, z) * W (s, z)) +
        (∫ z in t..s, V (s, z) * B (s, z)) + (∫ z in t..s, V (s, z) * R (s, z)) := by
    calc
      _ = ∫ z in t..s, (amplitude h s * (V (s, z) * W (s, z)) + V (s, z) * B (s, z)) +
          V (s, z) * R (s, z) := by
        apply intervalIntegral.integral_congr
        intro z _
        have he : chartPsi S s z = amplitude h s * W (s, z) + B (s, z) + R (s, z) :=
          exterior_scalar_decomposition h hP hmass (s, z)
        change V (s, z) * chartPsi S s z = _
        rw [he]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hwi.const_mul _).add hbi) hri,
          intervalIntegral.integral_add (hwi.const_mul _) hbi, intervalIntegral.integral_const_mul]
  have hAbsW : |amplitude h s * (∫ z in t..s, V (s, z) * W (s, z))| ≤
      |amplitude h s| * (4 * P * S.r s t ^ (-2 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hWB.1]
    exact mul_le_mul_of_nonneg_left hWB.2 (abs_nonneg _)
  have habs : |(amplitude h s * (∫ z in t..s, V (s, z) * W (s, z)) +
      (∫ z in t..s, V (s, z) * B (s, z))) + (∫ z in t..s, V (s, z) * R (s, z))| ≤
      |amplitude h s| * (4 * P * S.r s t ^ (-2 : ℝ)) +
        Real.sqrt (K * E) * (4 * P / (2 - (1 / 2)) * S.r s t ^ ((1 / 2) - 2 : ℝ)) +
        (2 * P * C) * (4 * P / (2 - (-(1 / 2))) * S.r s t ^ ((-(1 / 2)) - 2 : ℝ)) :=
    (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hAbsW hBB)) hRB)
  have heq := incoming_wave_representation h ht hint
  rw [heq]
  have heq' : S.dupsi s s + (∫ z in t..s, chartPotential S s z * chartPsi S s z) - S.dupsi s s =
      ∫ z in t..s, V (s, z) * chartPsi S s z := by dsimp [V]; ring
  rw [heq', hsplit]
  apply habs.trans_eq
  dsimp [C, E]
  norm_num
  ring

/-- The incoming derivative estimate with a constant depending only on K,
after absorbing the smaller remainder tail. Paper `e1a0fd5`,
`eq:observability-incoming-derivative-bound`, lines 1813–1819. -/
theorem incoming_derivative_error_bound {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    |S.dupsi s t - S.dupsi s s| ≤
      4 * P * |amplitude h s| * S.r s t ^ (-2 : ℝ) +
        ((8 / 3) * Real.sqrt K + exteriorErrorCoefficient K / 10) * P *
          Real.sqrt (chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) := by
  have hK : 0 ≤ K := by linarith only [h.K_ge_one]
  have he := incoming_derivative_error_tails h hP hT hmass hp
  rw [exteriorErrorCoefficient_factor hK, Real.sqrt_mul hK] at he
  have ht := exterior_derivative_tail_absorb hP.le (exteriorDomain_interior h hP hp).2 hp.2.2
  have hC : 0 ≤ (16 / 5 : ℝ) * exteriorErrorCoefficient K *
      Real.sqrt (chartScalarEnergy S T) := by unfold exteriorErrorCoefficient; positivity
  have htail := mul_le_mul_of_nonneg_left ht hC
  calc
    _ ≤ _ := he
    _ ≤ 4 * P * |amplitude h s| * S.r s t ^ (-2 : ℝ) +
        (8 / 3) * P * (Real.sqrt K * Real.sqrt (chartScalarEnergy S T)) *
          S.r s t ^ (-(3 / 2) : ℝ) +
        ((16 / 5) * exteriorErrorCoefficient K * Real.sqrt (chartScalarEnergy S T)) *
          ((P / 32) * S.r s t ^ (-(3 / 2) : ℝ)) := by nlinarith only [htail]
    _ = _ := by ring

/-- The same estimate with the actual boundary trace derivative,
almost everywhere in s. Paper `e1a0fd5`, lines 1813–1819. -/
theorem incoming_derivative_error_bound_ae {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    ∀ᵐ s, ∀ t, (s, t) ∈ exteriorDomain h P →
      |S.dupsi s t - deriv (fun s => chartPsi S s s) s + S.dvpsi s s| ≤
        4 * P * |amplitude h s| * S.r s t ^ (-2 : ℝ) +
          ((8 / 3) * Real.sqrt K + exteriorErrorCoefficient K / 10) * P *
            Real.sqrt (chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) := by
  filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs
  intro t hp
  have hd := (hs ⟨hp.1.1, hp.1.2.1⟩).deriv
  have hb := incoming_derivative_error_bound h hP hT hmass hp
  rw [hd]
  convert hb using 1
  congr 1
  ring

end PropA4
end AcExtensionPrinciple

end
