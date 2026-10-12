module

public import AcExtensionPrinciple.Observability.PropA4Remainder

/-!
# The concrete exterior remainder estimate

Paper `e1a0fd5`, `eq:observability-remainder-bound`, lines 1770–1779.
The exact chart power and time-oscillation integrals control the forcing;
weighted inversion gives the asserted uniform `P/√r` decay.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Dominate the absolute value of a triangular integral by a positive
comparison input. Paper `e1a0fd5`, lines 1770–1779. -/
theorem triangleVolterra_abs_le_on {V F G : ℝ × ℝ → ℝ} {s t : ℝ}
    (hts : t ≤ s) (hV : ContinuousOn V (chartTriangle t s))
    (hF : ContinuousOn F (chartTriangle t s))
    (hG : ContinuousOn G (chartTriangle t s))
    (hpos : ∀ p ∈ chartTriangle t s, 0 ≤ V p)
    (hbound : ∀ p ∈ chartTriangle t s, |F p| ≤ G p) :
    |triangleVolterra V F s t| ≤ triangleVolterra V G s t := by
  have hup := triangleVolterra_mono_on hts hV hF hG hpos
    (fun p hp => (le_abs_self (F p)).trans (hbound p hp))
  have hlo := triangleVolterra_mono_on hts hV hF.neg hG hpos
    (fun p hp => (neg_le_abs (F p)).trans (hbound p hp))
  have hneg : triangleVolterra V (-F) s t = -triangleVolterra V F s t := by
    simp only [triangleVolterra, Pi.neg_apply, mul_neg, intervalIntegral.integral_neg]
  rw [hneg] at hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- The exact remainder forcing is controlled by the half-power and
oscillation comparison kernels. Paper `e1a0fd5`, lines 1770–1779. -/
theorem exteriorRemainder_forcing_bound {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    |exteriorRemainder h hP hmass p -
      triangleVolterra (fun p => chartPotential S p.1 p.2)
        (exteriorRemainder h hP hmass) p.1 p.2| ≤
      P * ((32 / 3) * Real.sqrt (K * chartScalarEnergy S T) +
        4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * chartScalarEnergy S T)) *
          S.r p.1 p.2 ^ (-(1 / 2) : ℝ) := by
  let E := chartScalarEnergy S T
  let A := Real.sqrt (K * E)
  let C := 2 * Real.sqrt (3 * (1 + K) * E)
  let W := exteriorUnitSolution h hP hmass
  let Q := fun z => exteriorBoundaryPrimitive h z + (amplitude h z.1 - amplitude h p.1) * W z
  let R := fun z : ℝ × ℝ => S.r z.1 z.2 ^ (1 / 2 : ℝ)
  let J := fun z : ℝ × ℝ => Real.sqrt (p.1 - z.1)
  let V := fun z : ℝ × ℝ => chartPotential S z.1 z.2
  have hE : 0 ≤ E := h.scalar_energy_nonneg
  have hK : 0 ≤ K := by linarith [h.K_ge_one]
  have htri := exteriorDomain_triangle h hP hp
  have hint := exteriorDomain_interior h hP hp
  have ht : 0 ≤ p.2 := (mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hVc : ContinuousOn V (chartTriangle p.2 p.1) :=
    continuous_potential_on h (fun z hz => exteriorDomain_interior h hP (htri hz))
  have hWc := (exteriorUnitSolution_continuous h hP hmass).mono htri
  have hAc := (amplitude_continuous_on_exterior h hT).mono htri
  have hQc : ContinuousOn Q (chartTriangle p.2 p.1) :=
    ((exteriorBoundaryPrimitive_continuous h hP hT).mono htri).add
      ((hAc.sub continuousOn_const).mul hWc)
  have hRc : ContinuousOn R (chartTriangle p.2 p.1) :=
    ((h.continuous_r.mono (fun z hz => (htri hz).1)).rpow_const
      (fun z hz => Or.inl (exteriorDomain_interior h hP (htri hz)).2.ne'))
  have hJc : Continuous J := by dsimp [J]; fun_prop
  have hQbound : ∀ z ∈ chartTriangle p.2 p.1, |Q z| ≤ A * R z + C * J z := by
    intro z hz
    have hzD := htri hz
    have hprim := boundary_primitive_bound h (hzD.2.1.trans hzD.1.2.2.2) hzD.1
    have hosc := amplitude_oscillation h
      ⟨hzD.2.1.trans hzD.1.2.2.2, hzD.1.2.1⟩
      ⟨hp.2.1.trans hp.1.2.2.2, hp.1.2.1⟩ hz.2.2
    have hosc' : |amplitude h z.1 - amplitude h p.1| ≤
        Real.sqrt (3 * (1 + K) * E) * J z := by
      rw [abs_sub_comm]
      calc
        _ ≤ Real.sqrt (3 * (1 + K) * (p.1 - z.1) * E) := hosc
        _ = _ := by
          dsimp [J]
          rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * (1 + K) * E)]
          congr 1
          ring
    have hprim' : |exteriorBoundaryPrimitive h z| ≤ A * R z := by
      calc
        _ ≤ Real.sqrt (K * S.r z.1 z.2 * E) := hprim
        _ = _ := by
          dsimp [A, R]
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (mul_nonneg hK hE)]
          congr 1
          ring
    have hW := exteriorUnitSolution_bounds h hP hmass hzD
    have hW0 : 0 ≤ W z := by change 0 ≤ exteriorUnitSolution h hP hmass z; linarith [hW.1]
    have hprod : |(amplitude h z.1 - amplitude h p.1) * W z| ≤ C * J z := by
      rw [abs_mul, abs_of_nonneg hW0]
      calc
        _ ≤ (Real.sqrt (3 * (1 + K) * E) * J z) * 2 :=
          mul_le_mul hosc' hW.2 hW0 (by dsimp [J]; positivity)
        _ = _ := by dsimp [C]; ring
    exact (abs_add_le _ _).trans (add_le_add hprim' hprod)
  have hdom := triangleVolterra_abs_le_on hp.1.2.2.2 hVc hQc
    ((hRc.const_smul A).add (hJc.continuousOn.const_smul C))
    (fun z hz => h.potential_nonneg (htri hz).1) hQbound
  have hsplit : triangleVolterra V (A • R + C • J) p.1 p.2 =
      A * triangleVolterra V R p.1 p.2 + C * triangleVolterra V J p.1 p.2 := by
    rw [triangleVolterra_add_on hp.1.2.2.2 hVc (hRc.const_smul A)
      (hJc.continuousOn.const_smul C), triangleVolterra_smul, triangleVolterra_smul]
  rw [hsplit] at hdom
  have hpow := volterra_power_kernel_le h hP ht hint hp.2.2 hmass
    (by norm_num : (1 / 2 : ℝ) < 1)
  have htime := volterra_time_oscillation_kernel_le h hP ht hint hp.2.2 hmass
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg (K * E)))
    (mul_le_mul_of_nonneg_left htime (show 0 ≤ C by dsimp [C]; positivity))
  rw [exteriorRemainder_equation h hP hT hmass hp]
  apply hdom.trans
  convert hsum using 1
  dsimp [C, E]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  simp only [Real.rpow_neg hint.2.le, ← Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The paper's remainder estimate for the actual scalar field and
actual positive unit solution, uniform in the outer radius and duration.
Paper `e1a0fd5`, `eq:observability-remainder-bound`, lines 1777–1779. -/
theorem exteriorRemainder_bound {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    ∀ p ∈ exteriorDomain h P, |exteriorRemainder h hP hmass p| ≤
      2 * P * ((32 / 3) * Real.sqrt (K * chartScalarEnergy S T) +
        4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * chartScalarEnergy S T)) *
          S.r p.1 p.2 ^ (-(1 / 2) : ℝ) := by
  have hB : 0 ≤ P * ((32 / 3) * Real.sqrt (K * chartScalarEnergy S T) +
      4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * chartScalarEnergy S T)) :=
    by positivity
  intro p hp
  apply (exterior_residual_bound h hP hmass (by norm_num : (-(1 / 2) : ℝ) < 1)
    (by norm_num) hB (exteriorRemainder_continuous h hP hT hmass)
    (fun p hp => exteriorRemainder_forcing_bound h hP hT hmass hp) p hp).trans_eq
  ring

end PropA4
end AcExtensionPrinciple

end
