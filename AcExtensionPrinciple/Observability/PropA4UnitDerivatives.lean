module

public import AcExtensionPrinciple.Observability.PropA4UnitSolution

/-!
# The incoming derivative of the concrete exterior unit solution

Paper `e1a0fd5`, lines 1753–1759. Continuous extension of the kernel
allows differentiation on each closed exterior slice, including its
endpoints, without extending the physical solution beyond the chart.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Differentiation of the actual unit equation with respect to `s`.
The derivative is taken within the exterior slice. Paper `e1a0fd5`,
`eq:observability-unit-solution-bounds`, lines 1755–1759. -/
theorem exteriorUnitSolution_hasDerivWithinAt_s {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    HasDerivWithinAt (fun x => exteriorUnitSolution h hP hmass (x, t))
      (∫ z in t..s, chartPotential S s z * exteriorUnitSolution h hP hmass (s, z))
      {x | (x, t) ∈ exteriorDomain h P} s := by
  let F := fun p : ℝ × ℝ => chartPotential S p.1 p.2 * exteriorUnitSolution h hP hmass p
  have hFc : ContinuousOn F (exteriorDomain h P) :=
    (continuous_potential_on h (fun p hp => exteriorDomain_interior h hP hp)).mul
      (exteriorUnitSolution_continuous h hP hmass)
  obtain ⟨G, hG, hGeq⟩ := exteriorDomain_continuous_extension h hFc
  let I := fun x => ∫ z in t..x, G (x, z)
  have hIc : Continuous I :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x z : ℝ => G (x, z)) hG continuous_id
  have hd := (intervalIntegral.integral_hasDerivAt_right (hIc.intervalIntegrable t s)
    hIc.aestronglyMeasurable.stronglyMeasurableAtFilter hIc.continuousAt).const_add 1
  have hI : I s = ∫ z in t..s,
      chartPotential S s z * exteriorUnitSolution h hP hmass (s, z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hp.1.2.2.2] at hz
    exact hGeq (s, z) (exteriorDomain_triangle h hP hp ⟨hz.1, hz.2, le_rfl⟩)
  rw [hI] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ hp
  intro x hx
  rw [exteriorUnitSolution_equation h hP hmass hx]
  congr 1
  unfold triangleVolterra
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [uIcc_of_le hx.1.2.2.2] at hσ
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hσ.1] at hz
  exact (hGeq (σ, z) (exteriorDomain_triangle h hP hx ⟨hz.1, hz.2, hσ.2⟩)).symm

/-- The actual incoming derivative is nonnegative and has the exact
upper bound `4P/r²`. Paper `e1a0fd5`, lines 1755–1759. -/
theorem exteriorUnitSolution_s_integral_bounds {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    0 ≤ (∫ z in t..s, chartPotential S s z * exteriorUnitSolution h hP hmass (s, z)) ∧
      (∫ z in t..s, chartPotential S s z * exteriorUnitSolution h hP hmass (s, z)) ≤
        4 * P * S.r s t ^ (-2 : ℝ) := by
  have htri := exteriorDomain_triangle h hP hp
  have hint := exteriorDomain_interior h hP hp
  have ht : 0 ≤ t := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hPc : ContinuousOn (fun z : ℝ × ℝ => chartPotential S z.1 z.2)
      (chartTriangle t s) :=
    continuous_potential_on h (fun z hz => exteriorDomain_interior h hP (htri hz))
  have hline : MapsTo (fun z : ℝ => (s, z)) (Icc t s) (chartTriangle t s) :=
    fun z hz => ⟨hz.1, hz.2, le_rfl⟩
  have hpc : ContinuousOn (fun z : ℝ => chartPotential S s z) (Icc t s) :=
    hPc.comp (f := fun z : ℝ => (s, z))
      (show ContinuousOn (fun z : ℝ => (s, z)) (Icc t s) by fun_prop) hline
  have hwc : ContinuousOn (fun z : ℝ => exteriorUnitSolution h hP hmass (s, z))
      (Icc t s) :=
    (exteriorUnitSolution_continuous h hP hmass).comp (f := fun z : ℝ => (s, z))
      (show ContinuousOn (fun z : ℝ => (s, z)) (Icc t s) by fun_prop)
      (fun z hz => htri (hline hz))
  have hprod : IntervalIntegrable
      (fun z => chartPotential S s z * exteriorUnitSolution h hP hmass (s, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hpc.mul hwc
  have hpot : IntervalIntegrable (fun z => 2 * chartPotential S s z) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact continuousOn_const.mul hpc
  constructor
  · apply intervalIntegral.integral_nonneg hp.1.2.2.2
    intro z hz
    have hzD := htri (show (s, z) ∈ chartTriangle t s from ⟨hz.1, hz.2, le_rfl⟩)
    exact mul_nonneg (h.potential_nonneg hzD.1)
      (by linarith only [(exteriorUnitSolution_bounds h hP hmass hzD).1])
  · have hm := intervalIntegral.integral_mono_on hp.1.2.2.2 hprod hpot (fun z hz => by
      have hzD := htri (show (s, z) ∈ chartTriangle t s from ⟨hz.1, hz.2, le_rfl⟩)
      have hh := mul_le_mul_of_nonneg_left (exteriorUnitSolution_bounds h hP hmass hzD).2
        (h.potential_nonneg hzD.1)
      simpa only [mul_comm] using hh)
    rw [intervalIntegral.integral_const_mul] at hm
    have hb := outgoing_power_kernel_le h hP ht hint hp.2.2 hmass (by norm_num : (0 : ℝ) < 2)
    norm_num only [Real.rpow_zero, mul_one, sub_zero, zero_sub] at hb
    exact hm.trans (by nlinarith only [hb])

end PropA4
end AcExtensionPrinciple

end
