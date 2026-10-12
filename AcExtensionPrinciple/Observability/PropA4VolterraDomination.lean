module

public import AcExtensionPrinciple.Observability.PropA4VolterraKernel

/-!
# Domination in the weighted exterior Volterra norm

Paper `e1a0fd5`, `eq:observability-power-operator-bound`, lines 1742–1747.
The concrete power-kernel estimate controls arbitrary continuous inputs
on the characteristic triangle.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- A continuous triangular kernel has integrable outgoing sections.
Paper `e1a0fd5`, lines 1734–1747. -/
theorem triangle_section_integrable {F : ℝ × ℝ → ℝ} {t s σ : ℝ}
    (hF : ContinuousOn F (chartTriangle t s)) (hσ : σ ∈ Icc t s) :
    IntervalIntegrable (fun z => F (σ, z)) volume t σ := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hσ.1]
  exact hF.comp (f := fun z : ℝ => (σ, z))
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hz.1, hz.2, hσ.2⟩)

/-- A positive continuous kernel preserves order on the triangle.
Paper `e1a0fd5`, lines 1742–1755. -/
theorem triangleVolterra_mono_on {P F G : ℝ × ℝ → ℝ} {t s : ℝ}
    (hts : t ≤ s) (hP : ContinuousOn P (chartTriangle t s))
    (hF : ContinuousOn F (chartTriangle t s))
    (hG : ContinuousOn G (chartTriangle t s))
    (hpos : ∀ p ∈ chartTriangle t s, 0 ≤ P p)
    (hbound : ∀ p ∈ chartTriangle t s, F p ≤ G p) :
    triangleVolterra P F s t ≤ triangleVolterra P G s t := by
  have hi : IntervalIntegrable (fun σ => ∫ z in t..σ, P (σ, z) * F (σ, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral (hP.mul hF)
  have hj : IntervalIntegrable (fun σ => ∫ z in t..σ, P (σ, z) * G (σ, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral (hP.mul hG)
  apply intervalIntegral.integral_mono_on hts hi hj
  intro σ hσ
  apply intervalIntegral.integral_mono_on hσ.1
    (triangle_section_integrable (hP.mul hF) hσ)
    (triangle_section_integrable (hP.mul hG) hσ)
  intro z hz
  have hp : (σ, z) ∈ chartTriangle t s := ⟨hz.1, hz.2, hσ.2⟩
  exact mul_le_mul_of_nonneg_left (hbound _ hp) (hpos _ hp)

/-- The triangular operator is additive on continuous inputs.
Paper `e1a0fd5`, lines 1742–1755. -/
theorem triangleVolterra_add_on {P F G : ℝ × ℝ → ℝ} {t s : ℝ}
    (hts : t ≤ s) (hP : ContinuousOn P (chartTriangle t s))
    (hF : ContinuousOn F (chartTriangle t s))
    (hG : ContinuousOn G (chartTriangle t s)) :
    triangleVolterra P (F + G) s t = triangleVolterra P F s t + triangleVolterra P G s t := by
  have hi : IntervalIntegrable (fun σ => ∫ z in t..σ, P (σ, z) * F (σ, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral (hP.mul hF)
  have hj : IntervalIntegrable (fun σ => ∫ z in t..σ, P (σ, z) * G (σ, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral (hP.mul hG)
  unfold triangleVolterra
  rw [← intervalIntegral.integral_add hi hj]
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [uIcc_of_le hts] at hσ
  simp only [Pi.add_apply, mul_add]
  exact intervalIntegral.integral_add
    (triangle_section_integrable (hP.mul hF) hσ)
    (triangle_section_integrable (hP.mul hG) hσ)

/-- Scalars pass through both triangular integrations.
Paper `e1a0fd5`, lines 1742–1755. -/
theorem triangleVolterra_smul (P F : ℝ × ℝ → ℝ) (s t c : ℝ) :
    triangleVolterra P (c • F) s t = c * triangleVolterra P F s t := by
  simp only [triangleVolterra, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
    intervalIntegral.integral_const_mul]

/-- A weighted pointwise input bound gives the concrete weighted
Volterra bound. The continuity and input-bound premises are those
of the weighted continuous-function space used for the resolvent.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem volterra_weighted_bound {b T K P s t q B : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hB : 0 ≤ B) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (chartTriangle t s))
    (hbound : ∀ p ∈ chartTriangle t s, |F p| ≤ B * S.r p.1 p.2 ^ q) :
    |triangleVolterra (fun p => chartPotential S p.1 p.2) F s t| ≤
      B * (1 / (4 * (2 - q) * (1 - q))) * S.r s t ^ q := by
  have hts := hpoint.1.2.2.2
  have htri := h.volterra_triangle_subset ht hpoint
  have hPc := continuous_potential_on h htri
  have hpos : ∀ p ∈ chartTriangle t s, 0 ≤ chartPotential S p.1 p.2 :=
    fun p hp => h.potential_nonneg (htri hp).1
  have hRc := (h.continuous_r.mono (fun p hp => (htri hp).1)).rpow_const
    (p := q) (by intro p hp; exact Or.inl (htri hp).2.ne')
  have hGc : ContinuousOn (fun p => B * S.r p.1 p.2 ^ q) (chartTriangle t s) :=
    continuousOn_const.mul hRc
  have hup := triangleVolterra_mono_on hts hPc hF hGc hpos
    (fun p hp => (le_abs_self (F p)).trans (hbound p hp))
  have hlow := triangleVolterra_mono_on hts hPc hF.neg hGc hpos
    (fun p hp => (neg_le_abs (F p)).trans (hbound p hp))
  have hscale : triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => B * S.r p.1 p.2 ^ q) s t =
      B * triangleVolterra (fun p => chartPotential S p.1 p.2)
        (fun p => S.r p.1 p.2 ^ q) s t := by
    simp only [triangleVolterra, mul_left_comm _ B, intervalIntegral.integral_const_mul]
  have hneg : triangleVolterra (fun p => chartPotential S p.1 p.2) (-F) s t =
      -triangleVolterra (fun p => chartPotential S p.1 p.2) F s t := by
    simp only [triangleVolterra, Pi.neg_apply, mul_neg, intervalIntegral.integral_neg]
  rw [hscale] at hup hlow
  rw [hneg] at hlow
  have hh := (abs_le.mpr ⟨by linarith, hup⟩).trans
    (mul_le_mul_of_nonneg_left
      (volterra_power_coefficient_le h hP ht hpoint hcut hmass hq) hB)
  simpa only [mul_assoc] using hh

end PropA4
end AcExtensionPrinciple

end
