module

public import AcExtensionPrinciple.Observability.PropA4RemainderBound

/-!
# Single outgoing potential integrals on the exterior domain

Paper `e1a0fd5`, lines 1793–1819. Positive kernel domination and the
actual radial power calculation give weighted outgoing derivative bounds.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Weighted domination for a single outgoing potential integral.
Continuity and the input bound are the premises of the weighted
function space and are discharged for the primitive and remainder below.
Paper `e1a0fd5`, lines 1793–1819. -/
theorem outgoing_weighted_integral_bound {b T K P s t q A : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hp : (s, t) ∈ chartInterior (chartCylinder h.g T) S) (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 2) (hA : 0 ≤ A) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (chartTriangle t s))
    (hbound : ∀ p ∈ chartTriangle t s, |F p| ≤ A * S.r p.1 p.2 ^ q) :
    |∫ z in t..s, chartPotential S s z * F (s, z)| ≤
      A * (4 * P / (2 - q) * S.r s t ^ (q - 2)) := by
  have htri := h.volterra_triangle_subset ht hp
  have hPc : ContinuousOn (fun p : ℝ × ℝ => chartPotential S p.1 p.2) (chartTriangle t s) :=
    continuous_potential_on h htri
  have hRc : ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2 ^ q) (chartTriangle t s) :=
    (h.continuous_r.mono (fun p hp => (htri hp).1)).rpow_const
      (fun p hp => Or.inl (htri hp).2.ne')
  have hline : MapsTo (fun z : ℝ => (s, z)) (Icc t s) (chartTriangle t s) :=
    fun z hz => ⟨hz.1, hz.2, le_rfl⟩
  have hfc : ContinuousOn (fun z => chartPotential S s z * F (s, z)) (Icc t s) :=
    (hPc.mul hF).comp (f := fun z : ℝ => (s, z))
      (by fun_prop) hline
  have hgc : ContinuousOn (fun z => chartPotential S s z * (A * S.r s z ^ q)) (Icc t s) :=
    (hPc.mul (continuousOn_const.mul hRc)).comp (f := fun z : ℝ => (s, z))
      (by fun_prop) hline
  have hi : IntervalIntegrable (fun z => chartPotential S s z * F (s, z)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hfc
  have hj : IntervalIntegrable (fun z => chartPotential S s z * (A * S.r s z ^ q)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hgc
  have hup := intervalIntegral.integral_mono_on hp.1.2.2.2 hi hj (fun z hz =>
    mul_le_mul_of_nonneg_left ((le_abs_self (F (s, z))).trans (hbound _ (hline hz)))
      (h.potential_nonneg (htri (hline hz)).1))
  have hlo := intervalIntegral.integral_mono_on hp.1.2.2.2 hi.neg hj (fun z hz => by
    have hh := mul_le_mul_of_nonneg_left ((neg_le_abs (F (s, z))).trans (hbound _ (hline hz)))
      (h.potential_nonneg (htri (hline hz)).1)
    simpa only [Pi.neg_apply, mul_neg] using hh)
  simp only [Pi.neg_apply] at hlo
  rw [intervalIntegral.integral_neg] at hlo
  have he : (∫ z in t..s, chartPotential S s z * (A * S.r s z ^ q)) =
      A * (∫ z in t..s, chartPotential S s z * S.r s z ^ q) := by
    simp only [mul_left_comm _ A, intervalIntegral.integral_const_mul]
  rw [he] at hup hlo
  exact (abs_le.mpr ⟨by linarith only [hlo], hup⟩).trans
    (mul_le_mul_of_nonneg_left (outgoing_power_kernel_le h hP ht hp hcut hmass hq) hA)

end PropA4
end AcExtensionPrinciple

end
