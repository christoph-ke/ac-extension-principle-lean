module

public import AcExtensionPrinciple.Observability.PropA4IncomingKernel
public import AcExtensionPrinciple.Observability.PropA4OscillationKernel

/-!
# Incoming time-oscillation tail for the radial derivative

Paper `e1a0fd5`, lines 1790–1796. One factor of the affine incoming
radius is bounded below by the endpoint radius; the already evaluated
square-denominator oscillation integral gives the required `r^(-3/2)` tail.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Single incoming potential integral with the time-oscillation weight.
Paper `e1a0fd5`, lines 1790–1796. -/
theorem incoming_time_oscillation_kernel_le {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hp : (s, t) ∈ chartInterior (chartCylinder h.g T) S) (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    (∫ σ in t..s, chartPotential S σ t * Real.sqrt (s - σ)) ≤
      (4 * P / S.r s t) * (Real.pi * Real.sqrt 2 / Real.sqrt (S.r s t)) := by
  have htri := h.volterra_triangle_subset ht hp
  have hline : MapsTo (fun σ : ℝ => (σ, t)) (Icc t s) (chartTriangle t s) :=
    fun σ hσ => ⟨le_rfl, hσ.1, hσ.2⟩
  have hPc : ContinuousOn (fun p : ℝ × ℝ => chartPotential S p.1 p.2) (chartTriangle t s) :=
    continuous_potential_on h htri
  have hfc : ContinuousOn (fun σ => chartPotential S σ t * Real.sqrt (s - σ)) (Icc t s) :=
    (hPc.comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline).mul
      (show Continuous (fun σ : ℝ => Real.sqrt (s - σ)) by fun_prop).continuousOn
  have hpos : ∀ σ ∈ Icc t s, 0 < S.r s t + (s - σ) / 2 := by
    intro σ hσ
    linarith only [hp.2, hσ.2]
  have hgc : ContinuousOn
      (fun σ : ℝ => (4 * P / S.r s t) *
        (Real.sqrt (s - σ) / (S.r s t + (s - σ) / 2) ^ 2)) (Icc t s) :=
    continuousOn_const.mul
      (((show Continuous (fun σ : ℝ => Real.sqrt (s - σ)) by fun_prop).continuousOn).div
        (show Continuous (fun σ : ℝ => (S.r s t + (s - σ) / 2) ^ 2)
          by fun_prop).continuousOn (fun σ hσ => pow_ne_zero _ (hpos σ hσ).ne'))
  have hi : IntervalIntegrable (fun σ => chartPotential S σ t * Real.sqrt (s - σ)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hfc
  have hj : IntervalIntegrable
      (fun σ : ℝ => (4 * P / S.r s t) *
        (Real.sqrt (s - σ) / (S.r s t + (s - σ) / 2) ^ 2)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hgc
  have hm := intervalIntegral.integral_mono_on hp.1.2.2.2 hi hj (fun σ hσ => by
    have hσint := htri (hline hσ)
    have hrord := (h.volterra_radius_order ht hp hσ ⟨le_rfl, hσ.1⟩).1
    have hpot := potential_le_radius_power h hP ht hσint (hcut.trans hrord) hmass
    have hsep := incoming_radius_separation h hP ht hp hcut hmass hσ
    have hpow3 := Real.rpow_le_rpow_of_nonpos (hpos σ hσ) hsep (by norm_num : (-3 : ℝ) ≤ 0)
    have hbase : S.r s t ≤ S.r s t + (s - σ) / 2 := by linarith only [hσ.2]
    have hpow1 := Real.rpow_le_rpow_of_nonpos hp.2 hbase (by norm_num : (-1 : ℝ) ≤ 0)
    have he : (S.r s t + (s - σ) / 2) ^ (-3 : ℝ) =
        (S.r s t + (s - σ) / 2) ^ (-1 : ℝ) * (S.r s t + (s - σ) / 2) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add (hpos σ hσ)]
      norm_num
    have hrad : chartPotential S σ t ≤
        (4 * P / S.r s t) * (S.r s t + (s - σ) / 2) ^ (-2 : ℝ) := by
      calc
        _ ≤ 4 * P * (S.r s t + (s - σ) / 2) ^ (-3 : ℝ) :=
          hpot.trans (mul_le_mul_of_nonneg_left hpow3 (by positivity))
        _ = (4 * P * (S.r s t + (s - σ) / 2) ^ (-1 : ℝ)) *
            (S.r s t + (s - σ) / 2) ^ (-2 : ℝ) := by rw [he]; ring
        _ ≤ (4 * P * S.r s t ^ (-1 : ℝ)) * (S.r s t + (s - σ) / 2) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 (by positivity))
            (Real.rpow_nonneg (hpos σ hσ).le _)
        _ = _ := by rw [Real.rpow_neg_one]; ring
    have hh := mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg (s - σ))
    rw [Real.rpow_neg (hpos σ hσ).le 2, Real.rpow_two] at hh
    simpa only [div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using hh)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (incoming_affine_oscillation_integral_le hp.2 hp.1.2.2.2)
    (show 0 ≤ 4 * P / S.r s t from div_nonneg (by positivity) hp.2.le))

end PropA4
end AcExtensionPrinciple

end
