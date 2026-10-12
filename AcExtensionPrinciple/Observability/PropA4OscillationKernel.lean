module

public import AcExtensionPrinciple.Observability.PropA4VolterraDomination
public import AcExtensionPrinciple.Observability.Oscillation

/-!
# Time oscillation of the concrete exterior Volterra kernel

Paper `e1a0fd5`, `eq:observability-time-oscillation-kernel`, lines 1749–1752.
The chart calculation has the exact coefficient `2π√2 M*/√r`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set Filter MeasureTheory

/-- Restrict the exact infinite time-oscillation integral to a finite
characteristic interval. Paper `e1a0fd5`, lines 1749–1752. -/
theorem incoming_affine_oscillation_integral_le {r t s : ℝ}
    (hr : 0 < r) (hts : t ≤ s) :
    (∫ σ in t..s, Real.sqrt (s - σ) / (r + (s - σ) / 2) ^ 2) ≤
      Real.pi * Real.sqrt 2 / Real.sqrt r := by
  let F := fun ξ : ℝ => Real.sqrt ξ / (r + ξ / 2) ^ 2
  have he := observability_time_oscillation_integral hr
  have hi : IntegrableOn F (Ioi 0) := by
    by_contra hn
    have hz := integral_undef hn
    change (∫ ξ in Ioi 0, F ξ) = _ at he
    rw [hz] at he
    have hp : 0 < Real.pi * Real.sqrt 2 / Real.sqrt r := by positivity
    linarith
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    exact div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hm := setIntegral_mono_set hi hnon
    (Ioc_subset_Ioi_self : Ioc 0 (s - t) ⊆ Ioi 0).eventuallySubset
  rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hts)] at hm
  rw [intervalIntegral.integral_comp_sub_left F s, sub_self]
  exact hm.trans_eq he

/-- The time-oscillation bound for the actual chart potential.
Paper `e1a0fd5`, `eq:observability-time-oscillation-kernel`, lines 1749–1752. -/
theorem volterra_time_oscillation_kernel_le {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => Real.sqrt (s - p.1)) s t ≤
        2 * P * (Real.pi * Real.sqrt 2 / Real.sqrt (S.r s t)) := by
  have hts := hpoint.1.2.2.2
  have htri := h.volterra_triangle_subset ht hpoint
  have hPc := continuous_potential_on h htri
  have hsqrt : Continuous (fun p : ℝ × ℝ => Real.sqrt (s - p.1)) := by fun_prop
  have hi : IntervalIntegrable
      (fun σ => ∫ z in t..σ, chartPotential S σ z * Real.sqrt (s - σ)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral (hPc.mul hsqrt.continuousOn)
  have hpos : ∀ σ ∈ Icc t s, 0 < S.r s t + (s - σ) / 2 := by
    intro σ hσ
    linarith [hpoint.2, hσ.2]
  have hj : IntervalIntegrable
      (fun σ => 2 * P * (Real.sqrt (s - σ) / (S.r s t + (s - σ) / 2) ^ 2)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    apply continuousOn_const.mul
    apply (show Continuous (fun σ : ℝ => Real.sqrt (s - σ)) by fun_prop).continuousOn.div
      (show Continuous (fun σ : ℝ => (S.r s t + (s - σ) / 2) ^ 2) by fun_prop).continuousOn
    exact fun σ hσ => pow_ne_zero _ (hpos σ hσ).ne'
  have hb := intervalIntegral.integral_mono_on hts hi hj (fun σ hσ => by
    have hσpoint := htri (show (σ, t) ∈ chartTriangle t s from ⟨le_rfl, hσ.1, hσ.2⟩)
    have hrord := (h.volterra_radius_order ht hpoint hσ ⟨le_rfl, hσ.1⟩).1
    have he := outgoing_power_kernel_le (q := 0) h hP ht hσpoint (hcut.trans hrord) hmass
      (by norm_num)
    norm_num only [Real.rpow_zero, mul_one, sub_zero] at he
    have hsep := incoming_radius_separation h hP ht hpoint hcut hmass hσ
    have hpow := Real.rpow_le_rpow_of_nonpos (hpos σ hσ) hsep (by norm_num : (-2 : ℝ) ≤ 0)
    rw [intervalIntegral.integral_mul_const]
    calc
      _ ≤ (4 * P / 2 * S.r σ t ^ (-2 : ℝ)) * Real.sqrt (s - σ) :=
        mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _)
      _ ≤ (4 * P / 2 * (S.r s t + (s - σ) / 2) ^ (-2 : ℝ)) * Real.sqrt (s - σ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
          (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.rpow_neg (hpos σ hσ).le, Real.rpow_two]
        ring)
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (incoming_affine_oscillation_integral_le hpoint.2 hts) (by positivity))

end PropA4
end AcExtensionPrinciple

end
