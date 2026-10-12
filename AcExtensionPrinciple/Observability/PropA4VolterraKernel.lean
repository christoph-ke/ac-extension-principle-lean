module

public import AcExtensionPrinciple.Observability.PropA4PowerKernel
public import AcExtensionPrinciple.Observability.VolterraBounds

/-!
# The weighted Volterra estimate in a normalized chart

Paper `e1a0fd5`, `eq:observability-power-operator-bound`, lines 1734–1747.
Both integrations are performed on the concrete characteristic triangle;
the constants are independent of its duration and outer radius.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The finite incoming affine-radius integral is bounded by the
printed infinite tail. Paper `e1a0fd5`, lines 1742–1747. -/
theorem incoming_affine_power_integral_le {r t s q : ℝ}
    (hr : 0 < r) (hts : t ≤ s) (hq : q < 1) :
    (∫ σ in t..s, (r + (s - σ) / 2) ^ (q - 2)) ≤
      2 * r ^ (q - 1) / (1 - q) := by
  have hq0 : 1 - q ≠ 0 := by linarith
  have hpos : ∀ σ ∈ Icc t s, 0 < r + (s - σ) / 2 := by
    intro σ hσ
    linarith [hσ.2]
  have hbase : Continuous (fun σ : ℝ => r + (s - σ) / 2) := by fun_prop
  have hder (σ : ℝ) (hσ : σ ∈ Ioo t s) :
      HasDerivAt (fun σ => 2 * (r + (s - σ) / 2) ^ (q - 1) / (1 - q))
        ((r + (s - σ) / 2) ^ (q - 2)) σ := by
    have hd : HasDerivAt (fun σ : ℝ => r + (s - σ) / 2) (-1 / 2) σ := by
      convert (((hasDerivAt_const σ s).sub (hasDerivAt_id σ)).div_const 2).const_add r using 1 <;>
        simp
    convert ((hd.rpow_const (p := q - 1)
      (Or.inl (hpos σ ⟨hσ.1.le, hσ.2.le⟩).ne')).const_mul 2).div_const (1 - q) using 1
    norm_num only [sub_sub]
    field_simp [hq0]
    ring
  have hcont : ContinuousOn
      (fun σ => 2 * (r + (s - σ) / 2) ^ (q - 1) / (1 - q)) (Icc t s) :=
    ((hbase.continuousOn.rpow_const
      (by intro σ hσ; exact Or.inl (hpos σ hσ).ne')).const_mul 2).div_const _
  have hi : IntervalIntegrable (fun σ => (r + (s - σ) / 2) ^ (q - 2)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact hbase.continuousOn.rpow_const
      (by intro σ hσ; exact Or.inl (hpos σ hσ).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hts hcont hder hi]
  simp only [sub_self, zero_div, add_zero]
  have hn : 0 ≤ 2 * (r + (s - t) / 2) ^ (q - 1) / (1 - q) := by positivity
  linarith

/-- The inner integral of a continuous triangular kernel depends
continuously on the incoming time. Paper `e1a0fd5`, lines 1734–1747. -/
theorem continuousOn_outgoing_kernel_integral {F : ℝ × ℝ → ℝ} {t s : ℝ}
    (hF : ContinuousOn F (chartTriangle t s)) :
    ContinuousOn (fun σ => ∫ z in t..σ, F (σ, z)) (Icc t s) := by
  obtain ⟨G, hG, heq⟩ := chartTriangle_continuous_extension hF
  have hc : Continuous (fun σ => ∫ z in t..σ, G (σ, z)) :=
    continuous_moving_interval_integral hG continuous_const continuous_id
  apply hc.continuousOn.congr
  intro σ hσ
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hσ.1] at hz
  exact (heq (σ, z) ⟨hz.1, hz.2, hσ.2⟩).symm

/-- The exact power estimate for the chart's actual Volterra operator.
Paper `e1a0fd5`, `eq:observability-power-operator-bound`, lines 1742–1747. -/
theorem volterra_power_kernel_le {b T K P s t q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) :
    triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => S.r p.1 p.2 ^ q) s t ≤
        8 * P / ((2 - q) * (1 - q)) * S.r s t ^ (q - 1) := by
  have hts := hpoint.1.2.2.2
  have hcoef : 0 ≤ 4 * P / (2 - q) := div_nonneg (by positivity) (by linarith)
  have htri := h.volterra_triangle_subset ht hpoint
  have hR := h.continuous_r.mono (fun p hp => (htri hp).1)
  have hRc := hR.rpow_const (p := q) (by intro p hp; exact Or.inl (htri hp).2.ne')
  have hF := (continuous_potential_on h htri).mul hRc
  have hi : IntervalIntegrable
      (fun σ => ∫ z in t..σ, chartPotential S σ z * S.r σ z ^ q) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_outgoing_kernel_integral hF
  have hpos : ∀ σ ∈ Icc t s, 0 < S.r s t + (s - σ) / 2 := by
    intro σ hσ
    linarith [hpoint.2, hσ.2]
  have hbase : Continuous (fun σ : ℝ => S.r s t + (s - σ) / 2) := by fun_prop
  have hj : IntervalIntegrable
      (fun σ => 4 * P / (2 - q) * (S.r s t + (s - σ) / 2) ^ (q - 2)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_const.mul (hbase.continuousOn.rpow_const
      (by intro σ hσ; exact Or.inl (hpos σ hσ).ne'))
  have hb := intervalIntegral.integral_mono_on hts hi hj (fun σ hσ => by
    have hσpoint := htri (show (σ, t) ∈ chartTriangle t s from ⟨le_rfl, hσ.1, hσ.2⟩)
    have hrord := (h.volterra_radius_order ht hpoint hσ ⟨le_rfl, hσ.1⟩).1
    have he := outgoing_power_kernel_le h hP ht hσpoint (hcut.trans hrord) hmass
      (show q < 2 by linarith)
    have hsep := incoming_radius_separation h hP ht hpoint hcut hmass hσ
    exact he.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (hpos σ hσ) hsep (by linarith)) hcoef))
  rw [intervalIntegral.integral_const_mul] at hb
  change (∫ σ in t..s, ∫ z in t..σ, chartPotential S σ z * S.r σ z ^ q) ≤ _
  calc
    _ ≤ 4 * P / (2 - q) *
        (∫ σ in t..s, (S.r s t + (s - σ) / 2) ^ (q - 2)) := hb
    _ ≤ 4 * P / (2 - q) * (2 * S.r s t ^ (q - 1) / (1 - q)) :=
      mul_le_mul_of_nonneg_left (incoming_affine_power_integral_le hpoint.2 hts hq)
        hcoef
    _ = _ := by field_simp; ring

/-- The exterior cutoff turns the power estimate into its exact
dimensionless operator coefficient. Paper `e1a0fd5`, lines 1742–1747. -/
theorem exterior_power_coefficient_le {P r q : ℝ}
    (hr : 0 < r) (hcut : 32 * P ≤ r) (hq : q < 1) :
    8 * P / ((2 - q) * (1 - q)) * r ^ (q - 1) ≤
      1 / (4 * (2 - q) * (1 - q)) * r ^ q := by
  have hratio : 8 * P / r ≤ 1 / 4 := by
    rw [div_le_iff₀ hr]
    linarith
  have hden : 0 < (2 - q) * (1 - q) := mul_pos (by linarith) (by linarith)
  calc
    _ = ((8 * P / r) / ((2 - q) * (1 - q))) * r ^ q := by
      rw [Real.rpow_sub hr, Real.rpow_one]
      ring
    _ ≤ ((1 / 4) / ((2 - q) * (1 - q))) * r ^ q :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hratio hden.le)
        (Real.rpow_nonneg hr.le q)
    _ = _ := by field_simp

/-- The weighted pointwise operator coefficient for the actual chart.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem volterra_power_coefficient_le {b T K P s t q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) :
    triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => S.r p.1 p.2 ^ q) s t ≤
        1 / (4 * (2 - q) * (1 - q)) * S.r s t ^ q :=
  (volterra_power_kernel_le h hP ht hpoint hcut hmass hq).trans
    (exterior_power_coefficient_le hpoint.2 hcut hq)

/-- The concrete unweighted operator coefficient is `1/8`.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem volterra_unit_coefficient_le {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    triangleVolterra (fun p => chartPotential S p.1 p.2) (fun _ => 1) s t ≤ 1 / 8 := by
  have hh := volterra_power_coefficient_le (q := 0) h hP ht hpoint hcut hmass (by norm_num)
  norm_num only [Real.rpow_zero] at hh
  norm_num at hh ⊢
  exact hh

/-- The concrete half-power operator coefficient is `1/3`.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem volterra_half_power_coefficient_le {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => S.r p.1 p.2 ^ (1 / 2 : ℝ)) s t ≤ (1 / 3) * S.r s t ^ (1 / 2 : ℝ) := by
  have hh := volterra_power_coefficient_le (q := 1 / 2) h hP ht hpoint hcut hmass (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- The concrete negative-half-power operator coefficient is `1/15`.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem volterra_neg_half_power_coefficient_le {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    triangleVolterra (fun p => chartPotential S p.1 p.2)
      (fun p => S.r p.1 p.2 ^ (-1 / 2 : ℝ)) s t ≤ (1 / 15) * S.r s t ^ (-1 / 2 : ℝ) := by
  have hh := volterra_power_coefficient_le (q := -1 / 2) h hP ht hpoint hcut hmass (by norm_num)
  norm_num at hh ⊢
  exact hh

end PropA4
end AcExtensionPrinciple

end
