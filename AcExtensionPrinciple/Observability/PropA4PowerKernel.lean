module

public import AcExtensionPrinciple.Observability.PropA4Exterior
public import AcExtensionPrinciple.Observability.PowerIntegrals

/-!
# Radial power estimates for the exterior Volterra kernel

Paper `e1a0fd5`, `eq:observability-power-operator-bound`, lines 1734–1747.
The characteristic change of variable is obtained from the radius
primitive, with all regularity supplied by the normalized chart.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Integrate a radial power against the outgoing expansion. The
primitive and continuity premises are supplied by the chart equations.
Paper `e1a0fd5`, lines 1734–1747. -/
theorem radial_power_integral {R L : ℝ → ℝ} {a c q : ℝ}
    (hac : a ≤ c) (hR : ContinuousOn R (Icc a c))
    (hL : ContinuousOn L (Icc a c)) (hpos : ∀ z ∈ Icc a c, 0 < R z)
    (hprim : ∀ z ∈ Icc a c, IntervalPrimitive R L a z) (hq : q < 2) :
    (∫ z in a..c, L z * R z ^ (q - 3)) =
      (R a ^ (q - 2) - R c ^ (q - 2)) / (2 - q) := by
  have hq0 : q - 2 ≠ 0 := by linarith
  have hq1 : 2 - q ≠ 0 := by linarith
  have hder (z : ℝ) (hz : z ∈ Ioo a c) :
      HasDerivAt (fun z => R z ^ (q - 2) / (q - 2)) (L z * R z ^ (q - 3)) z := by
    have hd := intervalPrimitive_hasDerivAt hz hL hprim
    convert (hd.rpow_const (p := q - 2) (Or.inl (hpos z ⟨hz.1.le, hz.2.le⟩).ne')).div_const
      (q - 2) using 1
    norm_num only [sub_sub]
    field_simp
  have hcont : ContinuousOn (fun z => R z ^ (q - 2) / (q - 2)) (Icc a c) :=
    (hR.rpow_const (by intro z hz; exact Or.inl (hpos z hz).ne')).div_const _
  have hint : IntervalIntegrable (fun z => L z * R z ^ (q - 3)) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hac]
    exact hL.mul (hR.rpow_const (by intro z hz; exact Or.inl (hpos z hz).ne'))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac hcont hder hint]
  field_simp [hq0, hq1]
  ring

/-- Dropping the upper-endpoint term gives the outgoing power tail.
Paper `e1a0fd5`, lines 1734–1747. -/
theorem radial_power_integral_le {R L : ℝ → ℝ} {a c q : ℝ}
    (hac : a ≤ c) (hR : ContinuousOn R (Icc a c))
    (hL : ContinuousOn L (Icc a c)) (hpos : ∀ z ∈ Icc a c, 0 < R z)
    (hprim : ∀ z ∈ Icc a c, IntervalPrimitive R L a z) (hq : q < 2) :
    (∫ z in a..c, L z * R z ^ (q - 3)) ≤ R a ^ (q - 2) / (2 - q) := by
  rw [radial_power_integral hac hR hL hpos hprim hq]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have hh := Real.rpow_nonneg (hpos c ⟨hac, le_rfl⟩).le (q - 2)
  linarith

/-- The potential is continuous on compact chart sets away from the
axis. Paper `e1a0fd5`, lines 1734–1747. -/
theorem continuous_potential_on {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) {C : Set (ℝ × ℝ)}
    (hC : C ⊆ chartInterior (chartCylinder h.g T) S) :
    ContinuousOn (fun q => chartPotential S q.1 q.2) C := by
  have hr := h.continuous_r.mono (fun q hq => (hC hq).1)
  have hm := h.continuous_m.mono (fun q hq => (hC hq).1)
  have hl := h.continuous_lam.mono (fun q hq => (hC hq).1)
  have hn := h.continuous_nu.mono (fun q hq => (hC hq).1)
  have hμ : ContinuousOn (fun q => S.mu q.1 q.2) C :=
    (continuousOn_const.mul hm).div hr (fun q hq => (hC hq).2.ne')
  exact (((hμ.mul hn).mul hl).div
    ((continuousOn_const.sub hμ).mul (hr.pow 2)) (fun q hq =>
      mul_ne_zero (h.gap_pos (hC hq).1).ne' (pow_ne_zero _ (hC hq).2.ne'))).neg

/-- The inner outgoing integral in the actual chart has the printed
power-tail bound. Paper `e1a0fd5`, `eq:observability-power-operator-bound`,
lines 1734–1747. -/
theorem outgoing_power_kernel_le {b T K P s t q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hpoint : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 2) :
    (∫ z in t..s, chartPotential S s z * S.r s z ^ q) ≤
      4 * P / (2 - q) * S.r s t ^ (q - 2) := by
  have hts := hpoint.1.2.2.2
  have htri := h.volterra_triangle_subset ht hpoint
  have hseg : outSeg s t s ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_out_subset le_rfl le_rfl le_rfl).trans htri
  have hmap : MapsTo (fun z => (s, z)) (Icc t s)
      (chartInterior (chartCylinder h.g T) S) := fun z hz =>
    hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
  have hR : ContinuousOn (S.r s) (Icc t s) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => (hmap hz).1)
  have hL : ContinuousOn (S.lam s) (Icc t s) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => (hmap hz).1)
  have hpos : ∀ z ∈ Icc t s, 0 < S.r s z := fun z hz => (hmap hz).2
  have hprim : ∀ z ∈ Icc t s, IntervalPrimitive (S.r s) (S.lam s) t z :=
    fun z hz => h.equations.radius_t s t z hz.1
      (fun p hp => (hseg (show p ∈ outSeg s t s from
        ⟨hp.1, hp.2.1, hp.2.2.trans hz.2⟩)).1)
  have hPc : ContinuousOn (fun z => chartPotential S s z) (Icc t s) :=
    (continuous_potential_on (C := chartTriangle t s) h htri).comp
      (f := fun z : ℝ => (s, z))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hz.1, hz.2, le_rfl⟩)
  have hqcont := hR.rpow_const (p := q) (by intro z hz; exact Or.inl (hpos z hz).ne')
  have htailcont := hR.rpow_const (p := q - 3)
    (by intro z hz; exact Or.inl (hpos z hz).ne')
  have hi : IntervalIntegrable (fun z => chartPotential S s z * S.r s z ^ q) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact hPc.mul hqcont
  have hj : IntervalIntegrable (fun z => 4 * P * (S.lam s z * S.r s z ^ (q - 3)))
      volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact continuousOn_const.mul (hL.mul htailcont)
  have hb := intervalIntegral.integral_mono_on hts hi hj (fun z hz => by
    have hrord := (h.volterra_radius_order ht hpoint ⟨hts, le_rfl⟩ hz).2
    have he := potential_le_radial_density h hP (ht.trans hz.1) (hmap hz)
      (hcut.trans hrord) hmass
    have hmul := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (hpos z hz).le q)
    calc
      _ ≤ (4 * P * S.lam s z / S.r s z ^ 3) * S.r s z ^ q := hmul
      _ = _ := by
        rw [Real.rpow_sub (hpos z hz)]
        rw [show S.r s z ^ (3 : ℝ) = S.r s z ^ (3 : ℕ) from Real.rpow_natCast _ _]
        ring)
  rw [intervalIntegral.integral_const_mul] at hb
  have htail := radial_power_integral_le hts hR hL hpos hprim hq
  calc
    _ ≤ 4 * P * (∫ z in t..s, S.lam s z * S.r s z ^ (q - 3)) := hb
    _ ≤ 4 * P * (S.r s t ^ (q - 2) / (2 - q)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end PropA4
end AcExtensionPrinciple

end
