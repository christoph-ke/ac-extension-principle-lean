module

public import AcExtensionPrinciple.Observability.PropA4Statements

/-!
# Axis labels and the boundary primitive

Paper `e1a0fd5`, `eq:observability-axis-label-bounds`,
`eq:observability-amplitude`, `eq:observability-boundary-primitive`,
`equations.tex` lines 1692–1711. The label and primitive estimates are
derived from the chart and its finite boundary energy.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- All late axis labels are nonnegative, by the travel-time condition
and monotonicity of the axis graph. Paper `e1a0fd5`, lines 1692–1693. -/
theorem axis_label_nonneg {b T K s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T) (hlate : K * b ≤ s) :
    0 ≤ h.g s := by
  obtain ⟨s₀, hs₀, hg₀⟩ := h.axis_reached 0 ⟨le_rfl, h.T_nonneg⟩
    (by simpa using hlate.trans hs.2)
  have hs₀T : s₀ ∈ Icc 0 T :=
    ⟨hs₀.1, hs₀.2.trans (by simpa using hlate.trans hs.2)⟩
  have hle := h.monotone_g hs₀T hs (by linarith [hs₀.2])
  rwa [hg₀] at hle

/-- Radius and incoming-label distance are comparable on every late
slice, including the axis endpoint. Paper `e1a0fd5`,
`eq:observability-axis-label-bounds`, lines 1694–1698. -/
theorem radius_label_bounds {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hlate : K * b ≤ s)
    (hq : (s, t) ∈ chartCylinder h.g T) :
    (t - h.g s) / K ≤ S.r s t ∧ S.r s t ≤ t - h.g s := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hg0 := axis_label_nonneg h hs hlate
  have hgt := hq.2.2.1
  have hli : IntervalIntegrable (S.lam s) volume (h.g s) t :=
    (h.equations.radius_t s (h.g s) t hgt (h.out_subset hs le_rfl hq.2.2.2)).1
  have hbounds : ∀ᵐ z ∂volume.restrict (Icc (h.g s) t),
      K⁻¹ ≤ S.lam s z ∧ S.lam s z ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (by simp [ae_iff] : ∀ᵐ z : ℝ, z ≠ h.g s)] with z hz hne
    have hmem := h.out_subset hs le_rfl hq.2.2.2
      (show (s, z) ∈ outSeg s (h.g s) t from ⟨by simp, hz⟩)
    exact h.lam_bounds (hg0.trans hz.1)
      ⟨hmem, h.radius_pos hmem (lt_of_le_of_ne hz.1 (Ne.symm hne))⟩
  have hlo := intervalIntegral.integral_mono_ae_restrict hgt
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K⁻¹) volume (h.g s) t)
    hli (hbounds.mono (fun _ hh => hh.1))
  have hup := intervalIntegral.integral_mono_ae_restrict hgt hli
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (h.g s) t)
    (hbounds.mono (fun _ hh => hh.2))
  rw [intervalIntegral.integral_const] at hlo hup
  rw [h.radius_from_axis hq]
  constructor
  · simpa only [smul_eq_mul, div_eq_mul_inv] using hlo
  · simpa only [smul_eq_mul, mul_one] using hup

/-- The boundary primitive has squared size at most `KrE`. Paper
`e1a0fd5`, `eq:observability-boundary-primitive`, lines 1705–1711. -/
theorem boundary_primitive_sq {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hlate : K * b ≤ s)
    (hq : (s, t) ∈ chartCylinder h.g T) :
    (∫ z in h.g s..t, S.dvpsi z z) ^ 2 ≤ K * S.r s t * chartScalarEnergy S T := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hg0 := axis_label_nonneg h hs hlate
  have hgt := hq.2.2.1
  have htT := hq.2.2.2.trans hs.2
  have hsub : uIcc (h.g s) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le hgt, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hg0 htT
  have hcs := primitive_sq_le hgt (h.boundary_dvpsi_integrable.mono_set hsub)
    (h.boundary_scalar_square_integrable.2.mono_set hsub)
  have hmono : (∫ z in h.g s..t, S.dvpsi z z ^ 2) ≤ chartScalarEnergy S T := by
    have hh := intervalIntegral.integral_mono_interval hg0 hgt htT
      (Filter.Eventually.of_forall (fun z => sq_nonneg (S.dvpsi z z)))
      h.boundary_scalar_square_integrable.2
    unfold chartScalarEnergy
    rw [intervalIntegral.integral_add h.boundary_scalar_square_integrable.2
      h.boundary_psi_deriv_square_integrable]
    have hy : 0 ≤ ∫ z in 0..T, deriv (fun s => chartPsi S s s) z ^ 2 :=
      intervalIntegral.integral_nonneg h.T_nonneg (by intros; positivity)
    linarith
  have hK0 : 0 < K := by linarith [h.K_ge_one]
  have hlen := (div_le_iff₀ hK0).mp (radius_label_bounds h hlate hq).1
  exact hcs.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hgt)).trans
    (mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hlen) h.scalar_energy_nonneg))

/-- The displayed square-root bound for the boundary primitive. Paper
`e1a0fd5`, `eq:observability-boundary-primitive`, lines 1705–1711. -/
theorem boundary_primitive_bound {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hlate : K * b ≤ s)
    (hq : (s, t) ∈ chartCylinder h.g T) :
    |∫ z in h.g s..t, S.dvpsi z z| ≤ Real.sqrt (K * S.r s t * chartScalarEnergy S T) := by
  have hh := boundary_primitive_sq h hlate hq
  exact (Real.le_sqrt (abs_nonneg _) (le_trans (sq_nonneg _) hh)).mpr (by
    simpa only [sq_abs] using hh)

/-- The part of the free scalar representation independent of t. Paper
`e1a0fd5`, `eq:observability-amplitude`, lines 1700–1703. -/
@[expose] noncomputable def amplitude {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (s : ℝ) : ℝ :=
  chartPsi S s s - ∫ z in h.g s..s, S.dvpsi z z

/-- Exact Volterra representation split into its t-independent amplitude
and the primitive vanishing at the axis. Paper `e1a0fd5`,
`eq:observability-amplitude`, `eq:observability-scalar-decomposition`,
lines 1700–1703 and 1766–1769. -/
theorem volterra_amplitude {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hlate : K * b ≤ s)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    chartPsi S s t = amplitude h s + (∫ z in h.g s..t, S.dvpsi z z) +
      triangleVolterra (fun q => chartPotential S q.1 q.2)
        (fun q => chartPsi S q.1 q.2) s t := by
  have hg0 := axis_label_nonneg h ⟨hq.1.1, hq.1.2.1⟩ hlate
  have hgt := hq.1.2.2.1
  have hts := hq.1.2.2.2
  have hsub₁ : uIcc (h.g s) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le hgt, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hg0 (hts.trans hq.1.2.1)
  have hsub₂ : uIcc t s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hts, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc (hg0.trans hgt) hq.1.2.1
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (h.boundary_dvpsi_integrable.mono_set hsub₁)
    (h.boundary_dvpsi_integrable.mono_set hsub₂)
  rw [h.volterra (hg0.trans hgt) hq]
  unfold amplitude
  linarith

end PropA4
end AcExtensionPrinciple

end
