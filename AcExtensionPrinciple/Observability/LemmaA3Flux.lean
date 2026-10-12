module

public import AcExtensionPrinciple.Observability.LemmaA2
public import AcExtensionPrinciple.Observability.Annulus

/-!
# Lemma A.3: boundary mass flux

This module proves boundary mass-flux identities for Lemma A.3.
Paper `e1a0fd5`, `equations.tex` lines 1543–1663,
`eq:observability-boundary-mass-flux`. The fluxes use characteristic
amplitudes, which equal the radial amplitudes at the normalized boundary.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Incoming boundary mass flux density. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1552. -/
@[expose] noncomputable def chartIncomingFluxDensity (S : SSFields) (s : ℝ) : ℝ :=
  (1 - S.mu s s) / 2 * S.theta s s ^ 2

/-- Outgoing boundary mass flux density. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1552. -/
@[expose] noncomputable def chartOutgoingFluxDensity (S : SSFields) (s : ℝ) : ℝ :=
  (1 - S.mu s s) / 2 * S.zeta s s ^ 2

/-- Full incoming mass flux. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1552. -/
@[expose] noncomputable def chartIncomingFlux (S : SSFields) (T : ℝ) : ℝ :=
  ∫ s in 0..T, chartIncomingFluxDensity S s

/-- Full outgoing mass flux. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1552. -/
@[expose] noncomputable def chartOutgoingFlux (S : SSFields) (T : ℝ) : ℝ :=
  ∫ s in 0..T, chartOutgoingFluxDensity S s

/-- Total boundary mass flux. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1552. -/
@[expose] noncomputable def chartMassFlux (S : SSFields) (T : ℝ) : ℝ :=
  chartIncomingFlux S T + chartOutgoingFlux S T

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The mass is nonnegative, including the regular axis. Paper `e1a0fd5`,
`equations.tex` line 1553, `eq:observability-boundary-mass-flux`. -/
theorem mass_nonneg {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) : 0 ≤ S.m s t := by
  rcases hq.2.2.1.eq_or_lt with he | he
  · change h.g s = t at he
    rw [← he, (h.axis_values s ⟨hq.1, hq.2.1⟩).2]
  · have hr := h.radius_pos hq he
    have hm := (h.signs s t hq).2.2
    change 0 ≤ 2 * S.m s t / S.r s t at hm
    have := (le_div_iff₀ hr).mp hm
    linarith

/-- Both boundary mass flux densities have integrable squares of amplitudes
and continuous coefficients. Paper `e1a0fd5`, lines 1546–1553, 1522. -/
theorem flux_density_integrable :
    IntervalIntegrable (chartIncomingFluxDensity S) volume 0 T ∧
      IntervalIntegrable (chartOutgoingFluxDensity S) volume 0 T := by
  have hcφ : ContinuousOn (fun s => S.phi s s) (uIcc 0 T) := by
    rw [uIcc_of_le h.T_nonneg]
    exact h.continuous_phi.comp (continuous_id.prodMk continuous_id).continuousOn
      (fun s hs => h.boundary_mem hs)
  have hφ2 := (hcφ.pow 2).intervalIntegrable (μ := volume)
  have hμ : ContinuousOn (fun s => (1 - S.mu s s) / 2) (uIcc 0 T) := by
    have hm := h.boundary_traces_ac.2.continuousOn
    have hc : ContinuousOn (fun s => (1 - 2 * S.m s s / b) / 2) (uIcc 0 T) :=
      (continuousOn_const.sub ((hm.const_mul 2).div_const b)).div_const 2
    apply hc.congr
    intro s hs
    rw [uIcc_of_le h.T_nonneg] at hs
    simp only [SSFields.mu, (h.boundary_gauge s hs).1, massRatio]
  obtain ⟨hU, hV⟩ := h.boundary_scalar_square_integrable
  have hθm := ((hV.add hφ2).const_mul 2).mul_continuousOn hμ
  have hζm := ((hU.add hφ2).const_mul 2).mul_continuousOn hμ
  have hUmeas : AEStronglyMeasurable (fun s => S.dupsi s s) (volume.restrict (uIoc 0 T)) := (h.boundary_traces_ac.1.intervalIntegrable_deriv.def'.aestronglyMeasurable.sub
    h.boundary_dvpsi_integrable.def'.aestronglyMeasurable).congr (by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le h.T_nonneg]
      filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs hsI
      change deriv (fun s => chartPsi S s s) s - S.dvpsi s s = S.dupsi s s
      rw [(hs ⟨hsI.1.le, hsI.2⟩).deriv]
      simp)
  have hVmeas := h.boundary_dvpsi_integrable.def'.aestronglyMeasurable
  have hφmeas : AEStronglyMeasurable (fun s => S.phi s s) (volume.restrict (uIoc 0 T)) := hcφ.aestronglyMeasurable measurableSet_uIcc |>.mono_set uIoc_subset_uIcc
  have hμmeas : AEStronglyMeasurable (fun s => (1 - S.mu s s) / 2) (volume.restrict (uIoc 0 T)) := hμ.aestronglyMeasurable measurableSet_uIcc |>.mono_set uIoc_subset_uIcc
  have hIm : AEStronglyMeasurable (chartIncomingFluxDensity S) (volume.restrict (uIoc 0 T)) := by
    apply (hμmeas.mul ((hVmeas.sub hφmeas).pow 2)).congr
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le h.T_nonneg]
    filter_upwards with s hs
    simp [chartIncomingFluxDensity, SSFields.theta, (h.boundary_gauge s ⟨hs.1.le, hs.2⟩).2.2]
  have hOm : AEStronglyMeasurable (chartOutgoingFluxDensity S) (volume.restrict (uIoc 0 T)) := by
    apply (hμmeas.mul ((hUmeas.add hφmeas).pow 2)).congr
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le h.T_nonneg]
    filter_upwards with s hs
    simp [chartOutgoingFluxDensity, SSFields.zeta, (h.boundary_gauge s ⟨hs.1.le, hs.2⟩).2.1]
  constructor
  · apply hθm.mono_fun' hIm
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le h.T_nonneg]
    filter_upwards with s hs
    have hb := h.boundary_gauge s ⟨hs.1.le, hs.2⟩
    have hg := (h.gap_pos (h.boundary_mem ⟨hs.1.le, hs.2⟩)).le
    simp only [chartIncomingFluxDensity, SSFields.theta, hb.2.2, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (1 - S.mu s s) / 2)
        (sq_nonneg _)), Pi.pow_apply]
    nlinarith [mul_nonneg hg (sq_nonneg (S.dvpsi s s + S.phi s s))]
  · apply hζm.mono_fun' hOm
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le h.T_nonneg]
    filter_upwards with s hs
    have hb := h.boundary_gauge s ⟨hs.1.le, hs.2⟩
    have hg := (h.gap_pos (h.boundary_mem ⟨hs.1.le, hs.2⟩)).le
    simp only [chartOutgoingFluxDensity, SSFields.zeta, hb.2.1, neg_mul, one_mul,
      sub_neg_eq_add, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (1 - S.mu s s) / 2) (sq_nonneg _)),
      Pi.pow_apply]
    nlinarith [mul_nonneg hg (sq_nonneg (S.dupsi s s - S.phi s s))]

/-- Both full mass fluxes are nonnegative. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1553. -/
theorem flux_nonneg : 0 ≤ chartIncomingFlux S T ∧ 0 ≤ chartOutgoingFlux S T := by
  constructor <;> apply intervalIntegral.integral_nonneg h.T_nonneg <;> intro s hs
  · exact mul_nonneg (by linarith [h.gap_pos (h.boundary_mem hs)]) (sq_nonneg _)
  · exact mul_nonneg (by linarith [h.gap_pos (h.boundary_mem hs)]) (sq_nonneg _)

/-- Boundary mass balance in terms of the two physical fluxes. Paper `e1a0fd5`,
`eq:observability-boundary-mass-flux`, lines 1546–1553. -/
theorem boundary_mass_flux_balance {s : ℝ} (hs : s ∈ Icc 0 T) :
    S.m s s - S.m 0 0 =
      (∫ u in 0..s, chartIncomingFluxDensity S u) -
        (∫ u in 0..s, chartOutgoingFluxDensity S u) := by
  have hsub : uIcc 0 s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hs.1, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc le_rfl hs.2
  have hac := h.boundary_traces_ac.2.mono hsub
  have hd : ∀ᵐ u, u ∈ Ioo 0 s → HasDerivAt (fun u => S.m u u)
      (chartIncomingFluxDensity S u - chartOutgoingFluxDensity S u) u := by
    filter_upwards [h.boundary_mass_ae_hasDerivAt] with u hu huI
    have huT : u ∈ Icc 0 T := ⟨huI.1.le, huI.2.le.trans hs.2⟩
    apply (hu huT).congr_deriv
    simp [SSFields.massU, SSFields.massV, chartIncomingFluxDensity, chartOutgoingFluxDensity,
      (h.boundary_gauge u huT).2.1, (h.boundary_gauge u huT).2.2]
    ring
  rw [(ac_integral_eq_sub hs.1 hac hd).2,
    intervalIntegral.integral_sub (h.flux_density_integrable.1.mono_set hsub)
      (h.flux_density_integrable.2.mono_set hsub)]

/-- The incoming flux provides a uniform upper mass bound; outgoing flux
provides the lower boundary mass bound. Paper `e1a0fd5`, line 1553. -/
theorem mass_flux_bounds {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    0 ≤ S.m s t ∧ S.m s t ≤ S.m 0 0 + chartIncomingFlux S T ∧
      S.m 0 0 - chartOutgoingFlux S T ≤ S.m s s := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hin : (∫ u in 0..s, chartIncomingFluxDensity S u) ≤ chartIncomingFlux S T := by
    apply intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 _ h.flux_density_integrable.1
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    exact mul_nonneg (by linarith [h.gap_pos (h.boundary_mem ⟨hu.1.le, hu.2⟩)]) (sq_nonneg _)
  have hout : (∫ u in 0..s, chartOutgoingFluxDensity S u) ≤ chartOutgoingFlux S T := by
    apply intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 _ h.flux_density_integrable.2
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    exact mul_nonneg (by linarith [h.gap_pos (h.boundary_mem ⟨hu.1.le, hu.2⟩)]) (sq_nonneg _)
  have hn := intervalIntegral.integral_nonneg (μ := volume) hs.1 (fun u hu =>
    mul_nonneg (show 0 ≤ (1 - S.mu u u) / 2 by
      linarith [h.gap_pos (h.boundary_mem ⟨hu.1, hu.2.trans hs.2⟩)]) (sq_nonneg (S.theta u u)))
  have ho := intervalIntegral.integral_nonneg (μ := volume) hs.1 (fun u hu =>
    mul_nonneg (show 0 ≤ (1 - S.mu u u) / 2 by
      linarith [h.gap_pos (h.boundary_mem ⟨hu.1, hu.2.trans hs.2⟩)]) (sq_nonneg (S.zeta u u)))
  change 0 ≤ ∫ u in 0..s, chartIncomingFluxDensity S u at hn
  change 0 ≤ ∫ u in 0..s, chartOutgoingFluxDensity S u at ho
  have he := h.boundary_mass_flux_balance hs
  refine ⟨h.mass_nonneg hq, (h.mass_le_boundary hq).trans ?_, ?_⟩ <;> linarith

end NormalizedChartData

end AcExtensionPrinciple

end
