module

public import AcExtensionPrinciple.Observability.LemmaA3Flux

/-!
# Lemma A.3: physical mass flux compared with the observation

Paper `e1a0fd5`, `equations.tex` lines 1650–1663. The initial amplitude
is controlled by Lemma A.2, uniformly under scalar translations.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- Uniform boundary amplitude bound from the axis amplitude and boundary
Cauchy–Schwarz. Paper `e1a0fd5`, lines 1650–1655. -/
theorem lemmaA3_boundary_amplitude (hT : K * b ≤ T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    chartPsi S s s ^ 2 ≤ 8 * T * chartScalarEnergy S T := by
  have hc := axis_amplitude_cauchy_schwarz (P := fun s => chartPsi S s s)
    (x := fun s => S.dvpsi s s) hs.1 le_rfl hs.2 h.boundary_traces_ac.1
    h.boundary_dvpsi_integrable h.boundary_scalar_square_integrable.2
    h.boundary_psi_deriv_square_integrable
  simp only [intervalIntegral.integral_same, abs_zero, add_zero] at hc
  change |chartPsi S s s - chartPsi S 0 0| ≤ Real.sqrt (2 * s * chartScalarEnergy S T) at hc
  have hE := h.scalar_energy_nonneg
  have hrad : 0 ≤ 2 * s * chartScalarEnergy S T :=
    mul_nonneg (mul_nonneg (by norm_num) hs.1) hE
  have hsq : (chartPsi S s s - chartPsi S 0 0) ^ 2 ≤ 2 * s * chartScalarEnergy S T := by
    nlinarith [sq_abs (chartPsi S s s - chartPsi S 0 0),
      Real.sq_sqrt hrad, Real.sqrt_nonneg (2 * s * chartScalarEnergy S T),
      abs_nonneg (chartPsi S s s - chartPsi S 0 0)]
  have ha := h.axis_amplitude hT
  rw [sq_abs] at ha
  have htime := mul_le_mul_of_nonneg_right hs.2 hE
  have htime' := mul_le_mul_of_nonneg_right hT hE
  nlinarith [sq_nonneg (chartPsi S s s - 2 * chartPsi S 0 0)]

/-- Pointwise mass flux compared with the actual observed scalar derivatives.
Paper `e1a0fd5`, boundary amplitude identities at lines 1656–1662. -/
theorem lemmaA3_flux_density_le {s : ℝ} (hs : s ∈ Icc 0 T)
    (hd : HasDerivAt (fun s => chartPsi S s s) (S.dupsi s s + S.dvpsi s s) s) :
    chartIncomingFluxDensity S s + chartOutgoingFluxDensity S s ≤
      3 * (S.dvpsi s s ^ 2 + deriv (fun s => chartPsi S s s) s ^ 2) +
        3 / b ^ 2 * chartPsi S s s ^ 2 := by
  have hb := h.boundary_gauge s hs
  have hgap := (h.gap_pos (h.boundary_mem hs)).le
  have hμ := (h.signs s s (h.boundary_mem hs)).2.2
  have hφ : chartPsi S s s / b = S.phi s s := by
    rw [chartPsi, hb.1, mul_div_cancel_left₀ _ h.b_pos.ne']
  have hθ : S.theta s s = S.dvpsi s s - chartPsi S s s / b := by
    simp [SSFields.theta, hb.2.2, hφ]
  have hζ : S.zeta s s = deriv (fun s => chartPsi S s s) s - S.theta s s := by
    rw [hd.deriv]
    simp only [SSFields.zeta, SSFields.theta, hb.2.1, hb.2.2]
    ring
  have hI : chartIncomingFluxDensity S s ≤ S.theta s s ^ 2 / 2 := by
    unfold chartIncomingFluxDensity
    nlinarith [mul_nonneg hμ (sq_nonneg (S.theta s s))]
  have hO : chartOutgoingFluxDensity S s ≤ S.zeta s s ^ 2 / 2 := by
    unfold chartOutgoingFluxDensity
    nlinarith [mul_nonneg hμ (sq_nonneg (S.zeta s s))]
  have hsθ : S.theta s s ^ 2 ≤ 2 * S.dvpsi s s ^ 2 + 2 * (chartPsi S s s / b) ^ 2 := by
    rw [hθ]
    nlinarith [sq_nonneg (S.dvpsi s s + chartPsi S s s / b)]
  have hsζ : S.zeta s s ^ 2 ≤ 2 * deriv (fun s => chartPsi S s s) s ^ 2 + 2 * S.theta s s ^ 2 := by
    rw [hζ]
    nlinarith [sq_nonneg (deriv (fun s => chartPsi S s s) s + S.theta s s)]
  have he : 3 / b ^ 2 * chartPsi S s s ^ 2 = 3 * (chartPsi S s s / b) ^ 2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (deriv (fun s => chartPsi S s s) s)]

/-- The physical boundary mass flux is bounded by a constant times
`(1+H²)E`, with explicit constant. Paper `e1a0fd5`, lines 1650–1663. -/
theorem lemmaA3_mass_flux_le_observation (hT : K * b ≤ T) :
    chartMassFlux S T ≤ (3 + 24 * (T / b) ^ 2) * chartScalarEnergy S T := by
  have hP : IntervalIntegrable (fun s => chartPsi S s s ^ 2) volume 0 T :=
    (h.boundary_traces_ac.1.continuousOn.pow 2).intervalIntegrable
  have hE := h.boundary_scalar_square_integrable.2.add h.boundary_psi_deriv_square_integrable
  have hmajor := (hE.const_mul 3).add (hP.const_mul (3 / b ^ 2))
  have hi : chartMassFlux S T ≤
      ∫ s in 0..T, 3 * (S.dvpsi s s ^ 2 + deriv (fun s => chartPsi S s s) s ^ 2) +
        3 / b ^ 2 * chartPsi S s s ^ 2 := by
    unfold chartMassFlux chartIncomingFlux chartOutgoingFlux
    rw [← intervalIntegral.integral_add h.flux_density_integrable.1 h.flux_density_integrable.2]
    apply intervalIntegral.integral_mono_ae_restrict h.T_nonneg
      (h.flux_density_integrable.1.add h.flux_density_integrable.2) hmajor
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs hsI
    exact h.lemmaA3_flux_density_le hsI (hs hsI)
  have hPbound : (∫ s in 0..T, chartPsi S s s ^ 2) ≤ 8 * T ^ 2 * chartScalarEnergy S T := by
    have hh := intervalIntegral.integral_mono_on h.T_nonneg hP intervalIntegrable_const
      (fun s hs => h.lemmaA3_boundary_amplitude hT hs)
    rw [intervalIntegral.integral_const] at hh
    simp only [sub_zero, smul_eq_mul] at hh
    nlinarith
  rw [intervalIntegral.integral_add (hE.const_mul 3) (hP.const_mul (3 / b ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  change chartMassFlux S T ≤ 3 * chartScalarEnergy S T +
    3 / b ^ 2 * (∫ s in 0..T, chartPsi S s s ^ 2) at hi
  have hmul := mul_le_mul_of_nonneg_left hPbound (by positivity : 0 ≤ 3 / b ^ 2)
  have he : 3 * chartScalarEnergy S T +
      3 / b ^ 2 * (8 * T ^ 2 * chartScalarEnergy S T) =
      (3 + 24 * (T / b) ^ 2) * chartScalarEnergy S T := by field_simp; ring
  rw [← he]
  linarith

end NormalizedChartData

end AcExtensionPrinciple

end
