module

public import AcExtensionPrinciple.Observability.ChartBoundaryIntegrals

/-!
# Lemma A.2: shifted boundary balance and stability

Paper `e1a0fd5`, `lem:observability-axis-amplitude`,
`eq:observability-shifted-balance`, `eq:observability-shifted-stability`,
lines 1477–1502 and 1518–1522. Boundary AC and chain rules are conclusions
of the chart integral/BV hypotheses, not additional assumptions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The energy integral in Lemma A.2. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480. -/
@[expose] noncomputable def chartScalarEnergy (S : SSFields) (T : ℝ) : ℝ :=
  ∫ s in 0..T, S.dvpsi s s ^ 2 + deriv (fun s => chartPsi S s s) s ^ 2

/-- The stored energy has exactly the displayed formula. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480. -/
theorem chartShiftedEnergy_eq {b : ℝ} (S : SSFields) (s : ℝ) (hb : 0 < b) :
    chartShiftedEnergy b S s = chartPsi S s s ^ 2 / (2 * b) -
      b / 2 * Real.log (1 - massRatio b (S.m s s)) := by
  unfold chartShiftedEnergy boundaryEnergy
  field_simp

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The shifted energy is absolutely continuous. Paper `e1a0fd5`,
`eq:observability-shifted-balance`, lines 1518, 1522. -/
theorem shifted_energy_ac : AbsolutelyContinuousOnInterval (chartShiftedEnergy b S) 0 T := by
  obtain ⟨hψ, hm⟩ := h.boundary_traces_ac
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 T :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval (fun s => 1 - massRatio b (S.m s s)) 0 T := by
    convert hc.sub (hm.const_mul (2 / b)) using 1
    funext s
    unfold massRatio
    simp only [Pi.sub_apply]
    ring
  have hlog := positive_ac_log hgap (by
    intro s hs
    rw [uIcc_of_le h.T_nonneg] at hs
    have hh := h.gap_pos (h.boundary_mem hs)
    simpa only [SSFields.mu, (h.boundary_gauge s hs).1] using hh)
  have hA := hψ.const_mul b⁻¹
  convert ((hA.mul hA).sub hlog).const_mul (b / 2) using 1
  funext s
  simp only [chartShiftedEnergy, boundaryEnergy, pow_two, div_eq_mul_inv,
    Pi.mul_apply, Pi.sub_apply]
  ring

/-- Normalized boundary mass algebra. Paper `e1a0fd5`,
`eq:observability-shifted-balance`, lines 1518, 1497–1499. -/
theorem boundary_mass_algebra {s : ℝ} (hs : s ∈ Icc 0 T) :
    (S.massU s s + S.massV s s) / (1 - massRatio b (S.m s s)) =
      (S.dvpsi s s - S.phi s s) ^ 2 / 2 - (S.dupsi s s + S.phi s s) ^ 2 / 2 := by
  have hb := h.boundary_gauge s hs
  have hgap := h.gap_pos (h.boundary_mem hs)
  unfold SSFields.massU SSFields.massV SSFields.zeta SSFields.theta SSFields.mu at *
  rw [hb.1, hb.2.1, hb.2.2]
  have hne : 1 - massRatio b (S.m s s) ≠ 0 := by simpa [hb.1] using hgap.ne'
  field_simp
  ring

/-- The pointwise chain rule gives the shifted balance at every point with
the two trace derivatives. Paper `e1a0fd5`, lines 1518, 1522. -/
theorem hasDerivAt_shifted_energy {s : ℝ} (hs : s ∈ Icc 0 T)
    (hm : HasDerivAt (fun s => S.m s s) (S.massU s s + S.massV s s) s)
    (hψ : HasDerivAt (fun s => chartPsi S s s) (S.dupsi s s + S.dvpsi s s) s) :
    HasDerivAt (chartShiftedEnergy b S)
      (S.dvpsi s s * (S.dupsi s s + S.dvpsi s s) -
        (S.dupsi s s + S.dvpsi s s) ^ 2 / 2) s := by
  have hb0 := h.b_pos.ne'
  have hg : 1 - massRatio b (S.m s s) ≠ 0 := by
    have hh := h.gap_pos (h.boundary_mem hs)
    simpa only [SSFields.mu, (h.boundary_gauge s hs).1] using hh.ne'
  have hdlog := ((hasDerivAt_const s (1 : ℝ)).sub ((hm.const_mul 2).div_const b)).log hg
  have hd := (((hψ.div_const b).pow 2).sub hdlog).const_mul (b / 2)
  change HasDerivAt (fun s => b / 2 *
    ((chartPsi S s s / b) ^ 2 - Real.log (1 - massRatio b (S.m s s)))) _ s
  apply hd.congr_deriv
  simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.sub_apply]
  change b / 2 *
    (2 * (chartPsi S s s / b) * ((S.dupsi s s + S.dvpsi s s) / b) -
      (0 - 2 * (S.massU s s + S.massV s s) / b) / (1 - massRatio b (S.m s s))) = _
  have ha := h.boundary_mass_algebra hs
  have hψb : chartPsi S s s = b * S.phi s s := by
    rw [chartPsi, (h.boundary_gauge s hs).1]
  have halg : b / 2 *
      (2 * (chartPsi S s s / b) * ((S.dupsi s s + S.dvpsi s s) / b) -
        (0 - 2 * (S.massU s s + S.massV s s) / b) / (1 - massRatio b (S.m s s))) =
      S.phi s s * (S.dupsi s s + S.dvpsi s s) +
        (S.massU s s + S.massV s s) / (1 - massRatio b (S.m s s)) := by
    rw [hψb]
    field_simp
    ring
  rw [halg, ha]
  ring

/-- The shifted balance holds a.e. with the actual scalar trace derivative.
Paper `e1a0fd5`, `eq:observability-shifted-balance`, lines 1497–1499, 1518, 1522. -/
theorem shifted_balance_ae : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
    deriv (chartShiftedEnergy b S) s =
      S.dvpsi s s * deriv (fun s => chartPsi S s s) s -
        deriv (fun s => chartPsi S s s) s ^ 2 / 2 := by
  filter_upwards [h.boundary_mass_ae_hasDerivAt, h.boundary_psi_ae_hasDerivAt] with s hm hψ
  intro hs
  have hsI : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
  rw [(h.hasDerivAt_shifted_energy hsI (hm hsI) (hψ hsI)).deriv, (hψ hsI).deriv]

/-- The finite boundary energy is nonnegative. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480. -/
theorem scalar_energy_nonneg : 0 ≤ chartScalarEnergy S T :=
  intervalIntegral.integral_nonneg h.T_nonneg (by intros; positivity)

/-- Full shifted stability, with no extra finite-energy or boundary AC premise.
Paper `e1a0fd5`, `eq:observability-shifted-stability`, lines 1500–1502, 1518. -/
theorem shifted_stability {s : ℝ} (hs : s ∈ Icc 0 T) :
    chartShiftedEnergy b S 0 - chartScalarEnergy S T ≤ chartShiftedEnergy b S s ∧
      chartShiftedEnergy b S s ≤ chartShiftedEnergy b S 0 + chartScalarEnergy S T / 2 := by
  exact shifted_energy_stability hs h.shifted_energy_ac h.boundary_scalar_square_integrable.2
    h.boundary_psi_deriv_square_integrable h.shifted_balance_ae

end NormalizedChartData

end AcExtensionPrinciple

end
