module

public import AcExtensionPrinciple.Observability.LemmaA3Ray
public import AcExtensionPrinciple.Observability.LemmaA3TranslationObservation

/-!
# Appendix A, Lemma A.3 in the normalized chart

Paper statement for commit `e1a0fd5`, `equations.tex`
`lem:observability-positive-mass`, `eq:observability-positive-mass`,
lines 1533–1663. The constant is chosen before the mass-ratio threshold,
radius, scalar field, and normalized chart.
-/

public section

namespace AcExtensionPrinciple

/-- Observability for a positive initial mass ratio, with the paper's
logarithmic duration and a constant depending only on `K`. Paper `e1a0fd5`,
`lem:observability-positive-mass`, `eq:observability-positive-mass`,
`eq:observability-positive-mass-duration`, lines 1533–1663, including
every constant scalar translation at line 1540.
There are no auxiliary annular, AC, finite-energy, or small-flux assumptions. -/
theorem lemmaA3_translated {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (b : ℝ) (S : SSFields),
      NormalizedChartData b (lemmaA3Duration K ε * b) K S → ε ≤ S.mu 0 0 → ∀ q : ℝ,
        c * ε ^ 3 * b / (1 + |Real.log ε|) ^ 2 ≤
          chartTranslatedEnergy S (lemmaA3Duration K ε * b) q := by
  let C := lemmaA3DurationConstant K
  let c₀ := lemmaA3SmallConstant K
  have hc₀ : 0 < c₀ := (lemmaA3_constants hK).2.2.2.1
  let c := c₀ / (2 * (3 + 24 * C ^ 2))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro ε hε hε1 b S h hμ q
  let H := lemmaA3Duration K ε
  let L := 1 + |Real.log ε|
  let E := chartTranslatedEnergy S (H * b) q
  obtain ⟨hKH, hHC, hC⟩ := lemmaA3_duration_bounds hK hε
  change K ≤ H at hKH
  change H ≤ C * L at hHC
  change 1 ≤ C at hC
  have hCp : 0 < C := by linarith only [hC]
  have hH : 0 < H := by linarith
  have hL : 1 ≤ L := by dsimp [L]; exact le_add_of_nonneg_right (abs_nonneg _)
  have hLp : 0 < L := by linarith only [hL]
  have hT : K * b ≤ H * b := mul_le_mul_of_nonneg_right hKH h.b_pos.le
  have hE : 0 ≤ E := h.lemmaA3_translated_energy_nonneg q
  have hflux := h.lemmaA3_mass_flux_lower hT hε hε1 hμ
  have hb := (h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩).1
  have hmass : ε * b ≤ 2 * S.m 0 0 := by
    change ε ≤ 2 * S.m 0 0 / S.r 0 0 at hμ
    rw [hb] at hμ
    exact (le_div_iff₀ h.b_pos).mp hμ
  have hlower : c₀ / 2 * ε ^ 3 * b < chartMassFlux S (H * b) := by
    have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ c₀ * ε ^ 2 / 2 by positivity)
    change c₀ * ε ^ 2 * S.m 0 0 < chartMassFlux S (H * b) at hflux
    nlinarith
  have hupper := h.lemmaA3_translated_mass_flux_le_observation q hT
  have hratio : H * b / b = H := mul_div_cancel_right₀ H h.b_pos.ne'
  rw [hratio] at hupper
  change chartMassFlux S (H * b) ≤ (3 + 24 * H ^ 2) * E at hupper
  have hsq : H ^ 2 ≤ C ^ 2 * L ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hHC) (show 0 ≤ C * L + H by positivity)
    nlinarith
  have hcoef : 3 + 24 * H ^ 2 ≤ (3 + 24 * C ^ 2) * L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have hobs := mul_le_mul_of_nonneg_right hcoef hE
  change c * ε ^ 3 * b / L ^ 2 ≤ E
  apply (div_le_iff₀ (by positivity : 0 < L ^ 2)).mpr
  dsimp [c]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * (3 + 24 * C ^ 2))).mp
  have he : (2 * (3 + 24 * C ^ 2)) *
      (c₀ / (2 * (3 + 24 * C ^ 2)) * ε ^ 3 * b) = c₀ * ε ^ 3 * b := by field_simp
  rw [he]
  nlinarith

/-- Lemma A.3 without translation, obtained from the uniform translated
statement. Paper `e1a0fd5`, `lem:observability-positive-mass`,
`eq:observability-positive-mass`, lines 1533–1663. -/
theorem lemmaA3 {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (b : ℝ) (S : SSFields),
      NormalizedChartData b (lemmaA3Duration K ε * b) K S → ε ≤ S.mu 0 0 →
        c * ε ^ 3 * b / (1 + |Real.log ε|) ^ 2 ≤
          chartScalarEnergy S (lemmaA3Duration K ε * b) := by
  obtain ⟨c, hc, hbound⟩ := lemmaA3_translated hK
  refine ⟨c, hc, ?_⟩
  intro ε hε hε1 b S h hμ
  simpa only [chartTranslatedEnergy, chartScalarEnergy, add_zero] using
    hbound ε hε hε1 b S h hμ 0

end AcExtensionPrinciple

end
