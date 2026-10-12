module

public import AcExtensionPrinciple.Observability.LemmaA3Differential
public import AcExtensionPrinciple.Observability.LemmaA3Gronwall
public import AcExtensionPrinciple.Observability.LemmaA3Annulus

/-!
# Lemma A.3: crossing and retained mass

Paper `e1a0fd5`, `eq:observability-retained-mass` and
`eq:observability-mass-flux-lower`, lines 1623–1647.
The inherited axis-time bound supplies the crossing within `Kb`; the
paper's longer logarithmic duration also dominates this time.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The incoming ray meets any inner positive radius before the axis time.
Paper `e1a0fd5`, lines 1630–1642, `eq:observability-positive-mass-duration`.
Continuity and the geometric axis-time conclusion suffice for this crossing. -/
theorem lemmaA3_crossing (hT : K * b ≤ T) {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ τ, τ ∈ Icc 0 (K * b) ∧ S.r τ 0 = a ∧
      inSeg 0 0 τ ⊆ chartCylinder h.g T ∧ ∀ s ∈ Icc 0 τ, a ≤ S.r s 0 := by
  obtain ⟨σ, hσ, hg⟩ := h.axis_reached 0 ⟨le_rfl, h.T_nonneg⟩ (by simpa using hT)
  simp only [zero_add] at hσ
  have hσT : σ ≤ T := hσ.2.trans hT
  have hseg := h.in_subset (t := 0) (a := 0) (c := σ) le_rfl hσT le_rfl (by rw [hg])
  have hc : ContinuousOn (fun s => S.r s 0) (Icc 0 σ) := h.continuous_r.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun s hs => hseg ⟨hs, by simp⟩)
  have h0 := (h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩).1
  have hσ0 : S.r σ 0 = 0 := by
    simpa [hg] using (h.axis_values σ ⟨hσ.1, hσT⟩).1
  obtain ⟨τ, hτ, hr⟩ := intermediate_value_Icc' hσ.1 hc
    (show a ∈ Icc (S.r σ 0) (S.r 0 0) from by rw [hσ0, h0]; exact ⟨ha.le, hab.le⟩)
  refine ⟨τ, ⟨hτ.1, hτ.2.trans hσ.2⟩, hr, ?_, ?_⟩
  · exact fun q hq => hseg ⟨⟨hq.1.1, hq.1.2.trans hτ.2⟩, hq.2⟩
  · intro s hs
    rw [← hr]
    exact h.radius_s_antitone hs.2 (fun q hq => hseg
      ⟨⟨hs.1.trans hq.1.1, hq.1.2.trans hτ.2⟩, hq.2⟩)

/-- Small total flux is incompatible with the geometric gap. This is the
physical flux lower bound of Lemma A.3. Paper `e1a0fd5`,
`eq:observability-small-mass-flux`, `eq:observability-retained-mass`,
`eq:observability-mass-flux-lower`, lines 1554–1647. -/
theorem lemmaA3_mass_flux_lower (hT : K * b ≤ T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : ε ≤ S.mu 0 0) : lemmaA3SmallConstant K * ε ^ 2 * S.m 0 0 < chartMassFlux S T := by
  by_contra hnot
  have hJ := le_of_not_gt hnot
  let M := S.m 0 0
  let δ := lemmaA3Delta K
  let p := M + chartIncomingFlux S T
  let a := 2 * M * (1 + δ)
  let A := lemmaA3FluxCoefficient δ
  let c := lemmaA3SmallConstant K
  obtain ⟨hδ, hδ1, hA, hc, hcδ, hcA⟩ := lemmaA3_constants h.K_ge_one
  change 0 < δ at hδ
  change δ ≤ 1 at hδ1
  change 1 ≤ A at hA
  have hAp : 0 < A := by linarith only [hA]
  have hbp : 0 < b := h.b_pos
  change 0 < c at hc
  change c ≤ δ / 2 at hcδ
  change c ≤ δ ^ 3 * Real.exp (-8 / δ) / (8 * A) at hcA
  change chartMassFlux S T ≤ c * ε ^ 2 * M at hJ
  have hb0 := h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩
  have hμ' : ε * b ≤ 2 * M := by
    change ε ≤ 2 * S.m 0 0 / S.r 0 0 at hμ
    rw [hb0.1] at hμ
    exact (le_div_iff₀ h.b_pos).mp hμ
  have hM : 0 < M := by nlinarith only [hμ', mul_pos hε h.b_pos]
  have hμupper : 2 * M / b ≤ 1 - K⁻¹ := by
    have hg := h.gap 0 0 (h.boundary_mem ⟨le_rfl, h.T_nonneg⟩)
    change K⁻¹ ≤ 1 - 2 * S.m 0 0 / S.r 0 0 at hg
    rw [hb0.1] at hg
    linarith only [hg]
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := annular_inner_lt_outer h.K_ge_one hM.le h.b_pos hμupper
  have hflux := h.flux_nonneg
  have hinJ : chartIncomingFlux S T ≤ chartMassFlux S T := by unfold chartMassFlux; linarith
  obtain ⟨hgap, hda⟩ := annular_gap hM hδ hc.le hcδ hε.le hε1.le (hinJ.trans hJ)
  change δ * M ≤ a - 2 * p at hgap
  change δ / (2 * (1 + δ)) ≤ 1 - 2 * p / a at hda
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpM : p ≤ 2 * M := by
    have heps : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
    have hh := mul_le_mul_of_nonneg_left heps hc.le
    have hh' := mul_le_mul_of_nonneg_right hh hM.le
    have hcm := mul_le_mul_of_nonneg_right hcδ hM.le
    have hdm := mul_le_mul_of_nonneg_right hδ1 hM.le
    dsimp [p]
    nlinarith only [hJ, hinJ, hh', hcm, hdm, hM]
  have _hannular := lemmaA3_annular_estimates hp hM hδ hε ha.le hab.le hgap hμ' hpM
  obtain ⟨τ, hτ, hrτ, hseg, hlower⟩ := h.lemmaA3_crossing hT ha hab
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans hT⟩
  have hq (s : ℝ) (hs : s ∈ Icc 0 τ) : (s, 0) ∈ chartInterior (chartCylinder h.g T) S :=
    ⟨hseg ⟨hs, by simp⟩, ha.trans_le (hlower s hs)⟩
  have hpm (s : ℝ) (hs : s ∈ Icc 0 τ) (z : ℝ) (hz : z ∈ Icc 0 s) : S.m s z ≤ p := by
    have hm := h.out_subset ⟨hs.1, hs.2.trans hτT.2⟩ (hq s hs).1.2.2.1 le_rfl
      (show (s, z) ∈ outSeg s 0 s from ⟨by simp, hz⟩)
    exact (h.mass_flux_bounds hm).2.1
  have hpr (s : ℝ) (hs : s ∈ Icc 0 τ) : 2 * p < S.r s 0 := by
    have hh := hlower s hs
    linarith only [hh, hgap, mul_pos hδ hM]
  have hupper (s : ℝ) (hs : s ∈ Icc 0 τ) : S.r s 0 ≤ b := by
    have hh := h.radius_t_mono hs.1 (fun q hq' => (h.lemmaA3_out_interior (hq s hs) hq').1)
    simpa [(h.boundary_gauge s ⟨hs.1, hs.2.trans hτT.2⟩).1] using hh
  have hcoef (s : ℝ) (hs : s ∈ Icc 0 τ) : 2 / (1 - 2 * p / S.r s 0) - 1 ≤ A := by
    have hd : 0 < 1 - 2 * p / S.r s 0 := sub_pos.mpr ((div_lt_one (hq s hs).2).mpr (hpr s hs))
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 2 * p by positivity) ha (hlower s hs)
    have hg : δ / (2 * (1 + δ)) ≤ 1 - 2 * p / S.r s 0 := by linarith only [hda, hh]
    have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 < δ / (2 * (1 + δ))) hg
    have he : 2 / (δ / (2 * (1 + δ))) = A := by dsimp [A, lemmaA3FluxCoefficient]; field_simp; norm_num
    rw [he] at hb
    linarith only [hb]
  let D : ℝ → ℝ := fun s => S.m s s - S.m s 0
  let F : ℝ → ℝ := fun s => chartIncomingFluxDensity S s + A * chartOutgoingFluxDensity S s
  have hsub : uIcc 0 τ ⊆ uIcc 0 T := by
    rw [uIcc_of_le hτ.1, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc le_rfl hτT.2
  have hFi : IntervalIntegrable F volume 0 τ :=
    (h.flux_density_integrable.1.mono_set hsub).add
      ((h.flux_density_integrable.2.mono_set hsub).const_mul A)
  have hFp (s : ℝ) (hs : s ∈ Icc 0 τ) : 0 ≤ F s := by
    have hg := (h.gap_pos (h.boundary_mem ⟨hs.1, hs.2.trans hτT.2⟩)).le
    dsimp [F, chartIncomingFluxDensity, chartOutgoingFluxDensity]
    positivity
  have hDpos (s : ℝ) (hs : s ∈ Icc 0 τ) : 0 ≤ D s :=
    sub_nonneg.mpr (h.mass_le_boundary (hq s hs).1)
  have hac := h.lemmaA3_ray_ac hτT hseg
  have hw := lemmaA3_weighted_gronwall hτ.1 hp hac.1 hac.2 hpr hupper hDpos
    (by simp) hFi hFp (by
      filter_upwards [h.lemmaA3_ray_difference_ae hτT hseg] with s hs hsI
      have hscc : s ∈ Icc 0 τ := ⟨hsI.1.le, hsI.2.le⟩
      have hl := h.lemmaA3_annular_lapse_bounds (hq s hscc) (hpm s hscc) (hpr s hscc)
      have hdiff := h.lemmaA3_annular_differential (hq s hscc) (hpm s hscc) (hpr s hscc) (hs hsI).2
      have hO : 0 ≤ chartOutgoingFluxDensity S s := by
        dsimp [chartOutgoingFluxDensity]
        have hg := (h.gap_pos (h.boundary_mem ⟨hsI.1.le, hsI.2.le.trans hτT.2⟩)).le
        positivity
      have hmul := mul_le_mul_of_nonneg_right (hcoef s hscc) hO
      refine ⟨(hs hsI).1, (by linarith only [hl.1]), ?_⟩
      dsimp [F, D]
      linarith only [hdiff, hmul])
  have hFfull : (∫ s in 0..τ, F s) ≤ A * chartMassFlux S T := by
    have hFm : (∫ s in 0..τ, F s) ≤ ∫ s in 0..T, F s := by
      apply intervalIntegral.integral_mono_interval le_rfl hτ.1 hτT.2
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with s hs
        have hg := (h.gap_pos (h.boundary_mem ⟨hs.1.le, hs.2⟩)).le
        dsimp [F, chartIncomingFluxDensity, chartOutgoingFluxDensity]
        positivity
      · exact h.flux_density_integrable.1.add (h.flux_density_integrable.2.const_mul A)
    dsimp [F] at hFm
    rw [intervalIntegral.integral_add h.flux_density_integrable.1
      (h.flux_density_integrable.2.const_mul A), intervalIntegral.integral_const_mul] at hFm
    change (∫ s in 0..τ, chartIncomingFluxDensity S s + A * chartOutgoingFluxDensity S s) ≤
      chartIncomingFlux S T + A * chartOutgoingFlux S T at hFm
    unfold chartMassFlux
    nlinarith only [hFm, mul_nonneg (sub_nonneg.mpr hA) hflux.1]
  have hweighted : D τ * lemmaA3Weight p a ≤ b ^ 2 * A * (c * ε ^ 2 * M) := by
    rw [hrτ] at hw
    exact hw.trans ((mul_le_mul_of_nonneg_left hFfull (sq_nonneg b)).trans
      (by have hh := mul_le_mul_of_nonneg_left hJ (show 0 ≤ b ^ 2 * A by positivity)
          simpa only [mul_assoc] using hh))
  have hweightlow := lemmaA3Weight_lower hp hM hδ hpM hgap
  have hDw := mul_le_mul_of_nonneg_left hweightlow (hDpos τ ⟨hτ.1, le_rfl⟩)
  have hepsb : ε ^ 2 * b ^ 2 ≤ 4 * M ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hμ') (show 0 ≤ 2 * M + ε * b by positivity)
    nlinarith only [hh]
  have hsmall : 8 * A * c ≤ δ ^ 3 * Real.exp (-8 / δ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * A)).mp hcA
    nlinarith only [hh]
  have hDsmall : D τ ≤ δ / 2 * M := by
    have hm := mul_le_mul_of_nonneg_left hepsb (show 0 ≤ A * c * M by positivity)
    have hc' := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ M ^ 3 by positivity)
    have hnon : 0 < δ ^ 2 * M ^ 2 * Real.exp (-8 / δ) := by positivity
    apply (mul_le_mul_iff_right₀ hnon).mp
    nlinarith only [hm, hc', hweighted, hDw]
  have hOsmall : chartOutgoingFlux S T ≤ δ / 2 * M := by
    have hoJ : chartOutgoingFlux S T ≤ chartMassFlux S T := by unfold chartMassFlux; linarith only [hflux.1]
    have heps : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
    have hh := mul_le_mul_of_nonneg_left heps hc.le
    have hh' := mul_le_mul_of_nonneg_right hh hM.le
    have hcm := mul_le_mul_of_nonneg_right hcδ hM.le
    nlinarith only [hoJ, hJ, hh', hcm]
  have hB := (h.mass_flux_bounds (hq τ ⟨hτ.1, le_rfl⟩).1).2.2
  have hret : (1 - δ) * M ≤ S.m τ 0 := by
    change M - chartOutgoingFlux S T ≤ S.m τ τ at hB
    dsimp only [D] at hDsmall
    linarith only [hB, hDsmall, hOsmall]
  have hgapfinal := h.gap τ 0 (hq τ ⟨hτ.1, le_rfl⟩).1
  have hratio : (1 - δ) / (1 + δ) ≤ S.mu τ 0 := by
    change (1 - δ) / (1 + δ) ≤ 2 * S.m τ 0 / S.r τ 0
    rw [hrτ]
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + δ) ha).mpr
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_right hret (show 0 ≤ 2 * (1 + δ) by positivity)]
  have hcfinal := annular_delta_contradiction h.K_ge_one
  change 1 - (1 - δ) / (1 + δ) = 2 * δ / (1 + δ) ∧ 2 * δ / (1 + δ) < K⁻¹ at hcfinal
  linarith only [hgapfinal, hratio, hcfinal.1, hcfinal.2]

end NormalizedChartData

end AcExtensionPrinciple

end
