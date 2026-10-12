module

public import AcExtensionPrinciple.Weighted.Prop34WeightedSpace

/-!
# The actual finite-source L² space

Paper `e1a0fd5`, `eq:weighted-source-norm`, line 1152, and
`eq:frozen-solution-operators`, lines 1265–1287. Finite source energies
are closed under subtraction in the actual weighted measure.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The actual source-weighted measure on D_U. Paper `e1a0fd5`,
`eq:weighted-source-norm`, line 1152 and lines 1265–1287. -/
@[expose] noncomputable def weightedSourceMeasure (S : SSFields) (u₀ U : ℝ) :
    Measure (ℝ × ℝ) :=
  (volume.restrict (weightedTruncatedDomain u₀ U)).withDensity
    (fun p => ENNReal.ofReal (weightedSourceDensity S p))

/-- The actual source L² quotient for the frozen solution operator. Paper
`e1a0fd5`, `eq:weighted-source-norm`, line 1152 and lines 1265–1287. -/
noncomputable abbrev WeightedSourceL2 (S : SSFields) (u₀ U : ℝ) :=
  Lp ℝ 2 (weightedSourceMeasure S u₀ U)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual source density is measurable almost everywhere on D_U.
Paper `e1a0fd5`, lines 1152 and 1265–1287. -/
theorem weighted_source_density_aemeasurable {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    AEMeasurable (fun p => ENNReal.ofReal (weightedSourceDensity S p))
      (volume.restrict (weightedTruncatedDomain u₀ U)) := by
  obtain ⟨σ, hσ, heσ⟩ := h.weighted_exists_measurable_source_density hi hU
  refine hσ.ennreal_ofReal.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)] with p hp
  rw [← heσ hp]

/-- The weighted-measure source-square integral is exactly M_U².
Paper `e1a0fd5`, line 1152 and lines 1265–1287. -/
theorem weighted_source_measure_square_eq {u₀ U : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hF : Measurable F) :
    (∫⁻ p, ENNReal.ofReal (|F p| ^ 2) ∂weightedSourceMeasure S u₀ U) =
      weightedSourceNormSq S u₀ U F := by
  rw [weightedSourceMeasure,
    lintegral_withDensity_eq_lintegral_mul₀
      (h.weighted_source_density_aemeasurable hi hU)
      (show AEMeasurable (fun p => ENNReal.ofReal (|F p| ^ 2))
        (volume.restrict (weightedTruncatedDomain u₀ U)) by
          simpa only [Real.norm_eq_abs] using
            (hF.norm.pow_const 2).ennreal_ofReal.aemeasurable)]
  apply lintegral_congr
  intro p
  dsimp only [Pi.mul_apply]
  rw [mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

/-- The source L² seminorm for the actual weighted measure is M_U.
Paper `e1a0fd5`, line 1152 and lines 1265–1287. -/
theorem eLpNorm_weighted_source_eq {u₀ U : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hF : Measurable F) :
    eLpNorm F 2 (weightedSourceMeasure S u₀ U) = weightedSourceNorm S u₀ U F := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hF.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [h.weighted_source_measure_square_eq hi hU hF]
  rfl

/-- Finite M_U² is exactly source L² membership for measurable inputs.
Paper `e1a0fd5`, line 1152 and lines 1265–1287. -/
theorem memLp_weighted_source_iff {u₀ U : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hF : Measurable F) :
    MemLp F 2 (weightedSourceMeasure S u₀ U) ↔ weightedSourceNormSq S u₀ U F < ⊤ := by
  rw [memLp_iff, h.eLpNorm_weighted_source_eq hi hU hF]
  constructor
  · intro hmem
    rw [← weightedSourceNorm_sq]
    simpa only [pow_two] using ENNReal.mul_lt_top hmem hmem
  · intro henergy
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne

/-- The source difference of two finite-energy inputs is again finite
energy, without any additional hypothesis. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weighted_source_sub_normSq_lt_top {u₀ U : ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤) :
    weightedSourceNormSq S u₀ U (fun p => F₁ p - F₂ p) < ⊤ := by
  apply (h.memLp_weighted_source_iff hi hU (hF₁.sub hF₂)).mp
  exact ((h.memLp_weighted_source_iff hi hU hF₁).mpr hsource₁).sub
    ((h.memLp_weighted_source_iff hi hU hF₂).mpr hsource₂)

/-- The actual source-weighted measure has the same null sets as volume
on D_U. Paper `e1a0fd5`, lines 1265–1287, source representatives. -/
theorem ae_weightedSourceMeasure_iff {u₀ U : ℝ} {P : ℝ × ℝ → Prop}
    (hi : ui ≤ u₀) (hU : U < 0) :
    (∀ᵐ p ∂weightedSourceMeasure S u₀ U, P p) ↔
      ∀ᵐ p ∂volume.restrict (weightedTruncatedDomain u₀ U), P p := by
  rw [weightedSourceMeasure,
    ae_withDensity_iff' (h.weighted_source_density_aemeasurable hi hU)]
  constructor
  · intro hP
    filter_upwards [hP, ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)]
      with p hp hpD
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hpD
    apply hp
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact (sq_pos_of_pos (Real.exp_pos _)).trans_le (h.weightedSourceDensity_lower hpt)
  · intro hP
    exact hP.mono (fun _ hp _ => hp)

/-- Every source quotient element admits a measurable representative
with finite actual M_U², agreeing for volume on D_U. Paper `e1a0fd5`,
lines 1265–1287. -/
theorem weightedSourceL2_exists_measurable_representative {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (x : WeightedSourceL2 S u₀ U) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧
      (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F ∧
      weightedSourceNormSq S u₀ U F < ⊤ := by
  have hx := Lp.aestronglyMeasurable x
  refine ⟨hx.mk x, hx.measurable_mk,
    (h.ae_weightedSourceMeasure_iff hi hU).mp hx.ae_eq_mk, ?_⟩
  apply (h.memLp_weighted_source_iff hi hU hx.measurable_mk).mp
  exact (memLp_congr_ae hx.ae_eq_mk).mp (Lp.memLp x)

end StandingFull

end AcExtensionPrinciple

end
