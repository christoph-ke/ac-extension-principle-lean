module

public import AcExtensionPrinciple.Weighted.Prop34GlobalBounds
public import AcExtensionPrinciple.Weighted.Prop34Measure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual complete weighted remainder space

Paper `e1a0fd5`, `eq:weighted-remainder-norm`, line 1150, and the
fixed-point construction, lines 1278–1287. The measure is the actual
remainder density on D_U, not an abstract replacement norm.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The remainder-weighted measure on the proper triangle. Paper
`e1a0fd5`, `eq:weighted-remainder-norm`, line 1150 and lines 1278–1287. -/
@[expose] noncomputable def weightedRemainderMeasure (S : SSFields) (u₀ U : ℝ) :
    Measure (ℝ × ℝ) :=
  (volume.restrict (weightedTruncatedDomain u₀ U)).withDensity
    (fun p => ENNReal.ofReal (weightedRemainderDensity S p))

/-- The actual weighted L² quotient used for the remainder fixed point.
Paper `e1a0fd5`, lines 1278–1287, with norm `eq:weighted-remainder-norm`. -/
noncomputable abbrev WeightedRemainderL2 (S : SSFields) (u₀ U : ℝ) :=
  Lp ℝ 2 (weightedRemainderMeasure S u₀ U)

/-- The actual weighted remainder quotient is complete. Paper `e1a0fd5`,
lines 1278–1287, justification of the fixed-point space. -/
instance weightedRemainderL2_complete (S : SSFields) (u₀ U : ℝ) :
    CompleteSpace (WeightedRemainderL2 S u₀ U) := inferInstance

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual density is measurable almost everywhere on the proper
triangle, so its weighted measure has the usual integration formula.
Paper `e1a0fd5`, line 1150 and lines 1278–1287. -/
theorem weighted_remainder_density_aemeasurable {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    AEMeasurable (fun p => ENNReal.ofReal (weightedRemainderDensity S p))
      (volume.restrict (weightedTruncatedDomain u₀ U)) := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  refine hω.ennreal_ofReal.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)] with p hp
  rw [← heω hp]

/-- Weighted and unweighted almost-everywhere equality coincide on D_U,
since the remainder density is strictly positive there, including the
axis convention. Paper `e1a0fd5`, lines 1278–1287. -/
theorem ae_weightedRemainderMeasure_iff {u₀ U : ℝ} {P : ℝ × ℝ → Prop}
    (hi : ui ≤ u₀) (hU : U < 0) :
    (∀ᵐ p ∂weightedRemainderMeasure S u₀ U, P p) ↔
      ∀ᵐ p ∂volume.restrict (weightedTruncatedDomain u₀ U), P p := by
  rw [weightedRemainderMeasure,
    ae_withDensity_iff' (h.weighted_remainder_density_aemeasurable hi hU)]
  constructor
  · intro hP
    filter_upwards [hP, ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)]
      with p hp hpD
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hpD
    apply hp
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (neg_pos.mpr (h.nu_neg hpt))
      (mul_pos (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds hpt).2)) (h.lam_pos hpt))
  · intro hP
    exact hP.mono (fun _ hp _ => hp)

/-- Integration against the actual weighted measure reproduces N_U².
Paper `e1a0fd5`, line 1150 and lines 1278–1287. -/
theorem weighted_remainder_measure_square_eq {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W) :
    (∫⁻ p, ENNReal.ofReal (|W p| ^ 2) ∂weightedRemainderMeasure S u₀ U) =
      weightedRemainderNormSq S u₀ U W := by
  rw [weightedRemainderMeasure,
    lintegral_withDensity_eq_lintegral_mul₀
      (h.weighted_remainder_density_aemeasurable hi hU)
      (show AEMeasurable (fun p => ENNReal.ofReal (|W p| ^ 2))
        (volume.restrict (weightedTruncatedDomain u₀ U)) by
          simpa only [Real.norm_eq_abs] using
            (hW.norm.pow_const 2).ennreal_ofReal.aemeasurable)]
  apply lintegral_congr
  intro p
  dsimp only [Pi.mul_apply]
  rw [mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

/-- The L² seminorm for the actual weighted measure is exactly N_U.
Paper `e1a0fd5`, line 1150 and lines 1278–1287. -/
theorem eLpNorm_weighted_remainder_eq {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W) :
    eLpNorm W 2 (weightedRemainderMeasure S u₀ U) = weightedRemainderNorm S u₀ U W := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hW.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [h.weighted_remainder_measure_square_eq hi hU hW]
  rfl

/-- Finite paper remainder energy is exactly membership in the actual L²
space for measurable representatives. Paper `e1a0fd5`, lines 1278–1287. -/
theorem memLp_weighted_remainder_iff {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W) :
    MemLp W 2 (weightedRemainderMeasure S u₀ U) ↔
      weightedRemainderNormSq S u₀ U W < ⊤ := by
  rw [memLp_iff, h.eLpNorm_weighted_remainder_eq hi hU hW]
  constructor
  · intro hmem
    rw [← weightedRemainderNorm_sq]
    simpa only [pow_two] using ENNReal.mul_lt_top hmem hmem
  · intro henergy
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne

/-- Every element of the actual weighted L² quotient has a globally
measurable representative with finite paper energy and the same values
almost everywhere for unweighted volume on D_U. Paper `e1a0fd5`,
lines 1278–1287. -/
theorem weightedRemainderL2_exists_measurable_representative {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (x : WeightedRemainderL2 S u₀ U) :
    ∃ W : ℝ × ℝ → ℝ, Measurable W ∧
      (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W ∧
      weightedRemainderNormSq S u₀ U W < ⊤ := by
  have hx := Lp.aestronglyMeasurable x
  refine ⟨hx.mk x, hx.measurable_mk,
    (h.ae_weightedRemainderMeasure_iff hi hU).mp hx.ae_eq_mk, ?_⟩
  apply (h.memLp_weighted_remainder_iff hi hU hx.measurable_mk).mp
  exact (memLp_congr_ae hx.ae_eq_mk).mp (Lp.memLp x)

end StandingFull

end AcExtensionPrinciple

end
