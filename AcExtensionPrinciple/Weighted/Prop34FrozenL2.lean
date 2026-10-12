module

public import AcExtensionPrinciple.Weighted.Prop34GlobalDifference
public import AcExtensionPrinciple.Weighted.Prop34Initial

/-!
# Realizing the frozen formula in the actual weighted L² quotient

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287.
Finite initial and source energies give an actual quotient element,
with the global estimate and its almost-everywhere incoming formula.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A finite-source frozen formula defines an element of the actual
complete weighted remainder space, with the uniform global bound.
Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287. -/
theorem exists_weightedFrozenL2_element {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ} (hJ₀ : Measurable J₀) (hF : Measurable F)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∃ x : WeightedRemainderL2 S u₀ U,
      (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedFrozenSolution S u₀ J₀ F ∧
      ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) *
        (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
          (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
        ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
          weightedSourceNormSq S u₀ U F := by
  obtain ⟨Z, hZ, heZ⟩ := h.weightedFrozenSolution_exists_measurable_ae hi hU hJ₀ hF
  have hnorm : weightedRemainderNormSq S u₀ U Z =
      weightedRemainderNormSq S u₀ U (weightedFrozenSolution S u₀ J₀ F) := by
    apply lintegral_congr_ae
    filter_upwards [heZ] with p hp
    rw [hp]
  have hmem : MemLp Z 2 (weightedRemainderMeasure S u₀ U) := by
    apply (h.memLp_weighted_remainder_iff hi hU hZ).mpr
    rw [hnorm]
    exact h.weightedFrozenSolution_global_energy_lt_top hi hU hδ hsmall hJ₀ hF hinitial hsource
  refine ⟨hmem.toLp Z, ?_, ?_⟩
  · have hx : (hmem.toLp Z : ℝ × ℝ → ℝ)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] Z :=
      (h.ae_weightedRemainderMeasure_iff hi hU).mp hmem.coeFn_toLp
    exact hx.trans heZ.symm
  · rw [Lp.enorm_toLp, h.eLpNorm_weighted_remainder_eq hi hU hZ,
      weightedRemainderNorm_sq, hnorm]
    exact h.weightedFrozenSolution_global_energy_bound hi hU hδ hsmall hJ₀ hF hsource

/-- The quotient element represented by a frozen formula is unique.
Paper `e1a0fd5`, lines 1265–1287, the source solution operator. -/
theorem weightedFrozenL2_element_unique {u₀ U : ℝ} {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {x y : WeightedRemainderL2 S u₀ U}
    (hx : (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      weightedFrozenSolution S u₀ J₀ F)
    (hy : (y : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      weightedFrozenSolution S u₀ J₀ F) : x = y :=
  Lp.ext ((h.ae_weightedRemainderMeasure_iff hi hU).mpr (hx.trans hy.symm))

/-- Select the frozen operator on the actual source and remainder L²
quotients, using measurable representatives and the incoming formula.
Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287. -/
@[expose] noncomputable def weightedFrozenL2Operator {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (f : WeightedSourceL2 S u₀ U) : WeightedRemainderL2 S u₀ U := by
  classical
  let hf := Lp.aestronglyMeasurable f
  have hsource := (h.memLp_weighted_source_iff hi hU hf.measurable_mk).mp
    ((memLp_congr_ae hf.ae_eq_mk).mp (Lp.memLp f))
  exact Classical.choose (h.exists_weightedFrozenL2_element hi hU hδ hsmall
    hJ₀ hf.measurable_mk hinitial hsource)

/-- The selected quotient operator realizes the frozen formula of the
canonical measurable source representative. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1287. -/
theorem weightedFrozenL2Operator_formula {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (f : WeightedSourceL2 S u₀ U) :
    (h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial f : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedFrozenSolution S u₀ J₀ ((Lp.aestronglyMeasurable f).mk f) := by
  let hf := Lp.aestronglyMeasurable f
  have hsource := (h.memLp_weighted_source_iff hi hU hf.measurable_mk).mp
    ((memLp_congr_ae hf.ae_eq_mk).mp (Lp.memLp f))
  exact (Classical.choose_spec (h.exists_weightedFrozenL2_element hi hU hδ hsmall
    hJ₀ hf.measurable_mk hinitial hsource)).1

/-- The selected operator realizes the frozen formula for every measurable
finite-energy representative of its source element. Paper `e1a0fd5`,
lines 1275–1287, independence of the representative choice. -/
theorem weightedFrozenL2Operator_formula_of_representative {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (f : WeightedSourceL2 S u₀ U) {F : ℝ × ℝ → ℝ} (hF : Measurable F)
    (heF : (f : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    (h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial f : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] weightedFrozenSolution S u₀ J₀ F := by
  let hf := Lp.aestronglyMeasurable f
  have hsource' := (h.memLp_weighted_source_iff hi hU hf.measurable_mk).mp
    ((memLp_congr_ae hf.ae_eq_mk).mp (Lp.memLp f))
  have hevol : (f : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] hf.mk f :=
    (h.ae_weightedSourceMeasure_iff hi hU).mp hf.ae_eq_mk
  have he : hf.mk f =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F :=
    hevol.symm.trans heF
  exact (h.weightedFrozenL2Operator_formula hi hU hδ hsmall J₀ hJ₀ hinitial f).trans
    (h.weightedFrozenSolution_congr_ae hi hU hδ hsmall hJ₀ hf.measurable_mk hF
      hsource' hsource he)

/-- Select the actual initial datum once, before U and the source, and
obtain actual weighted L² frozen solutions with the paper's actual I₀
on the right-hand side. Paper `e1a0fd5`, lines 1275–1287. -/
theorem exists_actual_frozen_initial_with_L2_solutions {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    ∃ J₀ : ℝ → ℝ, Measurable J₀ ∧
      S.renormalizedRemainder S.radialDatumDerivative ui u₀
        =ᵐ[volume.restrict (Ioc u₀ 0)] J₀ ∧
      ∀ (U : ℝ) (F : ℝ × ℝ → ℝ), U < 0 → Measurable F →
        weightedSourceNormSq S u₀ U F < ⊤ →
        ∃ x : WeightedRemainderL2 S u₀ U,
          (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
            weightedFrozenSolution S u₀ J₀ F ∧
          ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) *
            (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
              (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
                ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
            ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
              weightedSourceNormSq S u₀ U F := by
  obtain ⟨J₀, hJ₀, heJ₀, henergy⟩ := h.exists_measurable_frozen_initial hi hu₀
  refine ⟨J₀, hJ₀, heJ₀, ?_⟩
  intro U F hU hF hsource
  have he : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) =
      ∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
          ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
    apply lintegral_congr_ae
    filter_upwards [heJ₀] with v hv
    rw [hv]
  simpa only [he] using
    h.exists_weightedFrozenL2_element hi hU hδ hsmall hJ₀ hF henergy hsource

/-- The actual frozen quotient operator retains the uniform squared
energy bound in terms of the source quotient norm. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1287. -/
theorem weightedFrozenL2Operator_energy_bound {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (f : WeightedSourceL2 S u₀ U) :
    ‖h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial f‖ₑ ^ 2 ≤
      ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) * (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) * ‖f‖ₑ ^ 2 := by
  let hf := Lp.aestronglyMeasurable f
  have hsource := (h.memLp_weighted_source_iff hi hU hf.measurable_mk).mp
    ((memLp_congr_ae hf.ae_eq_mk).mp (Lp.memLp f))
  have hb := (Classical.choose_spec (h.exists_weightedFrozenL2_element hi hU hδ hsmall
    hJ₀ hf.measurable_mk hinitial hsource)).2
  have hnorm : weightedSourceNorm S u₀ U (hf.mk f) = ‖f‖ₑ := by
    rw [← h.eLpNorm_weighted_source_eq hi hU hf.measurable_mk, Lp.enorm_def]
    exact eLpNorm_congr_ae hf.ae_eq_mk.symm
  calc
    _ ≤ ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) * (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
        ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
          weightedSourceNormSq S u₀ U (hf.mk f) := hb
    _ = _ := by rw [← weightedSourceNorm_sq, hnorm]

end AcExtensionPrinciple.StandingFull

end
