module

public import AcExtensionPrinciple.Weighted.Prop34TransportedSource
public import AcExtensionPrinciple.Weighted.Prop34Smallness

/-!
# Uniform constructed energy with the actual Section 3 data

Paper `e1a0fd5`, `eq:constructed-remainder-bound`, lines 1278–1287.
Both weighted operators, the actual initial trace and the transported
source are produced from the standing class. Identification is separate.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual transported source and admissible initial trace produce
a fixed point with the paper's uniform energy bound. The numerical
smallness premise is independent of U. Paper `e1a0fd5`,
`eq:constructed-remainder-bound`, lines 1278–1287. -/
theorem exists_actual_weighted_fixedPoint_with_energy {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hbudget : ε ^ 2 ≤
      (1 - 3 * δ) * weightedGapConstant ui S * (3 - δ) / 24) :
    ∃ J₀ : ℝ → ℝ, ∃ hJ₀ : Measurable J₀,
      ∃ hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤,
      S.renormalizedRemainder S.radialDatumDerivative ui u₀
        =ᵐ[volume.restrict (Ioc u₀ 0)] J₀ ∧
      ∀ U : ℝ, ∀ hU : U < 0,
        ∃ F₀ : WeightedSourceL2 S u₀ U, ∃ x : WeightedRemainderL2 S u₀ U,
          (F₀ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
            weightedRadialOperator S
              (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2) ∧
          h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
            (F₀ + h.weightedRadialL2Operator hi hU (by linarith) hε hsmall x) = x ∧
          ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
            (ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) *
              (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
                (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
                  ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
            ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
              (ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 4 *
                ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
                (∫⁻ a in Ioc ui 0, ENNReal.ofReal
                  |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) ^ 2)) := by
  obtain ⟨J₀, hJ₀, heJ₀, hinitial⟩ := h.exists_measurable_frozen_initial hi hu₀
  refine ⟨J₀, hJ₀, hinitial, heJ₀, ?_⟩
  intro U hU
  obtain ⟨F₀, heF₀, hF₀⟩ := h.exists_actual_weightedTransportedSourceL2 hi hU
    (by linarith) (fun p hp hpu => (hsmall p hp hpu).1)
  have hhalf := weighted_fixedPoint_half_of_smallness hδ hε h.weightedGapConstant_pos hbudget
  obtain ⟨x, hx, henergy, _⟩ := h.exists_weighted_remainder_fixedPoint_with_energy
    hi hU hδ hε hsmall J₀ hJ₀ hinitial hhalf F₀
  refine ⟨F₀, x, heF₀, hx, ?_⟩
  have heI : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) =
        ∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
          (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
            ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
    apply lintegral_congr_ae
    filter_upwards [heJ₀] with v hv
    rw [hv]
  rw [heI] at henergy
  exact henergy.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hF₀ zero_le)) zero_le)

end AcExtensionPrinciple.StandingFull

end
