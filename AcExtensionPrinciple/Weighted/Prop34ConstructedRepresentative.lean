module

public import AcExtensionPrinciple.Weighted.Prop34Constructed

/-!
# Incoming representatives of the actual weighted fixed point

Paper `e1a0fd5`, lines 1278–1316. Select the literal frozen incoming
formula so that the quotient fixed point retains its incoming equation.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A fixed point admits joint measurable representatives retaining the
literal incoming formula and the full radial source, with exactly its
quotient energy. Paper `e1a0fd5`, lines 1278–1316. -/
theorem prop34_fixedPoint_representatives {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (F₀ : WeightedSourceL2 S u₀ U) (x : WeightedRemainderL2 S u₀ U)
    (heF₀ : (F₀ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      weightedRadialOperator S
        (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2))
    (hx : h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
      (F₀ + h.weightedRadialL2Operator hi hU (by linarith) hε hsmall x) = x) :
    ∃ W F : ℝ × ℝ → ℝ, Measurable W ∧ Measurable F ∧
      EqOn (weightedFrozenSolution S u₀ J₀ F) W (weightedOffAxisStrip u₀ U) ∧
      weightedRemainderNormSq S u₀ U W = ‖x‖ₑ ^ 2 ∧
      weightedRemainderNormSq S u₀ U W < ⊤ ∧ weightedSourceNormSq S u₀ U F < ⊤ ∧
      F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        (fun p => weightedRadialOperator S
          (fun q => S.renormalizedInitial (transportedRadialDatum ui S) ui q.1 q.2) p +
          weightedRadialOperator S W p) := by
  let T := h.weightedRadialL2Operator hi hU (by linarith : δ < 3) hε hsmall
  let y := F₀ + T x
  obtain ⟨F, hF, heF, hFs⟩ := h.weightedSourceL2_exists_measurable_representative hi hU y
  obtain ⟨W, hW, heW⟩ := h.weightedFrozenSolution_measurable_strip hi hU hJ₀ hF
  have heZW : weightedFrozenSolution S u₀ J₀ F
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W := by
    filter_upwards [weightedOffAxisStrip_ae u₀ U] with p hp
    exact heW hp
  have heX : (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W := by
    have he := h.weightedFrozenL2Operator_formula_of_representative hi hU hδ hsmall
      J₀ hJ₀ hinitial y hF heF hFs
    rw [show h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial y = x from hx] at he
    exact he.trans heZW
  have hn : weightedRemainderNormSq S u₀ U W = ‖x‖ₑ ^ 2 := by
    rw [← weightedRemainderNorm_sq, h.weightedRemainderL2_norm_of_representative hi hU hW heX]
  have hWs : weightedRemainderNormSq S u₀ U W < ⊤ := by
    rw [hn, pow_two]
    exact ENNReal.mul_lt_top (enorm_ne_top.lt_top) (enorm_ne_top.lt_top)
  refine ⟨W, F, hW, hF, heW, hn, hWs, hFs, ?_⟩
  have heT := h.weightedRadialL2Operator_formula_of_representative hi hU
    (by linarith) hε hsmall x hW heX
  have heSum : (y : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      (fun p => (F₀ : ℝ × ℝ → ℝ) p + (T x : ℝ × ℝ → ℝ) p) :=
    (h.ae_weightedSourceMeasure_iff hi hU).mp (Lp.coeFn_add F₀ (T x))
  filter_upwards [heF, heSum, heF₀, heT] with p hpF hpSum hp₀ hpT
  rw [← hpF, hpSum, hp₀, hpT]

end AcExtensionPrinciple.StandingFull

end
