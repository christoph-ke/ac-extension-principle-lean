module

public import AcExtensionPrinciple.Integration.ObservabilityComplete
public import AcExtensionPrinciple.Integration.DecayFromContraction

/-!
# Decay and weighted estimates under the standing assumptions alone

Paper `e1a0fd5`, `lem:boundary-contraction`, `prop:uniform-mass-decay`,
`prop:common-scalar-limit`, and `lem:weighted-radial-estimates`, equations.tex
lines 751–989 and 1167–1224. The source chart and Lemma 2.5 discharge the
contraction premise using the same geometric K as the decay chain.
The constructed inner chart now discharges the small-mass estimate.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Source conclusion with all observation and contraction premises discharged.
Paper `e1a0fd5`, `prop:uniform-mass-decay`, lines 835–925. -/
theorem uniform_mass_decay :
    UniformMassDecayStatement ui S := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25
  exact h.uniform_mass_decay_of_contraction h25

/-- Source conclusion with all observation and contraction premises discharged.
Paper `e1a0fd5`, `prop:common-scalar-limit`, lines 931–989. -/
theorem common_scalar_limit :
    CommonScalarLimitStatement ui S ∧ NormalizedScalarAmplitudesVanishStatement ui S := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25
  exact h.common_scalar_limit_of_contraction h25

/-- The late weighted smallness required in Proposition 3.4 follows from
the complete mass-decay and scalar-continuity results. Paper `e1a0fd5`,
`eq:late-renormalized-smallness`, equations.tex lines 1130–1137. -/
theorem weighted_late_smallness {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧ WeightedLateSmallness ui S u₀ δ ε :=
  h.weighted_late_smallness_of_decay h.uniform_mass_decay h.common_scalar_limit.2 hδ hε

/-- Source conclusion with all observation and contraction premises discharged.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1167–1224. -/
theorem lemma33
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C₀ C₂ C₁ : ℝ, 0 ≤ C₀ ∧ 0 < C₂ ∧ 0 < C₁ ∧
      ∀ ε : ℝ, 0 < ε → ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧
        ∀ (U : ℝ) (f : ℝ → ℝ) (W : ℝ × ℝ → ℝ),
          u₀ < U → U < 0 →
          AEMeasurable f (volume.restrict (Ioc ui 0)) → Measurable W →
          weightedSourceNorm S u₀ U
              (weightedRadialOperator S (weightedTransportedDatum ui S f)) ≤
            ENNReal.ofReal C₀ * (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ∧
          weightedSourceNorm S u₀ U (weightedRadialOperator S W) ≤
            ENNReal.ofReal (C₂ * ε) * weightedRemainderNorm S u₀ U W ∧
          weightedSourceL1 S u₀ U (weightedRadialOperator S W) ≤
            ENNReal.ofReal (C₁ * ε) * weightedRemainderL1 S u₀ U W := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25
  exact h.lemma33_of_contraction h25 hδ0 hδ

/-- Source conclusion with all observation and contraction premises discharged.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1167–1202. -/
theorem lemma33_transported_initial
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 3) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧
      ∀ U : ℝ, U < 0 →
        weightedSourceNorm S u₀ U (weightedRadialOperator S
          (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2)) ≤
          ENNReal.ofReal C₀ * (∫⁻ a in Ioc ui 0,
            ENNReal.ofReal |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25
  exact h.lemma33_transported_initial_of_contraction h25 hδ0 hδ

end AcExtensionPrinciple.StandingFull

end
