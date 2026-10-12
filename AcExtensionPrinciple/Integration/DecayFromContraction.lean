module

public import AcExtensionPrinciple.Integration.CylinderStatements
public import AcExtensionPrinciple.Integration.WeightedDatum

/-!
# Decay and the weighted estimates from the remaining contraction lemma

Paper `e1a0fd5`, equations.tex lines 835–989 and 1130–1224.
Lemmas 2.3, 2.4 and 2.6 are supplied by the standing assumptions;
only the exact Lemma 2.5 statement remains as a source premise.
The contraction premise is supplied by `StandingFull.lemma25` in
`Integration/ObservabilityComplete.lean` and consumed in `Integration/DecayComplete.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 2.7 with only Lemma 2.5 remaining.
Paper `e1a0fd5`, `prop:uniform-mass-decay`, lines 835–925. -/
theorem uniform_mass_decay_of_contraction {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho) : UniformMassDecayStatement ui S :=
  h.uniform_mass_decay_of_pending_cylinder_lemmas h.lemma24 h25 (h.lemma26 h25.1)

/-- Proposition 2.8, including vanishing amplitudes, with only Lemma 2.5 remaining.
Paper `e1a0fd5`, `prop:common-scalar-limit`, lines 931–989. -/
theorem common_scalar_limit_of_contraction {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho) :
    CommonScalarLimitStatement ui S ∧ NormalizedScalarAmplitudesVanishStatement ui S :=
  h.common_scalar_limit_of_pending_decay_lemmas h.lemma23 h.lemma24 h25 (h.lemma26 h25.1)

/-- All three late Lemma 3.3 estimates with only Lemma 2.5 remaining;
the constants precede every epsilon and truncation parameter.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1167–1224. -/
theorem lemma33_of_contraction {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
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
            ENNReal.ofReal (C₁ * ε) * weightedRemainderL1 S u₀ U W :=
  h.lemma33_weighted_radial_estimates_of_decay (h.uniform_mass_decay_of_contraction h25)
    (h.common_scalar_limit_of_contraction h25).2 hδ0 hδ

/-- The late transported estimate for the actual initial datum, with only Lemma 2.5 remaining.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1167–1202. -/
theorem lemma33_transported_initial_of_contraction {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 3) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧
      ∀ U : ℝ, U < 0 →
        weightedSourceNorm S u₀ U (weightedRadialOperator S
          (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2)) ≤
          ENNReal.ofReal C₀ * (∫⁻ a in Ioc ui 0,
            ENNReal.ofReal |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) := by
  obtain ⟨C₀, hC₀, hb⟩ := h.lemma33_transported_initial_of_late_mass hδ
  obtain ⟨u₀, hi, hu₀, hsmall⟩ := h.weighted_late_smallness_of_decay
    (h.uniform_mass_decay_of_contraction h25) (h.common_scalar_limit_of_contraction h25).2
    hδ0 zero_lt_one
  exact ⟨C₀, hC₀, u₀, hi, hu₀, fun U hU =>
    hb u₀ U hi hU (fun p hp hu => (hsmall p hp hu).1)⟩

end AcExtensionPrinciple.StandingFull

end
