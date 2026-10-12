module

public import AcExtensionPrinciple.Integration.DecayFromObservability
public import AcExtensionPrinciple.Integration.SmallConesFromContraction

/-!
# Small outgoing cones from boundary observability and coercive energy

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, equations.tex lines 1324–1356.
The normalized chart construction discharges the contraction premise.
The remaining energy premise is exactly the Proposition 3.4 conclusion.
The observation and energy premises are supplied by `StandingFull.lemmaA1`
in `Integration/ObservabilityComplete.lean` and `StandingFull.proposition34`
in `Weighted/Prop34.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The small-cone sequence from normalized observability and finite coercive
energy. Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_cones_of_observability_and_energy
    (hA1 : PropA1Statement h.integrationCylinderK)
    (henergy : ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25_of_boundary_observability hA1
  exact h.small_outgoing_cones_of_contraction_and_energy h25 henergy

/-- The small-cone sequence from normalized observability and finite coercive
energy. Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_bv_cones_of_observability_and_energy
    (hA1 : PropA1Statement h.integrationCylinderK)
    (henergy : ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  obtain ⟨H, C, rho, h25⟩ := h.lemma25_of_boundary_observability hA1
  exact h.small_outgoing_bv_cones_of_contraction_and_energy h25 henergy

end AcExtensionPrinciple.StandingFull

end
