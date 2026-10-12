module

public import AcExtensionPrinciple.Weighted.Prop34Initial
public import AcExtensionPrinciple.Weighted.Prop34CutoffDomain

/-!
# Frozen construction with the actual admissible initial datum

Paper `e1a0fd5`, `eq:frozen-linear-transport` and `eq:frozen-solution-operators`, lines 1257–1276.
The measurable initial representative is chosen before every proper truncation and source. The
incoming formula has its actual initial trace and finite radius-cutoff energy, without a completion
argument.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Construct the admissible frozen initial representative once and obtain the actual initial trace
and every finite-M_U source's cutoff energy. Source incoming AC/equations are supplied by
`weightedFrozenSolution_ac_ae_of_finite_source`. Paper `e1a0fd5`, `eq:frozen-linear-transport`,
lines 1257–1276. -/
theorem exists_frozen_initial_with_cutoff_energy {u₀ : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) :
    ∃ J₀ : ℝ → ℝ, Measurable J₀ ∧
      (∀ F : ℝ × ℝ → ℝ, ∀ᵐ v ∂volume.restrict (Ioc u₀ 0),
        weightedFrozenSolution S u₀ J₀ F (u₀, v) =
          S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ∧
      (∀ (U η : ℝ) (F : ℝ × ℝ → ℝ), U < 0 → 0 < η → Measurable F →
        weightedSourceNormSq S u₀ U F < ⊤ →
        (∫⁻ p in weightedCutoffDomain S u₀ U η,
          ENNReal.ofReal (weightedRemainderDensity S p *
            |weightedFrozenSolution S u₀ J₀ F p| ^ 2)) < ⊤) := by
  obtain ⟨J₀, hJ₀, heJ₀, henergy⟩ := h.exists_measurable_frozen_initial hi hu₀
  refine ⟨J₀, hJ₀, ?_, ?_⟩
  · intro F
    filter_upwards [heJ₀, ae_restrict_mem measurableSet_Ioc] with v hv hvI
    rw [h.weightedFrozenSolution_initial hi hu₀ hvI.1 hvI.2 J₀ F]
    exact hv.symm
  · intro U η F hU hη hF hsource
    exact h.weightedFrozenSolution_cutoff_energy_lt_top hi hU hη hJ₀ hF henergy hsource

end AcExtensionPrinciple.StandingFull

end
