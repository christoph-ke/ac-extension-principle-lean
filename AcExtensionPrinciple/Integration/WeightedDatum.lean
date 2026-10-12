module

public import AcExtensionPrinciple.Integration.SectionThree
public import AcExtensionPrinciple.Weighted.Lemma33

/-!
# The weighted transported estimate for the actual Section 3 datum

Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1167–1202.
The κ-ratio transport agrees definitionally with Lemma 3.2's initial part.
Its initial measurability and L¹ integrability are now discharged.
Late mass-ratio smallness is supplied by `StandingFull.weighted_late_smallness`
in `Integration/DecayComplete.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The two transported initial data interfaces coincide.
Paper `e1a0fd5`, `eq:renormalized-initial-transport`, lines 1090–1093 and 1191. -/
theorem weightedTransportedDatum_eq_renormalizedInitial
    (ui : ℝ) (S : SSFields) (q : ℝ → ℝ → ℝ) :
    weightedTransportedDatum ui S (S.renormalizedDerivative q ui) =
      fun p => S.renormalizedInitial q ui p.1 p.2 := rfl

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The transported estimate for j_in from Lemma 3.2, with only the late
mass-ratio premise remaining. Its constant is fixed before u₀ and U.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1171–1173, 1186–1202. -/
theorem lemma33_transported_initial_of_late_mass {δ : ℝ} (hδ : δ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ U : ℝ, ui ≤ u₀ → U < 0 →
      (∀ p ∈ pastTriangle ui, u₀ ≤ p.1 → S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) →
      weightedSourceNorm S u₀ U
          (weightedRadialOperator S
            (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2)) ≤
        ENNReal.ofReal C *
          (∫⁻ a in Ioc ui 0,
            ENNReal.ofReal |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) := by
  let C := (weightedGapConstant ui S)⁻¹ ^ 2 *
    Real.sqrt ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u₀ U hi hU hsmall
  have hf := (h.sectionThreeDatumInputs.renormalized_fields_measurable h
    le_rfl h.initial_negative).1.aemeasurable
  simpa only [weightedTransportedDatum_eq_renormalizedInitial] using
    h.lemma33_transported_of_late_mass_bound hi hU hδ hf hsmall

end StandingFull

end AcExtensionPrinciple

end
