module

public import AcExtensionPrinciple.Observability.PropA4
public import AcExtensionPrinciple.Observability.PropA1
public import AcExtensionPrinciple.Observability.LemmaA3

/-!
# Substitution of the available Appendix A assembly

Paper `e1a0fd5`, `prop:boundary-mass-observability` and
`prop:boundary-observability`, lines 1906–1930.
The normalized-chart A.4 assembly supplies A.1's premise. A.3 is proved by
`lemmaA3_statement` below; the small-mass premise is supplied by
`PropA4.small_mass_estimate` in `Integration/ObservabilityComplete.lean`.
-/

public section

namespace AcExtensionPrinciple

/-- The translated A.3 proof supplies the exact observation interface;
the stored shift is the negative of the additive scalar translation.
Paper `e1a0fd5`, `lem:observability-positive-mass`, lines 1533–1663. -/
theorem lemmaA3_statement {K : ℝ} (hK : 1 ≤ K) : PropA4.LemmaA3Statement K := by
  obtain ⟨c, hc, hb⟩ := lemmaA3_translated hK
  refine ⟨c, hc, ?_⟩
  intro eps b S heps heps1 h hmu shift
  simpa only [PropA4.positiveMassDuration, lemmaA3Duration, lemmaA3Delta,
    chartTranslatedEnergy, PropA4.translatedScalarEnergy, sub_eq_add_neg] using
    hb eps heps heps1 b S h hmu (-shift)

/-- A.4 with the positive-mass observation premise discharged.
The small-mass input is proved by `PropA4.small_mass_estimate` in
`Integration/ObservabilityComplete.lean`.
Paper `e1a0fd5`, `prop:boundary-mass-observability`, lines 1665–1913. -/
theorem boundary_mass_observability_of_small_mass {K : ℝ} (hK : 1 ≤ K)
    (hsmall : PropA4.SmallMassEstimate K) : PropA4.Statement K :=
  PropA4.of_small_mass_estimate hK hsmall

/-- A.1 with both A.3 and the A.4 assembly substituted.
Paper `e1a0fd5`, `prop:boundary-observability`, lines 1906–1930. -/
theorem boundary_observability_of_small_mass {K : ℝ} (hK : 1 ≤ K)
    (hsmall : PropA4.SmallMassEstimate K) : PropA1.Statement K :=
  PropA1.of_propA4 hK (boundary_mass_observability_of_small_mass hK hsmall)

/-- Normalized A.1 conditional on the small-mass estimate, supplied by
`PropA4.small_mass_estimate` in `Integration/ObservabilityComplete.lean`.
The A.3 argument is unused because A.4 already invokes its proof. Source
charts are constructed by `exists_normalizedBoundaryCoordinates` in
`Observability/FromSolutionCoordinates.lean`. Paper `e1a0fd5`,
`prop:boundary-observability`, lines 1906–1930. -/
theorem boundary_observability_of_pending_observation {K : ℝ} (hK : 1 ≤ K)
    (_hA3 : PropA4.LemmaA3Statement K) (hsmall : PropA4.SmallMassEstimate K) :
    PropA1.Statement K :=
  PropA1.of_propA4 hK (PropA4.of_small_mass_estimate hK hsmall)

end AcExtensionPrinciple

end
