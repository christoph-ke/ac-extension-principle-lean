module

public import AcExtensionPrinciple.Integration.BoundaryFromSmallMass

/-!
# Appendix A packages for the constructed source charts

Paper `e1a0fd5`, equations.tex lines 1460–1531 and 1665–1930.
The standing class constructs every original cylinder's normalized chart,
including each constant scalar translation, and chooses its geometric K.
The small-mass premises below are supplied by
`StandingFull.integration_small_mass_estimate` in `Integration/ObservabilityComplete.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma A.2 on an actual source cylinder, including every scalar translation.
The standing class supplies the chart and its BV hypotheses. Paper `e1a0fd5`,
`lem:observability-axis-amplitude`, lines 1460–1531 and 1923–1929. -/
theorem lemmaA2_from_solution {b a₀ a₁ a d : ℝ}
    (c : DecayCylinder ui S b a₀ a₁) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁)
    (shift : ℝ) :
    ∃ q : NormalizedBoundaryCoordinates c a d (c.tau d - c.tau a),
      ∃ hc : NormalizedChartData b (c.tau d - c.tau a) h.integrationCylinderK
        (q.fields.integrationScalarShift shift), LemmaA2Conclusions hc := by
  obtain ⟨q⟩ := exists_normalizedBoundaryCoordinates c h h.integrationCylinderK_bounds ha had hd
  let hc := q.chart_data h h.integrationCylinderK_bounds ha hd
  let hcshift := hc.integrationScalarShift shift
    (q.integration_lam_t_variation h ha hd) (q.integration_nu_s_variation h ha hd)
  exact ⟨q, hcshift, lemmaA2 hcshift⟩

/-- A.4 at the source's geometric K, with only its small-mass estimate remaining.
Paper `e1a0fd5`, `prop:boundary-mass-observability`, lines 1665–1913. -/
theorem lemmaA4_of_small_mass
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK) :
    PropA4.Statement h.integrationCylinderK :=
  boundary_mass_observability_of_small_mass h.integrationCylinderK_bounds.1 hsmall

/-- A.1 at the source's geometric K, with only its small-mass estimate remaining.
Paper `e1a0fd5`, `prop:boundary-observability`, lines 1915–1930. -/
theorem lemmaA1_of_small_mass
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK) :
    PropA1.Statement h.integrationCylinderK :=
  boundary_observability_of_small_mass h.integrationCylinderK_bounds.1 hsmall

end AcExtensionPrinciple.StandingFull

end
