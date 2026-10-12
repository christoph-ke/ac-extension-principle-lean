module

public import AcExtensionPrinciple.Integration.SourceAppendix
public import AcExtensionPrinciple.Observability.InnerChartObservability

/-!
# Unconditional source observability and boundary contraction

Paper `e1a0fd5`, equations.tex lines 751–788 and 1665–1930.
The completed inner-chart construction discharges the small-mass premise
at the same geometric K chosen for the source solution.
-/

public section

namespace AcExtensionPrinciple

/-- The small-mass estimate follows from the constructed inner chart for
every K ≥ 1. Paper `e1a0fd5`, `prop:boundary-mass-observability`,
equations.tex lines 1675–1909. -/
theorem PropA4.small_mass_estimate {K : ℝ} (hK : 1 ≤ K) : PropA4.SmallMassEstimate K :=
  PropA4.small_mass_estimate_of_inner_chart hK (PropA4.innerChartStatement K)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The source solution's geometric K satisfies the complete small-mass
estimate. Paper `e1a0fd5`, `prop:boundary-mass-observability`,
equations.tex lines 1675–1909. -/
theorem integration_small_mass_estimate : PropA4.SmallMassEstimate h.integrationCylinderK :=
  PropA4.small_mass_estimate h.integrationCylinderK_bounds.1

/-- Complete A.4 at the source's geometric K. Paper `e1a0fd5`,
`prop:boundary-mass-observability`, equations.tex lines 1665–1913. -/
theorem lemmaA4 : PropA4.Statement h.integrationCylinderK :=
  h.lemmaA4_of_small_mass h.integration_small_mass_estimate

/-- Complete A.1 at the source's geometric K. Paper `e1a0fd5`,
`prop:boundary-observability`, equations.tex lines 1915–1930. -/
theorem lemmaA1 : PropA1.Statement h.integrationCylinderK :=
  h.lemmaA1_of_small_mass h.integration_small_mass_estimate

/-- Exact boundary contraction under the standing assumptions alone.
All normalized-chart and scalar-translation premises are discharged.
Paper `e1a0fd5`, `lem:boundary-contraction`, equations.tex lines 751–788. -/
theorem lemma25 : ∃ H C rho : ℝ, Lemma25Statement ui S H C rho :=
  h.lemma25_of_small_mass h.integration_small_mass_estimate

end StandingFull

end AcExtensionPrinciple

end
