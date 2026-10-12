module

public import AcExtensionPrinciple.Observability.InnerChartConstruction
public import AcExtensionPrinciple.Observability.PropA1

/-!
# The constructed inner chart discharges normalized A.4 and A.1

Paper `e1a0fd5`, `equations.tex` lines 1665–1930.
The constructed inner chart supplies the analytic inputs for normalized A.4 and A.1.
-/

public section

namespace AcExtensionPrinciple

/-- The uniform enclosed-mass observation follows with the constructed
inner chart and no outstanding coordinate premise. Paper `e1a0fd5`,
`prop:boundary-mass-observability`, lines 1665–1913. -/
theorem PropA4.of_constructed_inner_chart {K : ℝ} (hK : 1 ≤ K) : PropA4.Statement K :=
  PropA4.of_inner_chart hK (PropA4.innerChartStatement K)

/-- Normalized boundary observability follows with the constructed
inner chart and no outstanding coordinate premise. Paper `e1a0fd5`,
`prop:boundary-observability`, lines 1915–1930. -/
theorem PropA1.of_constructed_inner_chart {K : ℝ} (hK : 1 ≤ K) : PropA1.Statement K :=
  PropA1.of_inner_chart hK (PropA4.innerChartStatement K)

end AcExtensionPrinciple

end
