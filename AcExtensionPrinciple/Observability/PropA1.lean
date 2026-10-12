module

public import AcExtensionPrinciple.Observability.PropA4
public import AcExtensionPrinciple.Observability.PropA4SmallMass
public import AcExtensionPrinciple.Observability.PropA4Mass

/-!
# Proposition A.1 from uniform mass observation

Paper `e1a0fd5`, `prop:boundary-observability`, `equations.tex` lines
1915–1930. This proves the normalized-chart implication from A.4.
The A.4 premise is proved by `PropA4.of_constructed_inner_chart` in
`Observability/InnerChartObservability.lean`. The chart scalar is the
translated scalar used in Lemma A.2.
-/

public section

namespace AcExtensionPrinciple
namespace PropA1

/-- Boundary observability in the normalized chart. The constants precede
all radii and charts. Paper `e1a0fd5`, `prop:boundary-observability`,
`eq:imported-boundary-observability`, lines 1453–1455 and 1915–1930. -/
@[expose] def Statement (K : ℝ) : Prop :=
  ∃ H σ : ℝ, K + 4 ≤ H ∧ 0 < σ ∧ σ ≤ 1 ∧
    ∀ (b : ℝ) (S : SSFields), NormalizedChartData b (H * b) K S →
      σ * chartShiftedEnergy b S 0 ≤ chartScalarEnergy S (H * b)

/-- A.4 and the amplitude estimate give A.1 with explicit observation
constant `c/(K(c+1))`. No positive initial-mass premise is needed.
Paper `e1a0fd5`, proof of `prop:boundary-observability`, lines 1915–1920. -/
theorem of_mass_observation {b T K c : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T)
    (hc : 0 < c) (hm : c * S.m 0 0 ≤ chartScalarEnergy S T) :
    0 < c / (K * (c + 1)) ∧ c / (K * (c + 1)) ≤ 1 ∧
      c / (K * (c + 1)) * chartShiftedEnergy b S 0 ≤ chartScalarEnergy S T :=
  observability_assembly h.K_ge_one hc (PropA4.initial_shiftedEnergy_le h hT) hm

/-- Proposition A.1 follows from Proposition A.4 uniformly in all normalized
charts with the same K. Paper `e1a0fd5`, `prop:boundary-observability`,
lines 1915–1930. -/
theorem of_propA4 {K : ℝ} (hK : 1 ≤ K) (hA4 : PropA4.Statement K) : Statement K := by
  obtain ⟨H, c, hH, hc, hm⟩ := hA4
  have hσ := observability_assembly (F := 0) (E := 0) (m := 0) hK hc
    (by simp) (by simp)
  refine ⟨H, c / (K * (c + 1)), hH, hσ.1, hσ.2.1, ?_⟩
  intro b S h
  have hT : K * b ≤ H * b := mul_le_mul_of_nonneg_right (by linarith) h.b_pos.le
  exact (of_mass_observation h hT hc (hm b S h)).2.2

/-- Normalized A.1 conditional on the small-mass estimate, proved by
`PropA4.small_mass_estimate` in `Integration/ObservabilityComplete.lean`. Paper `e1a0fd5`,
`prop:boundary-observability`, lines 1915–1930. -/
theorem of_small_mass_estimate {K : ℝ} (hK : 1 ≤ K)
    (hsmall : PropA4.SmallMassEstimate K) : Statement K :=
  of_propA4 hK (PropA4.of_small_mass_estimate hK hsmall)

/-- Normalized A.1 from the inner-coordinate interface, supplied by
`PropA4.innerChartStatement` in `Observability/InnerChartConstruction.lean`. Paper
`e1a0fd5`, `prop:boundary-observability`, lines 1915–1930. -/
theorem of_inner_chart {K : ℝ} (hK : 1 ≤ K)
    (hchart : PropA4.InnerChartStatement K) : Statement K :=
  of_propA4 hK (PropA4.of_inner_chart hK hchart)

/-- The inequality in A.1 written using the displayed logarithmic energy.
Paper `e1a0fd5`, `eq:imported-boundary-observability`, lines 1922–1930.
The original-coordinate and constant-translation identities are a separate
coordinate interface; here `S.phi` is already the translated scalar. -/
theorem displayed_inequality {b T K c : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T)
    (hc : 0 < c) (hm : c * S.m 0 0 ≤ chartScalarEnergy S T) :
    (c / (K * (c + 1))) * (b / 2) *
      (S.phi 0 0 ^ 2 - Real.log (1 - massRatio b (S.m 0 0))) ≤
        chartScalarEnergy S T := by
  have hh := (of_mass_observation h hT hc hm).2.2
  have hr := (h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩).1
  simpa only [chartShiftedEnergy, boundaryEnergy, chartPsi, hr,
    mul_div_cancel_left₀ _ h.b_pos.ne', mul_assoc] using hh

end PropA1
end AcExtensionPrinciple

end
