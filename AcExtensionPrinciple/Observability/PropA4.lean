module

public import AcExtensionPrinciple.Observability.PropA4InnerChart
public import AcExtensionPrinciple.Observability.PropA4LemmaA3
public import AcExtensionPrinciple.Observability.PropA4Constants
public import AcExtensionPrinciple.Observability.PropA4Exterior
public import AcExtensionPrinciple.Observability.PropA4Amplitude
public import AcExtensionPrinciple.Observability.PropA4AmplitudeRegularity
public import AcExtensionPrinciple.Observability.PropA4Derivatives
public import AcExtensionPrinciple.Observability.PropA4OscillationKernel
public import AcExtensionPrinciple.Observability.PropA4ExteriorDomain
public import AcExtensionPrinciple.Observability.PropA4RemainderBound
public import AcExtensionPrinciple.Observability.PropA4IncomingDerivative
public import AcExtensionPrinciple.Observability.PropA4UnitRadialDerivatives
public import AcExtensionPrinciple.Observability.PropA4LateExterior
public import AcExtensionPrinciple.Observability.PropA4RadialScalar

/-!
# The large-mass regime and final assembly of Proposition A.4

Paper `e1a0fd5`, `equations.tex` lines 1906–1913. The assembly combines
A.3 with the small-mass estimate. That premise is proved by
`PropA4.small_mass_estimate` in `Integration/ObservabilityComplete.lean`,
using `small_mass_estimate_of_inner_chart` and the constructed inner chart.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- The part of A.4 requiring the exterior Volterra and inner-cylinder
argument. It is proved by `PropA4.small_mass_estimate` in
`Integration/ObservabilityComplete.lean`.
Paper `e1a0fd5`, lines 1675–1909. -/
@[expose] def SmallMassEstimate (K : ℝ) : Prop :=
  ∃ ε δ : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧
    ∀ (b : ℝ) (S : SSFields), NormalizedChartData b ((K + 4) * b) K S →
      0 < S.m 0 0 → S.m 0 0 / b ≤ ε →
        δ * S.m 0 0 ≤ chartScalarEnergy S ((K + 4) * b)

/-- A.3 supplies linear mass observation on the large-mass regime, after
restriction to its exact duration. Paper `e1a0fd5`, lines 1910–1911. -/
theorem large_mass_observation {K : ℝ} (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H b : ℝ) (S : SSFields),
      positiveMassDuration K (2 * ε) ≤ H →
      NormalizedChartData b (H * b) K S →
      ε ≤ S.m 0 0 / b → c * S.m 0 0 ≤ chartScalarEnergy S (H * b) := by
  obtain ⟨c₃, hc₃, hobs⟩ := lemmaA3Statement hK
  let c := 2 * (c₃ * (2 * ε) ^ 3 / (1 + |Real.log (2 * ε)|) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro H b S hH h hratio
  have hD : 0 ≤ positiveMassDuration K (2 * ε) := by
    have := le_max_left (K + 1) (1 + Real.log (2 / ((2 * ε) * (1 / (8 * K)))))
    change K + 1 ≤ positiveMassDuration K (2 * ε) at this
    linarith
  have hT : positiveMassDuration K (2 * ε) * b ≤ H * b :=
    mul_le_mul_of_nonneg_right hH h.b_pos.le
  have hshort := restrict h (mul_nonneg hD h.b_pos.le) hT
  have hμ : 2 * ε ≤ S.mu 0 0 := by
    rw [SSFields.mu, (h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩).1, massRatio]
    have hh := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2 by norm_num)
    simpa only [mul_div_assoc] using hh
  have he := hobs (2 * ε) b S (by positivity) (by linarith) hshort hμ 0
  rw [translatedScalarEnergy_zero] at he
  have he' := he.trans (scalarEnergy_mono h (mul_nonneg hD h.b_pos.le) hT)
  have hm := (initial_mass_bounds h).2
  have hcoef : 0 ≤ c₃ * (2 * ε) ^ 3 / (1 + |Real.log (2 * ε)|) ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hcoef
  calc
    c * S.m 0 0 = (c₃ * (2 * ε) ^ 3 / (1 + |Real.log (2 * ε)|) ^ 2) *
        (2 * S.m 0 0) := by dsimp [c]; ring
    _ ≤ (c₃ * (2 * ε) ^ 3 / (1 + |Real.log (2 * ε)|) ^ 2) * b := hh
    _ = c₃ * (2 * ε) ^ 3 * b / (1 + |Real.log (2 * ε)|) ^ 2 := by ring
    _ ≤ chartScalarEnergy S (H * b) := he'

/-- Given the small-mass estimate, A.3 assembles both regimes into
the exact uniform statement of A.4. Both final constants are chosen before
radius, solution, and mass ratio. Paper `e1a0fd5`, lines 1906–1913. -/
theorem of_small_mass_estimate {K : ℝ} (hK : 1 ≤ K)
    (hsmall : SmallMassEstimate K) : Statement K := by
  obtain ⟨ε, δ, hε, hε1, hδ, hsmall⟩ := hsmall
  obtain ⟨c, hc, hlarge⟩ := large_mass_observation hK hε hε1
  let H := max (K + 4) (positiveMassDuration K (2 * ε))
  refine ⟨H, min δ c, le_max_left _ _, lt_min hδ hc, ?_⟩
  intro b S h
  have hM := (initial_mass_bounds h).1
  by_cases hM0 : S.m 0 0 = 0
  · simpa [hM0] using h.scalar_energy_nonneg
  by_cases hratio : S.m 0 0 / b ≤ ε
  · have hT : (K + 4) * b ≤ H * b :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) h.b_pos.le
    have hU : 0 ≤ (K + 4) * b := mul_nonneg (by linarith) h.b_pos.le
    have hshort := restrict h hU hT
    exact (mul_le_mul_of_nonneg_right (min_le_left δ c) hM).trans
      ((hsmall b S hshort (lt_of_le_of_ne hM (Ne.symm hM0)) hratio).trans
        (scalarEnergy_mono h hU hT))
  · exact (mul_le_mul_of_nonneg_right (min_le_right δ c) hM).trans
      (hlarge H b S (le_max_right _ _) h (le_of_not_ge hratio))

end PropA4
end AcExtensionPrinciple

end
