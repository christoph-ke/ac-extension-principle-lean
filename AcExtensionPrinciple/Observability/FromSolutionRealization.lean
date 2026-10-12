module

public import AcExtensionPrinciple.Observability.FromSolutionChart
public import AcExtensionPrinciple.Observability.FromSolutionObservation
public import AcExtensionPrinciple.Observability.FromSolutionEnergy

/-!
# Exact realization and boundary measure transport of the source chart

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1923–1929.
The constructed chart discharges the earlier realization obligation.
Boundary scalar AC is obtained from the source Lemma 2.4 discharge.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace NormalizedBoundaryCoordinates

variable {ui b a₀ a₁ a d T : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The clock inverse returns the original cylinder parameter. Paper
`e1a0fd5`, lines 1460 and 1926–1927. -/
theorem inverse_clock (u : ℝ) (hu : u ∈ Icc a d) :
    q.U (normalizedCylinderClock c a u) = u := by
  rw [← q.clock u hu, q.U.apply_symm_apply]

/-- The entire boundary observation integral has the physical measure dτ_b=(-ν_b)du, with exactly
the radial derivative and scalar derivative in the boundary measure transport. Paper `e1a0fd5`,
lines 1923–1929. -/
theorem observation_integral_eq (h : StandingFull ui S)
    (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) (shift : ℝ) :
    (∫ s in 0..T, (q.fields.dvpsi s s - shift) ^ 2 +
      deriv (fun s => chartPsi q.fields s s) s ^ 2) =
    ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
      b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u)) := by
  obtain ⟨_, _, h24⟩ := h.lemma24_statement
  have hsub : uIcc a d ⊆ uIcc a₀ a₁ := by
    rw [uIcc_of_le had, uIcc_of_le c.ordered]
    exact Icc_subset_Icc ha hd
  have hphi := (h24 b a₀ a₁ c).2.2.1.mono hsub
  have hFmem (u : ℝ) (hu : u ∈ Icc a d) : normalizedCylinderClock c a u ∈ Icc 0 T := by
    rw [← q.clock u hu]
    constructor
    · simpa only [← q.U_initial, q.U.symm_apply_apply] using q.U.symm.monotone hu.1
    · simpa only [← q.U_terminal, q.U.symm_apply_apply] using q.U.symm.monotone hu.2
  apply normalized_clock_observation_integral_eq h c ha had hd q.duration
    q.U q.V q.dU q.dV hphi q.inverse_clock
  · intro u hu
    have hs := hFmem u (Ioo_subset_Icc_self hu)
    have he := q.U_derivative (normalizedCylinderClock c a u)
    rw [q.U_jacobian _ hs, q.inverse_clock u (Ioo_subset_Icc_self hu)] at he
    exact he
  · intro u hu
    simpa only [q.inverse_clock u hu] using q.V_jacobian _ (hFmem u hu)
  · intro s hs
    exact ⟨Icc_subset_Icc ha hd (q.U_mem hs), q.boundary s hs⟩

end NormalizedBoundaryCoordinates

/-- Normalized chart and boundary measure realization for every regular physical subinterval, from
the standing solution and its geometric K alone. Paper `e1a0fd5`, lines 1460–1473 and 1923–1929. -/
theorem cylinder_chart_realization {ui K H : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hK : CylinderKBounds ui S K) :
    CylinderChartRealization ui S K H := by
  intro b a₀ a₁ c a d ha had hd htime
  obtain ⟨q, hchart⟩ := normalized_chart_from_solution c h hK ha had hd
  refine ⟨q.fields, ?_, ?_, ?_, ?_⟩
  · simpa only [htime] using hchart
  · simp only [NormalizedBoundaryCoordinates.fields, SSFields.normalizedPullback,
      q.boundary 0 ⟨le_rfl, q.T_nonneg⟩, q.U_initial, sub_zero, cylinderPhi]
  · simp only [q.fields_mu, q.boundary 0 ⟨le_rfl, q.T_nonneg⟩, q.U_initial]
  · intro shift
    simpa only [htime] using q.observation_integral_eq h ha had hd shift

end AcExtensionPrinciple

end
