module

public import AcExtensionPrinciple.Integration.ScalarTranslation
public import AcExtensionPrinciple.Integration.SourceChartVariation
public import AcExtensionPrinciple.Integration.Observability
public import AcExtensionPrinciple.Decay.Lemma25

/-!
# Source boundary contraction from the remaining small-mass estimate

Paper `e1a0fd5`, equations.tex lines 751–788, 1460–1480 and 1923–1929.
The normalized Appendix A statement and `CylinderObservabilityBound` differ in their
scalar-translation quantifier. Translating the constructed source chart
bridges that difference; its expansion BV follows from the standing class.
The small-mass premise is supplied by `PropA4.small_mass_estimate` in
`Integration/ObservabilityComplete.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The unshifted normalized A.1 package gives every scalar shift on every
source cylinder. Expansion BV in the translated chart is discharged by the
source class and the constructed inverse Jacobians. Paper `e1a0fd5`,
`eq:imported-boundary-observability`, lines 762–769 and 1923–1929. -/
theorem cylinder_observability_of_normalized_propA1 {ui K : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hK : CylinderKBounds ui S K)
    (hA1 : PropA1.Statement K) :
    ∃ H sigma : ℝ, 0 < H ∧ 0 < sigma ∧ sigma ≤ 1 ∧
      CylinderObservabilityBound ui S H sigma := by
  obtain ⟨H, sigma, hH, hs, hs1, hobs⟩ := hA1
  refine ⟨H, sigma, by linarith [hK.1], hs, hs1, ?_⟩
  intro b a₀ a₁ c a d ha had hd htime shift
  obtain ⟨q⟩ := exists_normalizedBoundaryCoordinates c h hK ha had hd
  let hc := q.chart_data h hK ha hd
  let hcshift := hc.integrationScalarShift shift
    (q.integration_lam_t_variation h ha hd) (q.integration_nu_s_variation h ha hd)
  have hchart : NormalizedChartData b (H * b) K (q.fields.integrationScalarShift shift) := by
    simpa only [htime] using hcshift
  have ho := hobs b (q.fields.integrationScalarShift shift) hchart
  rw [← htime, hc.integrationScalarShift_initial shift,
    hc.integrationScalarShift_energy shift] at ho
  have hi := q.observation_integral_eq h ha had hd shift
  change PropA4.translatedScalarEnergy q.fields (c.tau d - c.tau a) shift = _ at hi
  rw [hi] at ho
  have hphi : q.fields.phi 0 0 = cylinderPhi S c a := by
    simp only [q.fields_phi, q.boundary 0 ⟨le_rfl, q.T_nonneg⟩,
      q.U_initial, cylinderPhi]
  have hmu : q.fields.mu 0 0 = S.mu a (c.v a) := by
    rw [q.fields_mu, q.U_initial, q.boundary 0 ⟨le_rfl, q.T_nonneg⟩, q.U_initial]
  rw [hphi, hmu] at ho
  convert ho using 1
  ring

/-- Exact Lemma 2.5 from the chosen solution's K and its small-mass estimate.
The normalized A.1 assembly, all translations and all chart premises are
proved internally. Paper `e1a0fd5`, `lem:boundary-contraction`, lines 751–788;
`prop:boundary-observability`, lines 1915–1930. -/
theorem StandingFull.lemma25_of_small_mass {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S)
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK) :
    ∃ H C rho : ℝ, Lemma25Statement ui S H C rho := by
  obtain ⟨H, sigma, hH, hs, hs1, hobs⟩ := cylinder_observability_of_normalized_propA1 h
    h.integrationCylinderK_bounds
    (boundary_observability_of_small_mass h.integrationCylinderK_bounds.1 hsmall)
  exact ⟨H, 1 + H / 2 + 2 / sigma, 1 - sigma / 4,
    lemma25_of_cylinder_observability h h.lemma24 hH hs hs1 hobs⟩

end AcExtensionPrinciple

end
