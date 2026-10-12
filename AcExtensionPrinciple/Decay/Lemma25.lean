module

public import AcExtensionPrinciple.Decay.Lemma25Analysis
public import AcExtensionPrinciple.Observability.FromSolutionObservation
public import AcExtensionPrinciple.Observability.FromSolutionEnergy
public import AcExtensionPrinciple.Observability.FromSolutionRealization

/-!
# Lemma 2.5 from normalized boundary observability

Paper `e1a0fd5`, `lem:boundary-contraction`, `equations.tex` lines 751–788.
The result proves `Lemma25Statement`. The constructed source
chart and class energy identity discharge the coordinate and Lemma 2.4
obligations. Dissipation integrability follows from the AC balance.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

/-- The observed initial expression is exactly the cylinder energy when
shift is the initial outgoing datum. Paper `e1a0fd5`, line 771. -/
theorem cylinder_observed_initial_eq {ui b a₀ a₁ a : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (ha : a ∈ Icc a₀ a₁) :
    b / 2 * ((cylinderPhi S c a - cylinderDatum S c a) ^ 2 -
      Real.log (1 - S.mu a (c.v a))) = decayCylinderEnergy S c a := by
  simp only [decayCylinderEnergy, boundaryEnergy, SSFields.mu, (c.points a ha).2.2]
  rw [sub_sq_comm]

/-- The contraction constants lie in the stated ranges. Paper `e1a0fd5`,
`eq:contraction-from-dissipation`, lines 780–787. -/
theorem lemma25_constants {H sigma : ℝ} (hH : 0 < H)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    0 < 1 + H / 2 + 2 / sigma ∧ 0 < 1 - sigma / 4 ∧ 1 - sigma / 4 < 1 := by
  refine ⟨by positivity, ?_, ?_⟩ <;> linarith

/-- Lemma 2.4 plus the physical form of Prop A.1 implies Lemma 2.5 exactly, with C=1+H/2+2/σ and
ρ=1-σ/4. The observability premise is supplied by `cylinder_observability_of_normalized_propA1` in
`Integration/BoundaryFromSmallMass.lean`, using normalized A.1 and the boundary measure transport
theorem. Paper `e1a0fd5`, lines 762–788. -/
theorem lemma25_of_cylinder_observability {ui H sigma : ℝ} {S : SSFields}
    (h : StandingFull ui S) (h24 : Lemma24Statement ui S)
    (hH : 0 < H) (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (hobs : CylinderObservabilityBound ui S H sigma) :
    Lemma25Statement ui S H (1 + H / 2 + 2 / sigma) (1 - sigma / 4) := by
  obtain ⟨hC, hr0, hr1⟩ := lemma25_constants hH hs hs1
  refine ⟨hH, hC, hr0, hr1, ?_⟩
  intro b a₀ a₁ c a d ha had hd htime
  have hb : 0 < b := c.radius_pos
  obtain ⟨C24, hC24, h24all⟩ := h24
  obtain ⟨hcomp, hmAC, hphiAC, hPAC, hEAC, hbal, hstab⟩ := h24all b a₀ a₁ c
  have hsub : uIcc a d ⊆ uIcc a₀ a₁ := by
    rw [uIcc_of_le had, uIcc_of_le c.ordered]
    exact Icc_subset_Icc ha hd
  have hphi := hphiAC.mono hsub
  have hP := hPAC.mono hsub
  have hE := hEAC.mono hsub
  have hmem {u : ℝ} (hu : u ∈ Icc a d) : u ∈ Icc a₀ a₁ :=
    ⟨ha.trans hu.1, hu.2.trans hd⟩
  have hp {u : ℝ} (hu : u ∈ Icc a₀ a₁) : (u, c.v u) ∈ pastTriangle ui :=
    ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
      (c.points u hu).1.le, (c.points u hu).2.1⟩
  let E := decayCylinderEnergy S c
  let P := cylinderDatum S c
  let phi := cylinderPhi S c
  let w := fun u => -S.nu u (c.v u)
  let D := fun u => b ^ 2 / 2 * deriv phi u ^ 2 / w u
  have hw : ContinuousOn w (Icc a d) :=
    (h.regularCenter.continuous_nu.comp
      (continuousOn_id.prodMk (c.smooth_v.continuousOn.mono (Icc_subset_Icc ha hd)))
      (fun u hu => hp (hmem hu))).neg
  have hwpos (u : ℝ) (hu : u ∈ Icc a d) : 0 < w u := neg_pos.mpr (h.nu_neg (hp (hmem hu)))
  have hE0 (u : ℝ) (hu : u ∈ Icc a d) : 0 ≤ E u := by
    have hc := (hcomp u (hmem hu)).2.1
    exact (mul_nonneg (by positivity) (sq_nonneg _)).trans hc
  have hA (u : ℝ) (hu : u ∈ Icc a d) : b / 2 * (P u - phi u) ^ 2 ≤ E u :=
    (hcomp u (hmem hu)).2.1
  have hbalance : ∀ᵐ u ∂volume, u ∈ Ioo a d → deriv E u + D u = b * (P u - phi u) * deriv P u := by
    filter_upwards [hbal] with u hu huI
    exact hu ⟨ha.trans_lt huI.1, huI.2.trans_le hd⟩
  have hcoeff : ContinuousOn (fun u => P u - phi u) (Icc a d) := by
    have hc : ContinuousOn (P - phi) (Icc a d) := by
      simpa only [uIcc_of_le had] using hP.continuousOn.sub hphi.continuousOn
    exact hc.congr (fun _ _ => rfl)
  have hD := dissipation_integrable_of_ac_balance had hE hP hcoeff hbalance
  have hIntBalance : E d - E a + (∫ u in a..d, D u) =
      ∫ u in a..d, b * (P u - phi u) * deriv P u := by
    apply boundary_energy_integral_balance hE hD
    filter_upwards [hbalance, show ∀ᵐ u : ℝ, u ≠ d by simp [ae_iff]] with u hu hune
    intro huI
    rw [uIoc_of_le had] at huI
    exact hu ⟨huI.1, lt_of_le_of_ne huI.2 hune⟩
  have hBV : BoundedVariationOn P (Icc a d) := by
    simpa only [uIcc_of_le had] using hP.boundedVariationOn
  have hstability (u : ℝ) (hu : u ∈ Icc a d) : Real.sqrt (E u) ≤ Real.sqrt (E a) +
      Real.sqrt (b / 2) * (eVariationOn P (Icc a d)).toReal := by
    have hv : cylinderVariation S c a u ≤ (eVariationOn P (Icc a d)).toReal := by
      apply ENNReal.toReal_mono hBV
      exact eVariationOn.mono _ (Icc_subset_Icc le_rfl hu.2)
    apply (hstab a u ha hu.1 (hu.2.trans hd)).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg (b / 2)))
  have hwork := integrated_work_le had c.radius_pos hP hphi hA hstability
  have hobserved : sigma * E a ≤ ∫ u in a..d, w u * (P u - P a) ^ 2 + 2 * D u := by
    have hob := hobs b a₀ a₁ c a d ha had hd htime (P a)
    have hinit := cylinder_observed_initial_eq c (hmem (left_mem_Icc.mpr had))
    rw [show sigma * b / 2 = sigma * (b / 2) by ring, mul_assoc, hinit] at hob
    convert hob using 1
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only [w, P, D, phi]
    ring
  have hdiss := observed_dissipation_le had hP hw (fun u hu => (hwpos u hu).le) hD
    ((c.clock a d ha had hd).2.symm.trans htime) hobserved
  exact energy_contraction_of_dissipation c.radius_pos hH hs hs1
    (hE0 a (left_mem_Icc.mpr had)) ENNReal.toReal_nonneg hIntBalance hdiss hwork

/-- Generic assembly of `Lemma25Statement` from Prop A.1 and chart
realization, discharged by `cylinder_chart_realization` below. Constants
are chosen before all cylinder variables. Paper
`e1a0fd5`, `lem:boundary-contraction`, lines 751–788, 1460–1473, 1923–1929. -/
theorem lemma25_of_propA1_and_chart_realization {ui K : ℝ} {S : SSFields}
    (h : StandingFull ui S)
    (hA1 : PropA1Statement K)
    (hcharts : ∀ H : ℝ, 0 < H → CylinderChartRealization ui S K H) :
    ∃ H C rho : ℝ, Lemma25Statement ui S H C rho := by
  obtain ⟨H, sigma, hH, hs, hs1, hobs⟩ := hA1
  exact ⟨H, 1 + H / 2 + 2 / sigma, 1 - sigma / 4,
    lemma25_of_cylinder_observability h h.lemma24_statement hH hs hs1
      (cylinder_observability_of_chart_realization (hcharts H hH) hobs)⟩

/-- Lemma 2.5 from normalized Prop A.1: the source class discharges both Lemma 2.4 and the complete
normalized chart and boundary measure realization. The K premise is the geometric conclusion of
Lemma 1.1, discharged in the source theorem below. Paper `e1a0fd5`, `lem:boundary-contraction`,
lines 751–788, 1460–1473 and 1923–1929. -/
theorem lemma25_of_propA1 {ui K : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hK : CylinderKBounds ui S K)
    (hA1 : PropA1Statement K) :
    ∃ H C rho : ℝ, Lemma25Statement ui S H C rho :=
  lemma25_of_propA1_and_chart_realization h hA1
    (fun _ _ => cylinder_chart_realization h hK)

/-- The source-level Lemma 2.5 with the quantifiers of `Lemma25Statement`.
Normalized Prop A.1 is a helper premise, proved by
`PropA1.of_constructed_inner_chart` in `Observability/InnerChartObservability.lean`;
all coordinates, geometric bounds and Lemma 2.4 come from the standing
solution. Paper `e1a0fd5`, `lem:boundary-contraction`, lines 751–788. -/
theorem StandingFull.lemma25_boundary_contraction {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S)
    (hA1 : ∀ K : ℝ, 1 ≤ K → PropA1Statement K) :
    ∃ H C rho : ℝ, Lemma25Statement ui S H C rho := by
  obtain ⟨K, hK⟩ := h.exists_cylinder_K
  exact lemma25_of_propA1 h hK (hA1 K hK.1)

end AcExtensionPrinciple

end
