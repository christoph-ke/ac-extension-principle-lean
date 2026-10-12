module

public import AcExtensionPrinciple.Observability.FromSolutionEquations
public import AcExtensionPrinciple.Observability.FromSolutionVariation

/-!
# A normalized observability chart constructed from the standing solution

Paper `e1a0fd5`, `equations.tex` lines 1460–1473.
This discharges the full NormalizedChartData interface using the regular incoming extension with
matching derivative at the join.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace NormalizedBoundaryCoordinates

variable {ui b a₀ a₁ a d T K : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The pulled-back standing solution satisfies every normalized chart
field, including both uniform BV bounds and the arrival-time field.
Paper `e1a0fd5`, lines 1460–1473 and 1441–1443. -/
@[expose] noncomputable def chart_data (h : StandingFull ui S) (hK : CylinderKBounds ui S K)
    (ha : a₀ ≤ a) (hd : d ≤ a₁) : NormalizedChartData b T K q.fields := by
  let D := chartCylinder q.axisGraph T
  let f := fun p : ℝ × ℝ => (q.U p.1, q.V p.2)
  have hf : Continuous f := (q.U.continuous.comp continuous_fst).prodMk
    (q.V.continuous.comp continuous_snd)
  have hm : MapsTo f D (pastTriangle ui) := fun p hp => q.source_mem ha hd hp
  refine {
    g := q.axisGraph
    b_pos := c.radius_pos
    T_nonneg := q.T_nonneg
    K_ge_one := hK.1
    continuous_g := q.axisGraph_continuous_monotone.1
    monotone_g := q.axisGraph_continuous_monotone.2.monotoneOn _
    axis_before_boundary := fun s hs => q.axis_before_boundary ha hd hs
    equations := q.chart_equations h ha hd
    continuous_r := h.regularCenter.continuous_r.comp hf.continuousOn hm
    continuous_m := h.regularCenter.continuous_m.comp hf.continuousOn hm
    continuous_phi := ?_
    continuous_lam := ?_
    continuous_nu := ?_
    signs := ?_
    gap := ?_
    axis_values := ?_
    boundary_gauge := fun s hs => q.boundary_gauge h ha hd hs
    incoming_ratio := fun _ _ ht hts hsT hp => q.incoming_ratio h hK ha hd ht hts hsT hp
    axis_reached := fun _ ht hwait => q.axis_reached h hK ha hd ht hwait
    psi_t_variation := q.psi_t_variation h ha hd
    psi_s_variation := q.psi_s_variation h ha hd }
  · apply (h.regularCenter.continuous_phi.comp hf.continuousOn hm).congr
    intro p _
    simp only [Function.comp_apply, f, fields, SSFields.normalizedPullback, sub_zero]
  · exact (h.regularCenter.continuous_lam.comp hf.continuousOn hm).mul
      (q.dV_continuous.comp continuous_snd).continuousOn
  · exact (h.regularCenter.continuous_nu.comp hf.continuousOn hm).mul
      (q.dU_continuous.comp continuous_fst).continuousOn
  · intro s t hp
    have hs := q.source_mem ha hd hp
    refine ⟨mul_pos (h.lam_pos hs) (q.dV_positive t),
      mul_neg_of_neg_of_pos (h.nu_neg hs) (q.dU_positive s), ?_⟩
    simpa only [q.fields_mu] using (h.mu_bounds hs).1
  · intro s t hp
    rw [q.fields_mu]
    exact (hK.2 _ (q.source_mem ha hd hp)).2.2.1
  · intro s hs
    have hu := Icc_subset_Icc ha hd (q.U_mem hs)
    have hp : (q.U s, q.U s) ∈ pastTriangle ui :=
      ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative, le_rfl,
        (hu.2.trans_lt c.terminal_negative).le⟩
    simpa only [fields, SSFields.normalizedPullback, axisGraph, q.V.apply_symm_apply] using
      h.regularCenter.localBV.axis_values (q.U s) hp

end NormalizedBoundaryCoordinates

/-- A regular source cylinder has a normalized chart for its exact boundary duration, with the
source geometric K. The inverse incoming coordinate has the matching affine extension to earlier
labels. Paper `e1a0fd5`, lines 1460–1473. -/
theorem normalized_chart_from_solution {ui b a₀ a₁ a d K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    ∃ q : NormalizedBoundaryCoordinates c a d (c.tau d - c.tau a),
      Nonempty (NormalizedChartData b (c.tau d - c.tau a) K q.fields) := by
  obtain ⟨q⟩ := exists_normalizedBoundaryCoordinates c h hK ha had hd
  exact ⟨q, ⟨q.chart_data h hK ha hd⟩⟩

end AcExtensionPrinciple

end
