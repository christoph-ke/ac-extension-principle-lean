module

public import AcExtensionPrinciple.Observability.InnerChartVariation

/-!
# A re-normalized inner chart with the same geometric K

Paper `e1a0fd5`, `equations.tex` lines 1877–1907, especially line 1901.
The ten equations, full axis, regular gauge, and both compact uniform BV
bounds are inherited from the outer normalized chart.
-/

public section

namespace AcExtensionPrinciple.InnerBoundaryCoordinates

open Set MeasureTheory

variable {b T K a s₀ s₁ T' : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable {c : InnerCylinder h a s₀ s₁} (q : InnerBoundaryCoordinates c T')

/-- The constructed coordinates give every field of a normalized inner
chart with exactly the original K. Paper `e1a0fd5`, line 1901,
lines 1460–1473 and 1877–1907. -/
@[expose] noncomputable def chart_data : NormalizedChartData a T' K q.fields := by
  let D := chartCylinder q.axisGraph T'
  let f := fun p : ℝ × ℝ => (q.U p.1, q.V p.2)
  have hf : Continuous f := (q.U.continuous.comp continuous_fst).prodMk
    (q.V.continuous.comp continuous_snd)
  have hm : MapsTo f D (chartCylinder h.g T) := fun p hp => q.source_mem hp
  refine {
    g := q.axisGraph
    b_pos := c.a_pos
    T_nonneg := q.T_nonneg
    K_ge_one := h.K_ge_one
    continuous_g := q.axisGraph_regular.1
    monotone_g := q.axisGraph_regular.2
    axis_before_boundary := fun _ hx => q.axis_before_boundary hx
    equations := q.chart_equations
    continuous_r := h.continuous_r.comp hf.continuousOn hm
    continuous_m := h.continuous_m.comp hf.continuousOn hm
    continuous_phi := h.continuous_phi.comp hf.continuousOn hm
    continuous_lam := ?_
    continuous_nu := ?_
    signs := ?_
    gap := ?_
    axis_values := ?_
    boundary_gauge := fun _ hx => q.boundary_gauge hx
    incoming_ratio := fun _ _ hy hyx hxT hp => q.incoming_ratio hy hyx hxT hp
    axis_reached := fun _ hy hwait => q.axis_reached hy hwait
    psi_t_variation := q.psi_t_variation
    psi_s_variation := q.psi_s_variation }
  · exact (h.continuous_lam.comp hf.continuousOn hm).mul
      (q.dV_continuous.comp continuous_snd).continuousOn
  · exact (h.continuous_nu.comp hf.continuousOn hm).mul
      (q.dU_continuous.comp continuous_fst).continuousOn
  · intro x y hp
    have hs := h.signs _ _ (q.source_mem hp)
    exact ⟨mul_pos hs.1 (q.dV_positive y),
      mul_neg_of_neg_of_pos hs.2.1 (q.dU_positive x), hs.2.2⟩
  · intro x y hp
    rw [q.fields_mu]
    exact h.gap _ _ (q.source_mem hp)
  · intro x hx
    have hs := (c.source_mem (q.U_mem hx)).1
    simpa only [fields, PropA4.separatePullback, axisGraph, q.V.apply_symm_apply]
      using h.axis_values (q.U x) ⟨hs.1, hs.2.1⟩

end AcExtensionPrinciple.InnerBoundaryCoordinates

end
