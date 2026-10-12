module

public import AcExtensionPrinciple.Minimal.ScalarAxis
public import AcExtensionPrinciple.Minimal.OneSidedBackward

/-!
# Restore the joint normalized scalar traces from the four one-sided traces

Paper `e1a0fd5`, `equations.tex` lines 99–105, 220–261,
`eq:normalized-scalar-transport`, `eq:regular-axis-scalar-traces`.
Joint scalar continuity has already been derived without joint normalized traces.
Outgoing and backward incoming damping now recover the two joint normalized
traces, before scalar AC and λ continuity are restored.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Outgoing damping and derived scalar continuity recover the joint incoming
normalized trace. Paper `e1a0fd5`, lines 247–261, 974–986,
`eq:regular-axis-scalar-traces`, `eq:incoming-scalar-comparison`. -/
theorem StandingAssumptions.axis_dupsi_trace {ui a : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.dupsi p.1 p.2 / S.nu p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) :=
  h.oneSided_dupsi_joint_of_phi_continuous ha
    (h.continuous_phi (a, a) (axis_subset_pastTriangle ui ha))

/-- Backward incoming damping and derived scalar continuity recover the joint
outgoing normalized trace. Neither λ continuity nor a uniform blueshift-tail
estimate is used. Paper `e1a0fd5`, lines 99–105, 247–261,
`eq:normalized-scalar-transport`, `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.axis_dvpsi_trace {ui a : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.mp
    (h.continuous_phi (a, a) (axis_subset_pastTriangle ui ha)) (ε / 2) (by positivity)
  refine ⟨min δ (-a / 2), lt_min hδ (by linarith [ha.2.1]), ?_⟩
  intro p hp hpd
  have hpdφ := hpd.trans_le (min_le_left _ _)
  have hv : p.2 < 0 := by
    have hd := (show dist p.2 a ≤ dist p (a, a) from le_max_right _ _).trans_lt
      (hpd.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at hd
    linarith [ha.2.1]
  have hc := h.oneSided_datum_comparison hp.1 hv (L := S.phi a a) (M := ε / 2) (by
    intro s hs
    have hsQ : (s, p.2) ∈ pastTriangle ui :=
      ⟨hp.1.1.trans hs.1, hs.2.trans_lt hv, hs.2, hp.1.2.2.2⟩
    have hnear := oneSided_box_near hpdφ hs ⟨hp.1.2.2.1, le_rfl⟩
    have hh := hb hsQ hnear
    rw [Real.dist_eq] at hh
    exact hh.le)
  rw [Real.dist_eq]
  exact hc.trans_lt (by linarith)

end AcExtensionPrinciple

end
