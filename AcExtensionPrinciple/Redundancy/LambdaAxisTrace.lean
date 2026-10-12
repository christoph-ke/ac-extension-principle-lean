module

public import AcExtensionPrinciple.Redundancy.FluxVariation

/-!
# Outgoing traces of the normalized expansion without joint λ continuity
Paper commit `e1a0fd5`, `equations.tex` lines 220–275,
`eq:regular-axis`, `eq:regular-axis-scalar-traces`.
The scalar traces give continuous μ at the axis; retained outgoing AC gives the λ trace.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The core mass ratio is continuous at every axis point, including stored axis values.
Paper `e1a0fd5`, lines 247–275, `eq:regular-axis-scalar-traces`. -/
theorem q1_mu_axis_continuous {ui a : ℝ} {S : SSFields} (h : Q1StandingCore ui S)
    (ha : (a, a) ∈ axis ui) :
    ContinuousWithinAt (fun p : ℝ × ℝ => S.mu p.1 p.2) (pastTriangle ui) (a, a) := by
  have hzero : S.mu a a = 0 := by
    simp [SSFields.mu, massRatio,
      (h.regularCenter.localBV.axis_values a (axis_subset_pastTriangle ui ha)).1]
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp (q1_mu_axis_trace h ha) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpd
  rw [hzero]
  by_cases hpa : p ∈ axis ui
  · have hpzero : S.mu p.1 p.2 = 0 := by
      rw [hpa.2.2]
      simp [SSFields.mu, massRatio,
        (h.regularCenter.localBV.axis_values p.1
          (axis_subset_pastTriangle ui (show (p.1, p.1) ∈ axis ui from
            ⟨hpa.1, hpa.2.1, rfl⟩))).1]
    simp [hpzero, hε]
  · exact hd ⟨hp, hpa⟩ hpd

/-- μ is jointly continuous without the λ continuity field. The off-axis proof only divides
retained continuous r and m. Paper `e1a0fd5`, lines 220–275, `eq:scalar-and-mass-ratio`. -/
theorem continuous_mu_without_continuous_lam {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) :
    ContinuousOn (fun p => S.mu p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have heq : p = (p.1, p.1) := Prod.ext rfl he.symm
    rw [heq]
    exact q1_mu_axis_continuous h.toQ1StandingCore ha
  · exact ((continuousWithinAt_const.mul (h.continuous_m p hp)).div
      (h.continuous_r p hp) (h.toQ1StandingCore.r_pos hp he).ne')

/-- log κ is continuous on every outgoing characteristic, including its axis endpoint,
without joint λ continuity. Paper `e1a0fd5`, lines 220–275, `eq:normalized-expansions`. -/
theorem q1_log_kappa_out_continuous {ui u : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (fun v => Real.log (S.kappa u v)) (Icc u 0) := by
  have hs := outSeg_subset_triangle hu hu0 le_rfl le_rfl
  have hl := (h.ac_lam_out u u 0 hu0.le hs).continuousOn
  rw [uIcc_of_le hu0.le] at hl
  have hm := (continuous_mu_without_continuous_lam h).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun v hv => hs ⟨mem_singleton u, hv⟩)
  have hκ : ContinuousOn (fun v => S.kappa u v) (Icc u 0) :=
    hl.div (continuousOn_const.sub hm) (fun v hv =>
      (sub_pos.mpr (h.toQ1StandingCore.mu_bounds (p := (u, v)) ⟨hu, hu0, hv.1, hv.2⟩).2).ne')
  intro v hv
  exact (Real.continuousAt_log
    (h.toQ1StandingCore.kappa_pos (p := (u, v)) ⟨hu, hu0, hv.1, hv.2⟩).ne').comp_continuousWithinAt
      (hκ v hv)

end AcExtensionPrinciple

end
