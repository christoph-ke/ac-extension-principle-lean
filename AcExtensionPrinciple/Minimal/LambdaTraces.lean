module

public import AcExtensionPrinciple.Minimal.LambdaInterior

/-!
# Joint λ continuity after recovering outgoing continuity
Paper `e1a0fd5`, `equations.tex` lines 220–275.
Scalar variation controls incoming log κ; retained ν controls its diagonal value.
The outgoing λ trace uses the expansion-sum limit, never outgoing λ AC.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- μ is jointly continuous without the λ continuity field. The off-axis proof only divides
retained continuous r and m. Paper `e1a0fd5`, lines 220–275, `eq:scalar-and-mass-ratio`. -/
theorem MinimalExpansionDraft.continuous_mu {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
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
theorem MinimalExpansionDraft.log_kappa_out_continuous {ui u : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (fun v => Real.log (S.kappa u v)) (Icc u 0) := by
  have hs := outSeg_subset_triangle hu hu0 le_rfl le_rfl
  have hl := h.lam_out_continuous hu hu0
  have hm := h.continuous_mu.comp
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
