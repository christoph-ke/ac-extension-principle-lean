module

public import AcExtensionPrinciple.Minimal.ExpansionCore

/-!
# λ continuity from its incoming integrating factor
Paper `e1a0fd5`, `equations.tex` lines 87–89, 122–124 and 220–275.
The integrating factor coefficient contains r, m and ν, whose continuity
is available before λ regularity. The expansion sum fixes the axis value.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The incoming integrating factor coefficient is continuous using r, m and ν only.
All denominator signs come from the core. Paper `e1a0fd5`,
`eq:logarithmic-expansions`, lines 87–89 and 222. -/
theorem MinimalExpansionDraft.kernel_continuous {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ContinuousOn (fun p => S.gamma p.1 p.2 * S.varkappa p.1 p.2)
      (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hr := h.continuous_r.mono hs
  have hm : ContinuousOn (fun p => S.mu p.1 p.2) (cylinderScalarRegion ui) :=
    (continuousOn_const.mul (h.continuous_m.mono hs)).div hr
      (fun p hp => (h.toQ1StandingCore.r_pos (hs hp) hp.2.1).ne')
  exact ((h.continuous_nu.mono hs).div (continuousOn_const.sub hm)
    (fun p hp => (sub_pos.mpr (h.toQ1StandingCore.mu_bounds (hs hp)).2).ne')).mul
    (hm.div hr (fun p hp => (h.toQ1StandingCore.r_pos (hs hp) hp.2.1).ne'))

/-- Off-axis λ is continuous by the incoming primitive and the constant initial gauge.
Neither λ continuity nor outgoing λ AC is a premise. Paper `e1a0fd5`,
`eq:lambda-integrating-factor`, lines 87–89, 122–124 and 222. -/
theorem MinimalExpansionDraft.continuous_lam_offAxis {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ContinuousOn (fun p => S.lam p.1 p.2) (cylinderScalarRegion ui) := by
  have hc := Real.continuous_exp.comp_continuousOn
    (cylinder_primitive_continuous_region
      (F := fun u v => S.gamma u v * S.varkappa u v) h.kernel_continuous)
  apply hc.congr
  intro p hp
  have he := (h.toQ1StandingCore.log_lam_primitive hp.1 le_rfl
    (hp.2.1.trans_le hp.2.2) hp.2.1 hp.2.2).2
  have hg := (h.initial_gauge p.2 ⟨hp.1.trans hp.2.1.le, hp.2.2⟩).2
  dsimp only at he
  rw [hg, Real.log_one, sub_zero] at he
  change S.lam p.1 p.2 = Real.exp (∫ s in ui..p.1, S.gamma s p.2 * S.varkappa s p.2)
  rw [← he, Real.exp_log (h.toQ1StandingCore.lam_pos (cylinderScalarRegion_subset ui hp))]

/-- Retained ν continuity and the expansion-sum trace determine the stored outgoing λ trace.
Paper `e1a0fd5`, `eq:regular-axis`, lines 222–246. -/
theorem MinimalExpansionDraft.lam_axis_out_continuous {ui u : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousWithinAt (S.lam u) (Icc u 0) u := by
  have hp : (u, u) ∈ pastTriangle ui := ⟨hu, hu0, le_rfl, hu0.le⟩
  have hn : ContinuousWithinAt (S.nu u) (Icc u 0) u :=
    (h.continuous_nu (u, u) hp).comp_of_eq
      (continuous_const.prodMk continuous_id).continuousWithinAt
      (fun w hw => ⟨hu, hu0, hw⟩) rfl
  have ht : Tendsto (fun w : ℝ => w - u) (𝓝[Icc u 0 \ {u}] u) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_id.tendsto u).mono_left
        (nhdsWithin_le_nhds : 𝓝[Icc u 0 \ {u}] u ≤ 𝓝 u)).sub_const u
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact sub_pos.mpr (lt_of_le_of_ne hw.1.1 (by simpa [eq_comm] using hw.2))
  have hs := (h.regularCenter.localBV.expansion_axis_limit u hp).comp ht
  have hl := hs.sub (hn.mono sdiff_subset).tendsto
  have ha := h.regularCenter.axis_expansions u (show (u, u) ∈ axis ui from ⟨hu, hu0, rfl⟩)
  have he : -S.nu u u = S.lam u u := by rw [ha, neg_neg]
  have hshift : ∀ w : ℝ, u + (w - u) = w := by intro w; ring
  apply continuousWithinAt_sdiff_self.mp
  simpa only [ContinuousWithinAt, Function.comp_apply, add_sub_cancel_left,
    sub_add_cancel, hshift, zero_sub, he] using hl

/-- Outgoing λ restrictions are continuous before outgoing λ AC is restored.
Paper `e1a0fd5`, `eq:regular-axis`, lines 220–275. -/
theorem MinimalExpansionDraft.lam_out_continuous {ui u : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (S.lam u) (Icc u 0) := by
  intro v hv
  rcases hv.1.eq_or_lt with he | he
  · subst v
    exact h.lam_axis_out_continuous hu hu0
  · have hc := (h.continuous_lam_offAxis (u, v) ⟨hu, he, hv.2⟩).comp_of_eq
      ((continuous_const.prodMk continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun w : ℝ => (u, w)) (Icc u 0 ∩ Ioi u) v)
      (fun w hw => ⟨hu, hw.2, hw.1.2⟩) rfl
    exact hc.mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Ioi_mem_nhds he)))

end AcExtensionPrinciple

end
