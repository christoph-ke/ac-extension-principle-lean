module

public import AcExtensionPrinciple.Weighted.Prop34ActualMeasurable

/-!
# The actual incoming source as a joint measurable function

Paper `e1a0fd5`, `eq:renormalized-remainder-transport`, lines 1090–1104
and 1292–1316. Off-axis local integrability follows from the uniform
interaction bound and the radius lower bound.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Joint measurability of the outgoing scalar derivative on the proper
strip. Paper `e1a0fd5`, lines 1043–1069 and 1292–1316. -/
theorem prop34_dvphi_measurable_strip {u₀ U : ℝ} (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ V : ℝ × ℝ → ℝ, Measurable V ∧
      EqOn (fun p => S.dvphi p.1 p.2) V (weightedOffAxisStrip u₀ U) := by
  classical
  rw [weightedOffAxisStrip_eq_iUnion]
  apply measurable_piecewise_of_countable_extensions
    (fun _ => measurableSet_Icc.prod measurableSet_Icc)
  intro q
  let D := weightedStripRectangle u₀ U q
  have hv := (h.dvphi_continuous_rectangle (hi.trans q.2.1) q.2.2.2
    ((min_le_left _ _).trans_lt hU) q.2.2.1 le_rfl).mono
      (show D ⊆ Icc ui (min U (q.1.1 : ℝ)) ×ˢ Icc (q.1.2 : ℝ) 0 from
        fun p hp => ⟨⟨hi.trans hp.1.1, hp.1.2⟩, hp.2⟩)
  refine ⟨D.piecewise (fun p => S.dvphi p.1 p.2) (fun _ => 0),
    hv.measurable_piecewise continuousOn_const
      (measurableSet_Icc.prod measurableSet_Icc), ?_⟩
  exact fun p hp => (piecewise_eq_of_mem D (fun p => S.dvphi p.1 p.2) (fun _ => 0) hp).symm

/-- The actual source C/r has a representative agreeing at every proper
off-axis point. Paper `e1a0fd5`, `eq:renormalized-remainder-transport`,
lines 1100–1104 and 1292–1316. -/
theorem prop34_interactionSource_measurable_strip {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ H : ℝ × ℝ → ℝ, Measurable H ∧
      EqOn (fun p => S.renormalizedInteraction p.1 p.2 / S.r p.1 p.2)
        H (weightedOffAxisStrip u₀ U) := by
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_r
  obtain ⟨M, hM, heM⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_m
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_lam
  obtain ⟨A, hA, heA⟩ := h.weighted_exists_measurable_amplitude_strip hi hU
  obtain ⟨V, hV, heV⟩ := h.prop34_dvphi_measurable_strip hi hU
  let μ := fun p => 2 * M p / R p
  have hμ : Measurable μ := (hM.const_mul 2).div hR
  refine ⟨fun p => (μ p + (1 - μ p) * (R p / L p * V p) * A p) / R p,
    (hμ.add (((measurable_const.sub hμ).mul ((hR.div hL).mul hV)).mul hA)).div hR, ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U := ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2⟩
  have ha := heA hp
  have hv := heV hp
  dsimp only at ha hv
  simp only [μ, ← heR hpD, ← heM hpD, ← heL hpD, ← ha, ← hv,
    SSFields.renormalizedInteraction, Renormalized.interactionOf, massRatio,
    weightedIncomingAmplitude]

/-- Each incoming rectangle slice of the actual source is integrable,
without any coercive energy premise. Paper `e1a0fd5`,
lines 1100–1104 and 1305–1316. -/
theorem prop34_interactionSource_integrable_in {u₀ U b v : ℝ} {H : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbv : b < v) (hv : v ≤ 0) (hH : Measurable H)
    (heH : EqOn (fun p => S.renormalizedInteraction p.1 p.2 / S.r p.1 p.2)
      H (weightedOffAxisStrip u₀ U)) :
    IntervalIntegrable (fun s => H (s, v)) volume u₀ b := by
  obtain ⟨M, hM, hcoeff⟩ := h.section3_uniform_coefficients
  let d := Real.exp (-Bstar ui S) * (v - b)
  have hd : 0 < d := mul_pos (Real.exp_pos _) (sub_pos.mpr hbv)
  let C := (1 + 2 * M ^ 2) / d
  have hiC : IntervalIntegrable (fun _ : ℝ => C) volume u₀ b := intervalIntegrable_const
  apply hiC.mono_fun' ((hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hab] at hs
  have hpS : (s, v) ∈ weightedOffAxisStrip u₀ U :=
    ⟨hs.1.le, hs.2.trans hbU, hs.2.trans_lt hbv, hv⟩
  have hp : (s, v) ∈ pastTriangle ui :=
    ⟨hi.trans hs.1.le, hs.2.trans_lt (hbU.trans_lt hU), (hs.2.trans_lt hbv).le, hv⟩
  have hsrc := heH hpS
  dsimp only at hsrc
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.norm_eq_abs, ← hsrc, abs_div, abs_of_pos (h.r_pos hp hpS.2.2.1)]
  exact div_le_div₀ (by positivity) (hcoeff (s, v) hp).2.2 hd
    ((mul_le_mul_of_nonneg_left (by dsimp only; linarith [hs.2]) (Real.exp_pos _).le).trans
      (h.radius_bounds hp).1)

end AcExtensionPrinciple.StandingFull

end
