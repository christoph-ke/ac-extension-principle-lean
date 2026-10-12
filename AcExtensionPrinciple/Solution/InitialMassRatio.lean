module

public import AcExtensionPrinciple.Solution.Geometry
public import AcExtensionPrinciple.Solution.EndpointPrimitive
public import Mathlib.Topology.Order.LeftRight

/-!
# Mass-ratio continuity on the initial cone

Paper `e1a0fd5`, `eq:initial-radius-gauge`,
`eq:regular-axis-scalar-traces`, `eq:initial-gap-and-expansion-bound`.
The axis value μ = 0 is shown to be a continuous extension, rather than
assuming continuity of a quotient with vanishing denominator.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Points just to the right of the initial axis lie on the initial cone.
Paper `e1a0fd5`, `eq:past-triangle`, `eq:initial-radius-gauge`. -/
theorem initial_right_mem : ∀ᶠ v in 𝓝[>] ui, v ∈ Ioc ui 0 := by
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ v in 𝓝 ui, v < 0 from Iio_mem_nhds h.initial_negative)] with v hv hv0
  exact ⟨hv, hv0.le⟩

/-- The initial outgoing scalar amplitude tends to zero at its regular vertex.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, lines 247–275. -/
theorem theta_initial_tendsto_zero :
    Tendsto (S.theta ui) (𝓝[>] ui) (𝓝 0) := by
  have hpair : Tendsto (fun v : ℝ => (ui, v)) (𝓝[>] ui)
      (𝓝[pastTriangle ui \ axis ui] (ui, ui)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
    filter_upwards [h.initial_right_mem] with v hv
    refine ⟨⟨le_rfl, h.initial_negative, hv.1.le, hv.2⟩, ?_⟩
    change ¬(ui ≤ ui ∧ ui < 0 ∧ v = ui)
    exact fun he => (ne_of_gt hv.1) he.2.2
  have ht := (h.regularCenter.axis_dvpsi_trace ui
    ⟨le_rfl, h.initial_negative, rfl⟩).comp hpair
  have hdv : Tendsto (S.dvpsi ui) (𝓝[>] ui) (𝓝 (S.phi ui ui)) := by
    apply ht.congr'
    filter_upwards [h.initial_right_mem] with v hv
    simp only [Function.comp_def, (h.initial_gauge v ⟨hv.1.le, hv.2⟩).2, div_one]
  have hp : (ui, ui) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
  have hc : Tendsto (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (𝓝[pastTriangle ui] (ui, ui)) (𝓝 (S.phi ui ui)) :=
    h.regularCenter.continuous_phi (ui, ui) hp
  have hphi : Tendsto (S.phi ui) (𝓝[>] ui) (𝓝 (S.phi ui ui)) :=
    hc.comp (hpair.mono_right (nhdsWithin_mono _ sdiff_subset))
  have hd : Tendsto (fun v => S.dvpsi ui v - S.phi ui v) (𝓝[>] ui) (𝓝 0) := by
    simpa using hdv.sub hphi
  apply hd.congr'
  filter_upwards [h.initial_right_mem] with v hv
  simp only [SSFields.theta, (h.initial_gauge v ⟨hv.1.le, hv.2⟩).2, one_mul]

/-- The mass integrand vanishes in the initial right-axis limit.
Paper `e1a0fd5`, `eq:mass`, line 275, `eq:initial-gap-and-expansion-bound`. -/
theorem massV_initial_tendsto_zero :
    Tendsto (S.massV ui) (𝓝[>] ui) (𝓝 0) := by
  have hb : ∀ᶠ v in 𝓝[>] ui,
      0 ≤ S.massV ui v ∧ S.massV ui v ≤ S.theta ui v ^ 2 / 2 := by
    filter_upwards [h.initial_right_mem] with v hv
    have hp : (ui, v) ∈ pastTriangle ui :=
      ⟨le_rfl, h.initial_negative, hv.1.le, hv.2⟩
    have hm := h.mu_bounds hp
    have hgap : 0 ≤ 1 - S.mu ui v := (sub_pos.mpr hm.2).le
    have hgap1 : 1 - S.mu ui v ≤ 1 := by linarith [hm.1]
    simp only [SSFields.massV, (h.initial_gauge v ⟨hv.1.le, hv.2⟩).2, mul_one]
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (sq_nonneg _) hgap1) (by norm_num)
  have ht : Tendsto (fun v => S.theta ui v ^ 2 / 2) (𝓝[>] ui) (𝓝 0) := by
    simpa using (h.theta_initial_tendsto_zero.pow 2).div_const 2
  exact squeeze_zero' (hb.mono (fun _ hx => hx.1)) (hb.mono (fun _ hx => hx.2)) ht

/-- μ tends to zero at the initial regular vertex, by the mass primitive and radius gauge.
Paper `e1a0fd5`, line 275, `eq:initial-gap-and-expansion-bound`, lines 309–310. -/
theorem mu_initial_tendsto_zero : Tendsto (S.mu ui) (𝓝[>] ui) (𝓝 0) := by
  have hp : (ui, ui) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
  have hm0 := (h.regularCenter.localBV.axis_values ui hp).2
  have ht := intervalPrimitive_right_slope h.initial_negative
    (fun v hv => h.regularCenter.localBV.mass_out ui ui v hv.1
      (outSeg_subset_triangle le_rfl h.initial_negative le_rfl hv.2))
    h.massV_initial_tendsto_zero
  have ht' : Tendsto (fun v => 2 * (S.m ui v / (v - ui))) (𝓝[>] ui) (𝓝 0) := by
    simpa only [hm0, sub_zero, mul_zero] using ht.const_mul 2
  apply ht'.congr'
  filter_upwards [h.initial_right_mem] with v hv
  simp only [SSFields.mu, massRatio, (h.initial_gauge v ⟨hv.1.le, hv.2⟩).1]
  ring

/-- μ is continuous on the full compact initial segment, including its axis point.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`, lines 309–310. -/
theorem continuous_mu_initial : ContinuousOn (S.mu ui) (Icc ui 0) := by
  have hs := outSeg_subset_triangle (ui := ui) le_rfl h.initial_negative le_rfl le_rfl
  have hm := continuous_out h.regularCenter.continuous_m hs
  have hr := continuous_out h.regularCenter.continuous_r hs
  intro v hv
  rcases hv.1.eq_or_lt with he | he
  · subst v
    have hc : ContinuousWithinAt (S.mu ui) (Ioi ui) ui := by
      change Tendsto (S.mu ui) (𝓝[>] ui) (𝓝 (S.mu ui ui))
      rw [h.mu_axis ⟨le_rfl, h.initial_negative, rfl⟩]
      exact h.mu_initial_tendsto_zero
    exact (continuousWithinAt_Ioi_iff_Ici.mp hc).mono Icc_subset_Ici_self
  · exact ((hm v hv).const_mul 2).div (hr v hv)
      (ne_of_gt (h.r_pos ⟨le_rfl, h.initial_negative, hv.1, hv.2⟩ he))

end AcExtensionPrinciple.StandingFull

end
