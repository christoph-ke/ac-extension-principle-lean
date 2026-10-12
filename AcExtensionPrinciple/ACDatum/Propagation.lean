module

public import AcExtensionPrinciple.ACDatum.CorrectionDerivative
public import AcExtensionPrinciple.ACDatum.EndpointAC

/-!
# Absolute continuity on every proper closed outgoing cone

Paper `e1a0fd5`, `lem:ac-datum-propagation`, lines 562 and 594–601.
The off-axis incoming correction is AC. Finite BV and the axis trace/value
identities extend the result to both endpoints of the closed cone.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The normalized datum has finite BV on each proper closed cone.
Paper `e1a0fd5`, line 222 and the endpoint argument at line 601. -/
theorem normalized_datum_bv_out {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    BoundedVariationOn (fun v => S.dvpsi u v / S.lam u v) (Icc u 0) := by
  have hs := outSeg_subset_triangle hu hu0 (a := u) le_rfl (b := 0) le_rfl
  obtain ⟨C, hb, _⟩ := h.regularCenter.localBV.psi_variation (outSeg u u 0)
    (isCompact_singleton.prod isCompact_Icc) hs
  have hd : BoundedVariationOn (S.dvpsi u) (Icc u 0) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb u u 0 hu0.le (Subset.refl _))
  have hl := h.regularCenter.ac_lam_out u u 0 hu0.le hs
  have hinv := positive_ac_inv hl (fun v hv => by
    rw [uIcc_of_le hu0.le] at hv
    exact h.lam_pos (p := (u, v)) ⟨hu, hu0, hv⟩)
  have hi : BoundedVariationOn (fun v => (S.lam u v)⁻¹) (Icc u 0) := by
    simpa only [uIcc_of_le hu0.le] using hinv.boundedVariationOn
  simpa only [div_eq_mul_inv] using hd.fun_mul hi

/-- The new axis-value identity identifies the limit with the actual datum
value on the axis. Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, lines 247–261. -/
theorem normalized_datum_continuous_axis {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousWithinAt (fun v => S.dvpsi u v / S.lam u v) (Icc u 0) u := by
  have hmap : Tendsto (fun v : ℝ => (u, v)) (𝓝[Ioc u 0] u)
      (𝓝[pastTriangle ui \ axis ui] (u, u)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    refine ⟨⟨hu, hu0, hv.1.le, hv.2⟩, ?_⟩
    intro ha
    exact hv.1.ne' ha.2.2
  have ht := (h.regularCenter.axis_dvpsi_trace u ⟨hu, hu0, rfl⟩).comp hmap
  rw [← h.regularCenter.axis_dvpsi_value u ⟨hu, hu0, rfl⟩] at ht
  have hc : ContinuousWithinAt (fun v => S.dvpsi u v / S.lam u v) (Ioc u 0) u := ht
  apply hc.insert.mono
  intro v hv
  rcases eq_or_lt_of_le hv.1 with he | he
  · exact mem_insert_iff.mpr (Or.inl he.symm)
  · exact mem_insert_iff.mpr (Or.inr ⟨he, hv.2⟩)

/-- The normalized datum is continuous on every proper closed cone, including
the terminal incoming ray. Paper `e1a0fd5`, lines 422–426 and 601. -/
theorem normalized_datum_continuous_out {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (fun v => S.dvpsi u v / S.lam u v) (Icc u 0) := by
  intro v hv
  rcases eq_or_lt_of_le hv.1 with he | he
  · subst v
    exact h.normalized_datum_continuous_axis hu hu0
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hc := h.dvpsi_continuous_out hu hu0 hua (hav.le.trans hv.2) le_rfl
  have hl := continuous_out h.regularCenter.continuous_lam
    (outSeg_subset_triangle hu hu0 hua.le le_rfl)
  have hq : ContinuousOn (fun w => S.dvpsi u w / S.lam u w) (Icc a 0) :=
    hc.div hl (fun w hw => (h.lam_pos (p := (u, w))
      ⟨hu, hu0, (hua.trans_le hw.1).le, hw.2⟩).ne')
  have hm : Icc a 0 ∈ 𝓝[Icc u 0] v := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hav)] with w hw haw
    exact ⟨haw.le, hw.2⟩
  exact (hq v ⟨hav.le, hv.2⟩).mono_left (nhdsWithin_le_of_mem hm)

/-- The normalized datum is absolutely continuous on each proper closed outgoing cone. Paper
`e1a0fd5`, `lem:ac-datum-propagation`, lines 562, 594–601. -/
theorem normalized_datum_ac_out {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AbsolutelyContinuousOnInterval (fun v => S.dvpsi u v / S.lam u v) u 0 :=
  ac_of_continuous_bv_of_ac_interior hu0
    (h.normalized_datum_continuous_out hu hu0) (h.normalized_datum_bv_out hu hu0)
    (fun _a _b hua hab hb => h.normalized_datum_ac_out_interior hu hu0 hua hab hb)

end StandingFull

end AcExtensionPrinciple

end
