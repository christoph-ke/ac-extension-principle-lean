module

public import AcExtensionPrinciple.Cylinder.ClassEnergy

/-!
# Continuous scalar derivative fields at the regular axis

Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259,
and `equations.tex` lines 1460–1473. Joint off-axis continuity and the
axis trace/value conditions supply compact uniform field bounds for BV
transport by the constructed Jacobians.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- An off-axis continuous field with a continuous prescribed axis
value and the correct trace is continuous on the full source domain.
Paper `e1a0fd5`, line 259 and lines 1460–1473. -/
theorem chart_field_continuous_from_axis {ui : ℝ} {F G : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (cylinderScalarRegion ui))
    (hG : ContinuousOn G (pastTriangle ui)) (haxis : EqOn F G (axis ui))
    (htrace : ∀ a, (a, a) ∈ axis ui →
      Tendsto F (𝓝[cylinderScalarRegion ui] (a, a)) (𝓝 (G (a, a)))) :
    ContinuousOn F (pastTriangle ui) := by
  rintro ⟨u, v⟩ hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    subst v
    have ha : (u, u) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have ht : ContinuousWithinAt F (cylinderScalarRegion ui) (u, u) := by
      change Tendsto F _ (𝓝 (F (u, u)))
      rw [haxis ha]
      exact htrace u ha
    have hta : ContinuousWithinAt F (axis ui) (u, u) := by
      have hg := (hG (u, u) hp).mono (axis_subset_pastTriangle ui)
      rw [ContinuousWithinAt, ← haxis ha] at hg
      apply hg.congr'
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (haxis hp).symm
    have hunion : cylinderScalarRegion ui ∪ axis ui = pastTriangle ui := by
      rw [cylinderScalarRegion_eq_axisComplement]
      exact sdiff_union_of_subset (axis_subset_pastTriangle ui)
    rw [← hunion, ContinuousWithinAt, nhdsWithin_union]
    exact Filter.Tendsto.sup ht hta
  · apply (hF (u, v) ⟨hp.1, he, hp.2.2.2⟩).mono_of_mem_nhdsWithin
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), p.1 < p.2 :=
      (isOpen_lt continuous_fst continuous_snd).mem_nhds he
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with p hp hlt
    exact ⟨hp.1, hlt, hp.2.2.2⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming ψ derivative is jointly continuous through the regular axis.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259, 1460–1473. -/
theorem chart_dupsi_continuous :
    ContinuousOn (fun p => S.dupsi p.1 p.2) (pastTriangle ui) := by
  apply chart_field_continuous_from_axis h.cylinder_dupsi_continuous
    (h.regularCenter.continuous_nu.mul h.regularCenter.continuous_phi)
  · rintro ⟨u, v⟩ ha
    have hv : v = u := ha.2.2
    subst v
    have hn := (h.nu_neg (axis_subset_pastTriangle ui ha)).ne
    have he := (div_eq_iff hn).mp (h.regularCenter.axis_dupsi_value u ha)
    simpa only [Pi.mul_apply, mul_comm] using he
  · exact fun a ha => h.cylinder_dupsi_axis_tendsto ha

/-- Outgoing ψ derivative is jointly continuous through the regular axis.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259, 1460–1473. -/
theorem chart_dvpsi_continuous :
    ContinuousOn (fun p => S.dvpsi p.1 p.2) (pastTriangle ui) := by
  apply chart_field_continuous_from_axis h.cylinder_dvpsi_continuous
    (h.regularCenter.continuous_lam.mul h.regularCenter.continuous_phi)
  · rintro ⟨u, v⟩ ha
    have hv : v = u := ha.2.2
    subst v
    have hl := (h.lam_pos (axis_subset_pastTriangle ui ha)).ne'
    have he := (div_eq_iff hl).mp (h.regularCenter.axis_dvpsi_value u ha)
    simpa only [Pi.mul_apply, mul_comm] using he
  · intro a ha
    have hq := h.regularCenter.axis_dvpsi_trace a ha
    rw [← cylinderScalarRegion_eq_axisComplement] at hq
    have hl := (h.regularCenter.continuous_lam (a, a)
      (axis_subset_pastTriangle ui ha)).mono (cylinderScalarRegion_subset ui)
    have he := hq.mul hl
    rw [mul_comm (S.phi a a) (S.lam a a)] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact div_mul_cancel₀ _ (h.lam_pos (cylinderScalarRegion_subset ui hp)).ne'

end StandingFull

end AcExtensionPrinciple

end
