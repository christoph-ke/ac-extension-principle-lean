module

public import AcExtensionPrinciple.Sanity.ClassicalLocalBV
public import AcExtensionPrinciple.Sanity.BlueshiftIdentity

/-!
# Classical non-vacuity of the standing hypotheses
Paper `e1a0fd5`, `thm:main`, lines 112–132 and 220–275;
Christodoulou CPAM p. 1157. No solution-class field or source hypothesis is added.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace ClassicalTriangleSolution

variable {ui : ℝ} {S : SSFields} (h : ClassicalTriangleSolution ui S)
include h

/-- Classical fields satisfy the regular-center scalar derivative values.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem scalar_axis_values {a : ℝ} (ha : (a, a) ∈ AcExtensionPrinciple.axis ui) :
    S.dvpsi a a / S.lam a a = S.phi a a ∧ S.dupsi a a / S.nu a a = S.phi a a := by
  have hx := h.expansions (a, a) ⟨ha.1, le_rfl, ha.2.1.le⟩
  constructor
  · apply (div_eq_iff hx.1.ne').mpr
    rw [h.dvpsi_axis ha]
    ring
  · apply (div_eq_iff hx.2.ne).mpr
    rw [h.dupsi_axis ha]
    ring

/-- The classical structure entails every regular-center AC/BV field.
Paper `e1a0fd5`, lines 114 and 220–275; Christodoulou CPAM p. 1157. -/
theorem regularCenter_full : RegularCenterFull ui S := by
  refine ⟨h.localBV_full, h.c1_r.continuousOn.mono (classical_past_subset_closed ui),
    h.c1_m.continuousOn.mono (classical_past_subset_closed ui),
    h.c1_lam.continuousOn.mono (classical_past_subset_closed ui),
    h.c1_nu.continuousOn.mono (classical_past_subset_closed ui),
    h.c1_phi.continuousOn.mono (classical_past_subset_closed ui),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u a b hab hs
    exact classical_ac_out (f := fun p : ℝ × ℝ => S.lam p.1 p.2) h.c1_lam hab
      (hs.trans (classical_past_subset_closed ui))
  · intro a ha; exact (h.axis a ha.1 ha.2.1.le).2.2
  · intro a ha
    have hc := h.c1_dvpsi.continuousOn.div h.c1_lam.continuousOn
      (fun p hp => (h.expansions p hp).1.ne')
    have ht : Tendsto (fun p : ℝ × ℝ => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
        (𝓝[closedTriangle ui] (a, a)) (𝓝 (S.dvpsi a a / S.lam a a)) :=
      hc (a, a) ⟨ha.1, le_rfl, ha.2.1.le⟩
    rw [(h.scalar_axis_values ha).1] at ht
    exact ht.mono_left (nhdsWithin_mono _
      (fun p hp => classical_past_subset_closed ui hp.1))
  · intro a ha
    have hc := h.c1_dupsi.continuousOn.div h.c1_nu.continuousOn
      (fun p hp => (h.expansions p hp).2.ne)
    have ht : Tendsto (fun p : ℝ × ℝ => S.dupsi p.1 p.2 / S.nu p.1 p.2)
        (𝓝[closedTriangle ui] (a, a)) (𝓝 (S.dupsi a a / S.nu a a)) :=
      hc (a, a) ⟨ha.1, le_rfl, ha.2.1.le⟩
    rw [(h.scalar_axis_values ha).2] at ht
    exact ht.mono_left (nhdsWithin_mono _
      (fun p hp => classical_past_subset_closed ui hp.1))
  · intro a ha; exact (h.scalar_axis_values ha).1
  · intro a ha; exact (h.scalar_axis_values ha).2

/-- The classical signs restrict to the past domain.
Paper `e1a0fd5`, `thm:main`, line 120. -/
theorem signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
    0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1 := by
  intro p hp hlt
  have hc := classical_past_subset_closed ui hp
  exact ⟨(h.expansions p hc).1, (h.expansions p hc).2, h.mass_ratio p hc hlt⟩

/-- Every classical solution on the closed triangle with a regular apex lies in the standing class.
Compact positivity of λ supplies finite blueshift through the exact identity. Paper `e1a0fd5`,
`thm:main`, lines 112–132, 220–275; Christodoulou CPAM p. 1157. -/
theorem standing_full : StandingFull ui S := by
  refine ⟨h.initial_negative, h.regularCenter_full, h.signs, h.initial_gauge, ?_, ?_⟩
  · exact classical_ac_out (f := fun p : ℝ × ℝ => S.dvpsi p.1 p.2) h.c1_dvpsi
      h.initial_negative.le
      ((outSeg_subset_triangle (ui := ui) le_rfl h.initial_negative le_rfl le_rfl).trans
        (classical_past_subset_closed ui))
  · obtain ⟨c, hc, hb⟩ := h.expansion_bounds
    apply (blueshift_finite_iff_axis_lam_lower h.regularCenter_full h.signs h.initial_gauge).mpr
    exact ⟨c, hc, fun v hv => (hb (v, v) ⟨hv.1.le, le_rfl, hv.2.le⟩).1⟩

/-- Every classical solution satisfies the minimal regular-center source class.
Paper `e1a0fd5`, lines 114 and 220–275, `eq:regular-axis-scalar-traces`. -/
theorem regularCenter : RegularCenterLocalACBV ui S :=
  h.regularCenter_full.toMinimal

/-- Classical solutions with a regular apex satisfy the minimal standing hypotheses.
Paper `e1a0fd5`, `thm:main`, lines 112–132 and 220–275. -/
theorem standing : StandingAssumptions ui S :=
  h.standing_full.toMinimal

end ClassicalTriangleSolution

end AcExtensionPrinciple

end
