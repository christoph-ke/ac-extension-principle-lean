module

public import AcExtensionPrinciple.Weighted.ClassNorms
public import AcExtensionPrinciple.Weighted.ConeEstimates
public import AcExtensionPrinciple.Gauge.Primitive

/-!
# Outgoing radius as an integration coordinate

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1191–1215. Compact continuity of λ makes the radius
primitive differentiable within its closed cone, including the terminal ray.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter Function
open scoped ENNReal

/-- A measurable inverse on a compact strictly increasing interval.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem exists_measurable_radial_inverse {r : ℝ → ℝ} {u R : ℝ}
    (hu : u < 0) (hr : ContinuousOn r (Icc u 0))
    (hm : StrictMonoOn r (Icc u 0)) (haxis : r u = 0) (hR : r 0 = R) :
    ∃ g : ℝ → ℝ, Measurable g ∧
      (∀ x ∈ Icc 0 R, g x ∈ Icc u 0 ∧ r (g x) = x) ∧
      (∀ v ∈ Icc u 0, g (r v) = v) ∧ MonotoneOn g (Icc 0 R) := by
  have himage : r '' Icc u 0 = Icc 0 R := by
    simpa [haxis, hR] using hr.image_Icc_of_monotoneOn hu.le hm.monotoneOn
  let g₀ := invFunOn r (Icc u 0)
  have hg₀ (x : ℝ) (hx : x ∈ Icc 0 R) : g₀ x ∈ Icc u 0 ∧ r (g₀ x) = x :=
    invFunOn_pos (by rwa [← mem_image, himage])
  have hgm : MonotoneOn g₀ (Icc 0 R) := by
    intro x hx y hy hxy
    exact (hm.le_iff_le (hg₀ x hx).1 (hg₀ y hy).1).mp
      (by simpa [(hg₀ x hx).2, (hg₀ y hy).2] using hxy)
  have hl : BddBelow (g₀ '' Icc 0 R) := by
    refine ⟨u, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hg₀ x hx).1.1
  have hh : BddAbove (g₀ '' Icc 0 R) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hg₀ x hx).1.2
  obtain ⟨g, hgm', heq⟩ := hgm.exists_monotone_extension hl hh
  refine ⟨g, hgm'.measurable, ?_, ?_, hgm'.monotoneOn _⟩
  · intro x hx
    rw [← heq hx]
    exact hg₀ x hx
  · intro v hv
    have hx : r v ∈ Icc 0 R := by rw [← himage]; exact mem_image_of_mem r hv
    rw [← heq hx]
    exact hm.injOn.leftInvOn_invFunOn hv

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The within-cone radius derivative, at every point including both ends.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_radius_hasDerivWithinAt {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Icc u 0) : HasDerivWithinAt (S.r u) (S.lam u v) (Icc u 0) v := by
  exact hasDerivWithinAt_of_intervalPrimitives
    (fun x hx => h.regularCenter.localBV.radius_out u u x hx.1
      (outSeg_subset_triangle hu hu0 le_rfl hx.2))
    (continuous_out h.regularCenter.continuous_lam
      (outSeg_subset_triangle hu hu0 le_rfl le_rfl)) hv

/-- Radius is strictly increasing on a proper cone, from λ > 0.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_radius_strictMonoOn {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    StrictMonoOn (S.r u) (Icc u 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc u 0)
    (continuous_out h.regularCenter.continuous_r
      (outSeg_subset_triangle hu hu0 le_rfl le_rfl))
  intro v hv
  have hv' : v ∈ Ioo u 0 := by simpa only [interior_Icc] using hv
  rw [((h.weighted_radius_hasDerivWithinAt hu hu0 (Ioo_subset_Icc_self hv')).hasDerivAt
    (Icc_mem_nhds hv'.1 hv'.2)).deriv]
  exact h.lam_pos (p := (u, v)) ⟨hu, hu0, hv'.1.le, hv'.2.le⟩

/-- Every outgoing cone has a measurable radius inverse. Paper `e1a0fd5`,
`lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_exists_radial_inverse {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ∃ g : ℝ → ℝ, Measurable g ∧
      (∀ x ∈ Icc 0 (S.r u 0), g x ∈ Icc u 0 ∧ S.r u (g x) = x) ∧
      (∀ v ∈ Icc u 0, g (S.r u v) = v) ∧ MonotoneOn g (Icc 0 (S.r u 0)) := by
  exact exists_measurable_radial_inverse hu0
    (continuous_out h.regularCenter.continuous_r
      (outSeg_subset_triangle hu hu0 le_rfl le_rfl))
    (h.weighted_radius_strictMonoOn hu hu0)
    (h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1 rfl

/-- Positive radial intervals correspond exactly to off-axis cone intervals.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_radius_image_Ioc {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Icc u 0) : S.r u '' Ioc u v = Ioc 0 (S.r u v) := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 le_rfl hv.2)
  have hm := (h.weighted_radius_strictMonoOn hu hu0).mono (Icc_subset_Icc_right hv.2)
  simpa [(h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1] using
    hc.image_Ioc_of_strictMonoOn hv.1 hm

/-- Pull back a lower integrand expressed in radius. Paper `e1a0fd5`,
`lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_lintegral_radius_pullback {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hv : v ∈ Icc u 0) (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioc u v, ENNReal.ofReal (S.lam u s) * F (S.r u s)) =
      ∫⁻ x in Ioc 0 (S.r u v), F x := by
  have he := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioc
    (fun s hs => (h.weighted_radius_hasDerivWithinAt hu hu0
      ⟨hs.1.le, hs.2.trans hv.2⟩).mono
      (fun t ht => ⟨ht.1.le, ht.2.trans hv.2⟩))
    ((h.weighted_radius_strictMonoOn hu hu0).monotoneOn.mono
      (fun s hs => ⟨hs.1.le, hs.2.trans hv.2⟩)) F
  rw [h.weighted_radius_image_Ioc hu hu0 hv] at he
  exact he.symm

/-- The λ-weighted cone lower integral equals the radius lower integral,
without an integrability or measurability premise on the integrand.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1191–1215. -/
theorem weighted_lintegral_change_radius {u v : ℝ} {g : ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hv : v ∈ Icc u 0)
    (hg : ∀ s ∈ Icc u 0, g (S.r u s) = s) (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioc u v, ENNReal.ofReal (S.lam u s) * F s) =
      ∫⁻ x in Ioc 0 (S.r u v), F (g x) := by
  have he := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioc
    (fun s hs => (h.weighted_radius_hasDerivWithinAt hu hu0
      ⟨hs.1.le, hs.2.trans hv.2⟩).mono
      (fun t ht => ⟨ht.1.le, ht.2.trans hv.2⟩))
    ((h.weighted_radius_strictMonoOn hu hu0).monotoneOn.mono
      (fun s hs => ⟨hs.1.le, hs.2.trans hv.2⟩)) (fun x => F (g x))
  rw [h.weighted_radius_image_Ioc hu hu0 hv] at he
  refine Eq.trans ?_ he.symm
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [hg s ⟨hs.1.le, hs.2.trans hv.2⟩]

/-- The signed radial primitive changes variables as well, including the
nonintegrable Bochner convention. Paper `e1a0fd5`,
`eq:weighted-radial-operator`, lines 1158 and 1204–1208. -/
theorem weighted_integral_change_radius {u v : ℝ} {g : ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hv : v ∈ Icc u 0)
    (hg : ∀ s ∈ Icc u 0, g (S.r u s) = s) (F : ℝ → ℝ) :
    (∫ s in u..v, F s) =
      ∫ x in Ioo 0 (S.r u v), F (g x) / S.lam u (g x) := by
  have he := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioc
    (fun s hs => (h.weighted_radius_hasDerivWithinAt hu hu0
      ⟨hs.1.le, hs.2.trans hv.2⟩).mono
      (fun t ht => ⟨ht.1.le, ht.2.trans hv.2⟩))
    ((h.weighted_radius_strictMonoOn hu hu0).monotoneOn.mono
      (fun s hs => ⟨hs.1.le, hs.2.trans hv.2⟩))
    (fun x => F (g x) / S.lam u (g x))
  rw [h.weighted_radius_image_Ioc hu hu0 hv, integral_Ioc_eq_integral_Ioo] at he
  rw [intervalIntegral.integral_of_le hv.1]
  refine Eq.trans ?_ he.symm
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [hg s ⟨hs.1.le, hs.2.trans hv.2⟩, smul_eq_mul]
  exact (mul_div_cancel₀ (F s) (h.lam_pos (p := (u, s))
    ⟨hu, hu0, hs.1.le, hs.2.trans hv.2⟩).ne').symm

end StandingFull

end AcExtensionPrinciple

end
