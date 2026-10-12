module

public import AcExtensionPrinciple.GeometricBounds.Blueshift
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# Regular radius cylinders

Paper `e1a0fd5`, `equations.tex` lines 661–679,
`eq:cylinder-tangent` and `eq:cylinder-time`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The radius-b cylinder's available outgoing rays. Paper `e1a0fd5`, lines 661–666. -/
@[expose] def cylinderDomain (ui b : ℝ) (S : SSFields) : Set ℝ :=
  {u | ui ≤ u ∧ u < 0 ∧ b < S.r u 0}

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Strict outgoing radius monotonicity, including the regular axis and terminal ray.
Paper `e1a0fd5`, `eq:radius-from-axis`, lines 661–666. -/
theorem radius_strictMono {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    StrictMonoOn (S.r u) (Icc u 0) := by
  intro a ha b hb hab
  have hs := outSeg_subset_triangle hu hu0 ha.1 hb.2
  have hp := h.regularCenter.localBV.radius_out u a b hab.le hs
  have hc := continuous_out h.regularCenter.continuous_lam hs
  have hi : 0 < ∫ s in a..b, S.lam u s :=
    intervalIntegral.integral_pos hab hc
      (fun s hs' => (h.lam_pos (p := (u, s)) (hs ⟨by simp, hs'.1.le, hs'.2⟩)).le)
      ⟨a, ⟨le_rfl, hab.le⟩, h.lam_pos (p := (u, a)) (hs ⟨by simp, le_rfl, hab.le⟩)⟩
  linarith [hp.2]

/-- Each available outgoing ray meets r=b exactly once in (u,0).
Paper `e1a0fd5`, lines 661–666, `eq:cylinder-tangent`. -/
theorem existsUnique_cylinder_point {b u : ℝ} (hb : 0 < b)
    (hu : u ∈ cylinderDomain ui b S) :
    ∃! v, v ∈ Ioo u 0 ∧ S.r u v = b := by
  have hs := outSeg_subset_triangle hu.1 hu.2.1 le_rfl le_rfl
  have hc := continuous_out h.regularCenter.continuous_r hs
  have hr0 := (h.regularCenter.localBV.axis_values u
    ⟨hu.1, hu.2.1, le_rfl, hu.2.1.le⟩).1
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc hu.2.1.le hc
    (show b ∈ Icc (S.r u u) (S.r u 0) by rw [hr0]; exact ⟨hb.le, hu.2.2.le⟩)
  have hvu : u < v := lt_of_le_of_ne hv.1 (by intro he'; subst v; linarith)
  have hv0 : v < 0 := lt_of_le_of_ne hv.2 (by intro he'; subst v; linarith [hu.2.2])
  refine ⟨v, ⟨⟨hvu, hv0⟩, he⟩, ?_⟩
  intro w hw
  exact (h.radius_strictMono hu.1 hu.2.1).injOn
    ⟨hw.1.1.le, hw.1.2.le⟩ hv (hw.2.trans he.symm)

end StandingFull

/-- Canonical cylinder curve, with value zero outside its domain.
Paper `e1a0fd5`, lines 661–666, `eq:cylinder-tangent`. -/
@[expose] noncomputable def cylinderV {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) (b : ℝ) (u : ℝ) : ℝ := by
  classical
  exact if hh : 0 < b ∧ u ∈ cylinderDomain ui b S then
    Classical.choose (h.existsUnique_cylinder_point hh.1 hh.2) else 0

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The canonical curve lies strictly between the axis and terminal ray and has radius b.
Paper `e1a0fd5`, lines 661–666, `eq:cylinder-tangent`. -/
theorem cylinderV_spec {b u : ℝ} (hb : 0 < b) (hu : u ∈ cylinderDomain ui b S) :
    cylinderV h b u ∈ Ioo u 0 ∧ S.r u (cylinderV h b u) = b := by
  simp only [cylinderV, dite_eq_left (show 0 < b ∧ u ∈ cylinderDomain ui b S from ⟨hb, hu⟩)]
  exact (Classical.choose_spec (h.existsUnique_cylinder_point hb hu)).1

/-- Uniqueness identifies any radius-b point with the canonical cylinder.
Paper `e1a0fd5`, lines 661–666, `eq:cylinder-tangent`. -/
theorem cylinderV_eq {b u v : ℝ} (hb : 0 < b) (hu : u ∈ cylinderDomain ui b S)
    (hv : v ∈ Ioo u 0) (hr : S.r u v = b) : cylinderV h b u = v := by
  simp only [cylinderV, dite_eq_left (show 0 < b ∧ u ∈ cylinderDomain ui b S from ⟨hb, hu⟩)]
  exact ((Classical.choose_spec (h.existsUnique_cylinder_point hb hu)).2 v ⟨hv, hr⟩).symm

/-- The cylinder stays inside the regular off-axis triangle.
Paper `e1a0fd5`, lines 661–666. -/
theorem cylinder_mem {b u : ℝ} (hb : 0 < b) (hu : u ∈ cylinderDomain ui b S) :
    (u, cylinderV h b u) ∈ pastTriangle ui := by
  have hv := (h.cylinderV_spec hb hu).1
  exact ⟨hu.1, hu.2.1, hv.1.le, hv.2.le⟩

end StandingFull

end AcExtensionPrinciple

end
