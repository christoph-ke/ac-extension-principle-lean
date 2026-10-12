module

public import AcExtensionPrinciple.Renormalized.ClassACComposition
public import AcExtensionPrinciple.Renormalized.ClassHardy
public import AcExtensionPrinciple.GeometricBounds.Blueshift

/-!
# The inverse-radius coordinate and AC outgoing radius profile

Paper `e1a0fd5`, `equations.tex` lines 1006–1015.
The geometric lower bound for λ makes the inverse coordinate Lipschitz.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- Inverse radius on a proper outgoing cone. Paper `e1a0fd5`, lines 1006–1015. -/
@[expose] noncomputable def SSFields.coneRadiusInverse (S : SSFields) (u ρ : ℝ) : ℝ :=
  Function.invFunOn (S.r u) (Icc u 0) ρ

/-- The normalized outgoing datum in radius coordinates.
Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1015. -/
@[expose] noncomputable def SSFields.coneRadiusProfile (S : SSFields) (u ρ : ℝ) : ℝ :=
  S.outgoingDatum u (S.coneRadiusInverse u ρ)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The inverse-radius coordinate stays on the cone and inverts radius.
Paper `e1a0fd5`, lines 1006–1015. -/
theorem coneRadiusInverse_mem_eq {u ρ : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hρ : ρ ∈ Icc 0 (S.r u 0)) :
    S.coneRadiusInverse u ρ ∈ Icc u 0 ∧ S.r u (S.coneRadiusInverse u ρ) = ρ := by
  rw [← h.cone_radius_image hu hu0] at hρ
  exact Function.invFunOn_pos hρ

/-- The inverse-radius coordinate is the left inverse on the cone.
Paper `e1a0fd5`, lines 1006–1015. -/
theorem coneRadiusInverse_radius {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Icc u 0) : S.coneRadiusInverse u (S.r u v) = v :=
  (h.cone_radius_strictMono hu hu0).injOn.leftInvOn_invFunOn hv

/-- The inverse coordinate is increasing on the radius interval.
Paper `e1a0fd5`, lines 1006–1015. -/
theorem coneRadiusInverse_monotone {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    MonotoneOn (S.coneRadiusInverse u) (Icc 0 (S.r u 0)) := by
  intro x hx y hy hxy
  obtain ⟨hx', hex⟩ := h.coneRadiusInverse_mem_eq hu hu0 hx
  obtain ⟨hy', hey⟩ := h.coneRadiusInverse_mem_eq hu hu0 hy
  apply ((h.cone_radius_strictMono hu hu0).le_iff_le hx' hy').mp
  simpa only [hex, hey] using hxy

/-- The λ lower bound controls every radius increment on the cone.
Paper `e1a0fd5`, `eq:radius-comparison`, lines 1006–1015. -/
theorem cone_radius_increment_lower {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (ha : a ∈ Icc u 0) (hb : b ∈ Icc u 0) (hab : a ≤ b) :
    Real.exp (-Bstar ui S) * (b - a) ≤ S.r u b - S.r u a := by
  have hp := h.regularCenter.localBV.radius_out u a b hab
    (outSeg_subset_triangle hu hu0 ha.1 hb.2)
  rw [hp.2]
  calc
    _ = ∫ _s in a..b, Real.exp (-Bstar ui S) := by simp [mul_comm]
    _ ≤ _ := intervalIntegral.integral_mono_on hab intervalIntegrable_const hp.1
      (fun s hs => (h.lam_bounds (p := (u, s)) ⟨hu, hu0, ha.1.trans hs.1, hs.2.trans hb.2⟩).1)

/-- Quantitative Lipschitz inverse for radius on each proper cone.
Paper `e1a0fd5`, lines 1006–1015, change-of-variable calculus. -/
theorem coneRadiusInverse_lipschitz {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    LipschitzOnWith ⟨Real.exp (Bstar ui S), (Real.exp_pos _).le⟩
      (S.coneRadiusInverse u) (Icc 0 (S.r u 0)) := by
  have hbound {x y : ℝ} (hx : x ∈ Icc 0 (S.r u 0)) (hy : y ∈ Icc 0 (S.r u 0))
      (hxy : x ≤ y) :
      dist (S.coneRadiusInverse u x) (S.coneRadiusInverse u y) ≤
        Real.exp (Bstar ui S) * dist x y := by
    obtain ⟨hx', hex⟩ := h.coneRadiusInverse_mem_eq hu hu0 hx
    obtain ⟨hy', hey⟩ := h.coneRadiusInverse_mem_eq hu hu0 hy
    have hle := h.coneRadiusInverse_monotone hu hu0 hx hy hxy
    have hb := h.cone_radius_increment_lower hu hu0 hx' hy' hle
    rw [hex, hey] at hb
    have he : Real.exp (Bstar ui S) * Real.exp (-Bstar ui S) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (Bstar ui S)).le
    rw [← mul_assoc, he, one_mul] at hm
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hm
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (S.coneRadiusInverse u x) (S.coneRadiusInverse u y) ≤
    Real.exp (Bstar ui S) * dist x y
  rcases le_total x y with hxy | hyx
  · exact hbound hx hy hxy
  · simpa only [dist_comm] using hbound hy hx hyx

/-- The constructed radius profile pulls back to the actual outgoing datum.
Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1015. -/
theorem coneRadiusProfile_radius {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Icc u 0) : S.coneRadiusProfile u (S.r u v) = S.outgoingDatum u v := by
  unfold SSFields.coneRadiusProfile
  rw [h.coneRadiusInverse_radius hu hu0 hv]

/-- The radius profile is AC from exactly the outgoing AC conclusion of
Lemma 2.2. Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1015. -/
theorem coneRadiusProfile_ac_of_ac_datum {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0) :
    AbsolutelyContinuousOnInterval (S.coneRadiusProfile u) 0 (S.r u 0) := by
  have hR := h.r_pos (u := u) (v := 0) ⟨hu, hu0, hu0.le, le_rfl⟩ hu0
  apply ac_comp_monotone_lipschitz hP
  · simpa only [uIcc_of_le hR.le] using h.coneRadiusInverse_monotone hu hu0
  · simpa only [uIcc_of_le hR.le] using h.coneRadiusInverse_lipschitz hu hu0
  · intro ρ hρ
    rw [uIcc_of_le hR.le] at hρ
    rw [uIcc_of_le hu0.le]
    exact (h.coneRadiusInverse_mem_eq hu hu0 hρ).1

end StandingFull

end AcExtensionPrinciple

end
