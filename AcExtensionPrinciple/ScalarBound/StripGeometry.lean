module

public import AcExtensionPrinciple.ScalarBound.RadiusIntegrals

/-!
# Elementary strip geometry

Paper commit `e1a0fd5`, `equations.tex`
lines 435–470, `eq:scalar-bound-strip-geometry`. Constants in these
estimates do not depend on the size of the incoming expansion.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Constant derivative bounds control interval-primitive differences.
Paper `e1a0fd5`, lines 441–468. -/
theorem primitive_abs_difference_le {f g : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hi : IntervalPrimitive f g a b)
    (hbound : ∀ s ∈ Icc a b, |g s| ≤ C) : |f b - f a| ≤ C * (b - a) := by
  rw [hi.2]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := g) (C := C) (by
      intro s hs
      rw [uIoc_of_le hab] at hs
      simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1.le, hs.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hb

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Hawking mass is nonnegative and strictly below r/2 off the axis.
Paper `e1a0fd5`, lines 395, 463 and 518. -/
theorem scalar_mass_bounds {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    0 ≤ S.m u v ∧ S.m u v < S.r u v / 2 := by
  have hr := h.r_pos hp huv
  have hm := h.mu_bounds hp
  change 0 ≤ 2 * S.m u v / S.r u v ∧ 2 * S.m u v / S.r u v < 1 at hm
  constructor
  · have ht := (le_div_iff₀ hr).mp hm.1
    nlinarith
  · have ht := (div_lt_iff₀ hr).mp hm.2
    linarith

/-- The outgoing radius increases by at most the coordinate width.
Paper `e1a0fd5`, `eq:scalar-bound-strip-geometry`, lines 441–448. -/
theorem scalar_radius_difference {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u ≤ a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    0 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ b - a := by
  have hi := h.regularCenter.localBV.radius_out u a b hab
    (outSeg_subset_triangle hu hu0 hua hb0)
  rw [hi.2]
  constructor
  · exact intervalIntegral.integral_nonneg hab (fun s hs =>
      (h.lam_pos (p := (u, s)) ⟨hu, hu0, hua.trans hs.1, hs.2.trans hb0⟩).le)
  · calc
      _ ≤ ∫ s in a..b, (1 : ℝ) := intervalIntegral.integral_mono_on hab hi.1
        intervalIntegrable_const (fun s hs =>
          (h.lam_bounds (p := (u, s)) ⟨hu, hu0, hua.trans hs.1, hs.2.trans hb0⟩).2)
      _ = b - a := by simp

/-- A strip of width at most half the reference radius stays at comparable
positive radii. Paper `e1a0fd5`, `eq:scalar-bound-strip-geometry`, lines 443–444. -/
theorem scalar_strip_radius {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hwidth : b - a ≤ S.r u b / 2) :
    S.r u b / 2 ≤ S.r u a ∧ S.r u a ≤ S.r u b := by
  have hr := h.scalar_radius_difference hu hu0 hua.le hab hb0
  constructor <;> linarith

/-- The incoming expansion on a radial strip is bounded by its value on
the right edge. Paper `e1a0fd5`, lines 445–447. -/
theorem scalar_strip_neg_nu {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    0 < -S.nu u a ∧ -S.nu u a ≤ -S.nu u b := by
  exact ⟨neg_pos.mpr (h.nu_neg (p := (u, a)) ⟨hu, hu0, hua.le, hab.trans hb0⟩),
    neg_le_neg (h.nu_le_of_le hu hu0 hua hab hb0)⟩

/-- The incoming radius decreases along the reference ray, so the final
radius controls all earlier strip widths. Paper `e1a0fd5`, lines 428–439. -/
theorem scalar_radius_in_antitone {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b ≤ v) (hv0 : v ≤ 0) : S.r b v ≤ S.r a v := by
  have hi := h.regularCenter.localBV.radius_in v a b hab
    (inSeg_subset_triangle ha hb0 hbv hv0)
  have hn : (∫ s in a..b, S.nu s v) ≤ 0 := by
    have ht := intervalIntegral.integral_nonneg (μ := volume) hab
      (f := fun s => -S.nu s v) (fun s hs =>
        (neg_pos.mpr (h.nu_neg (p := (s, v))
          ⟨ha.trans hs.1, hs.2.trans_lt hb0, hs.2.trans hbv, hv0⟩)).le)
    rw [intervalIntegral.integral_neg] at ht
    linarith
  have he := hi.2
  dsimp only at he
  linarith

end StandingFull

end AcExtensionPrinciple

end
