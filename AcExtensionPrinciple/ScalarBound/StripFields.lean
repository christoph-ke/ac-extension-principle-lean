module

public import AcExtensionPrinciple.ScalarBound.StripGeometry

/-!
# Mass and scalar comparisons on the bootstrapped strip

Paper commit `e1a0fd5`, `equations.tex`
lines 450–470, `eq:scalar-bound-strip-mass-and-incoming-field`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Upper mass-density bound from the bootstrapped amplitude bound.
Paper `e1a0fd5`, lines 450–461. -/
theorem scalar_mass_density_upper {gap lam theta ell F : ℝ}
    (hgap : 0 ≤ gap) (hgap1 : gap ≤ 1) (hell : 0 < ell) (hlam : ell ≤ lam)
    (hF : 0 ≤ F) (htheta : |theta| ≤ 2 * F) :
    |gap * theta ^ 2 / (2 * lam)| ≤ 2 * F ^ 2 / ell := by
  have hlam0 : 0 < lam := hell.trans_le hlam
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hgap (sq_nonneg _)) (by positivity))]
  have hs : theta ^ 2 ≤ 4 * F ^ 2 := by
    have ht := mul_self_le_mul_self (abs_nonneg theta) htheta
    nlinarith only [ht, sq_abs theta]
  have hn : gap * theta ^ 2 ≤ 4 * F ^ 2 :=
    (mul_le_mul_of_nonneg_right hgap1 (sq_nonneg _)).trans (by simpa using hs)
  have hd := div_le_div₀ (by positivity : 0 ≤ 4 * F ^ 2) hn
    (by positivity : 0 < 2 * ell) (by linarith : 2 * ell ≤ 2 * lam)
  exact hd.trans_eq (by field_simp; ring)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The bootstrapped amplitude controls the mass difference across the
strip. Paper `e1a0fd5`, `eq:scalar-bound-strip-mass-and-incoming-field`, lines 458–461. -/
theorem scalar_strip_mass_difference {u a b F : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hF : 0 ≤ F) (htheta : ∀ s ∈ Icc a b, |S.theta u s| ≤ 2 * F) :
    |S.m u a - S.m u b| ≤ (2 / Real.exp (-Bstar ui S)) * F ^ 2 * (b - a) := by
  rw [abs_sub_comm]
  have ht := primitive_abs_difference_le hab
    (h.regularCenter.localBV.mass_out u a b hab
      (outSeg_subset_triangle hu hu0 hua.le hb0))
    (C := 2 * F ^ 2 / Real.exp (-Bstar ui S)) (by
      intro s hs
      have hp : (u, s) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
      have hm := h.mu_bounds hp
      exact scalar_mass_density_upper (sub_pos.mpr hm.2).le (by linarith [hm.1])
        (Real.exp_pos _) (h.lam_bounds hp).1 hF (htheta s hs))
  exact ht.trans_eq (by ring)

/-- The bootstrapped amplitude controls the incoming scalar-amplitude
difference, with ν appearing only as a factor. Paper `e1a0fd5`,
`eq:scalar-bound-strip-mass-and-incoming-field`, lines 459–461. -/
theorem scalar_strip_zeta_difference {u a b F : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hF : 0 ≤ F) (hwidth : b - a ≤ S.r u b / 2)
    (htheta : ∀ s ∈ Icc a b, |S.theta u s| ≤ 2 * F) :
    |S.zeta u a - S.zeta u b| ≤ 4 * F * (-S.nu u b) * (b - a) / S.r u b := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hr := h.r_pos hp (hua.trans_le hab)
  have hn := neg_pos.mpr (h.nu_neg hp)
  have hdiff := primitive_abs_difference_le hab
    (h.zeta_primitive_out hab hu hu0 hua hb0)
    (C := 4 * F * (-S.nu u b) / S.r u b) (by
      intro s hs
      have hps : (u, s) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
      have hnS := h.scalar_strip_neg_nu hu hu0 (hua.trans_le hs.1) hs.2 hb0
      have hrS := h.scalar_strip_radius hu hu0 (hua.trans_le hs.1) hs.2 hb0
        (by linarith [hs.1])
      rw [abs_mul, abs_of_pos hnS.1, SSFields.dvphi, abs_div,
        abs_of_pos (h.r_pos hps (hua.trans_le hs.1))]
      have ht := div_le_div₀ (by positivity : 0 ≤ 2 * F) (htheta s hs)
        (by positivity : 0 < S.r u b / 2) hrS.1
      calc
        _ ≤ (-S.nu u b) * (2 * F / (S.r u b / 2)) := mul_le_mul hnS.2 ht
          (div_nonneg (abs_nonneg _) (h.r_pos hps (hua.trans_le hs.1)).le) hn.le
        _ = _ := by field_simp; ring)
  rw [abs_sub_comm]
  exact hdiff.trans_eq (by ring)

end StandingFull

end AcExtensionPrinciple

end
