module

public import AcExtensionPrinciple.ScalarBound.StripFields

/-!
# Strip comparisons of the geometric coefficients

Paper commit `e1a0fd5`, `equations.tex`
lines 441–470, `eq:scalar-bound-strip-geometry` and
`eq:scalar-bound-strip-coefficient`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Uniform upper radius coefficient on a comparable-radius strip.
Paper `e1a0fd5`, lines 441–470. -/
theorem scalar_radius_coefficient_upper {mu lam nu r R g N : ℝ}
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hg : 0 < g) (hgap : g ≤ 1 - mu) (hR : 0 < R) (hr : R / 2 ≤ r)
    (hN : 0 ≤ N) (hnu : |nu| ≤ N) :
    |mu * lam * nu / ((1 - mu) * r)| ≤ 2 * N / (g * R) := by
  have hr0 : 0 < r := (by positivity : 0 < R / 2).trans_le hr
  have hgap0 : 0 < 1 - mu := hg.trans_le hgap
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hmu, abs_of_nonneg hlam,
    abs_of_pos (mul_pos hgap0 hr0)]
  have hml : mu * lam ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlam1 hmu).trans (by simpa using hmu1)
  have hn : mu * lam * |nu| ≤ N := by
    calc
      _ ≤ 1 * |nu| := mul_le_mul_of_nonneg_right hml (abs_nonneg _)
      _ ≤ N := by simpa using hnu
  have hd : g * R / 2 ≤ (1 - mu) * r := by
    have ht := mul_le_mul hgap hr (by positivity : 0 ≤ R / 2) hgap0.le
    nlinarith
  have ht := div_le_div₀ hN hn (by positivity : 0 < g * R / 2) hd
  exact ht.trans_eq (by field_simp)

/-- Stable mass-ratio comparison on a strip at comparable radii.
The premises come from the radius and mass strip estimates.
Paper `e1a0fd5`, `eq:scalar-bound-strip-coefficient`, lines 463–468. -/
theorem scalar_mass_ratio_difference {r R m m₀ K F d : ℝ}
    (hR : 0 < R) (hr : R / 2 ≤ r) (hK : 0 ≤ K) (hF : 1 ≤ F) (hd : 0 ≤ d)
    (hmu₀ : 0 ≤ 2 * m₀ / R ∧ 2 * m₀ / R ≤ 1)
    (hm : |m - m₀| ≤ K * F ^ 2 * d) (hrr : |R - r| ≤ d) :
    |2 * m / r - 2 * m₀ / R| ≤ (4 * K + 2) * F ^ 2 * d / R := by
  have hr0 : 0 < r := (by positivity : 0 < R / 2).trans_le hr
  have he : 2 * m / r - 2 * m₀ / R =
      (2 * (m - m₀) + (2 * m₀ / R) * (R - r)) / r := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hr0]
  have hn : |2 * (m - m₀) + (2 * m₀ / R) * (R - r)| ≤
      (2 * K + 1) * F ^ 2 * d := by
    calc
      _ ≤ |2 * (m - m₀)| + |(2 * m₀ / R) * (R - r)| := abs_add_le _ _
      _ = 2 * |m - m₀| + (2 * m₀ / R) * |R - r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hmu₀.1]
        norm_num
      _ ≤ 2 * (K * F ^ 2 * d) + 1 * d := by
        exact add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
          (mul_le_mul hmu₀.2 hrr (abs_nonneg _) zero_le_one)
      _ ≤ (2 * K + 1) * F ^ 2 * d := by
        have hFd : d ≤ F ^ 2 * d := by nlinarith [mul_nonneg hd (by nlinarith : 0 ≤ F ^ 2 - 1)]
        nlinarith
  have ht := div_le_div₀ (by positivity : 0 ≤ (2 * K + 1) * F ^ 2 * d) hn
    (by positivity : 0 < R / 2) hr
  exact ht.trans_eq (by field_simp; ring)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming expansion difference, with only a linear dependence on the
reference expansion. The gap premise is discharged by G2.
Paper `e1a0fd5`, `eq:scalar-bound-strip-geometry`, lines 445–470. -/
theorem scalar_strip_nu_difference {u a b g : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hwidth : b - a ≤ S.r u b / 2)
    (hgap : ∀ s ∈ Icc a b, g ≤ 1 - S.mu u s) :
    |S.nu u a - S.nu u b| ≤ (2 / g) * (-S.nu u b) * (b - a) / S.r u b := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hr := h.r_pos hp (hua.trans_le hab)
  have hn := neg_pos.mpr (h.nu_neg hp)
  have hdiff := primitive_abs_difference_le hab
    (h.regularCenter.localBV.nu_out u a b hab (outSeg_subset_offAxis hu hu0 hua hb0))
    (C := 2 * (-S.nu u b) / (g * S.r u b)) (by
      intro s hs
      have hps : (u, s) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
      have hm := h.mu_bounds hps
      have hnS := h.scalar_strip_neg_nu hu hu0 (hua.trans_le hs.1) hs.2 hb0
      have hrS := h.scalar_strip_radius hu hu0 (hua.trans_le hs.1) hs.2 hb0
        (by linarith [hs.1])
      have hl := h.lam_bounds hps
      exact scalar_radius_coefficient_upper hm.1 hm.2.le (h.lam_pos hps).le hl.2
        hg (hgap s hs) hr hrS.1 hn.le (by rw [abs_of_neg (h.nu_neg hps)]; exact hnS.2))
  rw [abs_sub_comm]
  exact hdiff.trans_eq (by ring)

/-- The μ strip comparison has a constant independent of F, width,
reference ray and ν. Paper `e1a0fd5`, `eq:scalar-bound-strip-coefficient`, lines 463–470. -/
theorem scalar_strip_mu_difference {u a b F : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hF : 1 ≤ F) (hwidth : b - a ≤ S.r u b / 2)
    (htheta : ∀ s ∈ Icc a b, |S.theta u s| ≤ 2 * F) :
    |S.mu u a - S.mu u b| ≤
      (8 / Real.exp (-Bstar ui S) + 2) * F ^ 2 * (b - a) / S.r u b := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hm := h.mu_bounds hp
  have hd := h.scalar_radius_difference hu hu0 hua.le hab hb0
  have ht := scalar_mass_ratio_difference (h.r_pos hp (hua.trans_le hab))
    (h.scalar_strip_radius hu hu0 hua hab hb0 hwidth).1
    (by positivity : 0 ≤ 2 / Real.exp (-Bstar ui S)) hF (sub_nonneg.mpr hab)
    ⟨hm.1, hm.2.le⟩ (h.scalar_strip_mass_difference hu hu0 hua hab hb0 (by linarith) htheta)
    (by rw [abs_of_nonneg hd.1]; exact hd.2)
  exact ht.trans_eq (by ring)

end StandingFull

end AcExtensionPrinciple

end
