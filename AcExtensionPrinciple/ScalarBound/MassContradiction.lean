module

public import AcExtensionPrinciple.ScalarBound.StripGeometry

/-!
# Large scalar amplitude contradicts the mass bound

Paper commit `e1a0fd5`, `equations.tex`
lines 516–524, `eq:scalar-bound-mass-contradiction`. The numerical
constant is explicit; it depends only on the geometric gap and δ.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- A persistent amplitude forces a lower mass density.
Paper `e1a0fd5`, `eq:scalar-bound-mass-contradiction`, lines 518–522. -/
theorem scalar_mass_density_lower {gap lam theta g F : ℝ}
    (hg : 0 < g) (hgap : g ≤ gap) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hF : 0 ≤ F) (htheta : F / 4 ≤ |theta|) :
    g * F ^ 2 / 32 ≤ gap * theta ^ 2 / (2 * lam) := by
  have hs : F ^ 2 / 16 ≤ theta ^ 2 := by nlinarith [sq_abs theta]
  have hm : g * F ^ 2 / 16 ≤ gap * theta ^ 2 := by
    calc
      _ = g * (F ^ 2 / 16) := by ring
      _ ≤ g * theta ^ 2 := mul_le_mul_of_nonneg_left hs hg.le
      _ ≤ gap * theta ^ 2 := mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
  apply (le_div_iff₀ (mul_pos (by norm_num) hlam)).mpr
  nlinarith [mul_nonneg (sq_nonneg F) (sub_nonneg.mpr hlam1)]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Persistence on a radial strip of width δr/F bounds F uniformly.
The gap premise comes from G2, and persistence from lines 514–516.
Paper `e1a0fd5`, `eq:scalar-bound-mass-contradiction`, lines 516–524. -/
theorem scalar_mass_contradiction {u a b g F δ : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hF : 0 < F) (hδ : 0 < δ)
    (hgap : ∀ s ∈ Icc a b, g ≤ 1 - S.mu u s)
    (hpersist : ∀ s ∈ Icc a b, F / 4 ≤ |S.theta u s|)
    (hwidth : b - a = δ * S.r u b / F) : F ≤ 16 / (g * δ) := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hr := h.r_pos hp (hua.trans_le hab)
  have hi := h.regularCenter.localBV.mass_out u a b hab
    (outSeg_subset_triangle hu hu0 hua.le hb0)
  have hI : g * F ^ 2 / 32 * (b - a) ≤ ∫ s in a..b, S.massV u s := by
    calc
      _ = ∫ s in a..b, g * F ^ 2 / 32 := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
      _ ≤ _ := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi.1 (by
        intro s hs
        have hps : (u, s) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
        exact scalar_mass_density_lower hg (hgap s hs) (h.lam_pos hps)
          (h.lam_bounds hps).2 hF.le (hpersist s hs))
  have hm := h.scalar_mass_bounds hp (hua.trans_le hab)
  have hmA := (h.scalar_mass_bounds
    (show (u, a) ∈ pastTriangle ui from ⟨hu, hu0, hua.le, hab.trans hb0⟩) hua).1
  have hsmall : g * δ * F * S.r u b / 32 < S.r u b / 2 := by
    have he : g * F ^ 2 / 32 * (b - a) = g * δ * F * S.r u b / 32 := by
      rw [hwidth]
      field_simp
    rw [he] at hI
    have heMass := hi.2
    linarith
  apply (le_div_iff₀ (mul_pos hg hδ)).mpr
  have ht : g * δ * F < 16 := by nlinarith
  nlinarith

end StandingFull

end AcExtensionPrinciple

end
