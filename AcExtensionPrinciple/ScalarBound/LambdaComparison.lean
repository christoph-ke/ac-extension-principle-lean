module

public import AcExtensionPrinciple.ScalarBound.ComparisonAlgebra

/-!
# Comparing λ across the bootstrapped strip

Paper commit `e1a0fd5`, `equations.tex`
lines 472–483, `eq:scalar-bound-lambda-comparison`. Passing from
logarithms to λ uses λ ≤ 1 and does not require a small log difference.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Exponentiation is 1-Lipschitz for logarithms of numbers in (0,1].
Paper `e1a0fd5`, lines 480–483. -/
theorem scalar_expansion_difference_le_log {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    |x - y| ≤ |Real.log x - Real.log y| := by
  have ordered : ∀ {x y : ℝ}, 0 < x → 0 < y → x ≤ y → y ≤ 1 →
      y - x ≤ Real.log y - Real.log x := by
    intro x y hx hy hxy hy1
    have hl : Real.log x ≤ Real.log y := (Real.log_le_log_iff hx hy).mpr hxy
    have ht := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at ht
    have ht' : (1 + Real.log x - Real.log y) * y ≤ x :=
      (le_div_iff₀ hy).mp (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hy1 (sub_nonneg.mpr hl)
    nlinarith
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr ((Real.log_le_log_iff hx hy).mpr hxy))]
    linarith [ordered hx hy hxy hy1]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr ((Real.log_le_log_iff hy hx).mpr hyx))]
    exact ordered hy hx hyx hx1

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- λ comparison obtained by integrating the coefficient difference.
The gap premise comes from G2; θ is the strip bootstrap premise.
Paper `e1a0fd5`, `eq:scalar-bound-lambda-comparison`, lines 472–483. -/
theorem scalar_strip_lambda_difference {U a b F g u : ℝ}
    (hU : ui ≤ U) (hUa : U < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hF : 1 ≤ F) (hwidth : b - a ≤ S.r U b / 2)
    (hgap : ∀ p ∈ Icc ui U ×ˢ Icc a b, g ≤ 1 - S.mu p.1 p.2)
    (htheta : ∀ p ∈ Icc ui U ×ˢ Icc a b, |S.theta p.1 p.2| ≤ 2 * F)
    (hu : u ∈ Icc ui U) :
    |S.lam u a - S.lam u b| ≤
      scalarStripCoefficientConstant ui S g * F ^ 2 * (b - a) / S.r u b := by
  have hU0 : U < 0 := hUa.trans_le (hab.trans hb0)
  have huv : u < b := hu.2.trans_lt (hUa.trans_le hab)
  have hua : u < a := hu.2.trans_lt hUa
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, huv.le, hb0⟩
  have hpA : (u, a) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, hua.le, hab.trans hb0⟩
  have hL := h.log_lam_primitive hu.1 le_rfl hp.2.1 hua (hab.trans hb0)
  have hL₀ := h.log_lam_primitive hu.1 le_rfl hp.2.1 huv hb0
  have hR := h.inv_radius_primitive hu.1 le_rfl hp.2.1 huv hb0
  let C := scalarStripCoefficientConstant ui S g
  have hC : 0 ≤ C := by dsimp [C, scalarStripCoefficientConstant]; positivity
  have he : Real.log (S.lam u a) - Real.log (S.lam u b) =
      ∫ s in ui..u, S.gamma s a * S.varkappa s a - S.gamma s b * S.varkappa s b := by
    have heA := hL.2
    have heB := hL₀.2
    dsimp only at heA heB
    rw [(h.initial_gauge a ⟨hU.trans hUa.le, hab.trans hb0⟩).2, Real.log_one, sub_zero] at heA
    rw [(h.initial_gauge b ⟨hU.trans (hUa.le.trans hab), hb0⟩).2, Real.log_one, sub_zero] at heB
    rw [intervalIntegral.integral_sub hL.1 hL₀.1]
    linarith
  have hI : |Real.log (S.lam u a) - Real.log (S.lam u b)| ≤
      C * F ^ 2 * (b - a) * (∫ s in ui..u, -S.nu s b / S.r s b ^ 2) := by
    rw [he]
    calc
      _ ≤ ∫ s in ui..u, |S.gamma s a * S.varkappa s a - S.gamma s b * S.varkappa s b| :=
        intervalIntegral.abs_integral_le_integral_abs hu.1
      _ ≤ ∫ s in ui..u, (C * F ^ 2 * (b - a)) * (-S.nu s b / S.r s b ^ 2) :=
        intervalIntegral.integral_mono_on hu.1 (hL.1.sub hL₀.1).abs
          (hR.1.const_mul _) (by
            intro s hs
            have hsU : s ∈ Icc ui U := ⟨hs.1, hs.2.trans hu.2⟩
            have hrmono := h.scalar_radius_in_antitone hsU.2 hsU.1 hU0
              (hUa.le.trans hab) hb0
            have ht := h.scalar_strip_coefficient_difference hs.1 (hs.2.trans_lt hp.2.1)
              (hs.2.trans_lt hua) hab hb0 hg hF (by linarith)
              (fun t ht => hgap (s, t) ⟨hsU, ht⟩)
              (fun t ht => htheta (s, t) ⟨hsU, ht⟩)
            exact ht.trans_eq (by dsimp [C]; ring))
      _ = _ := intervalIntegral.integral_const_mul _ _
  calc
    _ ≤ |Real.log (S.lam u a) - Real.log (S.lam u b)| :=
      scalar_expansion_difference_le_log (h.lam_pos hpA) (h.lam_pos hp)
        (h.lam_bounds hpA).2 (h.lam_bounds hp).2
    _ ≤ _ := hI
    _ ≤ (C * F ^ 2 * (b - a)) * (1 / S.r u b) :=
      mul_le_mul_of_nonneg_left (h.radius_time_integral_le hp huv)
        (mul_nonneg (mul_nonneg hC (sq_nonneg F)) (sub_nonneg.mpr hab))
    _ = _ := by ring

end StandingFull

end AcExtensionPrinciple

end
