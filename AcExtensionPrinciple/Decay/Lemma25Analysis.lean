module

public import AcExtensionPrinciple.Analysis.EnergyContraction
public import AcExtensionPrinciple.BoundaryEnergy.Stability

/-!
# The analytic steps in boundary contraction

Paper `e1a0fd5`, `equations.tex` lines 771–787. Integrability of the
nonnegative dissipation follows from the AC energy balance; no separate
square-integrability hypothesis is imposed on the scalar trace.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

/-- Pointwise variation controls displacement from the initial datum.
Paper `e1a0fd5`, `equations.tex` lines 771–776. -/
theorem boundary_datum_displacement_le {P : ℝ → ℝ} {a d u : ℝ}
    (had : a ≤ d) (hP : AbsolutelyContinuousOnInterval P a d) (hu : u ∈ Icc a d) :
    |P u - P a| ≤ (eVariationOn P (Icc a d)).toReal := by
  have hBV : BoundedVariationOn P (Icc a d) := by
    simpa only [uIcc_of_le had] using hP.boundedVariationOn
  simpa only [Real.dist_eq] using hBV.dist_le hu (left_mem_Icc.mpr had)

/-- The balance makes dissipation integrable whenever the work coefficient is
continuous and the energy and datum are AC. Paper `e1a0fd5`, lines 771–778,
`eq:boundary-energy-balance`. -/
theorem dissipation_integrable_of_ac_balance {E P A D : ℝ → ℝ} {a d b : ℝ}
    (had : a ≤ d) (hE : AbsolutelyContinuousOnInterval E a d)
    (hP : AbsolutelyContinuousOnInterval P a d) (hA : ContinuousOn A (Icc a d))
    (hbal : ∀ᵐ u ∂volume, u ∈ Ioo a d → deriv E u + D u = b * A u * deriv P u) :
    IntervalIntegrable D volume a d := by
  have hc : ContinuousOn (fun u => b * A u) (uIcc a d) := by
    simpa only [uIcc_of_le had] using hA.const_mul b
  have hi := hP.intervalIntegrable_deriv.mul_continuousOn hc
  apply (hi.sub hE.intervalIntegrable_deriv).congr_ae
  change ∀ᵐ u ∂volume.restrict (uIoc a d), deriv P u * (b * A u) - deriv E u = D u
  rw [uIoc_of_le had, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hbal, show ∀ᵐ u : ℝ, u ≠ d by simp [ae_iff]] with u hu hune
  intro huI
  have h := hu ⟨huI.1, lt_of_le_of_ne huI.2 hune⟩
  change deriv P u * (b * A u) - deriv E u = D u
  nlinarith

/-- Stability and the quadratic energy comparison bound the work coefficient.
Paper `e1a0fd5`, `equations.tex` line 778. -/
theorem work_coefficient_le {b E E0 A V : ℝ} (hb : 0 < b)
    (hA : b / 2 * A ^ 2 ≤ E)
    (hstab : Real.sqrt E ≤ Real.sqrt E0 + Real.sqrt (b / 2) * V) :
    b * |A| ≤ Real.sqrt (2 * b * E0) + b * V := by
  have hAs : Real.sqrt (b / 2) * |A| ≤ Real.sqrt E := by
    simpa only [Real.sqrt_mul (show 0 ≤ b / 2 by positivity),
      Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hA
  have hproduct : Real.sqrt (2 * b) * Real.sqrt (b / 2) = b := by
    rw [← Real.sqrt_mul (show 0 ≤ 2 * b by positivity)]
    calc
      Real.sqrt (2 * b * (b / 2)) = Real.sqrt (b ^ 2) := by congr 1; ring
      _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have h := mul_le_mul_of_nonneg_left (hAs.trans hstab) (Real.sqrt_nonneg (2 * b))
  rw [mul_add, ← mul_assoc, hproduct, ← Real.sqrt_mul (show 0 ≤ 2 * b by positivity)] at h
  simpa only [← mul_assoc, hproduct] using h

/-- The integrated work is bounded using total variation and stability.
Paper `e1a0fd5`, `equations.tex` line 778. -/
theorem integrated_work_le {E P phi : ℝ → ℝ} {a d b : ℝ}
    (had : a ≤ d) (hb : 0 < b)
    (hP : AbsolutelyContinuousOnInterval P a d)
    (hphi : AbsolutelyContinuousOnInterval phi a d)
    (hA : ∀ u ∈ Icc a d, b / 2 * (P u - phi u) ^ 2 ≤ E u)
    (hstab : ∀ u ∈ Icc a d, Real.sqrt (E u) ≤ Real.sqrt (E a) +
      Real.sqrt (b / 2) * (eVariationOn P (Icc a d)).toReal) :
    (∫ u in a..d, b * (P u - phi u) * deriv P u) ≤
      Real.sqrt (2 * b * E a) * (eVariationOn P (Icc a d)).toReal +
        b * (eVariationOn P (Icc a d)).toReal ^ 2 := by
  let V := (eVariationOn P (Icc a d)).toReal
  let C := Real.sqrt (2 * b * E a) + b * V
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : ContinuousOn (fun u => b * (P u - phi u)) (uIcc a d) :=
    continuousOn_const.mul (hP.continuousOn.sub hphi.continuousOn)
  have hi := hP.intervalIntegrable_deriv.mul_continuousOn hc
  have he : IntervalIntegrable (fun u => b * (P u - phi u) * deriv P u) volume a d := by
    simpa only [mul_comm (deriv P _) (b * _)] using hi
  have hbound : (∫ u in a..d, b * (P u - phi u) * deriv P u) ≤
      C * (∫ u in a..d, |deriv P u|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on had he (hP.intervalIntegrable_deriv.abs.const_mul C)
    intro u hu
    have hcoeff := work_coefficient_le hb (hA u hu) (hstab u hu)
    calc
      b * (P u - phi u) * deriv P u ≤ |b * (P u - phi u) * deriv P u| := le_abs_self _
      _ = (b * |P u - phi u|) * |deriv P u| := by rw [abs_mul, abs_mul, abs_of_pos hb]
      _ ≤ C * |deriv P u| := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
  have hBV : BoundedVariationOn P (Icc a d) := by
    simpa only [uIcc_of_le had] using hP.boundedVariationOn
  have ht := mul_le_mul_of_nonneg_left (integral_abs_deriv_le_variation had hBV) hC
  calc
    _ ≤ C * (∫ u in a..d, |deriv P u|) := hbound
    _ ≤ C * V := ht
    _ = _ := by dsimp [C, V]; ring

/-- The observed integral gives the lower bound for dissipation printed in
Lemma 2.5. Paper `e1a0fd5`, `eq:observed-dissipation`, lines 771–776. -/
theorem observed_dissipation_le {P w D : ℝ → ℝ} {a d b H sigma E0 : ℝ}
    (had : a ≤ d) (hP : AbsolutelyContinuousOnInterval P a d)
    (hw : ContinuousOn w (Icc a d)) (hw0 : ∀ u ∈ Icc a d, 0 ≤ w u)
    (hD : IntervalIntegrable D volume a d)
    (htime : (∫ u in a..d, w u) = H * b)
    (hobs : sigma * E0 ≤ ∫ u in a..d, w u * (P u - P a) ^ 2 + 2 * D u) :
    sigma / 2 * E0 - H * b / 2 * (eVariationOn P (Icc a d)).toReal ^ 2 ≤
      ∫ u in a..d, D u := by
  let V := (eVariationOn P (Icc a d)).toReal
  have hV := ENNReal.toReal_nonneg (a := eVariationOn P (Icc a d))
  have hPc : ContinuousOn P (Icc a d) := by simpa [uIcc_of_le had] using hP.continuousOn
  have hQc : ContinuousOn (fun u => w u * (P u - P a) ^ 2) (Icc a d) :=
    hw.mul ((hPc.sub continuousOn_const).pow 2)
  have hQ := hQc.intervalIntegrable_of_Icc (μ := volume) had
  have hsmall : (∫ u in a..d, w u * (P u - P a) ^ 2) ≤ H * b * V ^ 2 := by
    rw [← htime, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on had hQ
      (hw.intervalIntegrable_of_Icc (μ := volume) had |>.mul_const _)
    intro u hu
    have hdisp := boundary_datum_displacement_le had hP hu
    apply mul_le_mul_of_nonneg_left _ (hw0 u hu)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hV).mpr hdisp
  rw [intervalIntegral.integral_add hQ (hD.const_mul 2),
    intervalIntegral.integral_const_mul] at hobs
  dsimp [V] at hsmall
  linarith

end AcExtensionPrinciple

end
