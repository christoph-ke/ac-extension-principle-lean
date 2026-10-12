module

public import AcExtensionPrinciple.Weighted.Radial

/-!
# Weighted L² radial estimate

One-cone estimate for paper commit `e1a0fd5`, `equations.tex`
lines 1204–1215 (`eq:remainder-radial-estimate`). The proof uses the
Cauchy–Schwarz and Tonelli form of the weighted Hardy inequality.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The power kernel from the centre to radius `r`; paper `e1a0fd5`,
`equations.tex` lines 1204–1215. -/
theorem lintegral_rpow_head {r α : ℝ} (hr : 0 < r) (hα : -1 < α) :
    (∫⁻ s in Ioo 0 r, ENNReal.ofReal (s ^ α)) =
      ENNReal.ofReal (r ^ (α + 1) / (α + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr hα)]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl hα), Real.zero_rpow (by linarith : α + 1 ≠ 0), sub_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact Real.rpow_nonneg hs.1.le _

/-- Cauchy–Schwarz with the optimal power splitting of the radial primitive;
paper `e1a0fd5`, `equations.tex` lines 1204–1215. -/
theorem radial_primitive_sq_le {f : ℝ → ℝ} {r α : ℝ}
    (hf : Measurable f) (hr : 0 < r) (hα : -1 < α) :
    ENNReal.ofReal |∫ s in Ioo 0 r, s * f s| ^ 2 ≤
      ENNReal.ofReal (r ^ (α + 1) / (α + 1)) *
        ∫⁻ s in Ioo 0 r, ENNReal.ofReal (s ^ (2 - α) * |f s| ^ 2) := by
  have hF : Measurable (fun s : ℝ ↦ ENNReal.ofReal (s ^ α)) :=
    (measurable_id.pow_const α).ennreal_ofReal
  have hG : Measurable (fun s : ℝ ↦ ENNReal.ofReal (s ^ (2 - α) * |f s| ^ 2)) := by
    simpa only [Pi.mul_apply, Real.norm_eq_abs, id_eq] using
      ((measurable_id.pow_const (2 - α)).mul (hf.norm.pow_const 2)).ennreal_ofReal
  have hcs := lintegral_sqrt_mul_sq_le (μ := volume.restrict (Ioo 0 r))
    hF.aemeasurable hG.aemeasurable
  have heq : (∫⁻ s in Ioo 0 r, ENNReal.ofReal (s ^ α) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (s ^ (2 - α) * |f s| ^ 2) ^ (1 / 2 : ℝ)) =
      ∫⁻ s in Ioo 0 r, ENNReal.ofReal (s * |f s|) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    change ENNReal.ofReal (s ^ α) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (s ^ (2 - α) * |f s| ^ 2) ^ (1 / 2 : ℝ) = _
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), ← mul_assoc,
      ← Real.rpow_add hs.1, show α + (2 - α) = 2 by ring, Real.rpow_two,
      ← mul_pow, ENNReal.ofReal_pow (mul_nonneg hs.1.le (abs_nonneg _)),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [heq, lintegral_rpow_head hr hα] at hcs
  exact (pow_le_pow_left' (radial_primitive_abs_le f r) 2).trans hcs

/-- Pointwise quadratic radial bound with a free power splitting;
paper `e1a0fd5`, `equations.tex` lines 1204–1215. -/
theorem weighted_radial_l2_pointwise {w f : ℝ → ℝ} {r R α : ℝ}
    (hf : Measurable f) (hr : 0 < r) (hrR : r ≤ R)
    (hwr : 0 ≤ w r) (hα : -1 < α) :
    ENNReal.ofReal (w r * |radialOperator f r| ^ 2) ≤
      ENNReal.ofReal (1 / (α + 1)) *
        ∫⁻ s in Ioc 0 R, if s < r then
          ENNReal.ofReal (w r * r ^ (-(3 - α))) *
            ENNReal.ofReal (s ^ (2 - α)) * ENNReal.ofReal (|f s| ^ 2) else 0 := by
  have hcs := radial_primitive_sq_le (α := α) hf hr hα
  have hfactor : 0 ≤ w r * (r ^ 2)⁻¹ ^ 2 := by positivity
  rw [radialOperator, abs_mul, mul_pow,
    abs_of_nonneg (by positivity : 0 ≤ (r ^ 2)⁻¹), ← mul_assoc,
    ENNReal.ofReal_mul hfactor, ENNReal.ofReal_pow (abs_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal (w r * (r ^ 2)⁻¹ ^ 2) *
        (ENNReal.ofReal (r ^ (α + 1) / (α + 1)) *
          ∫⁻ s in Ioo 0 r, ENNReal.ofReal (s ^ (2 - α) * |f s| ^ 2)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hfactor,
        radial_inner_lintegral_eq hrR, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      split_ifs with hsr
      · rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
        have hid : w r * (r ^ 2)⁻¹ ^ 2 * (r ^ (α + 1) / (α + 1)) =
            (1 / (α + 1)) * (w r * r ^ (-(3 - α))) := by
          rw [show (r ^ 2)⁻¹ ^ 2 = r ^ (-(4 : ℝ)) by simp [← pow_mul],
            ← mul_div_assoc, mul_assoc, ← Real.rpow_add hr]
          rw [show -(4 : ℝ) + (α + 1) = -(3 - α) by ring]
          ring
        rw [hid, ENNReal.ofReal_mul (one_div_nonneg.mpr (by linarith))]
        ring
      · simp

/-- The weighted radial L² estimate, with the paper's constant;
paper `e1a0fd5`, `eq:remainder-radial-estimate`, `equations.tex` lines 1204–1215.
In particular it applies when the weighted L² integral on the right is finite. -/
theorem weighted_radial_l2_le {w f : ℝ → ℝ} {R δ : ℝ}
    (hw : Measurable w) (hf : Measurable f)
    (hwpos : ∀ s ∈ Ioc 0 R, 0 ≤ w s) (hδ : δ < 3)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc 0 R, ENNReal.ofReal (w r * |radialOperator f r| ^ 2)) ≤
      ENNReal.ofReal ((2 / (3 - δ)) ^ 2) *
        ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s * |f s| ^ 2) := by
  let α := (1 - δ) / 2
  have hα : -1 < α := by dsimp [α]; linarith
  have hp : δ + 1 < 3 - α := by dsimp [α]; linarith
  have hF : Measurable (fun s ↦ ENNReal.ofReal (|f s| ^ 2)) := by
    simpa only [Real.norm_eq_abs] using (hf.norm.pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ r in Ioc 0 R, ENNReal.ofReal (1 / (α + 1)) *
        ∫⁻ s in Ioc 0 R, if s < r then ENNReal.ofReal (w r * r ^ (-(3 - α))) *
          ENNReal.ofReal (s ^ (2 - α)) * ENNReal.ofReal (|f s| ^ 2) else 0 :=
      setLIntegral_mono' measurableSet_Ioc (fun r hr ↦
        weighted_radial_l2_pointwise hf hr.1 hr.2 (hwpos r hr) hα)
    _ ≤ ENNReal.ofReal (1 / (α + 1)) *
        ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s / (2 - α - δ)) *
          ENNReal.ofReal (|f s| ^ 2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have ht := weighted_radial_tonelli_le (p := 3 - α) (k := 2 - α)
        hw hF hwpos hp hgrowth
      have hzero : (2 - α) + 1 - (3 - α) = 0 := by ring
      have hdenom : (3 - α) - δ - 1 = 2 - α - δ := by ring
      simp only [hzero, hdenom, Real.rpow_zero, mul_one] at ht
      gcongr
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [← ENNReal.ofReal_mul (div_nonneg (hwpos s hs) (by linarith)),
        ← ENNReal.ofReal_mul (one_div_nonneg.mpr (by linarith)),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      dsimp [α]
      field_simp
      ring

end AcExtensionPrinciple

end
