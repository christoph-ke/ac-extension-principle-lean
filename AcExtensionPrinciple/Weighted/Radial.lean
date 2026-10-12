module

public import AcExtensionPrinciple.Weighted.Tonelli
public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# One-cone radial operator

Helpers for paper commit `e1a0fd5`, `equations.tex` lines 1204–1223.
Radius is the integration variable on a fixed cone. Lintegrals allow an infinite
right-hand side; the finite weighted L¹ and L² cases are included.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The radial primitive operator; paper `e1a0fd5`, `equations.tex`
lines 1204–1215 (`eq:remainder-radial-estimate`). -/
@[expose] noncomputable def radialOperator (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r ^ 2)⁻¹ * ∫ s in Ioo 0 r, s * f s

/-- Write the radial interval as an indicator in the full cone interval;
paper `e1a0fd5`, `equations.tex` lines 1204–1223. -/
theorem radial_inner_lintegral_eq {H : ℝ → ℝ≥0∞} {r R : ℝ} (hrR : r ≤ R) :
    (∫⁻ s in Ioo 0 r, H s) = ∫⁻ s in Ioc 0 R, if s < r then H s else 0 := by
  have heq : (fun s ↦ if s < r then H s else 0) = (Iio r).indicator H := by
    funext s
    simp [indicator, mem_Iio]
  rw [heq, setLIntegral_indicator measurableSet_Iio]
  have hset : Iio r ∩ Ioc 0 R = Ioo 0 r := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · tauto
    · rintro ⟨hs0, hsr⟩
      exact ⟨hsr, hs0, hsr.le.trans hrR⟩
  rw [hset]

/-- The absolute value of a radial primitive is bounded by its positive
kernel; paper `e1a0fd5`, `equations.tex` lines 1204–1223. -/
theorem radial_primitive_abs_le (f : ℝ → ℝ) (r : ℝ) :
    ENNReal.ofReal |∫ s in Ioo 0 r, s * f s| ≤
      ∫⁻ s in Ioo 0 r, ENNReal.ofReal (s * |f s|) := by
  have h := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioo 0 r))
    (fun s ↦ s * f s)
  have heq : (∫⁻ s in Ioo 0 r, ‖s * f s‖ₑ) =
      ∫⁻ s in Ioo 0 r, ENNReal.ofReal (s * |f s|) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    change ‖s * f s‖ₑ = ENNReal.ofReal (s * |f s|)
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos hs.1]
  rw [heq, Real.enorm_eq_ofReal_abs] at h
  exact h

/-- The one-cone weighted L¹ estimate with constant `1/(1-δ)`;
paper `e1a0fd5`, `eq:radial-l1-estimate`, `equations.tex` lines 1217–1223. -/
theorem weighted_radial_l1_le {w f : ℝ → ℝ} {R δ : ℝ}
    (hw : Measurable w) (hf : Measurable f)
    (hwpos : ∀ s ∈ Ioc 0 R, 0 ≤ w s) (hδ : δ < 1)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc 0 R, ENNReal.ofReal (w r * |radialOperator f r|)) ≤
      ENNReal.ofReal (1 / (1 - δ)) *
        ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s * |f s|) := by
  calc
    _ ≤ ∫⁻ r in Ioc 0 R, ∫⁻ s in Ioc 0 R,
        if s < r then ENNReal.ofReal (w r * r ^ (-(2 : ℝ))) *
          ENNReal.ofReal (s ^ (1 : ℝ)) * ENNReal.ofReal |f s| else 0 := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro r hr
      have hpoint := radial_primitive_abs_le f r
      rw [radial_inner_lintegral_eq hr.2] at hpoint
      have hfactor : 0 ≤ w r * (r ^ 2)⁻¹ := mul_nonneg (hwpos r hr) (by positivity)
      simp only [radialOperator, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (r ^ 2)⁻¹),
        ← mul_assoc, ENNReal.ofReal_mul hfactor]
      calc
        _ ≤ ENNReal.ofReal (w r * (r ^ 2)⁻¹) *
            ∫⁻ s in Ioc 0 R, if s < r then ENNReal.ofReal (s * |f s|) else 0 := by
          gcongr
        _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply setLIntegral_congr_fun measurableSet_Ioc
          intro s hs
          dsimp only
          split_ifs <;> simp [Real.rpow_one, ENNReal.ofReal_mul hs.1.le, mul_assoc]
    _ ≤ ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s / (1 - δ)) * ENNReal.ofReal |f s| := by
      simpa only [show (1 : ℝ) + 1 - 2 = 0 by norm_num, Real.rpow_zero, mul_one,
        show (2 : ℝ) - δ - 1 = 1 - δ by ring] using
        weighted_radial_tonelli_le (p := 2) (k := 1) hw
        (by simpa only [Real.norm_eq_abs] using hf.norm.ennreal_ofReal) hwpos
        (by linarith : δ + 1 < 2) hgrowth
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - δ)),
        ← ENNReal.ofReal_mul (div_nonneg (hwpos s hs) (by linarith))]
      congr 1
      ring

end AcExtensionPrinciple

end
