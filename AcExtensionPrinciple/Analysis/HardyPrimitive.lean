module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

/-!
# Radial primitive and Hardy bound

Internal helpers for paper commit `e1a0fd5`, `equations.tex`
lines 1006–1015 (`eq:scalar-radial-primitive`, `eq:scalar-radial-hardy`).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Integration by parts in the regular-center average; paper `e1a0fd5`,
`equations.tex` lines 1006–1015 (`eq:scalar-radial-primitive`). -/
theorem radial_primitive_eq {P : ℝ → ℝ} {R r : ℝ}
    (hP : AbsolutelyContinuousOnInterval P 0 R) (hr : 0 < r) (hrR : r ≤ R) :
    P r - (1 / r) * (∫ s in 0..r, P s) =
      (1 / r) * (∫ s in 0..r, s * deriv P s) := by
  have hPr : AbsolutelyContinuousOnInterval P 0 r := hP.mono (by
    rw [uIcc_of_le hr.le, uIcc_of_le (hr.le.trans hrR)]
    exact Icc_subset_Icc le_rfl hrR)
  have hid : AbsolutelyContinuousOnInterval (fun s : ℝ ↦ s) 0 r :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hi := hid.integral_mul_deriv_eq_deriv_mul hPr
  simp only [deriv_id'', one_mul, zero_mul, sub_zero] at hi
  rw [hi]
  field_simp

/-- The radial Hardy kernel has total mass `1/s` beyond `s > 0`; paper
`e1a0fd5`, `equations.tex` lines 1006–1015 (`eq:scalar-radial-hardy`). -/
theorem lintegral_inv_sq_Ioi {s : ℝ} (hs : 0 < s) :
    (∫⁻ r in Ioi s, ENNReal.ofReal (1 / r ^ 2)) = ENNReal.ofReal (1 / s) := by
  have heq (r : ℝ) : 1 / r ^ 2 = r ^ (-2 : ℝ) := by simp [one_div]
  simp_rw [heq]
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hs]
    norm_num [Real.rpow_neg_one, one_div]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hs.trans hr).le _

/-- Tonelli bound for the positive radial averaging kernel; paper `e1a0fd5`,
`equations.tex` lines 1006–1015 (`eq:scalar-radial-hardy`). -/
theorem lintegral_radial_kernel_le {R : ℝ} {q : ℝ → ℝ}
    (hq : Measurable q) :
    (∫⁻ r in Ioc 0 R, ∫⁻ s in Ioc 0 R,
      if s < r then ENNReal.ofReal (s * |q s|) * ENNReal.ofReal (1 / r ^ 2) else 0) ≤
      ∫⁻ s in Ioc 0 R, ENNReal.ofReal (|q s|) := by
  let K (r s : ℝ) : ℝ≥0∞ :=
    if s < r then ENNReal.ofReal (s * |q s|) * ENNReal.ofReal (1 / r ^ 2) else 0
  have hK : Measurable (Function.uncurry K) := by
    have hqabs : Measurable (fun p : ℝ × ℝ ↦ |q p.2|) := by
      simpa only [Real.norm_eq_abs, Function.comp_def] using (hq.comp measurable_snd).norm
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · exact ((measurable_snd.mul hqabs).ennreal_ofReal).mul
        ((measurable_const.div (measurable_fst.pow_const 2)).ennreal_ofReal)
    · exact measurable_const
  change (∫⁻ r in Ioc 0 R, ∫⁻ s in Ioc 0 R, K r s) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi 0, ∫⁻ s in Ioc 0 R, K r s :=
      lintegral_mono_set Ioc_subset_Ioi_self
    _ = ∫⁻ s in Ioc 0 R, ∫⁻ r in Ioi 0, K r s := lintegral_lintegral_swap hK.aemeasurable
    _ ≤ _ := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      have heq : (fun r ↦ K r s) = (Ioi s).indicator
          (fun r ↦ ENNReal.ofReal (s * |q s|) * ENNReal.ofReal (1 / r ^ 2)) := by
        funext r
        simp [K, Set.indicator, mem_Ioi]
      rw [heq, setLIntegral_indicator measurableSet_Ioi,
        inter_eq_left.mpr (Ioi_subset_Ioi hs.1.le),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inv_sq_Ioi hs.1,
        ← ENNReal.ofReal_mul (mul_nonneg hs.1.le (abs_nonneg _))]
      have hid : s * |q s| * (1 / s) = |q s| := by field_simp [hs.1.ne']
      rw [hid]

/-- The regular-center Hardy estimate with the integral of the absolute
derivative on the right; paper `e1a0fd5`, `equations.tex` lines 1006–1015
(`eq:scalar-radial-hardy`). -/
theorem radial_hardy_le_integral_abs_deriv {P : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hP : AbsolutelyContinuousOnInterval P 0 R) :
    (∫⁻ r in Ioc 0 R,
      ENNReal.ofReal (|P r - (1 / r) * (∫ s in 0..r, P s)| / r)) ≤
        ENNReal.ofReal (∫ s in 0..R, |deriv P s|) := by
  have hpoint (r : ℝ) (hr : r ∈ Ioc 0 R) :
      ENNReal.ofReal (|P r - (1 / r) * (∫ s in 0..r, P s)| / r) ≤
        ∫⁻ s in Ioc 0 R,
          if s < r then ENNReal.ofReal (s * |deriv P s|) *
            ENNReal.ofReal (1 / r ^ 2) else 0 := by
    have hPr := hP.mono (show uIcc 0 r ⊆ uIcc 0 R by
      rw [uIcc_of_le hr.1.le, uIcc_of_le hR.le]
      exact Icc_subset_Icc le_rfl hr.2)
    have hsq : IntervalIntegrable (fun s ↦ s * |deriv P s|) volume 0 r :=
      hPr.intervalIntegrable_deriv.abs.continuousOn_mul continuousOn_id
    have hinner :
        (∫⁻ s in Ioc 0 R,
          if s < r then ENNReal.ofReal (s * |deriv P s|) *
            ENNReal.ofReal (1 / r ^ 2) else 0) =
        ENNReal.ofReal ((∫ s in 0..r, s * |deriv P s|) / r ^ 2) := by
      have heq : (fun s ↦ if s < r then ENNReal.ofReal (s * |deriv P s|) *
          ENNReal.ofReal (1 / r ^ 2) else 0) =
          (Iio r).indicator (fun s ↦ ENNReal.ofReal (s * |deriv P s|) *
            ENNReal.ofReal (1 / r ^ 2)) := by
        funext s
        simp [Set.indicator, mem_Iio]
      have hset : Iio r ∩ Ioc 0 R = Ioo 0 r := by
        ext s
        simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
        constructor
        · tauto
        · rintro ⟨hs0, hsr⟩
          exact ⟨hsr, hs0, hsr.le.trans hr.2⟩
      rw [heq, setLIntegral_indicator measurableSet_Iio, hset]
      simp_rw [mul_comm _ (ENNReal.ofReal (1 / r ^ 2))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr.1.le).mp hsq)]
      · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.1.le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact mul_nonneg hs.1.le (abs_nonneg _)
    rw [hinner, radial_primitive_eq hP hr.1 hr.2, abs_mul,
      abs_of_pos (one_div_pos.mpr hr.1)]
    have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun s ↦ s * deriv P s)
      (a := 0) (b := r) hr.1.le
    have habs : (∫ s in 0..r, |s * deriv P s|) = ∫ s in 0..r, s * |deriv P s| := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hr.1.le] at hs
      change |s * deriv P s| = s * |deriv P s|
      rw [abs_mul, abs_of_nonneg hs.1]
    rw [habs] at hnorm
    apply ENNReal.ofReal_le_ofReal
    have heq : (1 / r) * |∫ s in 0..r, s * deriv P s| / r =
        |∫ s in 0..r, s * deriv P s| / r ^ 2 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hnorm (sq_nonneg r)
  calc
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioc hpoint
    _ ≤ ∫⁻ s in Ioc 0 R, ENNReal.ofReal (|deriv P s|) :=
      lintegral_radial_kernel_le (measurable_deriv P)
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [intervalIntegral.integral_of_le hR.le]
      · simpa only [uIoc_of_le hR.le, IntegrableOn] using hP.intervalIntegrable_deriv.abs.def'
      · exact ae_of_all _ (fun s ↦ abs_nonneg _)

end AcExtensionPrinciple

end
