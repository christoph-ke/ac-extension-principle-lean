module

public import AcExtensionPrinciple.Weighted.Kernels

/-!
# Tonelli estimate for weighted radial kernels

Helpers for paper commit `e1a0fd5`, `equations.tex` lines 1204–1223.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Tonelli with the radial power kernel; paper `e1a0fd5`, `equations.tex`
lines 1204–1223 (`eq:remainder-radial-estimate`, `eq:radial-l1-estimate`). -/
theorem weighted_radial_tonelli_le {w : ℝ → ℝ} {F : ℝ → ℝ≥0∞} {R δ p k : ℝ}
    (hw : Measurable w) (hF : Measurable F)
    (hwpos : ∀ s ∈ Ioc 0 R, 0 ≤ w s) (hp : δ + 1 < p)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc 0 R, ∫⁻ s in Ioc 0 R,
      if s < r then ENNReal.ofReal (w r * r ^ (-p)) *
        ENNReal.ofReal (s ^ k) * F s else 0) ≤
      ∫⁻ s in Ioc 0 R,
        ENNReal.ofReal (w s * s ^ (k + 1 - p) / (p - δ - 1)) * F s := by
  let K (r s : ℝ) : ℝ≥0∞ := if s < r then
    ENNReal.ofReal (w r * r ^ (-p)) * ENNReal.ofReal (s ^ k) * F s else 0
  have hK : Measurable (Function.uncurry K) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · exact (((hw.comp measurable_fst).mul (measurable_fst.pow_const _)).ennreal_ofReal.mul
        (measurable_snd.pow_const _).ennreal_ofReal).mul (hF.comp measurable_snd)
    · exact measurable_const
  change (∫⁻ r in Ioc 0 R, ∫⁻ s in Ioc 0 R, K r s) ≤ _
  rw [lintegral_lintegral_swap hK.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioc
  intro s hs
  have heq : (fun r ↦ K r s) = (Ioi s).indicator
      (fun r ↦ ENNReal.ofReal (s ^ k) * F s * ENNReal.ofReal (w r * r ^ (-p))) := by
    funext r
    simp only [K, indicator, mem_Ioi]
    split_ifs <;> simp [mul_comm, mul_assoc]
  have hset : Ioi s ∩ Ioc 0 R = Ioc s R := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · tauto
    · rintro ⟨hsr, hrR⟩
      exact ⟨hsr, hs.1.trans hsr, hrR⟩
  rw [heq, setLIntegral_indicator measurableSet_Ioi, hset]
  have horder (r : ℝ) : ENNReal.ofReal (s ^ k) * F s *
      ENNReal.ofReal (w r * r ^ (-p)) =
      (ENNReal.ofReal (w r * r ^ (-p)) * ENNReal.ofReal (s ^ k)) * F s := by ring
  simp_rw [horder]
  have hm : Measurable (fun r ↦ ENNReal.ofReal (w r * r ^ (-p)) *
      ENNReal.ofReal (s ^ k)) := by
    simpa only [Pi.mul_apply, id_eq] using
      (((hw.mul (measurable_id.pow_const (-p))).ennreal_ofReal).mul_const
        (ENNReal.ofReal (s ^ k)))
  rw [lintegral_mul_const (F s)
      hm,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hkernel := weighted_rpow_kernel_le hs.1 (hwpos s hs) hp hgrowth
  calc
    _ ≤ (ENNReal.ofReal (w s * s ^ (1 - p) / (p - δ - 1)) *
        ENNReal.ofReal (s ^ k)) * F s := by
      gcongr
    _ = _ := by
      rw [mul_comm (ENNReal.ofReal (w s * s ^ (1 - p) / (p - δ - 1))),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
      congr 2
      rw [← mul_div_assoc, mul_left_comm, ← Real.rpow_add hs.1]
      rw [show k + (1 - p) = k + 1 - p by ring]

end AcExtensionPrinciple

end
