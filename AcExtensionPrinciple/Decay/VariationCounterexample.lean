module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic

/-!
# Nonnegativity is necessary for the abstract variation estimate

Audit: paper `e1a0fd5`, `equations.tex` lines 952–962,
`eq:terminal-scalar-variation`. The paper uses a nonnegative blueshift density.
The abstract variation estimate requires the explicit condition `g ≥ 0`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

/-- A signed integrable weight with zero integral can dominate a nonconstant AC function's absolute
derivative after multiplication by `|A|`. Thus the variation estimate for signed weights fails even
with `B=0` and `sup |A|=1`. Paper `e1a0fd5`, `equations.tex` lines 952–962. -/
theorem signed_weight_variation_counterexample :
    ∃ P g A : ℝ → ℝ,
      AbsolutelyContinuousOnInterval P (-1) 1 ∧
      IntervalIntegrable g volume (-1) 1 ∧
      (∀ᵐ x ∂volume, |deriv P x| ≤ g x * |A x|) ∧
      (∫ x in (-1 : ℝ)..1, g x) = 0 ∧
      (∀ x : ℝ, |A x| ≤ 1) ∧ A (-1) = 1 ∧
      0 < eVariationOn P (Icc (-1) 1) := by
  let P : ℝ → ℝ := fun x ↦ min x 0
  let g : ℝ → ℝ := fun x ↦ if x ≤ 0 then 1 else -1
  let A : ℝ → ℝ := fun x ↦ if x ≤ 0 then 1 else 0
  have hP : AbsolutelyContinuousOnInterval P (-1) 1 :=
    (LipschitzWith.id.min_const 0).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgL : g =ᵐ[volume.restrict (Ι (-1 : ℝ) 0)] fun _ ↦ (1 : ℝ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact Eventually.of_forall (fun x hx ↦ by
      have hx' : x ∈ Ioc (-1 : ℝ) 0 := by simpa using hx
      simp [g, hx'.2])
  have hgR : g =ᵐ[volume.restrict (Ι (0 : ℝ) 1)] fun _ ↦ (-1 : ℝ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact Eventually.of_forall (fun x hx ↦ by
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
      simp [g, not_le.mpr hx'.1])
  have hiL : IntervalIntegrable g volume (-1) 0 := intervalIntegrable_const.congr_ae hgL.symm
  have hiR : IntervalIntegrable g volume 0 1 := intervalIntegrable_const.congr_ae hgR.symm
  have hint : (∫ x in (-1 : ℝ)..1, g x) = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR,
      intervalIntegral.integral_congr_ae_restrict hgL,
      intervalIntegral.integral_congr_ae_restrict hgR]
    norm_num
  have hder : ∀ᵐ x ∂volume, |deriv P x| ≤ g x * |A x| := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have heq : P =ᶠ[𝓝 x] id := by
        filter_upwards [gt_mem_nhds hxneg] with y hy
        exact min_eq_left hy.le
      rw [heq.deriv_eq]
      simp [g, A, hxneg.le]
    · have heq : P =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [lt_mem_nhds hxpos] with y hy
        exact min_eq_right hy.le
      rw [heq.deriv_eq]
      simp [g, A, not_le.mpr hxpos]
  refine ⟨P, g, A, hP, hiL.trans hiR, hder, hint, ?_, ?_, ?_⟩
  · intro x
    simp only [A]
    split_ifs <;> norm_num
  · norm_num [A]
  · have hbound := eVariationOn.edist_le P
      (show (-1 : ℝ) ∈ Icc (-1) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    have hpos : (0 : ℝ≥0∞) < edist (P (-1)) (P 1) := by
      simp [P]
    exact hpos.trans_le hbound

end AcExtensionPrinciple

end
