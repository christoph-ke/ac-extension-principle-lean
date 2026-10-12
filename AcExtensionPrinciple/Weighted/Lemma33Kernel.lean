module

public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The transported-data L¹ to L² kernel argument

Paper `e1a0fd5`, `eq:transported-radial-estimate`,
`equations.tex` lines 1196–1202. Weighted Cauchy–Schwarz in the initial
label followed by Tonelli proves the integral form of Minkowski used here.
-/

public section

namespace AcExtensionPrinciple

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/-- The squared label integral is bounded by its L¹ mass times the label
integral of the squared kernel. Paper `e1a0fd5`, lines 1196–1202. -/
theorem lintegral_label_cauchySchwarz {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f K : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hK : AEMeasurable K μ) :
    (∫⁻ a, f a * K a ∂μ) ^ 2 ≤
      (∫⁻ a, f a ∂μ) * ∫⁻ a, f a * K a ^ 2 ∂μ := by
  have h := lintegral_sqrt_mul_sq_le hf (hf.mul (hK.pow_const 2))
  convert h using 3
  funext a
  dsimp only [Pi.mul_apply]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Uniform L² kernel bounds give an L¹ to L² operator estimate. The weight
may be unbounded and all lower integrals retain infinity. Paper `e1a0fd5`,
`eq:transported-radial-estimate`, lines 1196–1202. -/
theorem weighted_label_kernel_l2_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {f : β → ℝ≥0∞} {K : α → β → ℝ≥0∞}
    {ω : α → ℝ≥0∞} {C : ℝ≥0∞} (hf : Measurable f)
    (hK : Measurable (Function.uncurry K)) (hω : Measurable ω)
    (hbound : ∀ a, (∫⁻ x, ω x * K x a ^ 2 ∂μ) ≤ C) :
    (∫⁻ x, ω x * (∫⁻ a, f a * K x a ∂ν) ^ 2 ∂μ) ≤
      C * (∫⁻ a, f a ∂ν) ^ 2 := by
  have hH : Measurable (fun p : α × β => ω p.1 * (f p.2 * K p.1 p.2 ^ 2)) :=
    (hω.comp measurable_fst).mul ((hf.comp measurable_snd).mul (hK.pow_const 2))
  calc
    _ ≤ ∫⁻ x, ω x * ((∫⁻ a, f a ∂ν) * ∫⁻ a, f a * K x a ^ 2 ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      exact mul_le_mul le_rfl (lintegral_label_cauchySchwarz hf.aemeasurable
        (hK.of_uncurry_left.aemeasurable)) zero_le zero_le
    _ = (∫⁻ a, f a ∂ν) * ∫⁻ x, ∫⁻ a, ω x * (f a * K x a ^ 2) ∂ν ∂μ := by
      simp_rw [mul_left_comm (ω _) (∫⁻ a, f a ∂ν)]
      rw [lintegral_const_mul _ (by fun_prop)]
      congr 1
      apply lintegral_congr
      intro x
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = (∫⁻ a, f a ∂ν) * ∫⁻ a, f a * ∫⁻ x, ω x * K x a ^ 2 ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hH.aemeasurable]
      congr 1
      apply lintegral_congr
      intro a
      simp_rw [mul_left_comm (ω _) (f a)]
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ (∫⁻ a, f a ∂ν) * ∫⁻ a, f a * C ∂ν := by
      gcongr with a
      exact hbound a
    _ = _ := by
      rw [lintegral_mul_const C hf]
      ring

/-- The same kernel estimate for measurable equivalence classes on the
restricted domain and label interval. Paper `e1a0fd5`, lines 1196–1202. -/
theorem weighted_label_kernel_l2_le_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {f : β → ℝ≥0∞} {K : α → β → ℝ≥0∞}
    {ω : α → ℝ≥0∞} {C : ℝ≥0∞} (hf : AEMeasurable f ν)
    (hK : AEMeasurable (Function.uncurry K) (μ.prod ν)) (hω : AEMeasurable ω μ)
    (hbound : ∀ᵐ a ∂ν, (∫⁻ x, ω x * K x a ^ 2 ∂μ) ≤ C) :
    (∫⁻ x, ω x * (∫⁻ a, f a * K x a ∂ν) ^ 2 ∂μ) ≤
      C * (∫⁻ a, f a ∂ν) ^ 2 := by
  have hs : ∀ᵐ x ∂μ, AEMeasurable (K x) ν := by
    filter_upwards [ae_ae_of_ae_prod hK.ae_eq_mk] with x hx
    have hm : Measurable (fun a => hK.mk (Function.uncurry K) (x, a)) :=
      hK.measurable_mk.comp (measurable_const.prodMk measurable_id)
    have he : K x =ᵐ[ν] (fun a => hK.mk (Function.uncurry K) (x, a)) :=
      (ae_iff).mpr hx
    exact hm.aemeasurable.congr he.symm
  have hJ : AEMeasurable (fun x => ∫⁻ a, f a * K x a ^ 2 ∂ν) μ :=
    (hf.comp_snd.mul (hK.pow_const 2)).lintegral_prod_right
  have hH : AEMeasurable (fun p : α × β => ω p.1 * (f p.2 * K p.1 p.2 ^ 2))
      (μ.prod ν) := hω.comp_fst.mul (hf.comp_snd.mul (hK.pow_const 2))
  calc
    _ ≤ ∫⁻ x, ω x * ((∫⁻ a, f a ∂ν) * ∫⁻ a, f a * K x a ^ 2 ∂ν) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hs] with x hx
      exact mul_le_mul le_rfl (lintegral_label_cauchySchwarz hf hx) zero_le zero_le
    _ = (∫⁻ a, f a ∂ν) * ∫⁻ x, ∫⁻ a, ω x * (f a * K x a ^ 2) ∂ν ∂μ := by
      simp_rw [mul_left_comm (ω _) (∫⁻ a, f a ∂ν)]
      rw [lintegral_const_mul'' _ (show AEMeasurable
        (fun x => ω x * ∫⁻ a, f a * K x a ^ 2 ∂ν) μ from hω.mul hJ)]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [hs] with x hx
      exact (lintegral_const_mul'' _ (show AEMeasurable
        (fun a => f a * K x a ^ 2) ν from hf.mul (hx.pow_const 2))).symm
    _ = (∫⁻ a, f a ∂ν) * ∫⁻ a, f a * ∫⁻ x, ω x * K x a ^ 2 ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hH]
      congr 1
      apply lintegral_congr_ae
      have hKa : ∀ᵐ a ∂ν, AEMeasurable (fun x => K x a) μ := by
        filter_upwards [ae_ae_of_ae_prod hK.prod_swap.ae_eq_mk] with a ha
        have hm : Measurable (fun x => hK.prod_swap.mk
          (fun z : β × α => (Function.uncurry K) z.swap) (a, x)) :=
          hK.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
        have he : (fun x => K x a) =ᵐ[μ] (fun x => hK.prod_swap.mk
            (fun z : β × α => (Function.uncurry K) z.swap) (a, x)) := (ae_iff).mpr ha
        exact hm.aemeasurable.congr he.symm
      filter_upwards [hKa] with a ha
      simp_rw [mul_left_comm (ω _) (f a)]
      exact lintegral_const_mul'' _ (show AEMeasurable
        (fun x => ω x * K x a ^ 2) μ from hω.mul (ha.pow_const 2))
    _ ≤ (∫⁻ a, f a ∂ν) * ∫⁻ a, f a * C ∂ν := by
      apply mul_le_mul le_rfl ?_ zero_le zero_le
      exact lintegral_mono_ae (hbound.mono (fun _ ha => mul_le_mul le_rfl ha zero_le zero_le))
    _ = _ := by
      rw [lintegral_mul_const'' C hf]
      ring

end AcExtensionPrinciple

end
