module

public import AcExtensionPrinciple.Solution.PrimitiveCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Right endpoint calculus for characteristic primitives

Paper `e1a0fd5`, lines 222, 275 and 311:
finite one-sided limits of integrands determine one-sided slopes of primitives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A primitive's right slope tends to the right limit of its integrand.
Paper `e1a0fd5`, lines 222, 275, 311 (integral equations at the regular axis). -/
theorem intervalPrimitive_right_slope {f g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hp : ∀ x ∈ Icc a b, IntervalPrimitive f g a x)
    (hg : Tendsto g (𝓝[>] a) (𝓝 c)) :
    Tendsto (fun x => (f x - f a) / (x - a)) (𝓝[>] a) (𝓝 c) := by
  have hi := (hp b ⟨hab.le, le_rfl⟩).1
  have hev : ∀ᶠ x in 𝓝[>] a, x ∈ Ioc a b := by
    filter_upwards [eventually_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ x in 𝓝 a, x < b from Iio_mem_nhds hab)] with x hx hx'
    exact ⟨hx, hx'.le⟩
  have hm : StronglyMeasurableAtFilter g (𝓝[>] a) volume :=
    ⟨Ioc a b, hev, hi.1.aestronglyMeasurable⟩
  have hd : HasDerivWithinAt (fun x => ∫ s in a..x, g s) c (Ici a) a :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
      (IntervalIntegrable.refl) hm (hg.mono_left inf_le_left)
  have hd' : HasDerivWithinAt f c (Ici a) a := by
    apply (hd.add_const (f a)).congr_of_eventuallyEq
    · filter_upwards [eventually_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (show ∀ᶠ x in 𝓝 a, x < b from Iio_mem_nhds hab)] with x hx hx'
      have he := (hp x ⟨hx, hx'.le⟩).2
      linarith
    · simp
  have hd'' := hd'.mono Ioi_subset_Ici_self
  simpa only [slope_fun_def_field] using
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hd''

end AcExtensionPrinciple

end
