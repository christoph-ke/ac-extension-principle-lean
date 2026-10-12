module

public import AcExtensionPrinciple.Observability.InnerChartCalculus

/-!
# Comparing two moving characteristic integrals

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1460–1473, 1901.
The overlap is split into two endpoint strips and one common interval.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Integral bound for a pointwise bounded real density. Paper `e1a0fd5`,
characteristic calculus at line 1522 and the coordinate use at 1782. -/
theorem inner_integral_bound {f : ℝ → ℝ} {x y B : ℝ} (hxy : x ≤ y)
    (hb : ∀ z ∈ Icc x y, |f z| ≤ B) : |∫ z in x..y, f z| ≤ B * (y - x) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := x) (b := y) (fun z hz => by
      rw [uIoc_of_le hxy] at hz
      simpa only [Real.norm_eq_abs] using hb z ⟨hz.1.le, hz.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy), mul_comm] using hi

/-- Two overlapping integrals differ by their endpoint strips and the
change of integrand on their common interval. Paper `e1a0fd5`,
coordinate regularity at lines 1460–1473, 1901 and local AC calculus at 1412. -/
theorem inner_moving_integral_increment {f g : ℝ → ℝ} {l₀ l₁ x y C D : ℝ}
    (hlo : l₀ ≤ l₁) (hover : l₁ ≤ x) (hxy : x ≤ y)
    (hf : IntervalIntegrable f volume l₀ x) (hg : IntervalIntegrable g volume l₁ y)
    (hleft : ∀ z ∈ Icc l₀ l₁, |f z| ≤ C)
    (hmid : ∀ z ∈ Icc l₁ x, |f z - g z| ≤ D)
    (hright : ∀ z ∈ Icc x y, |g z| ≤ C) :
    |(∫ z in l₀..x, f z) - ∫ z in l₁..y, g z| ≤
      C * (l₁ - l₀) + D * (x - l₁) + C * (y - x) := by
  have hsub₀ : uIcc l₀ l₁ ⊆ uIcc l₀ x := by
    rw [uIcc_of_le hlo, uIcc_of_le (hlo.trans hover)]
    exact Icc_subset_Icc le_rfl hover
  have hsub₁ : uIcc l₁ x ⊆ uIcc l₀ x := by
    rw [uIcc_of_le hover, uIcc_of_le (hlo.trans hover)]
    exact Icc_subset_Icc hlo le_rfl
  have hsub₂ : uIcc l₁ x ⊆ uIcc l₁ y := by
    rw [uIcc_of_le hover, uIcc_of_le (hover.trans hxy)]
    exact Icc_subset_Icc le_rfl hxy
  have hsub₃ : uIcc x y ⊆ uIcc l₁ y := by
    rw [uIcc_of_le hxy, uIcc_of_le (hover.trans hxy)]
    exact Icc_subset_Icc hover le_rfl
  have hfadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set hsub₀) (hf.mono_set hsub₁)
  have hgadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.mono_set hsub₂) (hg.mono_set hsub₃)
  have hdiff := intervalIntegral.integral_sub (hf.mono_set hsub₁) (hg.mono_set hsub₂)
  have he : (∫ z in l₀..x, f z) - ∫ z in l₁..y, g z =
      (∫ z in l₀..l₁, f z) + (∫ z in l₁..x, f z - g z) - ∫ z in x..y, g z := by
    linarith
  rw [he]
  calc
    _ ≤ |∫ z in l₀..l₁, f z| + |∫ z in l₁..x, f z - g z| + |∫ z in x..y, g z| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (inner_integral_bound hlo hleft)
      (inner_integral_bound hover hmid)) (inner_integral_bound hxy hright)

end AcExtensionPrinciple

end
