module

public import AcExtensionPrinciple.GeometricBounds.RayBounds

/-!
# Extending local absolute continuity to finite-BV endpoints

Paper `e1a0fd5`, `lem:ac-datum-propagation`, `equations.tex` line 601.
Finite BV makes the derivative integrable, and continuity identifies the
endpoint values with the integral representation obtained in the interior.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- A continuous BV function that is AC on all closed interior intervals is
AC on the entire interval. Paper `e1a0fd5`, line 601. -/
theorem ac_of_continuous_bv_of_ac_interior {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hbv : BoundedVariationOn f (Icc a b))
    (hac : ∀ c d, a < c → c ≤ d → d < b → AbsolutelyContinuousOnInterval f c d) :
    AbsolutelyContinuousOnInterval f a b := by
  let c := (a + b) / 2
  have hac0 : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hi : IntervalIntegrable (deriv f) volume a b := by
    apply BoundedVariationOn.intervalIntegrable_deriv
    simpa only [uIcc_of_le hab.le] using hbv
  have hprimitive := hi.absolutelyContinuousOnInterval_intervalIntegral
    (c := c) (by rw [uIcc_of_le hab.le]; exact ⟨hac0.le, hcb.le⟩)
  have hg : AbsolutelyContinuousOnInterval (fun x => f c + ∫ t in c..x, deriv f t) a b :=
    ((LipschitzWith.const (f c)).lipschitzOnWith.absolutelyContinuousOnInterval).add hprimitive
  have he : ∀ x ∈ Ioo a b, f x = f c + ∫ t in c..x, deriv f t := by
    intro x hx
    rcases le_total c x with hcx | hxc
    · have hh := (hac c x hac0 hcx hx.2).integral_deriv_eq_sub
      linarith
    · have hh := (hac x c hx.1 hxc hcb).integral_deriv_eq_sub
      rw [intervalIntegral.integral_symm x c]
      linarith
  have hb : ∀ x ∈ Icc a b, f x - (f c + ∫ t in c..x, deriv f t) = 0 := by
    have hgc : ContinuousOn (fun x => f c + ∫ t in c..x, deriv f t) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hg.continuousOn
    have hh := interval_bounds_of_open hab (hc.sub hgc)
      (L := 0) (U := 0) (fun x hx => by
        change 0 ≤ f x - (f c + ∫ t in c..x, deriv f t) ∧
          f x - (f c + ∫ t in c..x, deriv f t) ≤ 0
        rw [he x hx, sub_self]
        exact ⟨le_rfl, le_rfl⟩)
    intro x hx
    exact le_antisymm (hh x hx).2 (hh x hx).1
  apply hg.congr
  intro x hx
  rw [uIcc_of_le hab.le] at hx
  exact (sub_eq_zero.mp (hb x hx)).symm

end AcExtensionPrinciple

end
