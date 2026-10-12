module

public import AcExtensionPrinciple.Solution.StandingFull
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Calculus for characteristic integral identities

Paper `e1a0fd5`, `equations.tex` lines 66–84
and 222 (ruling Q8). These generic lemmas recover AC and derivatives
from interval primitives; they impose no extra condition on the solution.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- An integral primitive is absolutely continuous. Paper `e1a0fd5`,
lines 66–84 and 222, ruling Q8. -/
theorem intervalPrimitive_ac {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, IntervalPrimitive f g a x) :
    AbsolutelyContinuousOnInterval f a b := by
  have hi := (h b ⟨hab, le_rfl⟩).1
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hac.fun_add hc).congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have he := (h x hx).2
  linarith

/-- An integral primitive has its prescribed derivative almost everywhere
in the open interval. Paper `e1a0fd5`, lines 66–84 and 222, ruling Q8. -/
theorem intervalPrimitive_ae_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, IntervalPrimitive f g a x) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (g x) x := by
  have hi := (h b ⟨hab, le_rfl⟩).1
  filter_upwards [hi.ae_hasDerivAt_integral] with x hx
  intro hxI
  have hd := (hx (by simpa [uIcc_of_le hab] using ⟨hxI.1.le, hxI.2.le⟩) a (by simp)).add_const (f a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hxI.1 hxI.2] with y hy
  have he := (h y hy).2
  linarith

/-- With a continuous integrand the derivative holds at every interior point.
Paper `e1a0fd5`, lines 66–84 and 222, ruling Q8. -/
theorem intervalPrimitive_hasDerivAt {f g : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hg : ContinuousOn g (Icc a b))
    (h : ∀ y ∈ Icc a b, IntervalPrimitive f g a y) : HasDerivAt f (g x) x := by
  have hab := le_trans hx.1.le hx.2.le
  have hi := (h x ⟨hx.1.le, hx.2.le⟩).1
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    ⟨Icc a b, Icc_mem_nhds hx.1 hx.2, hg.aestronglyMeasurable measurableSet_Icc⟩
    (hg.continuousAt (Icc_mem_nhds hx.1 hx.2))).add_const (f a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
  have he := (h y hy).2
  linarith

end AcExtensionPrinciple

end
