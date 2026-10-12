module

public import AcExtensionPrinciple.Solution.PrimitiveCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Calculus of positive AC functions

Paper `e1a0fd5`, `eq:logarithmic-expansions`
and `eq:raychaudhuri` (lines 87–92). Compact positivity permits composition
with reciprocal and logarithm without a global Lipschitz hypothesis.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Composition of a positive interval-AC function with a function smooth
on the positive half-line. Paper `e1a0fd5`, lines 87–92. -/
theorem positive_ac_comp {f F : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < f x)
    (hF : ContDiffOn ℝ 1 F (Ioi 0)) :
    AbsolutelyContinuousOnInterval (fun x => F (f x)) a b := by
  obtain ⟨x, hx, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc hf.continuousOn
  have hsub : Icc (f x) (f y) ⊆ Ioi 0 := by
    intro z hz
    exact (hpos x hx).trans_le hz.1
  obtain ⟨K, hK⟩ := (hF.mono hsub).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (fun z hz => ⟨hmin hz, hmax hz⟩) hf

/-- Reciprocal preserves AC on a compact positive interval range.
Paper `e1a0fd5`, `eq:normalized-expansions` and `eq:raychaudhuri`. -/
theorem positive_ac_inv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < f x) :
    AbsolutelyContinuousOnInterval (fun x => (f x)⁻¹) a b := by
  apply positive_ac_comp hf hpos
  exact contDiffOn_id.inv (fun x hx => ne_of_gt hx)

/-- Logarithm preserves AC on a compact positive interval range.
Paper `e1a0fd5`, `eq:logarithmic-expansions` and `eq:raychaudhuri`. -/
theorem positive_ac_log {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < f x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (f x)) a b := by
  exact positive_ac_comp hf hpos (Real.contDiffOn_log.mono (fun x hx => ne_of_gt hx))

/-- FTC with an explicitly prescribed a.e. derivative on the open interval.
Paper `e1a0fd5`, lines 87–92, 311–339. -/
theorem ac_integral_eq_sub {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (g x) x) :
    IntervalPrimitive f g a b := by
  have heq : g =ᵐ[volume.restrict (Ioc a b)] deriv f := by
    change ∀ᵐ x ∂volume.restrict (Ioc a b), g x = deriv f x
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hg, show ∀ᵐ x : ℝ ∂volume, x ≠ b by simp [ae_iff]] with x hx hxb
    intro hxI
    exact (hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩).deriv.symm
  have hi := hf.intervalIntegrable_deriv
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi |>.congr heq.symm
  · rw [← hf.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae_restrict
    simpa [uIoc_of_le hab] using heq.symm

end AcExtensionPrinciple

end
