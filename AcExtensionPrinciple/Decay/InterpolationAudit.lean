module

public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

/-!
# Audit of the abstract interpolation assumptions

Audit: paper `e1a0fd5`, `equations.tex` lines 618–659,
`eq:ac-interpolation`. The paper supplies a strictly positive mass coefficient
and an AC amplitude. The interpolation estimate requires positivity of
`c₃` and integrability of the squared amplitude; both are explicit helper premises.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- With `r=1`, `A=1`, `m=0`, `ω=0`, `C₁=c₃=0`, `C₂=1`, all the literal interpolation inequalities
with zero mass coefficient hold but no interpolation constant works. Paper `e1a0fd5`,
`equations.tex` lines 618–659; the positive coefficient in the paper comes from `eq:radial-mass` and
`eq:mass-gap-and-nu-bound`. -/
theorem interpolation_requires_positive_mass_coefficient :
    let A : ℝ → ℝ := fun _ ↦ 1
    let m : ℝ → ℝ := fun _ ↦ 0
    (∀ t ∈ Icc (1 / 2 : ℝ) 1,
      |A t| ≤ 1 ∧ |A t - A 1| ≤ 0 * (0 + Real.log (1 / t)) ∧
      0 ≤ m t ∧ m 1 - m t ≥ 0 * (∫ s in t..1, A s ^ 2)) ∧
    ¬∃ C : ℝ, |A 1| ^ 3 ≤ C * (massRatio 1 (m 1) + (0 : ℝ) ^ 3) := by
  norm_num [massRatio]

end AcExtensionPrinciple

end
