module

public import AcExtensionPrinciple.Observability.PropA4InnerChart
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Required re-normalization of a late inner cylinder

Paper `e1a0fd5`, `eq:observability-inner-boundary-measure` and
`eq:observability-inner-boundary-lower-bound`, lines 1877–1904.
This is the explicit `InnerChartStatement` interface. Its
premises are supplied by the exterior mass bound, the retained inner mass,
and the final interval-fit choice. The construction proving this interface is given in
`innerChartStatement`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- An inner chart with the same `K`, exact boundary-energy transport,
and the differentiable increasing inner-cylinder trace needed to estimate
that energy in outer time. The interval starts at `s₀`; its outer duration
is at most twice its normalized duration. The initial mass ratio is the
one at the corresponding outer point. Paper `e1a0fd5`, lines 1877–1904. -/
@[expose] def InnerChartStatement (K : ℝ) : Prop :=
  ∀ (b T : ℝ) (S : SSFields) (h : NormalizedChartData b T K S)
    (P a ε s₀ : ℝ),
    0 < P →
    (∀ s t, (s, t) ∈ chartCylinder h.g T → S.m s t ≤ P) →
    32 * P ≤ a → a < b → 0 < ε → ε < 1 →
    (K + 2) * b ≤ s₀ → s₀ + 2 * (positiveMassDuration K ε * a) ≤ T →
    ∃ (c : ℝ) (tₐ : ℝ → ℝ) (inner : SSFields),
      s₀ ≤ c ∧ c ≤ s₀ + 2 * (positiveMassDuration K ε * a) ∧
      (∀ s ∈ Icc s₀ c, (s, tₐ s) ∈ chartCylinder h.g T ∧ S.r s (tₐ s) = a) ∧
      ContinuousOn tₐ (Icc s₀ c) ∧ StrictMonoOn tₐ (Icc s₀ c) ∧
      (∀ s ∈ Icc s₀ c,
        HasDerivWithinAt tₐ ((-S.nu s (tₐ s)) / S.lam s (tₐ s)) (Icc s₀ c) s) ∧
      Nonempty (NormalizedChartData a (positiveMassDuration K ε * a) K inner) ∧
      inner.mu 0 0 = S.mu s₀ (tₐ s₀) ∧
      IntervalIntegrable (fun s => innerBoundaryDensity S s (tₐ s)) volume s₀ c ∧
      chartScalarEnergy inner (positiveMassDuration K ε * a) =
        ∫ s in s₀..c, innerBoundaryDensity S s (tₐ s)

end PropA4
end AcExtensionPrinciple

end
