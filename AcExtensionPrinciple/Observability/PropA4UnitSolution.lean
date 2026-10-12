module

public import AcExtensionPrinciple.Observability.PropA4Operator

/-!
# The concrete positive unit solution on the exterior domain

Paper `e1a0fd5`, lines 1753–1759. The Neumann inverse of the actual
chart operator produces the continuous function `W`, with `1 ≤ W ≤ 2`
and the exact integral equation.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set
open scoped Topology BoundedContinuousFunction

/-- The bounded continuous unit solution of the actual exterior operator.
Paper `e1a0fd5`, lines 1753–1755. -/
@[expose] noncomputable def exteriorUnitFunction {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    exteriorDomain h P →ᵇ ℝ :=
  observationResolvent (weightedVolterraOperator h hP hmass (by norm_num : (0 : ℝ) < 1))
    (BoundedContinuousFunction.const (exteriorDomain h P) 1)

/-- The unit solution as a function of the chart coordinates. Values
outside the exterior domain are unused. Paper `e1a0fd5`, lines 1753–1759. -/
@[expose] noncomputable def exteriorUnitSolution {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) : ℝ × ℝ → ℝ :=
  weightedExteriorLift h P 0 (exteriorUnitFunction h hP hmass)

/-- On its domain, the coordinate function equals the bounded continuous
unit function. Paper `e1a0fd5`, lines 1753–1759. -/
theorem exteriorUnitSolution_eq {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    exteriorUnitSolution h hP hmass p = exteriorUnitFunction h hP hmass ⟨p, hp⟩ := by
  simp [exteriorUnitSolution, weightedExteriorLift_eq h _ hp]

/-- The unit solution is continuous on the invariant exterior domain.
Paper `e1a0fd5`, lines 1753–1759. -/
theorem exteriorUnitSolution_continuous {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    ContinuousOn (exteriorUnitSolution h hP hmass) (exteriorDomain h P) :=
  weightedExteriorLift_continuous h hP _

/-- Positivity and the concrete operator norm imply the exact printed
bounds on `W`. Paper `e1a0fd5`, line 1755. -/
theorem exteriorUnitSolution_bounds {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    1 ≤ exteriorUnitSolution h hP hmass p ∧ exteriorUnitSolution h hP hmass p ≤ 2 := by
  rw [exteriorUnitSolution_eq h hP hmass hp]
  apply observation_unit_solution_bounds
  · exact (weightedVolterraOperator_norm_le h hP hmass (by norm_num : (0 : ℝ) < 1)).trans
      (by norm_num)
  · intro f hf p
    exact weightedVolterraOperator_positive h hP hmass (by norm_num) f hf p

/-- The unit solution satisfies `W = 1 + 𝒦W` for the concrete chart
integral operator. Paper `e1a0fd5`, lines 1753–1759. -/
theorem exteriorUnitSolution_equation {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    exteriorUnitSolution h hP hmass p = 1 +
      triangleVolterra (fun p => chartPotential S p.1 p.2)
        (exteriorUnitSolution h hP hmass) p.1 p.2 := by
  let A := weightedVolterraOperator h hP hmass (by norm_num : (0 : ℝ) < 1)
  let e := BoundedContinuousFunction.const (exteriorDomain h P) (1 : ℝ)
  have hi := (weightedVolterraOperator_inverse h hP hmass
    (by norm_num : (0 : ℝ) < 1) (by norm_num)).1
  have he := congrArg (fun B : (exteriorDomain h P →ᵇ ℝ) →L[ℝ]
    (exteriorDomain h P →ᵇ ℝ) => B e ⟨p, hp⟩) hi
  change (exteriorUnitFunction h hP hmass - A (exteriorUnitFunction h hP hmass)) ⟨p, hp⟩ =
    1 at he
  simp only [BoundedContinuousFunction.sub_apply] at he
  have ha : A (exteriorUnitFunction h hP hmass) ⟨p, hp⟩ =
      triangleVolterra (fun p => chartPotential S p.1 p.2)
        (exteriorUnitSolution h hP hmass) p.1 p.2 := by
    simp [A, weightedVolterraOperator_apply, weightedVolterraValue, exteriorUnitSolution]
  rw [ha, ← exteriorUnitSolution_eq h hP hmass hp] at he
  linarith

end PropA4
end AcExtensionPrinciple

end
