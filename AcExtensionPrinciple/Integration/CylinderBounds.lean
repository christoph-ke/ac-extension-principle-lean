module

public import AcExtensionPrinciple.Cylinder.Energy
public import AcExtensionPrinciple.ScalarBound.Uniform

/-!
# The uniform cylinder energy bound

Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 684–707.
The scalar and mass-gap estimates discharge the cylinder upper-bound premises.
The trace calculus and balance are proved by `StandingFull.lemma24` in
`Integration/CylinderStatements.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The uniform upper bound in Lemma 2.4 under standing assumptions alone,
with its constant chosen before radius and cylinder. Paper `e1a0fd5`,
`eq:boundary-energy-comparison`, lines 684–688 and 707. -/
theorem cylinder_energy_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → ∀ v : ℝ → ℝ, ∀ u : ℝ,
      (u, v u) ∈ pastTriangle ui → u < v u → S.r u (v u) = b →
      cylinderEnergy S b v u ≤ C * b := by
  obtain ⟨M, hM⟩ := h.uniform_scalar_bound
  have hM0 : 0 ≤ M := by
    have hb := hM (ui, ui) ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    exact (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).trans hb
  apply cylinder_energy_upper_of_geometric_scalar
    (mul_pos h.initialGap_pos (Real.exp_pos _)) hM0 (fun _ hp => h.mass_gap_lower hp)
  intro p hp _huv
  have hb := hM p hp
  have ht := abs_sub (S.dvpsi p.1 p.2 / S.lam p.1 p.2) (S.phi p.1 p.2)
  linarith [abs_nonneg (S.theta p.1 p.2 / S.lam p.1 p.2)]

end AcExtensionPrinciple.StandingFull

end
