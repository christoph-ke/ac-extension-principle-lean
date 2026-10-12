module

public import AcExtensionPrinciple.Cylinder.ClassBoundary
public import AcExtensionPrinciple.ScalarBound.Uniform

/-!
# Complete class-level boundary energy identity

Paper statements, paper `e1a0fd5`, `lem:boundary-energy-identity`, `equations.tex` lines 681–737.
Lemma 2.1 supplies the uniform amplitude bound; all conclusions now follow from the standing
assumptions on every regular cylinder interval.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The upper energy comparison is uniform before choosing the cylinder or its interval.
Lemma 2.1 discharges the last scalar premise of the comparison helper.
Paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688, 707. -/
theorem cylinder_energy_upper_regular :
    ∃ C : ℝ, 0 < C ∧ ∀ b a0 a1 : ℝ, 0 < b →
      RegularCylinderInterval ui S b a0 a1 → ∀ u ∈ Icc a0 a1,
        cylinderEnergy S b (cylinderV h b) u ≤ C * b := by
  obtain ⟨M, hM⟩ := h.uniform_scalar_bound_offAxis
  apply h.cylinder_energy_upper_of_scalar_bound (M := max M 0) (le_max_right _ _)
  intro p hp
  calc
    |S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2| ≤
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (S.dvpsi p.1 p.2 / S.lam p.1 p.2) (-S.phi p.1 p.2)
    _ ≤ |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| := by
      linarith [abs_nonneg (S.theta p.1 p.2 / S.lam p.1 p.2)]
    _ ≤ M := hM p (cylinderScalarRegion_subset ui hp) hp.2.1
    _ ≤ max M 0 := le_max_left _ _

/-- Lemma 2.4: AC traces, all energy comparisons, exact integral balance and √E stability.
The constant depends on the standing solution and precedes every cylinder variable.
Initial-ray and terminal-ray endpoints and zero-length intervals are included.
Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 681–737. -/
theorem cylinder_boundary_energy_identity :
    ∃ C : ℝ, 0 < C ∧ ∀ b a0 a1 : ℝ, 0 < b →
      RegularCylinderInterval ui S b a0 a1 →
      (AbsolutelyContinuousOnInterval (fun u => S.m u (cylinderV h b u)) a0 a1 ∧
        AbsolutelyContinuousOnInterval (fun u => S.phi u (cylinderV h b u)) a0 a1 ∧
        AbsolutelyContinuousOnInterval (cylinderP S (cylinderV h b)) a0 a1 ∧
        AbsolutelyContinuousOnInterval (cylinderEnergy S b (cylinderV h b)) a0 a1) ∧
      (∀ u ∈ Icc a0 a1,
        S.m u (cylinderV h b u) ≤ cylinderEnergy S b (cylinderV h b) u ∧
        (b / 2) * ((b / S.lam u (cylinderV h b u)) *
          S.dvphi u (cylinderV h b u)) ^ 2 ≤ cylinderEnergy S b (cylinderV h b) u ∧
        cylinderEnergy S b (cylinderV h b) u ≤ C * b) ∧
      (cylinderEnergy S b (cylinderV h b) a1 - cylinderEnergy S b (cylinderV h b) a0 +
        (∫ u in a0..a1, (b ^ 2 / 2) *
          (deriv (fun s => S.phi s (cylinderV h b s)) u) ^ 2 /
            (-S.nu u (cylinderV h b u))) =
        ∫ u in a0..a1, b * (cylinderP S (cylinderV h b) u - S.phi u (cylinderV h b u)) *
          deriv (cylinderP S (cylinderV h b)) u) ∧
      Real.sqrt (cylinderEnergy S b (cylinderV h b) a1) ≤
        Real.sqrt (cylinderEnergy S b (cylinderV h b) a0) + Real.sqrt (b / 2) *
          (eVariationOn (cylinderP S (cylinderV h b)) (Icc a0 a1)).toReal := by
  obtain ⟨C, hC, hbound⟩ := h.cylinder_energy_upper_regular
  refine ⟨C, hC, ?_⟩
  intro b a0 a1 hb hI
  refine ⟨h.cylinder_traces_ac_regular hb hI, ?_,
    h.cylinder_boundary_integral_balance_regular hb hI,
    h.cylinder_boundary_stability_regular hb hI⟩
  intro u hu
  obtain ⟨hm, hA⟩ := h.cylinder_energy_comparison_regular hb hI hu
  exact ⟨hm, hA, hbound b a0 a1 hb hI u hu⟩

end AcExtensionPrinciple.StandingFull

end
