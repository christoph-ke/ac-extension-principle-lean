module

public import AcExtensionPrinciple.Observability.PropA4UnitRadialDerivatives

/-!
# Coercivity of the radial unit-solution weight

Paper `e1a0fd5`, lines 1823–1829 and 1849–1853. The quantity `W/r-W_r`
is bounded below by `1/r` and above by `5/(2r)` on the exterior domain.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- The radial unit weight `W/r-W_r`, expressed through its proved
potential integral. Paper `e1a0fd5`, lines 1823–1829. -/
@[expose] noncomputable def exteriorUnitRadialWeight {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) (s t : ℝ) : ℝ :=
  (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t +
    exteriorUnitSolution h hP hmass (s, t) / S.r s t

/-- The unit weight supplies the paper's lower bound and a uniform upper
bound of the same radius scale. Paper `e1a0fd5`, lines 1823–1829 and 1849–1853. -/
theorem exteriorUnitRadialWeight_bounds {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    1 / S.r s t ≤ exteriorUnitRadialWeight h hP hmass s t ∧
      exteriorUnitRadialWeight h hP hmass s t ≤ (5 / 2) / S.r s t := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hW := exteriorUnitSolution_bounds h hP hmass hp
  have hI := exteriorUnitSolution_radial_integral_bounds h hP hmass hp
  have hsmall : 16 * P * S.r s t ^ (-2 : ℝ) ≤ (1 / 2) / S.r s t := by
    rw [Real.rpow_neg hr.le, Real.rpow_two]
    field_simp
    nlinarith only [hp.2.2, hr]
  unfold exteriorUnitRadialWeight
  constructor
  · have hh := div_le_div_of_nonneg_right hW.1 hr.le
    linarith only [hh, hI.1]
  · have hh := div_le_div_of_nonneg_right hW.2 hr.le
    have hb := hI.2.trans hsmall
    calc
      _ ≤ (1 / 2) / S.r s t + 2 / S.r s t := add_le_add hb hh
      _ = _ := by ring

end PropA4
end AcExtensionPrinciple

end
