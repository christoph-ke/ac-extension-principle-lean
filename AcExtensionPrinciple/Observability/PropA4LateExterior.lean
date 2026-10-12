module

public import AcExtensionPrinciple.Observability.PropA4ExteriorDomain

/-!
# Every late exterior annulus lies in the invariant operator domain

Paper `e1a0fd5`, lines 1820–1822. The incoming ray with entry label
`Kb` has already crossed the exterior cutoff after another `2b` units
of boundary time. Radius monotonicity then covers the entire annulus.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set

/-- On every slice after `(K+2)b`, every point above the exterior cutoff
belongs to the operator domain. Paper `e1a0fd5`, lines 1820–1822. -/
theorem late_exterior_mem {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ chartCylinder h.g T) (hcut : 32 * P ≤ S.r s t)
    (hlate : (K + 2) * b ≤ s) : (s, t) ∈ exteriorDomain h P := by
  refine ⟨hp, ?_, hcut⟩
  have hKb0 : 0 ≤ K * b := mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le
  have hKbs : K * b ≤ s := by nlinarith only [hlate, h.b_pos]
  by_contra hn
  have htKb : t ≤ K * b := (lt_of_not_ge hn).le
  have hrad := h.radius_t_mono htKb (h.out_subset ⟨hp.1, hp.2.1⟩ hp.2.2.1 hKbs)
  have hcutKb : 32 * P ≤ S.r s (K * b) := hcut.trans hrad
  have hpKb : (s, K * b) ∈ chartInterior (chartCylinder h.g T) S :=
    ⟨⟨hp.1, hp.2.1, hp.2.2.1.trans htKb, hKbs⟩, by linarith only [hP, hcutKb]⟩
  have hsep := incoming_radius_separation h hP hKb0 hpKb hcutKb hmass ⟨le_rfl, hKbs⟩
  have hb := (h.boundary_gauge (K * b) ⟨hKb0, hKbs.trans hp.2.1⟩).1
  rw [hb] at hsep
  nlinarith only [hsep, hpKb.2, hlate]

end PropA4
end AcExtensionPrinciple

end
