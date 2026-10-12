module

public import AcExtensionPrinciple.Observability.PropA4Statements

/-!
# Differentiated scalar representation

Paper `e1a0fd5`, `eq:observability-differentiated-representation`,
`equations.tex` lines 1783–1789. The identities follow directly from
the characteristic wave primitives, avoiding differentiation of a
two-dimensional integral with merely BV scalar derivatives.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The incoming scalar derivative is its boundary value plus the radial
potential integral. Paper `e1a0fd5`,
`eq:observability-differentiated-representation`, lines 1783–1789. -/
theorem incoming_wave_representation {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    S.dupsi s t = S.dupsi s s + ∫ z in t..s, chartPotential S s z * chartPsi S s z := by
  have htri := h.volterra_triangle_subset ht hq
  have hi := (h.wave_t_integral hq.1.2.2.2
    ((chartTriangle_out_subset le_rfl le_rfl le_rfl).trans htri)).2
  simp only [neg_mul, intervalIntegral.integral_neg] at hi
  linarith

/-- The radial scalar derivative equals the entry value divided by `r_t`
minus the incoming potential integral divided by `r_t`. Paper `e1a0fd5`,
`eq:observability-differentiated-representation`, lines 1783–1789. -/
theorem radial_wave_representation {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    S.dvpsi s t / S.lam s t = S.dvpsi t t / S.lam s t -
      (∫ σ in t..s, chartPotential S σ t * chartPsi S σ t) / S.lam s t := by
  have htri := h.volterra_triangle_subset ht hq
  have hi := (h.wave_s_integral hq.1.2.2.2
    ((chartTriangle_in_subset le_rfl le_rfl le_rfl).trans htri)).2
  simp only [neg_mul, intervalIntegral.integral_neg] at hi
  have heq : S.dvpsi s t = S.dvpsi t t -
      ∫ σ in t..s, chartPotential S σ t * chartPsi S σ t := by linarith
  rw [heq]
  ring

/-- Using the boundary chain rule gives the exact incoming representation
with the actual boundary trace derivative, almost everywhere in s and
simultaneously for every entered point on that slice. Paper `e1a0fd5`,
`eq:observability-differentiated-representation`, lines 1783–1789. -/
theorem incoming_wave_representation_ae {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) :
    ∀ᵐ s, s ∈ Icc 0 T → ∀ t, 0 ≤ t →
      (s, t) ∈ chartInterior (chartCylinder h.g T) S →
        S.dupsi s t = deriv (fun s => chartPsi S s s) s - S.dvpsi s s +
          ∫ z in t..s, chartPotential S s z * chartPsi S s z := by
  filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs
  intro hsI t ht hq
  rw [incoming_wave_representation h ht hq, (hs hsI).deriv]
  ring

end PropA4
end AcExtensionPrinciple

end
