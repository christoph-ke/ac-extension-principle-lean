module

public import AcExtensionPrinciple.ScalarBound.UniformAmplitude
public import AcExtensionPrinciple.ScalarBound.AxisTraces
public import AcExtensionPrinciple.GeometricBounds.IncomingFlux

/-!
# Lemma 2.1: uniform scalar bounds

Paper commit `e1a0fd5`, `equations.tex`
lines 374–535, `lem:uniform-scalar-bound`, `eq:uniform-scalar-bound`.
The geometric helper premises are discharged by Lemma 1.1. The final
theorem uses the raw fields throughout the past triangle: the regular-axis
value identities make the trace representatives agree with them there.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The amplitude estimate with precisely the G0, G2 gap and G6
conclusions from Lemma 1.1. Paper `e1a0fd5`, lines 428–524,
`eq:scalar-bound-mass-contradiction`. -/
theorem exists_theta_bound_of_geometric
    (hci : 0 < initialGap ui S)
    (hgap : ∀ p ∈ pastTriangle ui,
      initialGap ui S * Real.exp (-Bstar ui S) ≤ 1 - S.mu p.1 p.2)
    (hflux : ∀ v ∈ Ioc ui 0,
      (∫⁻ u in Ioo ui v, ENNReal.ofReal (S.r u v / (-S.nu u v) * S.duphi u v ^ 2)) ≤
        ENNReal.ofReal (Bstar ui S + Real.log (1 / initialGap ui S))) :
    ∃ T : ℝ, ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T := by
  apply h.exists_theta_bound_of_flux_and_gap (mul_pos hci (Real.exp_pos _))
    (K := max 0 (Bstar ui S + Real.log (1 / initialGap ui S))) (le_max_left _ _) hgap
  intro v hv
  exact (hflux v hv).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- Lemma 2.1 off the axis, including v = 0, taking only the
Lemma 1.1 conclusions. Paper `e1a0fd5`, `lem:uniform-scalar-bound`,
`eq:uniform-scalar-bound`, lines 374–534. -/
theorem uniform_scalar_bound_offAxis_of_geometric
    (hci : 0 < initialGap ui S)
    (hgap : ∀ p ∈ pastTriangle ui,
      initialGap ui S * Real.exp (-Bstar ui S) ≤ 1 - S.mu p.1 p.2)
    (hflux : ∀ v ∈ Ioc ui 0,
      (∫⁻ u in Ioo ui v, ENNReal.ofReal (S.r u v / (-S.nu u v) * S.duphi u v ^ 2)) ≤
        ENNReal.ofReal (Bstar ui S + Real.log (1 / initialGap ui S))) :
    ∃ C : ℝ, ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ C := by
  obtain ⟨T, hT⟩ := h.exists_theta_bound_of_geometric hci hgap hflux
  obtain ⟨A, _, hA⟩ := h.exists_initial_scalar_bound
  exact ⟨2 * (A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S))),
    fun p hp huv => h.scalar_sum_le_of_theta_bound (fun s hs => (hA s hs).1) hT hp huv⟩

/-- Lemma 2.1 for the raw fields throughout the past triangle, using
the regular-axis value identities. This takes exactly the G0/G2/G6
conclusions. Paper `e1a0fd5`, `eq:uniform-scalar-bound`, lines 524–535,
`eq:regular-axis-scalar-traces`. -/
theorem uniform_scalar_bound_of_geometric
    (hci : 0 < initialGap ui S)
    (hgap : ∀ p ∈ pastTriangle ui,
      initialGap ui S * Real.exp (-Bstar ui S) ≤ 1 - S.mu p.1 p.2)
    (hflux : ∀ v ∈ Ioc ui 0,
      (∫⁻ u in Ioo ui v, ENNReal.ofReal (S.r u v / (-S.nu u v) * S.duphi u v ^ 2)) ≤
        ENNReal.ofReal (Bstar ui S + Real.log (1 / initialGap ui S))) :
    ∃ C : ℝ, ∀ p ∈ pastTriangle ui,
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ C := by
  obtain ⟨T, hT⟩ := h.exists_theta_bound_of_geometric hci hgap hflux
  obtain ⟨A, _, hA⟩ := h.exists_initial_scalar_bound
  exact ⟨2 * (A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S))),
    h.scalar_sum_on_triangle_le_of_theta_bound (fun s hs => (hA s hs).1) hT⟩

/-- Uniform outgoing scalar amplitude under the standing assumptions,
with all Lemma 1.1 premises discharged. Paper `e1a0fd5`,
`lem:uniform-scalar-bound`, lines 428–524. -/
theorem exists_theta_bound :
    ∃ T : ℝ, ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T :=
  h.exists_theta_bound_of_geometric h.initialGap_pos
    (fun _ hp => h.mass_gap_lower hp) (fun _ hv => h.incoming_flux_le hv)

/-- Lemma 2.1 off the axis, including the terminal ray, under the
standing assumptions alone. Paper `e1a0fd5`, `lem:uniform-scalar-bound`,
`eq:uniform-scalar-bound`, lines 374–534. -/
theorem uniform_scalar_bound_offAxis :
    ∃ C : ℝ, ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ C :=
  h.uniform_scalar_bound_offAxis_of_geometric h.initialGap_pos
    (fun _ hp => h.mass_gap_lower hp) (fun _ hv => h.incoming_flux_le hv)

/-- Lemma 2.1 for the raw fields throughout the past triangle, including
the axis and terminal ray, under the standing assumptions alone.
Paper `e1a0fd5`, `lem:uniform-scalar-bound`, `eq:uniform-scalar-bound`,
lines 374–535 and `eq:regular-axis-scalar-traces`. -/
theorem uniform_scalar_bound :
    ∃ C : ℝ, ∀ p ∈ pastTriangle ui,
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ C :=
  h.uniform_scalar_bound_of_geometric h.initialGap_pos
    (fun _ hp => h.mass_gap_lower hp) (fun _ hv => h.incoming_flux_le hv)

end StandingFull

end AcExtensionPrinciple

end
