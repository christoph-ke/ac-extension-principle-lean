module

public import AcExtensionPrinciple.Observability.LemmaA2Amplitude
public import AcExtensionPrinciple.Observability.ChartGeometry

/-!
# Appendix A, Lemma A.2 in an abstract normalized chart

Paper statement for commit `e1a0fd5`, `equations.tex`
`lem:observability-axis-amplitude`, lines 1447–1531. The coordinate chart
and its inherited regularity are the interface; construction from the
original solution is a separate gauge-invariance task.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- All conclusions of Lemma A.2, with the characteristic integral/a.e.
interpretation of the chart equations. Paper `e1a0fd5`,
`lem:observability-axis-amplitude`, `eq:observability-chart-equations`,
`eq:observability-shifted-balance`, `eq:observability-shifted-stability`,
`eq:observability-volterra`, `eq:observability-axis-amplitude`, lines 1482–1531.
`theta = rφ_t`, `zeta = rφ_s`, and multiplication by `lam = r_t` converts
a radial derivative back to its characteristic derivative. -/
structure LemmaA2Conclusions {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) : Prop where
  potential_nonneg : ∀ s t, (s, t) ∈ chartCylinder h.g T → 0 ≤ chartPotential S s t
  outgoing_equations : ∀ s a c, a ≤ c →
    outSeg s a c ⊆ chartInterior (chartCylinder h.g T) S →
    ∀ᵐ t, t ∈ Ioo a c →
      HasDerivAt (S.m s)
        ((1 - S.mu s t) / 2 * (S.theta s t / S.lam s t) ^ 2 * S.lam s t) t ∧
      HasDerivAt (S.nu s)
        (S.mu s t * S.nu s t / ((1 - S.mu s t) * S.r s t) * S.lam s t) t ∧
      HasDerivAt (S.zeta s) (-S.nu s t * S.dvphi s t) t
  incoming_mass : ∀ t a c, a ≤ c → inSeg t a c ⊆ chartCylinder h.g T →
    ∀ᵐ s, s ∈ Ioo a c → HasDerivAt (fun s => S.m s t)
      ((1 - S.mu s t) / (2 * S.nu s t) * S.zeta s t ^ 2) s
  incoming_wave : ∀ t a c, a ≤ c →
    inSeg t a c ⊆ chartInterior (chartCylinder h.g T) S →
    IntervalPrimitive (fun s => S.dvpsi s t)
      (fun s => -chartPotential S s t * chartPsi S s t) a c
  outgoing_wave : ∀ s a c, a ≤ c →
    outSeg s a c ⊆ chartInterior (chartCylinder h.g T) S →
    IntervalPrimitive (S.dupsi s) (fun t => -chartPotential S s t * chartPsi S s t) a c
  boundary_traces_ac : AbsolutelyContinuousOnInterval (fun s => chartPsi S s s) 0 T ∧
    AbsolutelyContinuousOnInterval (fun s => S.m s s) 0 T
  shifted_balance : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
    deriv (chartShiftedEnergy b S) s = S.dvpsi s s * deriv (fun s => chartPsi S s s) s -
      deriv (fun s => chartPsi S s s) s ^ 2 / 2
  mass_comparison : ∀ s t, (s, t) ∈ chartCylinder h.g T →
    S.m s t ≤ chartShiftedEnergy b S s
  shifted_stability : ∀ s ∈ Icc 0 T,
    chartShiftedEnergy b S 0 - chartScalarEnergy S T ≤ chartShiftedEnergy b S s ∧
      chartShiftedEnergy b S s ≤ chartShiftedEnergy b S 0 + chartScalarEnergy S T / 2
  volterra : ∀ s t, 0 ≤ t → (s, t) ∈ chartInterior (chartCylinder h.g T) S →
    chartPsi S s t = chartPsi S s s - (∫ σ in t..s, S.dvpsi σ σ) +
      triangleVolterra (fun q => chartPotential S q.1 q.2) (fun q => chartPsi S q.1 q.2) s t
  axis_amplitude : K * b ≤ T → |chartPsi S 0 0| ^ 2 ≤ 2 * K * b * chartScalarEnergy S T

/-- Lemma A.2 follows from normalized chart data without assuming boundary
AC, chain rules, the Volterra identity, or its amplitude conclusion. Paper
`e1a0fd5`, `lem:observability-axis-amplitude`, `equations.tex` lines 1447–1531. -/
theorem lemmaA2 {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S) :
    LemmaA2Conclusions h where
  potential_nonneg := fun _ _ hq => h.potential_nonneg hq
  outgoing_equations := fun _ _ _ hac hseg => h.equations_t_ae hac hseg
  incoming_mass := fun _ _ _ hac hseg => h.mass_s_ae hac hseg
  incoming_wave := fun _ _ _ hac hseg => h.wave_s_integral hac hseg
  outgoing_wave := fun _ _ _ hac hseg => h.wave_t_integral hac hseg
  boundary_traces_ac := h.boundary_traces_ac
  shifted_balance := h.shifted_balance_ae
  mass_comparison := fun _ _ hq => h.mass_le_shiftedEnergy hq
  shifted_stability := fun _ hs => h.shifted_stability hs
  volterra := fun _ _ ht hq => h.volterra ht hq
  axis_amplitude := h.axis_amplitude

end AcExtensionPrinciple

end
