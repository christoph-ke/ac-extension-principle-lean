module

public import AcExtensionPrinciple.Observability.LemmaA2Energy

/-!
# Lemma A.2: the Volterra identity from characteristic primitives

Paper `e1a0fd5`, `eq:observability-volterra`, lines 1504–1511, 1520–1522.
The proof integrates the difference between a characteristic scalar trace
and the AC boundary trace, using the outgoing mixed equation.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Equality of integrands on a containing triangle preserves the Volterra
operator. Paper `e1a0fd5`, `equations.tex` lines 1520–1530. -/
theorem chart_triangleVolterra_congr {P ψ Q χ : ℝ × ℝ → ℝ} {a c s t : ℝ}
    (hat : a ≤ t) (hts : t ≤ s) (hsc : s ≤ c)
    (heq : ∀ q ∈ chartTriangle a c, P q * ψ q = Q q * χ q) :
    triangleVolterra P ψ s t = triangleVolterra Q χ s t := by
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [uIcc_of_le hts] at hσ
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hσ.1] at hz
  exact heq (σ, z) ⟨hat.trans hz.1, hz.2, hσ.2.trans hsc⟩

/-- Multiplication of the amplitude by a constant commutes with the linear
Volterra operator. Paper `e1a0fd5`, sign change at lines 1524–1530. -/
theorem chart_triangleVolterra_const_mul (P ψ : ℝ × ℝ → ℝ) (ε s t : ℝ) :
    triangleVolterra P (fun q => ε * ψ q) s t = ε * triangleVolterra P ψ s t := by
  have he (q : ℝ × ℝ) : P q * (ε * ψ q) = ε * (P q * ψ q) := by ring
  simp_rw [triangleVolterra, he, intervalIntegral.integral_const_mul]

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The positive potential is continuous on positive-radius subdomains.
Paper `e1a0fd5`, `eq:observability-chart-equations`, lines 1490–1492, 1522. -/
theorem continuous_potential_on {C : Set (ℝ × ℝ)}
    (hC : C ⊆ chartInterior (chartCylinder h.g T) S) :
    ContinuousOn (fun q => chartPotential S q.1 q.2) C := by
  obtain ⟨hμ, hn, hl, _⟩ := h.geometry_continuous_on hC
  have hr := h.continuous_r.mono (fun q hq => (hC hq).1)
  exact (((hμ.mul hn).mul hl).div ((continuousOn_const.sub hμ).mul (hr.pow 2))
    (fun q hq => mul_ne_zero (h.gap_pos (hC hq).1).ne' (pow_ne_zero _ (hC hq).2.ne'))).neg

/-- The scalar amplitude is continuous on the solid chart, including the axis.
Paper `e1a0fd5`, `equations.tex` lines 1522, 1530. -/
theorem continuous_psi : ContinuousOn (fun q => chartPsi S q.1 q.2) (chartCylinder h.g T) :=
  h.continuous_r.mul h.continuous_phi

/-- Every integration point remains above the axis. Paper `e1a0fd5`,
`equations.tex` line 1520 and `eq:observability-volterra`. -/
theorem volterra_triangle_subset {s t : ℝ} (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    chartTriangle t s ⊆ chartInterior (chartCylinder h.g T) S := by
  have hgt : h.g s < t := by
    rcases hq.1.2.2.1.eq_or_lt with he | he
    · have hz := (h.axis_values s ⟨hq.1.1, hq.1.2.1⟩).1
      rw [he] at hz
      linarith [hq.2]
    · exact he
  exact h.triangle_subset ht hq.1.2.2.2 hq.1.2.1 hgt

/-- Volterra's identity is a consequence of the chart integral equations.
Paper `e1a0fd5`, `eq:observability-volterra`, lines 1504–1511, 1520–1522. -/
theorem volterra {s t : ℝ} (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    chartPsi S s t = chartPsi S s s - (∫ σ in t..s, S.dvpsi σ σ) +
      triangleVolterra (fun q => chartPotential S q.1 q.2)
        (fun q => chartPsi S q.1 q.2) s t := by
  have hts := hq.1.2.2.2
  have hsT := hq.1.2.1
  have htri := h.volterra_triangle_subset ht hq
  have hprod : ContinuousOn (fun q => chartPotential S q.1 q.2 * chartPsi S q.1 q.2)
      (chartTriangle t s) := (h.continuous_potential_on htri).mul
    (h.continuous_psi.mono (fun q hq => (htri hq).1))
  obtain ⟨Q, hQ, hQeq⟩ := chartTriangle_continuous_extension hprod
  let J : ℝ → ℝ := fun σ => ∫ z in t..σ, Q (σ, z)
  have hJ : Continuous J :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun σ z => Q (σ, z)) hQ continuous_id
  have hJeq (σ : ℝ) (hσ : σ ∈ Icc t s) :
      J σ = ∫ z in t..σ, chartPotential S σ z * chartPsi S σ z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hσ.1] at hz
    exact hQeq (σ, z) ⟨hz.1, hz.2, hσ.2⟩
  have hsub {σ : ℝ} (hσ : σ ∈ Icc t s) :
      inSeg t t σ ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_in_subset le_rfl le_rfl hσ.2).trans htri
  have hcharAC := intervalPrimitive_ac hts (fun σ hσ =>
    h.equations.psi_s t t σ hσ.1 (fun q hq => (hsub hσ hq).1))
  have hcharDer := intervalPrimitive_ae_hasDerivAt hts (fun σ hσ =>
    h.equations.psi_s t t σ hσ.1 (fun q hq => (hsub hσ hq).1))
  have hboundaryAC := h.boundary_traces_ac.1.mono (by
    rw [uIcc_of_le hts, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc ht hsT)
  have hF : AbsolutelyContinuousOnInterval
      (fun σ => chartPsi S σ t - chartPsi S σ σ) t s := hcharAC.sub hboundaryAC
  have hder : ∀ᵐ σ ∂volume, σ ∈ Ioo t s →
      HasDerivAt (fun σ => chartPsi S σ t - chartPsi S σ σ)
        (-S.dvpsi σ σ + J σ) σ := by
    filter_upwards [hcharDer, h.boundary_psi_ae_hasDerivAt] with σ hchar hboundary
    intro hσ
    have hσI : σ ∈ Icc t s := ⟨hσ.1.le, hσ.2.le⟩
    have hσT : σ ∈ Icc 0 T := ⟨ht.trans hσ.1.le, hσ.2.le.trans hsT⟩
    have hi := (h.wave_t_integral hσ.1.le
      ((chartTriangle_out_subset le_rfl le_rfl hσ.2.le).trans htri)).2
    have hh : S.dupsi σ σ - S.dupsi σ t = -J σ := by
      rw [hJeq σ hσI]
      simpa only [neg_mul, intervalIntegral.integral_neg] using hi
    have hd := (hchar hσ).sub (hboundary hσT)
    change HasDerivAt (fun σ => chartPsi S σ t - chartPsi S σ σ)
      (S.dupsi σ t - (S.dupsi σ σ + S.dvpsi σ σ)) σ at hd
    exact hd.congr_deriv (by linarith)
  have hi := (ac_integral_eq_sub hts hF hder).2
  have hxi : IntervalIntegrable (fun σ => S.dvpsi σ σ) volume t s :=
    h.boundary_dvpsi_integrable.mono_set (by
      rw [uIcc_of_le hts, uIcc_of_le h.T_nonneg]
      exact Icc_subset_Icc ht hsT)
  change chartPsi S s t - chartPsi S s s - (chartPsi S t t - chartPsi S t t) =
    ∫ σ in t..s, -S.dvpsi σ σ + J σ at hi
  rw [intervalIntegral.integral_add (f := fun σ => -S.dvpsi σ σ) hxi.neg
      (hJ.intervalIntegrable t s),
    intervalIntegral.integral_neg] at hi
  have hJint : (∫ σ in t..s, J σ) =
      triangleVolterra (fun q => chartPotential S q.1 q.2)
        (fun q => chartPsi S q.1 q.2) s t := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hts] at hσ
    exact hJeq σ hσ
  rw [hJint] at hi
  linarith

end NormalizedChartData

end AcExtensionPrinciple

end
