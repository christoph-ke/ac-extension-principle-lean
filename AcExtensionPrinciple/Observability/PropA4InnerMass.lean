module

public import AcExtensionPrinciple.Observability.PropA4ExteriorMass

/-!
# Retained mass at the late inner cylinder

Paper `e1a0fd5`, `eq:observability-inner-mass-lower-bound`, lines 1855–1865.
The shifted energy controls the outer mass after subtracting the boundary
scalar amplitude. The exterior mass estimate then transfers this to `a=LP`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The shifted energy exceeds boundary mass by at most its scalar part
and the K-gap factor. Paper `e1a0fd5`, lines 1855–1860. -/
theorem shifted_energy_mass_upper {b T K s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T) :
    chartShiftedEnergy b S s ≤ chartPsi S s s ^ 2 / (2 * b) + K * S.m s s := by
  have hb := h.b_pos
  have hq := h.boundary_mem hs
  have hmu := (h.signs s s hq).2.2
  have hgap := h.gap s s hq
  rw [SSFields.mu, (h.boundary_gauge s hs).1] at hmu hgap
  have hlog := neg_log_gap_le h.K_ge_one hmu hgap
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ b / 2 by positivity)
  have heq : b / 2 * (K * massRatio b (S.m s s)) = K * S.m s s := by
    unfold massRatio
    field_simp [h.b_pos.ne']
  rw [heq] at hh
  rw [chartShiftedEnergy_eq S s h.b_pos]
  linarith only [hh]

/-- The boundary scalar part has size `C(K)P²/b + KE` on late slices.
Paper `e1a0fd5`, lines 1855–1858. -/
theorem boundary_scalar_mass_bound {b T K P s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) :
    chartPsi S s s ^ 2 / (2 * b) ≤
      amplitudeMassSquareConstant K * P ^ 2 / b + K * chartScalarEnergy S T := by
  have hb := h.b_pos
  have hA := amplitude_sq_mass_bound h hP hT hmass hs hlate hfit hE
  have hB := boundary_primitive_sq h (by nlinarith only [hlate, h.b_pos]) (h.boundary_mem hs)
  rw [(h.boundary_gauge s hs).1] at hB
  change exteriorBoundaryPrimitive h (s, s) ^ 2 ≤ K * b * chartScalarEnergy S T at hB
  have heq : chartPsi S s s = amplitude h s + exteriorBoundaryPrimitive h (s, s) := by
    unfold amplitude exteriorBoundaryPrimitive
    ring
  rw [div_le_iff₀ (show 0 < 2 * b by positivity)]
  have hbound : chartPsi S s s ^ 2 ≤ 2 * (amplitude h s ^ 2 +
      exteriorBoundaryPrimitive h (s, s) ^ 2) := by
    rw [heq]
    nlinarith [sq_nonneg (amplitude h s - exteriorBoundaryPrimitive h (s, s))]
  have he : (amplitudeMassSquareConstant K * P ^ 2 / b + K * chartScalarEnergy S T) *
      (2 * b) = 2 * (amplitudeMassSquareConstant K * P ^ 2 + K * b * chartScalarEnergy S T) := by
    field_simp [h.b_pos.ne']
  rw [he]
  linarith only [hbound, hA, hB]

/-- Explicit K-only coefficient in the retained inner mass estimate.
Paper `e1a0fd5`, lines 1859–1865. -/
@[expose] noncomputable def innerMassErrorConstant (K : ℝ) : ℝ :=
  exteriorMassConstant K + (K + 1) / K + amplitudeMassSquareConstant K / K

/-- Exterior-to-inner mass transfer with exactly the three printed errors.
The retained-energy premise is supplied by `total_mass_bound` under small
observation; all analytic estimates are discharged here. Paper `e1a0fd5`,
`eq:observability-inner-mass-lower-bound`, lines 1859–1865. -/
theorem inner_mass_lower_bound {b T K P s L u : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) (hL : 64 ≤ L)
    (hu : h.g s ≤ u) (hus : u ≤ s) (hru : S.r s u = L * P)
    (hretain : S.m 0 0 - chartScalarEnergy S T ≤ chartShiftedEnergy b S s) :
    S.m 0 0 / K - innerMassErrorConstant K *
      (chartScalarEnergy S T + P / L + P ^ 2 / b) ≤ S.m s u := by
  have hb := h.b_pos
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hL0 : 0 < L := by linarith only [hL]
  have hE0 := h.scalar_energy_nonneg
  have hA0 : 0 ≤ amplitudeMassSquareConstant K := by
    unfold amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  have hC0 : 0 ≤ exteriorMassConstant K := by unfold exteriorMassConstant; positivity
  have hB := boundary_scalar_mass_bound h hP hT hmass hs hlate hfit hE
  have hF := shifted_energy_mass_upper h hs
  have hM : S.m 0 0 ≤ K * S.m s s + (K + 1) * chartScalarEnergy S T +
      amplitudeMassSquareConstant K * P ^ 2 / b := by linarith only [hretain, hF, hB]
  have hMd := div_le_div_of_nonneg_right hM hK.le
  have heq : (K * S.m s s + (K + 1) * chartScalarEnergy S T +
      amplitudeMassSquareConstant K * P ^ 2 / b) / K =
      S.m s s + (K + 1) / K * chartScalarEnergy S T +
        amplitudeMassSquareConstant K / K * (P ^ 2 / b) := by
    field_simp [hK.ne']
  rw [heq] at hMd
  have hExt := exterior_mass_bound_scaled h hP hT hmass hs hlate hfit hE hL hu hus hru
  have hErr : exteriorMassConstant K * (P / L + chartScalarEnergy S T) +
      (K + 1) / K * chartScalarEnergy S T + amplitudeMassSquareConstant K / K * (P ^ 2 / b) ≤
      innerMassErrorConstant K * (chartScalarEnergy S T + P / L + P ^ 2 / b) := by
    unfold innerMassErrorConstant
    nlinarith [mul_nonneg hC0 (show 0 ≤ P ^ 2 / b by positivity),
      mul_nonneg (show 0 ≤ (K + 1) / K by positivity) (show 0 ≤ P / L by positivity),
      mul_nonneg (show 0 ≤ (K + 1) / K by positivity) (show 0 ≤ P ^ 2 / b by positivity),
      mul_nonneg (show 0 ≤ amplitudeMassSquareConstant K / K by positivity) hE0,
      mul_nonneg (show 0 ≤ amplitudeMassSquareConstant K / K by positivity)
        (show 0 ≤ P / L by positivity)]
  linarith only [hMd, hExt, hErr]

end PropA4
end AcExtensionPrinciple

end
