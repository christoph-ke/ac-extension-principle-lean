module

public import AcExtensionPrinciple.Observability.PropA4InnerTraceEnergy
public import AcExtensionPrinciple.Observability.PropA4InnerDerivativeErrors

/-!
# Integrated upper bound for the inner observation

Paper `e1a0fd5`, `eq:observability-inner-boundary-upper-bound`, lines 1890–1897.
The mass-controlled derivative errors are integrated in outer time, while
the transported boundary data use the exact inner-cylinder Jacobian.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The geometric density with two squared errors has an integrable
majorant. The geometry premises are the proved exterior bounds; the two
error premises are the proved derivative estimates. Paper `e1a0fd5`,
lines 1890–1897. -/
theorem inner_density_square_majorant {A X Y V U Q : ℝ}
    (hA : 1 / 2 ≤ A) (hA1 : A ≤ 1)
    (hX : (X - V) ^ 2 ≤ Q) (hY : (Y - U) ^ 2 ≤ Q) :
    A * X ^ 2 + (Y + A * X) ^ 2 / A ≤ 6 * A * V ^ 2 + 8 * U ^ 2 + 14 * Q := by
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 ≤ Q := (sq_nonneg _).trans hX
  have hx : X ^ 2 ≤ 2 * V ^ 2 + 2 * Q := by nlinarith [sq_nonneg (X - 2 * V)]
  have hy : Y ^ 2 ≤ 2 * U ^ 2 + 2 * Q := by nlinarith [sq_nonneg (Y - 2 * U)]
  have hsum : (Y + A * X) ^ 2 ≤ 2 * Y ^ 2 + 2 * (A * X) ^ 2 := by
    nlinarith [sq_nonneg (Y - A * X)]
  have hrec : 1 / A ≤ 2 := by rw [div_le_iff₀ hA0]; linarith only [hA]
  have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ 3 * A by positivity)
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 / A by positivity)
  have hUrec := mul_le_mul_of_nonneg_left hrec (show 0 ≤ 4 * U ^ 2 by positivity)
  have hQrec := mul_le_mul_of_nonneg_left hrec (show 0 ≤ 4 * Q by positivity)
  have hAQ := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ 6 * Q by positivity)
  calc
    _ ≤ A * X ^ 2 + (2 * Y ^ 2 + 2 * (A * X) ^ 2) / A := by gcongr
    _ = 3 * A * X ^ 2 + (2 / A) * Y ^ 2 := by field_simp [hA0.ne']; ring
    _ ≤ 3 * A * (2 * V ^ 2 + 2 * Q) + (2 / A) * (2 * U ^ 2 + 2 * Q) := by
      linarith only [hx', hy']
    _ ≤ _ := by
      ring_nf at hUrec hQrec hAQ ⊢
      linarith only [hUrec, hQrec, hAQ]

/-- Upper inner-cylinder energy on any late interval. The sole integrability
premise for the actual inner density comes from the normalized inner chart's
energy transport; all majorant integrability is proved here. Paper `e1a0fd5`,
`eq:observability-inner-boundary-upper-bound`, lines 1890–1897. -/
theorem inner_boundary_energy_upper {b T K P a u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hfit : 64 * P ≤ b) (hE : chartScalarEnergy S T ≤ P) (ha : 0 < a)
    (hcut : 32 * P ≤ a) (hu : (K + 2) * b ≤ u) (huv : u ≤ v) (hv : v ≤ T)
    (tₐ : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc u v, (s, tₐ s) ∈ chartCylinder h.g T ∧ S.r s (tₐ s) = a)
    (hc : ContinuousOn tₐ (Icc u v)) (hmono : MonotoneOn tₐ (Icc u v))
    (hd : ∀ s ∈ Icc u v,
      HasDerivWithinAt tₐ ((-S.nu s (tₐ s)) / S.lam s (tₐ s)) (Icc u v) s)
    (hEi : IntervalIntegrable (fun s => innerBoundaryDensity S s (tₐ s)) volume u v) :
    (∫ s in u..v, innerBoundaryDensity S s (tₐ s)) ≤ 28 * chartScalarEnergy S T +
      14 * innerDerivativeSquareError K P a (chartScalarEnergy S T) * (v - u) := by
  have hu0 : 0 ≤ u :=
    (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hu
  have hsI (s : ℝ) (hs : s ∈ Icc u v) : s ∈ Icc 0 T := ⟨hu0.trans hs.1, hs.2.trans hv⟩
  have hlate (s : ℝ) (hs : s ∈ Icc u v) : (K + 2) * b ≤ s := hu.trans hs.1
  have hext (s : ℝ) (hs : s ∈ Icc u v) : (s, tₐ s) ∈ exteriorDomain h P :=
    late_exterior_mem h hP hmass (hcurve s hs).1 (by rwa [(hcurve s hs).2]) (hlate s hs)
  obtain ⟨hVi, hV⟩ := inner_boundary_data_energy_le h hP hmass tₐ huv hext hc hmono hd
  have hsub : uIcc u v ⊆ uIcc 0 T := by
    rw [uIcc_of_le huv, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hu0 hv
  have hUi := h.boundary_scalar_square_integrable.1.mono_set hsub
  let Q := innerDerivativeSquareError K P a (chartScalarEnergy S T)
  have hQi : IntervalIntegrable (fun _ : ℝ => 14 * Q) volume u v := intervalIntegrable_const
  have hb := intervalIntegral.integral_mono_on huv hEi
    (((hVi.const_mul 6).add (hUi.const_mul 8)).add hQi) (by
      intro s hs
      have hp := hext s hs
      have ht0 := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
      have hgeom := (exterior_geometry_of_mass_bound h hP ht0
        (exteriorDomain_interior h hP hp) hp.2.2 hmass).2.1
      have hx := inner_radial_derivative_square h hP hT hmass (hsI s hs) (hlate s hs)
        hfit hE hp ha (hcurve s hs).2
      have hy := inner_incoming_derivative_square h hP hT hmass (hsI s hs) (hlate s hs)
        hfit hE hp ha (hcurve s hs).2
      have hh := inner_density_square_majorant hgeom.1 hgeom.2 hx hy
      convert hh using 1 <;> dsimp only [innerBoundaryDensity, Q] <;> ring)
  rw [intervalIntegral.integral_add ((hVi.const_mul 6).add (hUi.const_mul 8)) hQi,
    intervalIntegral.integral_add (hVi.const_mul 6) (hUi.const_mul 8),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hb
  have hU := boundary_incoming_energy_le h hu0 huv hv
  dsimp only [Q] at hb
  simp only [smul_eq_mul] at hb
  linarith only [hb, hV, hU]

/-- Explicit K-only constant for the integrated inner observation.
Paper `e1a0fd5`, lines 1890–1897. -/
@[expose] noncomputable def innerObservationUpperConstant (K : ℝ) : ℝ :=
  28 + 14336 * amplitudeMassSquareConstant K +
    56 * (incomingDerivativeErrorConstant K ^ 2 + radialDerivativeErrorConstant K ^ 2)

/-- The paper's integrated upper estimate, with a constant independent of
`H` and `L`. The outer-duration premise is part of `InnerChartStatement`.
Paper `e1a0fd5`, `eq:observability-inner-boundary-upper-bound`, lines 1893–1897. -/
theorem inner_boundary_energy_upper_scaled {b T K P L H u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hfit : 64 * P ≤ b) (hE : chartScalarEnergy S T ≤ P) (hL : 64 ≤ L) (hH : 0 ≤ H)
    (hu : (K + 2) * b ≤ u) (huv : u ≤ v) (hv : v ≤ T) (hduration : v - u ≤ 2 * H * (L * P))
    (tₐ : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc u v, (s, tₐ s) ∈ chartCylinder h.g T ∧ S.r s (tₐ s) = L * P)
    (hc : ContinuousOn tₐ (Icc u v)) (hmono : MonotoneOn tₐ (Icc u v))
    (hd : ∀ s ∈ Icc u v,
      HasDerivWithinAt tₐ ((-S.nu s (tₐ s)) / S.lam s (tₐ s)) (Icc u v) s)
    (hEi : IntervalIntegrable (fun s => innerBoundaryDensity S s (tₐ s)) volume u v) :
    (∫ s in u..v, innerBoundaryDensity S s (tₐ s)) ≤
      innerObservationUpperConstant K *
        (chartScalarEnergy S T + H * (P / L ^ 3 + chartScalarEnergy S T / L ^ 2)) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hE0 := h.scalar_energy_nonneg
  have hA0 : 0 ≤ amplitudeMassSquareConstant K := by
    unfold amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  have hb := inner_boundary_energy_upper h hP hT hmass hfit hE
    (show 0 < L * P by positivity) (by nlinarith only [hL, hP]) hu huv hv tₐ hcurve hc hmono hd hEi
  have hQ0 : 0 ≤ innerDerivativeSquareError K P (L * P) (chartScalarEnergy S T) := by
    unfold innerDerivativeSquareError
    positivity
  have htime := mul_le_mul_of_nonneg_left hduration (show 0 ≤ 14 *
    innerDerivativeSquareError K P (L * P) (chartScalarEnergy S T) by positivity)
  have heq : 14 * innerDerivativeSquareError K P (L * P) (chartScalarEnergy S T) *
      (2 * H * (L * P)) = 14336 * amplitudeMassSquareConstant K * (H * P / L ^ 3) +
      56 * (incomingDerivativeErrorConstant K ^ 2 + radialDerivativeErrorConstant K ^ 2) *
        (H * chartScalarEnergy S T / L ^ 2) := by
    unfold innerDerivativeSquareError
    field_simp [hP.ne', hL0.ne']
    ring
  rw [heq] at htime
  have hC₁ : 0 ≤ 14336 * amplitudeMassSquareConstant K := by positivity
  have hC₂ : 0 ≤ 56 *
      (incomingDerivativeErrorConstant K ^ 2 + radialDerivativeErrorConstant K ^ 2) := by positivity
  have hX : 0 ≤ H * P / L ^ 3 := by positivity
  have hY : 0 ≤ H * chartScalarEnergy S T / L ^ 2 := by positivity
  have hAbsorb : 28 * chartScalarEnergy S T +
      (14336 * amplitudeMassSquareConstant K) * (H * P / L ^ 3) +
      (56 * (incomingDerivativeErrorConstant K ^ 2 + radialDerivativeErrorConstant K ^ 2)) *
        (H * chartScalarEnergy S T / L ^ 2) ≤ innerObservationUpperConstant K *
          (chartScalarEnergy S T + H * (P / L ^ 3 + chartScalarEnergy S T / L ^ 2)) := by
    have hN := add_nonneg
      (add_nonneg (mul_nonneg hC₁ (add_nonneg hE0 hY))
        (mul_nonneg hC₂ (add_nonneg hE0 hX)))
      (mul_nonneg (show (0 : ℝ) ≤ 28 by norm_num) (add_nonneg hX hY))
    apply sub_nonneg.mp
    convert hN using 1
    unfold innerObservationUpperConstant
    ring
  linarith only [hb, htime, hAbsorb]

end PropA4
end AcExtensionPrinciple

end
