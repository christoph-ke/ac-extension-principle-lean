module

public import AcExtensionPrinciple.Observability.PropA4IncomingDerivative
public import AcExtensionPrinciple.Observability.PropA4IncomingOscillation
public import AcExtensionPrinciple.Observability.PropA4UnitRadialDerivatives

/-!
# The radial scalar derivative error on the exterior domain

Paper `e1a0fd5`, `eq:observability-radial-derivative-bound`, lines
1790–1811. The unit derivative is represented by its actual incoming
potential integral. All three error contributions have explicit uniform bounds.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Radial scalar derivative error, with the smaller remainder tail still
visible. The unit integral is `-W_r`, by its proved derivative formula.
Paper `e1a0fd5`, lines 1790–1811. -/
theorem radial_derivative_error_tails {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    |S.dvpsi s t / S.lam s t - S.dvpsi t t / S.lam s t +
      amplitude h s * ((∫ σ in t..s, chartPotential S σ t *
        exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t)| ≤
      (32 / 3) * P * Real.sqrt (K * chartScalarEnergy S T) * S.r s t ^ (-(3 / 2) : ℝ) +
      (64 / 5) * P ^ 2 * ((32 / 3) * Real.sqrt (K * chartScalarEnergy S T) +
        4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * chartScalarEnergy S T)) *
          S.r s t ^ (-(5 / 2) : ℝ) +
      (16 * P / S.r s t) * (Real.pi * Real.sqrt 2 / Real.sqrt (S.r s t)) *
        Real.sqrt (3 * (1 + K) * chartScalarEnergy S T) := by
  let V := fun p : ℝ × ℝ => chartPotential S p.1 p.2
  let W := exteriorUnitSolution h hP hmass
  let B := exteriorBoundaryPrimitive h
  let R := exteriorRemainder h hP hmass
  let A := fun p : ℝ × ℝ => (amplitude h p.1 - amplitude h s) * W p
  let E := chartScalarEnergy S T
  let C := (32 / 3) * Real.sqrt (K * E) +
    4 * Real.pi * Real.sqrt 2 * Real.sqrt (3 * (1 + K) * E)
  let D := 2 * Real.sqrt (3 * (1 + K) * E)
  have hK : 0 ≤ K := by linarith only [h.K_ge_one]
  have hE : 0 ≤ E := h.scalar_energy_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htri := exteriorDomain_triangle h hP hp
  have hint := exteriorDomain_interior h hP hp
  have ht : 0 ≤ t := (mul_nonneg hK h.b_pos.le).trans hp.2.1
  have hVc : ContinuousOn V (chartTriangle t s) :=
    continuous_potential_on h (fun p hp => exteriorDomain_interior h hP (htri hp))
  have hWc := (exteriorUnitSolution_continuous h hP hmass).mono htri
  have hBc := (exteriorBoundaryPrimitive_continuous h hP hT).mono htri
  have hRc := (exteriorRemainder_continuous h hP hT hmass).mono htri
  have hAc : ContinuousOn A (chartTriangle t s) :=
    (((amplitude_continuous_on_exterior h hT).mono htri).sub continuousOn_const).mul hWc
  have hline : MapsTo (fun σ : ℝ => (σ, t)) (Icc t s) (chartTriangle t s) :=
    fun σ hσ => ⟨le_rfl, hσ.1, hσ.2⟩
  have hvi := hVc.comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hai := hAc.comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hbi : IntervalIntegrable (fun σ => V (σ, t) * B (σ, t)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hBc).comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hri : IntervalIntegrable (fun σ => V (σ, t) * R (σ, t)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hRc).comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hwi : IntervalIntegrable (fun σ => V (σ, t) * W (σ, t)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact (hVc.mul hWc).comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have haint : IntervalIntegrable (fun σ => V (σ, t) * A (σ, t)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hvi.mul hai
  have hBbound : ∀ p ∈ chartTriangle t s,
      |B p| ≤ Real.sqrt (K * E) * S.r p.1 p.2 ^ (1 / 2 : ℝ) := by
    intro p hp'
    have hpD := htri hp'
    have hb := boundary_primitive_bound h (hpD.2.1.trans hpD.1.2.2.2) hpD.1
    calc
      _ ≤ Real.sqrt (K * S.r p.1 p.2 * E) := hb
      _ = _ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (mul_nonneg hK hE)]
        congr 1
        ring
  have hRbound : ∀ p ∈ chartTriangle t s, |R p| ≤ (2 * P * C) * S.r p.1 p.2 ^ (-(1 / 2) : ℝ) :=
    fun p hp' => exteriorRemainder_bound h hP hT hmass p (htri hp')
  have hAbound : ∀ σ ∈ Icc t s, |A (σ, t)| ≤ D * Real.sqrt (s - σ) := by
    intro σ hσ
    have hpD := htri (hline hσ)
    have hos := amplitude_oscillation h
      ⟨hpD.2.1.trans hpD.1.2.2.2, hpD.1.2.1⟩ ⟨hp.2.1.trans hp.1.2.2.2, hp.1.2.1⟩ hσ.2
    have hosc : |amplitude h σ - amplitude h s| ≤
        Real.sqrt (3 * (1 + K) * E) * Real.sqrt (s - σ) := by
      rw [abs_sub_comm]
      calc
        _ ≤ Real.sqrt (3 * (1 + K) * (s - σ) * E) := hos
        _ = _ := by
          rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * (1 + K) * E)]
          congr 1
          ring
    have hw := exteriorUnitSolution_bounds h hP hmass hpD
    have hw0 : 0 ≤ W (σ, t) := by linarith only [hw.1]
    change |(amplitude h σ - amplitude h s) * W (σ, t)| ≤ _
    rw [abs_mul, abs_of_nonneg hw0]
    calc
      _ ≤ (Real.sqrt (3 * (1 + K) * E) * Real.sqrt (s - σ)) * 2 :=
        mul_le_mul hosc hw.2 hw0 (by positivity)
      _ = _ := by dsimp [D]; ring
  have hBB := incoming_weighted_integral_bound h hP ht hint hp.2.2 hmass
    (by norm_num : (1 / 2 : ℝ) < 2) (Real.sqrt_nonneg (K * E)) hBc hBbound
  have hRB := incoming_weighted_integral_bound h hP ht hint hp.2.2 hmass
    (by norm_num : (-(1 / 2) : ℝ) < 2) (show 0 ≤ 2 * P * C by positivity) hRc hRbound
  have hGc : ContinuousOn (fun σ : ℝ => D * Real.sqrt (s - σ)) (Icc t s) := by fun_prop
  have hAB := interval_abs_integral_le_of_domination hp.1.2.2.2 hvi hai hGc
    (fun σ hσ => h.potential_nonneg (htri (hline hσ)).1) hAbound
  have hscale : (∫ σ in t..s, V (σ, t) * (D * Real.sqrt (s - σ))) =
      D * (∫ σ in t..s, chartPotential S σ t * Real.sqrt (s - σ)) := by
    dsimp [V]
    simp only [mul_left_comm _ D, intervalIntegral.integral_const_mul]
  dsimp only [Function.comp_def] at hAB
  rw [hscale] at hAB
  have hAT := hAB.trans (mul_le_mul_of_nonneg_left
    (incoming_time_oscillation_kernel_le h hP ht hint hp.2.2 hmass) hD)
  have hsplit : (∫ σ in t..s, V (σ, t) * chartPsi S σ t) =
      amplitude h s * (∫ σ in t..s, V (σ, t) * W (σ, t)) +
        ((∫ σ in t..s, V (σ, t) * B (σ, t)) +
          (∫ σ in t..s, V (σ, t) * R (σ, t)) + (∫ σ in t..s, V (σ, t) * A (σ, t))) := by
    calc
      _ = ∫ σ in t..s, amplitude h s * (V (σ, t) * W (σ, t)) +
          ((V (σ, t) * B (σ, t) + V (σ, t) * R (σ, t)) + V (σ, t) * A (σ, t)) := by
        apply intervalIntegral.integral_congr
        intro σ _
        have he : chartPsi S σ t = amplitude h σ * W (σ, t) + B (σ, t) + R (σ, t) :=
          exterior_scalar_decomposition h hP hmass (σ, t)
        change V (σ, t) * chartPsi S σ t = _
        rw [he]
        dsimp [A]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hwi.const_mul _) ((hbi.add hri).add haint),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hbi.add hri) haint,
          intervalIntegral.integral_add hbi hri]
  let I := (∫ σ in t..s, V (σ, t) * B (σ, t)) + (∫ σ in t..s, V (σ, t) * R (σ, t)) +
    (∫ σ in t..s, V (σ, t) * A (σ, t))
  have hI : |I| ≤ Real.sqrt (K * E) * (8 * P / (2 - (1 / 2)) * S.r s t ^ ((1 / 2) - 2 : ℝ)) +
      (2 * P * C) * (8 * P / (2 - (-(1 / 2))) * S.r s t ^ ((-(1 / 2)) - 2 : ℝ)) +
      D * ((4 * P / S.r s t) * (Real.pi * Real.sqrt 2 / Real.sqrt (S.r s t))) :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hBB hRB)) hAT)
  have hgeo := exterior_geometry_of_mass_bound h hP ht hint hp.2.2 hmass
  have hl : 0 < S.lam s t := by linarith only [hgeo.2.2.1]
  have hdiv : |I| / S.lam s t ≤ 2 * |I| := by
    apply (div_le_iff₀ hl).mpr
    nlinarith only [hgeo.2.2.1, abs_nonneg I]
  have heq := radial_wave_representation h ht hint
  rw [heq, hsplit]
  have hid : S.dvpsi t t / S.lam s t -
      (amplitude h s * (∫ σ in t..s, V (σ, t) * W (σ, t)) + I) / S.lam s t -
      S.dvpsi t t / S.lam s t + amplitude h s *
        ((∫ σ in t..s, V (σ, t) * W (σ, t)) / S.lam s t) = -I / S.lam s t := by ring
  change |S.dvpsi t t / S.lam s t -
    (amplitude h s * (∫ σ in t..s, V (σ, t) * W (σ, t)) + I) / S.lam s t -
    S.dvpsi t t / S.lam s t + amplitude h s *
      ((∫ σ in t..s, V (σ, t) * W (σ, t)) / S.lam s t)| ≤ _
  rw [hid, abs_div, abs_neg, abs_of_pos hl]
  apply (hdiv.trans (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
  dsimp [C, D, E]
  norm_num
  ring

end PropA4
end AcExtensionPrinciple

end
