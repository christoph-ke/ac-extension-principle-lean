module

public import AcExtensionPrinciple.Observability.PropA4UnitSolution
public import AcExtensionPrinciple.Observability.PropA4TriangleCalculus

/-!
# The radial derivative of the concrete exterior unit solution

Paper `e1a0fd5`, lines 1755–1759. Reversing the characteristic triangle
identifies the derivative in `t`; the exterior geometry controls its
radial rescaling by `1/λ`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Differentiation in the incoming label on the closed exterior slice.
Paper `e1a0fd5`, lines 1755–1759. -/
theorem exteriorUnitSolution_hasDerivWithinAt_t {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    HasDerivWithinAt (fun x => exteriorUnitSolution h hP hmass (s, x))
      (-(∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)))
      {x | (s, x) ∈ exteriorDomain h P} t := by
  let F := fun p : ℝ × ℝ => chartPotential S p.1 p.2 * exteriorUnitSolution h hP hmass p
  have hFc : ContinuousOn F (exteriorDomain h P) :=
    (continuous_potential_on h (fun p hp => exteriorDomain_interior h hP hp)).mul
      (exteriorUnitSolution_continuous h hP hmass)
  obtain ⟨G, hG, hGeq⟩ := exteriorDomain_continuous_extension h hFc
  have hd := (triangular_integral_hasDerivWithinAt_t hG hp.1.2.2.2).const_add 1
  have hI : (∫ σ in t..s, G (σ, t)) =
      ∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hp.1.2.2.2] at hσ
    exact hGeq (σ, t) (exteriorDomain_triangle h hP hp ⟨le_rfl, hσ.1, hσ.2⟩)
  rw [hI] at hd
  apply (hd.mono (fun x hx => hx.1.2.2.2)).congr_of_mem _ hp
  intro x hx
  rw [exteriorUnitSolution_equation h hP hmass hx]
  congr 1
  unfold triangleVolterra
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [uIcc_of_le hx.1.2.2.2] at hσ
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hσ.1] at hz
  exact (hGeq (σ, z) (exteriorDomain_triangle h hP hx ⟨hz.1, hz.2, hσ.2⟩)).symm

/-- Positivity and the incoming radius separation control the potential
integral in `-W_t` by `8P/r²`. Paper `e1a0fd5`, lines 1755–1759. -/
theorem exteriorUnitSolution_t_integral_bounds {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    0 ≤ (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) ∧
      (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) ≤
        8 * P * S.r s t ^ (-2 : ℝ) := by
  have htri := exteriorDomain_triangle h hP hp
  have hint := exteriorDomain_interior h hP hp
  have ht : 0 ≤ t := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hline : MapsTo (fun σ : ℝ => (σ, t)) (Icc t s) (exteriorDomain h P) :=
    fun σ hσ => htri ⟨le_rfl, hσ.1, hσ.2⟩
  have hPc : ContinuousOn (fun p : ℝ × ℝ => chartPotential S p.1 p.2) (exteriorDomain h P) :=
    continuous_potential_on h (fun p hp => exteriorDomain_interior h hP hp)
  have hc : ContinuousOn (fun σ => chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t))
      (Icc t s) :=
    (hPc.mul (exteriorUnitSolution_continuous h hP hmass)).comp (f := fun σ : ℝ => (σ, t))
      (show ContinuousOn (fun σ : ℝ => (σ, t)) (Icc t s) by fun_prop) hline
  have hpos : ∀ σ ∈ Icc t s, 0 < S.r s t + (s - σ) / 2 := by
    intro σ hσ
    linarith only [hint.2, hσ.2]
  have hj : ContinuousOn (fun σ : ℝ => 8 * P * (S.r s t + (s - σ) / 2) ^ (-3 : ℝ))
      (Icc t s) :=
    continuousOn_const.mul ((show Continuous (fun σ : ℝ => S.r s t + (s - σ) / 2)
      by fun_prop).continuousOn.rpow_const (fun σ hσ => Or.inl (hpos σ hσ).ne'))
  have hi : IntervalIntegrable
      (fun σ => chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hp.1.2.2.2] using hc
  have hji : IntervalIntegrable
      (fun σ : ℝ => 8 * P * (S.r s t + (s - σ) / 2) ^ (-3 : ℝ)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hj
  constructor
  · apply intervalIntegral.integral_nonneg hp.1.2.2.2
    intro σ hσ
    exact mul_nonneg (h.potential_nonneg (hline hσ).1)
      (by linarith only [(exteriorUnitSolution_bounds h hP hmass (hline hσ)).1])
  · have hm := intervalIntegral.integral_mono_on hp.1.2.2.2 hi
      hji (fun σ hσ => by
        have hσD := hline hσ
        have hσint := exteriorDomain_interior h hP hσD
        have hpot := potential_le_radial_density h hP ht hσint hσD.2.2 hmass
        have hgeo := exterior_geometry_of_mass_bound h hP ht hσint hσD.2.2 hmass
        have hsep := incoming_radius_separation h hP ht hint hp.2.2 hmass hσ
        have hpow := Real.rpow_le_rpow_of_nonpos (hpos σ hσ) hsep (by norm_num : (-3 : ℝ) ≤ 0)
        have hrad : chartPotential S σ t ≤ 4 * P * S.r σ t ^ (-3 : ℝ) := by
          rw [Real.rpow_neg hσint.2.le, Real.rpow_ofNat _ 3]
          have hb : 4 * P * S.lam σ t ≤ 4 * P :=
            by nlinarith only [hP, hgeo.2.2.2]
          exact hpot.trans (by simpa only [div_eq_mul_inv] using
            div_le_div_of_nonneg_right hb (pow_nonneg hσint.2.le 3))
        calc
          _ ≤ (4 * P * S.r σ t ^ (-3 : ℝ)) * 2 :=
            mul_le_mul hrad (exteriorUnitSolution_bounds h hP hmass hσD).2
              (by linarith only [(exteriorUnitSolution_bounds h hP hmass hσD).1])
              (mul_nonneg (by positivity : 0 ≤ 4 * P) (Real.rpow_nonneg hσint.2.le (-3)))
          _ ≤ (4 * P * (S.r s t + (s - σ) / 2) ^ (-3 : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) (by norm_num)
          _ = _ := by ring)
    rw [intervalIntegral.integral_const_mul] at hm
    have hb := incoming_affine_power_integral_le hint.2 hp.1.2.2.2 (by norm_num : (-1 : ℝ) < 1)
    norm_num only at hb
    exact hm.trans (by nlinarith only [hb, hP])

/-- The radial rescaling by `1/λ` has the printed sign and decay.
Together with the `t` derivative formula this is `0 ≤ -W_r ≤ 16P/r²`.
Paper `e1a0fd5`, `eq:observability-unit-solution-bounds`, lines 1757–1759. -/
theorem exteriorUnitSolution_radial_integral_bounds {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    0 ≤ (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t ∧
      (∫ σ in t..s, chartPotential S σ t * exteriorUnitSolution h hP hmass (σ, t)) / S.lam s t ≤
        16 * P * S.r s t ^ (-2 : ℝ) := by
  have ht : 0 ≤ t := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hgeo := exterior_geometry_of_mass_bound h hP ht
    (exteriorDomain_interior h hP hp) hp.2.2 hmass
  have hl : 0 < S.lam s t := by linarith only [hgeo.2.2.1]
  have hi := exteriorUnitSolution_t_integral_bounds h hP hmass hp
  refine ⟨div_nonneg hi.1 hl.le, (div_le_iff₀ hl).mpr ?_⟩
  have hr0 := Real.rpow_nonneg (exteriorDomain_interior h hP hp).2.le (-2)
  nlinarith only [hi.2, hgeo.2.2.1, mul_nonneg hP.le hr0]

end PropA4
end AcExtensionPrinciple

end
