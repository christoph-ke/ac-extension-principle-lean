module

public import AcExtensionPrinciple.Observability.PropA4RadialScalar
public import AcExtensionPrinciple.Observability.PropA4LateExterior

/-!
# Annular radius labels and mass coercivity

Paper `e1a0fd5`, `eq:observability-amplitude-mass-bound`, lines 1823–1836.
The radius labels are obtained from continuity, and the coercive estimate
uses only the printed mass gap and the already proved scalar error.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Every radius between axis and boundary has a characteristic label.
Paper `e1a0fd5`, annulus integration at lines 1823–1836. -/
theorem exists_radius_label {b T K s a : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ t ∈ Icc (h.g s) s, S.r s t = a := by
  have hc : ContinuousOn (S.r s) (Icc (h.g s) s) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => h.out_subset hs le_rfl le_rfl ⟨by simp, ht⟩)
  apply intermediate_value_Icc (h.axis_before_boundary s hs).le hc
  rw [(h.axis_values s hs).1, (h.boundary_gauge s hs).1]
  exact ⟨ha, hab⟩

/-- Two ordered positive radii have ordered labels in the same outgoing slice.
Paper `e1a0fd5`, annulus integration at lines 1823–1836. -/
theorem exists_annulus_labels {b T K s a : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T)
    (ha : 0 < a) (hab : 2 * a ≤ b) :
    ∃ u v, h.g s ≤ u ∧ u ≤ v ∧ v ≤ s ∧ S.r s u = a ∧ S.r s v = 2 * a := by
  obtain ⟨u, hu, hru⟩ := exists_radius_label h hs ha.le (by linarith)
  obtain ⟨v, hv, hrv⟩ := exists_radius_label h hs (by positivity) hab
  refine ⟨u, v, hu.1, ?_, hv.2, hru, hrv⟩
  by_contra hn
  have hh := h.radius_t_mono (le_of_not_ge hn) (h.out_subset hs hv.1 hu.2)
  rw [hru, hrv] at hh
  linarith

/-- The elementary squared error inequality in the annular argument.
Paper `e1a0fd5`, lines 1831–1836. -/
theorem coercive_square_error {x y d q e : ℝ} (he : |x + y - d + q| ≤ e) :
    y ^ 2 / 2 ≤ x ^ 2 + 3 * (d ^ 2 + q ^ 2 + e ^ 2) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hv : (x + y - d + q) ^ 2 ≤ e ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  nlinarith [sq_nonneg (2 * x + y),
    sq_nonneg (x + y - d + q - d),
    sq_nonneg (x + y - d + q + q), sq_nonneg (d + q)]

/-- The actual mass density controls the amplitude weight up to the three
squared errors, without requiring continuity of the BV scalar derivatives.
Paper `e1a0fd5`, lines 1823–1836. -/
theorem annular_mass_coercivity {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    amplitude h s ^ 2 * (S.lam s t / S.r s t ^ 2) / (4 * K) ≤
      S.massV s t + (3 / (2 * K)) *
        (S.dvpsi t t ^ 2 / S.lam s t +
          exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 * S.lam s t +
          ((radialDerivativeErrorConstant K + 2 * exteriorErrorCoefficient K) ^ 2 *
            P ^ 2 * chartScalarEnergy S T / S.r s t ^ 3) * S.lam s t) := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hl := (h.signs s t hp.1).1
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have he := coercive_square_error (radial_scalar_error_bound h hP hT hmass hp)
  have hweight := (exteriorUnitRadialWeight_bounds h hP hmass hp).1
  have hw2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / S.r s t) hweight 2
  have hy := mul_le_mul_of_nonneg_left hw2 (sq_nonneg (amplitude h s))
  rw [mul_pow, div_pow] at he
  have hp3 : (S.r s t ^ (-(3 / 2) : ℝ)) ^ 2 = 1 / S.r s t ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h.scalar_energy_nonneg, hp3] at he
  have hhe := mul_le_mul_of_nonneg_right he (show 0 ≤ S.lam s t / (2 * K) by positivity)
  have hgap := h.gap s t hp.1
  have hcoef : (S.theta s t / S.lam s t) ^ 2 * (S.lam s t / (2 * K)) ≤
      S.massV s t := by
    rw [chart_radial_mass_coefficient hl]
    have hh := mul_le_mul_of_nonneg_right hgap
      (div_nonneg (mul_nonneg (sq_nonneg (S.theta s t / S.lam s t)) hl.le)
        (by norm_num : (0 : ℝ) ≤ 2))
    simp only [inv_eq_one_div] at hh
    convert hh using 1 <;> ring
  have hhy := mul_le_mul_of_nonneg_right hy
    (show 0 ≤ S.lam s t / (4 * K) by positivity)
  have hbase : amplitude h s ^ 2 * (S.lam s t / S.r s t ^ 2) / (4 * K) ≤
      amplitude h s ^ 2 * exteriorUnitRadialWeight h hP hmass s t ^ 2 *
        (S.lam s t / (4 * K)) := by
    convert hhy using 1; ring
  calc
    _ ≤ _ := hbase
    _ ≤ ((S.theta s t / S.lam s t) ^ 2 + 3 *
        ((S.dvpsi t t / S.lam s t) ^ 2 +
          (exteriorBoundaryPrimitive h (s, t) / S.r s t) ^ 2 +
          (radialDerivativeErrorConstant K + 2 * exteriorErrorCoefficient K) ^ 2 *
            P ^ 2 * chartScalarEnergy S T * (1 / S.r s t ^ 3))) *
        (S.lam s t / (2 * K)) := by
      convert hhe using 1 <;> ring
    _ = (S.theta s t / S.lam s t) ^ 2 * (S.lam s t / (2 * K)) +
        (3 / (2 * K)) * (S.dvpsi t t ^ 2 / S.lam s t +
          exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 * S.lam s t +
          ((radialDerivativeErrorConstant K + 2 * exteriorErrorCoefficient K) ^ 2 *
            P ^ 2 * chartScalarEnergy S T / S.r s t ^ 3) * S.lam s t) := by
      field_simp
    _ ≤ _ := by gcongr

end PropA4
end AcExtensionPrinciple

end
