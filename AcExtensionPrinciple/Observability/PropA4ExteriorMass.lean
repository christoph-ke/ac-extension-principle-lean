module

public import AcExtensionPrinciple.Observability.PropA4PrimitiveHardy

/-!
# Exterior mass from the radial scalar estimate

Paper `e1a0fd5`, `eq:observability-exterior-mass`, lines 1849–1854.
The upper mass density is integrated against the radius primitive, using
Hardy for the only term that cannot be estimated by a power tail.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Four-term squared error estimate for the upper mass density.
Paper `e1a0fd5`, lines 1849–1854. -/
theorem square_error_upper {x y d q e : ℝ} (he : |x + y - d + q| ≤ e) :
    x ^ 2 ≤ 4 * (y ^ 2 + d ^ 2 + q ^ 2 + e ^ 2) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hv : (x + y - d + q) ^ 2 ≤ e ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  nlinarith [sq_nonneg (x + y - d + q + y),
    sq_nonneg (x + y - d + q - d), sq_nonneg (x + y - d + q + q),
    sq_nonneg (y + d), sq_nonneg (y - q), sq_nonneg (d + q)]

/-- Upper mass density with explicit amplitude, boundary, primitive and
remainder terms. Geometry supplies the expansion and mass-ratio factors.
Paper `e1a0fd5`, lines 1849–1854. -/
theorem exterior_mass_density_bound {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) :
    S.massV s t ≤ (25 / 2) * amplitude h s ^ 2 * (S.lam s t / S.r s t ^ 2) +
      4 * S.dvpsi t t ^ 2 +
      2 * (exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 * S.lam s t) +
      2 * radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T *
        (S.lam s t / S.r s t ^ 3) := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hl := (h.signs s t hp.1).1
  have ht0 : 0 ≤ t := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hgeom := exterior_geometry_of_mass_bound h hP ht0
    (exteriorDomain_interior h hP hp) hp.2.2 hmass
  have hw := exteriorUnitRadialWeight_bounds h hP hmass hp
  have hw0 : 0 ≤ exteriorUnitRadialWeight h hP hmass s t :=
    (by positivity : (0 : ℝ) ≤ 1 / S.r s t).trans hw.1
  have hw2 := pow_le_pow_left₀ hw0 hw.2 2
  have hy := mul_le_mul_of_nonneg_left hw2 (sq_nonneg (amplitude h s))
  have he := square_error_upper (radial_scalar_error_bound h hP hT hmass hp)
  have hp3 : (S.r s t ^ (-(3 / 2) : ℝ)) ^ 2 = 1 / S.r s t ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h.scalar_energy_nonneg, hp3] at he
  have hd : S.dvpsi t t ^ 2 / S.lam s t ≤ 2 * S.dvpsi t t ^ 2 := by
    rw [div_le_iff₀ hl]
    nlinarith [mul_nonneg (sq_nonneg (S.dvpsi t t))
      (show 0 ≤ 2 * S.lam s t - 1 by linarith only [hgeom.2.2.1])]
  have hm : S.massV s t ≤ (S.theta s t / S.lam s t) ^ 2 * S.lam s t / 2 := by
    rw [chart_radial_mass_coefficient hl]
    have hh := mul_le_mul_of_nonneg_right hgeom.1.2
      (div_nonneg (mul_nonneg (sq_nonneg (S.theta s t / S.lam s t)) hl.le)
        (by norm_num : (0 : ℝ) ≤ 2))
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ S.lam s t / 2 by positivity)
  have hy' := mul_le_mul_of_nonneg_right hy (show 0 ≤ 2 * S.lam s t by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ (S.theta s t / S.lam s t) ^ 2 * (S.lam s t / 2) := by convert hm using 1; ring
    _ ≤ 2 * (amplitude h s ^ 2 * exteriorUnitRadialWeight h hP hmass s t ^ 2) * S.lam s t +
        2 * (S.dvpsi t t ^ 2 / S.lam s t) +
        2 * (exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 * S.lam s t) +
        2 * radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T *
          (S.lam s t / S.r s t ^ 3) := by
      convert hh using 1
      unfold radialScalarErrorConstant
      field_simp
      ring
    _ ≤ _ := by
      have heq : 2 * (amplitude h s ^ 2 * exteriorUnitRadialWeight h hP hmass s t ^ 2) *
          S.lam s t ≤ (25 / 2) * amplitude h s ^ 2 * (S.lam s t / S.r s t ^ 2) := by
        convert hy' using 1 <;> ring
      linarith only [heq, hd']

/-- Explicit exterior-mass estimate before substituting `a=LP`.
The amplitude bound and Hardy are proved from the chart in this theorem.
Paper `e1a0fd5`, `eq:observability-exterior-mass`, lines 1849–1854. -/
theorem exterior_mass_bound {b T K P s a u : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) (ha : 0 < a) (hcut : 32 * P ≤ a)
    (hu : h.g s ≤ u) (hus : u ≤ s) (hru : S.r s u = a) :
    S.m s s - S.m s u ≤ (25 / 2) * amplitudeMassSquareConstant K * P ^ 2 / a +
      (4 + 8 * K ^ 2 + radialScalarErrorConstant K ^ 2 * P ^ 2 / a ^ 2) *
        chartScalarEnergy S T := by
  have hmem (t : ℝ) (ht : t ∈ Icc u s) : (s, t) ∈ chartCylinder h.g T :=
    h.out_subset hs hu le_rfl ⟨by simp, ht⟩
  have hrad (t : ℝ) (ht : t ∈ Icc u s) : a ≤ S.r s t := by
    rw [← hru]
    exact h.radius_t_mono ht.1 (h.out_subset hs hu ht.2)
  have hpos (t : ℝ) (ht : t ∈ Icc u s) : 0 < S.r s t := ha.trans_le (hrad t ht)
  have hR : ContinuousOn (S.r s) (Icc u s) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hL : ContinuousOn (S.lam s) (Icc u s) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hprim (t : ℝ) (ht : t ∈ Icc u s) : IntervalPrimitive (S.r s) (S.lam s) u t :=
    h.equations.radius_t s u t ht.1 (h.out_subset hs hu ht.2)
  have hI (n : ℕ) : IntervalIntegrable (fun t => S.lam s t / S.r s t ^ n) volume u s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hus]
    exact hL.div (hR.pow n) (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  have hp2 : (∫ t in u..s, S.lam s t / S.r s t ^ 2) ≤ 1 / a := by
    have hh := radial_power_integral_le hus hR hL hpos hprim (by norm_num : (1 : ℝ) < 2)
    norm_num at hh
    rw [hru, Real.rpow_neg_one] at hh
    convert hh using 1
    · apply congrArg (fun f : ℝ → ℝ => ∫ t in u..s, f t)
      funext t
      ring
    · simp only [one_div]
  have hp3 : (∫ t in u..s, S.lam s t / S.r s t ^ 3) ≤ 1 / (2 * a ^ 2) := by
    have hh := radial_power_integral_le hus hR hL hpos hprim (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    rw [hru] at hh
    convert hh using 1
    · apply congrArg (fun f : ℝ → ℝ => ∫ t in u..s, f t)
      funext t
      ring
    · ring
  have hg0 := axis_label_nonneg h hs (by nlinarith only [hlate, h.b_pos])
  have hu0 := hg0.trans hu
  have hsub : uIcc u s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hus, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hu0 hs.2
  have hdi := h.boundary_scalar_square_integrable.2.mono_set hsub
  obtain ⟨hQi, hQ⟩ := radial_primitive_hardy h hP hT hmass hs hlate hu hus le_rfl
    (by rwa [hru])
  have hmi := h.equations.mass_t s u s hus (h.out_subset hs hu le_rfl)
  have hh := intervalIntegral.integral_mono_on hus hmi.1
    ((((hI 2).const_mul ((25 / 2) * amplitude h s ^ 2)).add (hdi.const_mul 4)).add
      (hQi.const_mul 2) |>.add
        ((hI 3).const_mul (2 * radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T)))
    (fun t ht => exterior_mass_density_bound h hP hT hmass
      (late_exterior_mem h hP hmass (hmem t ht) (hcut.trans (hrad t ht)) hlate))
  have hAsq := amplitude_sq_mass_bound h hP hT hmass hs hlate hfit hE
  have hE0 := h.scalar_energy_nonneg
  have hA0 : 0 ≤ amplitudeMassSquareConstant K * P ^ 2 :=
    (sq_nonneg (amplitude h s)).trans hAsq
  have hI20 : 0 ≤ ∫ t in u..s, S.lam s t / S.r s t ^ 2 :=
    intervalIntegral.integral_nonneg hus (by
      intro t ht
      exact div_nonneg (h.signs s t (hmem t ht)).1.le (sq_nonneg _))
  have hDb := boundary_radial_energy_le h hu0 hus hs.2
  rw [← hmi.2] at hh
  rw [intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  · calc
      _ ≤ _ := hh
      _ ≤ (25 / 2) * (amplitudeMassSquareConstant K * P ^ 2) * (1 / a) +
          4 * chartScalarEnergy S T + 2 * (4 * K ^ 2 * chartScalarEnergy S T) +
          (2 * radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T) *
            (1 / (2 * a ^ 2)) := by
        gcongr
      _ = _ := by field_simp; ring
  all_goals repeat' first | exact (hI 2).const_mul _ | exact (hI 3).const_mul _ |
    exact hdi.const_mul _ | exact hQi.const_mul _ | apply IntervalIntegrable.add

/-- A K-only constant controlling the mass outside `a=LP`.
Paper `e1a0fd5`, `eq:observability-exterior-mass`, lines 1849–1854. -/
@[expose] noncomputable def exteriorMassConstant (K : ℝ) : ℝ :=
  (25 / 2) * amplitudeMassSquareConstant K + 4 + 8 * K ^ 2 + radialScalarErrorConstant K ^ 2

/-- The source exterior mass bound, with an explicit constant independent
of `L`, the observation duration, and `M/b`. Paper `e1a0fd5`,
`eq:observability-exterior-mass`, lines 1849–1854. -/
theorem exterior_mass_bound_scaled {b T K P s L u : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) (hL : 64 ≤ L)
    (hu : h.g s ≤ u) (hus : u ≤ s) (hru : S.r s u = L * P) :
    S.m s s - S.m s u ≤ exteriorMassConstant K * (P / L + chartScalarEnergy S T) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hE0 := h.scalar_energy_nonneg
  have hA0 : 0 ≤ amplitudeMassSquareConstant K := by
    unfold amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  have hb := exterior_mass_bound h hP hT hmass hs hlate hfit hE
    (show 0 < L * P by positivity) (by nlinarith only [hL, hP]) hu hus hru
  have heq : (25 / 2) * amplitudeMassSquareConstant K * P ^ 2 / (L * P) =
      (25 / 2) * amplitudeMassSquareConstant K * (P / L) := by
    field_simp [hP.ne']
  have hquot : P ^ 2 / (L * P) ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos (show 0 < L * P by positivity))]
    have hh := pow_le_pow_left₀ hP.le
      (show P ≤ L * P by nlinarith only [hL, hP]) 2
    simpa only [one_mul] using hh
  have hq := mul_le_mul_of_nonneg_left hquot (sq_nonneg (radialScalarErrorConstant K))
  simp only [mul_one] at hq
  rw [← mul_div_assoc] at hq
  rw [heq] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (25 / 2) * amplitudeMassSquareConstant K * (P / L) +
        (4 + 8 * K ^ 2 + radialScalarErrorConstant K ^ 2) * chartScalarEnergy S T := by
      gcongr
    _ ≤ exteriorMassConstant K * (P / L + chartScalarEnergy S T) := by
      unfold exteriorMassConstant
      nlinarith [mul_nonneg (show 0 ≤ (25 / 2) * amplitudeMassSquareConstant K by positivity) hE0,
        mul_nonneg (show 0 ≤ 4 + 8 * K ^ 2 + radialScalarErrorConstant K ^ 2 by positivity)
          (show 0 ≤ P / L by positivity)]

end PropA4
end AcExtensionPrinciple

end
