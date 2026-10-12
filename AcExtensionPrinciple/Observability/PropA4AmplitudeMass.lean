module

public import AcExtensionPrinciple.Observability.PropA4AnnularMass

/-!
# Amplitude controlled by the total enclosed mass

Paper `e1a0fd5`, `eq:observability-amplitude-mass-bound`, lines 1823–1836.
All integration is performed in the original characteristic label; the
radius primitive supplies the exact radial Jacobian and annular integral.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- K-only coefficient in the radial scalar error. Paper `e1a0fd5`,
`eq:observability-radial-scalar-bound`, lines 1823–1829. -/
@[expose] noncomputable def radialScalarErrorConstant (K : ℝ) : ℝ :=
  radialDerivativeErrorConstant K + 2 * exteriorErrorCoefficient K

/-- Observation bounds the radial boundary derivative on every subinterval.
Paper `e1a0fd5`, lines 1829–1836 and 1887–1892. -/
theorem boundary_radial_energy_le {b T K u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    (∫ t in u..v, S.dvpsi t t ^ 2) ≤ chartScalarEnergy S T := by
  have hm := intervalIntegral.integral_mono_interval hu huv hv
    (Filter.Eventually.of_forall (fun t => sq_nonneg (S.dvpsi t t)))
    h.boundary_scalar_square_integrable.2
  unfold chartScalarEnergy
  rw [intervalIntegral.integral_add h.boundary_scalar_square_integrable.2
    h.boundary_psi_deriv_square_integrable]
  have hd : 0 ≤ ∫ t in 0..T, deriv (fun s => chartPsi S s s) t ^ 2 :=
    intervalIntegral.integral_nonneg h.T_nonneg (by intros; positivity)
  linarith

/-- Replace the primitive and radial error on an annulus by integrable
majorants using its minimum radius. Paper `e1a0fd5`, lines 1829–1836. -/
theorem annular_mass_coercivity_majorant {b T K P s t a : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hp : (s, t) ∈ exteriorDomain h P) (hlate : (K + 2) * b ≤ s)
    (ha : 0 < a) (har : a ≤ S.r s t) :
    amplitude h s ^ 2 * (S.lam s t / S.r s t ^ 2) / (4 * K) ≤
      S.massV s t + (3 / (2 * K)) *
        (2 * S.dvpsi t t ^ 2 +
          (K * chartScalarEnergy S T / a + radialScalarErrorConstant K ^ 2 *
            P ^ 2 * chartScalarEnergy S T / a ^ 3) * S.lam s t) := by
  have hr := (exteriorDomain_interior h hP hp).2
  have hE0 := h.scalar_energy_nonneg
  have ht0 : 0 ≤ t := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hp.2.1
  have hgeom := exterior_geometry_of_mass_bound h hP
    ht0
    (exteriorDomain_interior h hP hp) hp.2.2 hmass
  have hl := (h.signs s t hp.1).1
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hd : S.dvpsi t t ^ 2 / S.lam s t ≤ 2 * S.dvpsi t t ^ 2 := by
    rw [div_le_iff₀ hl]
    nlinarith [mul_nonneg (sq_nonneg (S.dvpsi t t))
      (show 0 ≤ 2 * S.lam s t - 1 by linarith only [hgeom.2.2.1])]
  have hprim := boundary_primitive_sq h (by nlinarith only [hlate, h.b_pos]) hp.1
  have hq : exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 ≤
      K * chartScalarEnergy S T / a := by
    calc
      _ ≤ (K * S.r s t * chartScalarEnergy S T) / S.r s t ^ 2 :=
        div_le_div_of_nonneg_right hprim (sq_nonneg _)
      _ = K * chartScalarEnergy S T / S.r s t := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (by linarith only [h.K_ge_one]) h.scalar_energy_nonneg) ha har
  have he : radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T /
      S.r s t ^ 3 ≤ radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T /
        a ^ 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ ha.le har 3
  have hb := annular_mass_coercivity h hP hT hmass hp
  calc
    _ ≤ S.massV s t + (3 / (2 * K)) *
        (2 * S.dvpsi t t ^ 2 + K * chartScalarEnergy S T / a * S.lam s t +
          (radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T / a ^ 3) *
            S.lam s t) := by
      apply hb.trans
      change S.massV s t + (3 / (2 * K)) *
        (S.dvpsi t t ^ 2 / S.lam s t +
          exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 * S.lam s t +
          (radialScalarErrorConstant K ^ 2 * P ^ 2 * chartScalarEnergy S T /
            S.r s t ^ 3) * S.lam s t) ≤ _
      gcongr
    _ = _ := by ring

/-- On the radius annulus `[a,2a]`, integration gives the exact printed
amplitude coefficient `1/(8Ka)`. The radius and mass primitives discharge
all regularity needed here. Paper `e1a0fd5`, lines 1823–1836. -/
theorem amplitude_annular_mass_bound {b T K P s a u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s)
    (ha : 0 < a) (hcut : 32 * P ≤ a)
    (hu : h.g s ≤ u) (huv : u ≤ v) (hv : v ≤ s)
    (hru : S.r s u = a) (hrv : S.r s v = 2 * a) :
    amplitude h s ^ 2 / (8 * K * a) ≤ S.m s v - S.m s u +
      (3 / (2 * K)) * (2 * chartScalarEnergy S T +
        (K + radialScalarErrorConstant K ^ 2 * P ^ 2 / a ^ 2) * chartScalarEnergy S T) := by
  have hseg := h.out_subset hs hu hv
  have hmem (t : ℝ) (ht : t ∈ Icc u v) : (s, t) ∈ chartCylinder h.g T :=
    hseg ⟨by simp, ht⟩
  have hrad (t : ℝ) (ht : t ∈ Icc u v) : a ≤ S.r s t := by
    rw [← hru]
    exact h.radius_t_mono ht.1 (h.out_subset hs hu (ht.2.trans hv))
  have hR : ContinuousOn (S.r s) (Icc u v) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hL : ContinuousOn (S.lam s) (Icc u v) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hpos (t : ℝ) (ht : t ∈ Icc u v) : 0 < S.r s t := ha.trans_le (hrad t ht)
  have hL2 : IntervalIntegrable (fun t => S.lam s t / S.r s t ^ 2) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact hL.div (hR.pow 2) (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  have hprim (t : ℝ) (ht : t ∈ Icc u v) : IntervalPrimitive (S.r s) (S.lam s) u t :=
    h.equations.radius_t s u t ht.1 (h.out_subset hs hu (ht.2.trans hv))
  have hi := radial_power_integral huv hR hL hpos hprim (by norm_num : (1 : ℝ) < 2)
  norm_num at hi
  have hpower : (∫ t in u..v, S.lam s t / S.r s t ^ 2) = 1 / (2 * a) := by
    convert hi using 1
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      dsimp only
      ring
    · rw [hru, hrv, Real.rpow_neg_one, Real.rpow_neg_one]
      field_simp
      ring
  have hg0 := axis_label_nonneg h hs (by nlinarith only [hlate, h.b_pos])
  have hu0 := hg0.trans hu
  have hvT := hv.trans hs.2
  have hsub : uIcc u v ⊆ uIcc 0 T := by
    rw [uIcc_of_le huv, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hu0 hvT
  have hdi := h.boundary_scalar_square_integrable.2.mono_set hsub
  have hli : IntervalIntegrable (S.lam s) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le huv]
  have hmi := h.equations.mass_t s u v huv hseg
  let Q := K * chartScalarEnergy S T / a + radialScalarErrorConstant K ^ 2 *
    P ^ 2 * chartScalarEnergy S T / a ^ 3
  have hbound := intervalIntegral.integral_mono_on huv
    ((hL2.const_mul (amplitude h s ^ 2)).div_const (4 * K))
    (hmi.1.add (((hdi.const_mul 2).add (hli.const_mul Q)).const_mul (3 / (2 * K))))
    (fun t ht => annular_mass_coercivity_majorant h hP hT hmass
      (late_exterior_mem h hP hmass (hmem t ht) (hcut.trans (hrad t ht)) hlate)
      hlate ha (hrad t ht))
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hpower,
    intervalIntegral.integral_add hmi.1
      (((hdi.const_mul 2).add (hli.const_mul Q)).const_mul (3 / (2 * K))),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hdi.const_mul 2) (hli.const_mul Q),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← hmi.2, ← (hprim v ⟨huv, le_rfl⟩).2, hru, hrv] at hbound
  have hE := boundary_radial_energy_le h hu0 huv hvT
  have hK : 0 < K := by linarith only [h.K_ge_one]
  calc
    _ = amplitude h s ^ 2 * (1 / (2 * a)) / (4 * K) := by ring
    _ ≤ _ := hbound
    _ ≤ S.m s v - S.m s u + (3 / (2 * K)) *
        (2 * chartScalarEnergy S T + Q * (2 * a - a)) := by gcongr
    _ = _ := by dsimp [Q]; field_simp; ring

/-- Explicit coefficient of the observation error in the annular mass
estimate; it depends only on `K`. Paper `e1a0fd5`, lines 1831–1836. -/
@[expose] noncomputable def amplitudeMassErrorConstant (K : ℝ) : ℝ :=
  (3 / (2 * K)) * (2 + K + radialScalarErrorConstant K ^ 2 / 1024)

/-- The first displayed amplitude/mass inequality, with its exact coercive
coefficient and an explicit K-only error constant. Paper `e1a0fd5`,
`eq:observability-amplitude-mass-bound`, lines 1831–1836. -/
theorem amplitude_mass_bound {b T K P s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b) :
    amplitude h s ^ 2 / (8 * K * (32 * P)) ≤
      P + amplitudeMassErrorConstant K * chartScalarEnergy S T := by
  obtain ⟨u, v, hu, huv, hv, hru, hrv⟩ := exists_annulus_labels h hs
    (show 0 < 32 * P by positivity) (by linarith only [hfit])
  have hb := amplitude_annular_mass_bound h hP hT hmass hs hlate
    (show 0 < 32 * P by positivity) le_rfl hu huv hv hru hrv
  have hmu := (h.signs s u (h.out_subset hs hu (huv.trans hv)
    ⟨by simp, le_rfl, le_rfl⟩)).2.2
  change 0 ≤ 2 * S.m s u / S.r s u at hmu
  rw [hru] at hmu
  have hnon : 0 ≤ S.m s u := by
    have hh := (le_div_iff₀ (show 0 < 32 * P by positivity)).mp hmu
    linarith only [hh]
  have hmv := hmass s v (h.out_subset hs (hu.trans huv) hv ⟨by simp, le_rfl, le_rfl⟩)
  have heq : (3 / (2 * K)) * (2 * chartScalarEnergy S T +
      (K + radialScalarErrorConstant K ^ 2 * P ^ 2 / (32 * P) ^ 2) *
        chartScalarEnergy S T) = amplitudeMassErrorConstant K * chartScalarEnergy S T := by
    unfold amplitudeMassErrorConstant
    field_simp [hP.ne']
    ring
  rw [heq] at hb
  linarith only [hb, hnon, hmv]

/-- Explicit squared amplitude constant after using `E ≤ P`.
Paper `e1a0fd5`, lines 1831–1836. -/
@[expose] noncomputable def amplitudeMassSquareConstant (K : ℝ) : ℝ :=
  256 * K * (1 + amplitudeMassErrorConstant K)

/-- The second displayed amplitude bound in squared form, with a K-only
constant. The energy premise follows from small observation and `P=(K+2)M`.
Paper `e1a0fd5`, `eq:observability-amplitude-mass-bound`, lines 1831–1836. -/
theorem amplitude_sq_mass_bound {b T K P s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) :
    amplitude h s ^ 2 ≤ amplitudeMassSquareConstant K * P ^ 2 := by
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hC : 0 ≤ amplitudeMassErrorConstant K := by
    unfold amplitudeMassErrorConstant
    positivity
  have hb := amplitude_mass_bound h hP hT hmass hs hlate hfit
  have hh := mul_le_mul_of_nonneg_left hE hC
  have hb' : amplitude h s ^ 2 / (8 * K * (32 * P)) ≤
      (1 + amplitudeMassErrorConstant K) * P := by nlinarith only [hb, hh]
  have hf := (div_le_iff₀ (show 0 < 8 * K * (32 * P) by positivity)).mp hb'
  convert hf using 1
  unfold amplitudeMassSquareConstant
  ring

/-- The actual amplitude has size at most a K-only multiple of `P`.
Paper `e1a0fd5`, lines 1831–1836. -/
theorem amplitude_abs_mass_bound {b T K P s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s) (hfit : 64 * P ≤ b)
    (hE : chartScalarEnergy S T ≤ P) :
    |amplitude h s| ≤ Real.sqrt (amplitudeMassSquareConstant K) * P := by
  have hh := amplitude_sq_mass_bound h hP hT hmass hs hlate hfit hE
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hC : 0 ≤ amplitudeMassSquareConstant K := by
    unfold amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  have hsqrt := Real.sq_sqrt hC
  have ht : 0 ≤ Real.sqrt (amplitudeMassSquareConstant K) * P := by positivity
  have ha := sq_abs (amplitude h s)
  nlinarith only [hh, hsqrt, ha, abs_nonneg (amplitude h s), ht]

end PropA4
end AcExtensionPrinciple

end
