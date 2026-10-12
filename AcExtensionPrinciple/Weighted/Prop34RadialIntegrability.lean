module

public import AcExtensionPrinciple.Weighted.Prop34RadialAE

/-!
# Full-cone integrability for the actual radial L² operator

Paper `e1a0fd5`, lines 1278–1287. Finite N_U supplies full outgoing
L¹ rays; late smallness bounds the incoming amplitude on those rays.
The full radial integrals can consequently be added and subtracted.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The remainder density has a fixed positive lower bound on the entire
class domain. Paper `e1a0fd5`, line 1150 and lines 1278–1287. -/
theorem weightedRemainderDensity_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ weightedRemainderDensity S p := by
  have hg : 0 < 1 - S.mu p.1 p.2 := sub_pos.mpr (h.mu_bounds hp).2
  have hg1 : 1 - S.mu p.1 p.2 ≤ 1 := by linarith [(h.mu_bounds hp).1]
  have hden : (1 - S.mu p.1 p.2) ^ 2 * S.lam p.1 p.2 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul
        (by nlinarith [sq_nonneg (1 - (1 - S.mu p.1 p.2))])
        (h.lam_bounds hp).2 (h.lam_pos hp).le (by norm_num)
      _ = 1 := one_mul _
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hg) (h.lam_pos hp))).mpr
  calc
    _ ≤ Real.exp (-Bstar ui S) * 1 :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = Real.exp (-Bstar ui S) := mul_one _
    _ ≤ _ := h.neg_nu_lower hp

/-- Finite N_U gives actual unweighted L¹ on the full proper triangle.
Paper `e1a0fd5`, lines 1278–1287. -/
theorem weighted_remainder_integrableOn_of_energy {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W)
    (henergy : weightedRemainderNormSq S u₀ U W < ⊤) :
    IntegrableOn W (weightedTruncatedDomain u₀ U) := by
  have hL := h.weighted_remainder_l1_lt_top_of_energy hi hU hW henergy
  let c := Real.exp (-Bstar ui S)
  have hc : 0 < c := Real.exp_pos _
  refine ⟨hW.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  simp only [Real.enorm_eq_ofReal_abs]
  calc
    _ ≤ ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (weightedRemainderDensity S p * |W p|) := by
      apply setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
      intro p hp
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      apply ENNReal.ofReal_le_ofReal
      have hb := mul_le_mul_of_nonneg_right
        (h.weightedRemainderDensity_lower (weightedTruncatedDomain_subset_triangle hi hU hp))
        (abs_nonneg (W p))
      calc
        _ = c⁻¹ * (c * |W p|) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    _ = ENNReal.ofReal c⁻¹ * weightedRemainderL1 S u₀ U W :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL

/-- Finite N_U and late smallness supply integrability of the full radial
integrand on almost every entire outgoing cone, including radii below
every later cutoff. Paper `e1a0fd5`, lines 1278–1287. -/
theorem weighted_radial_integrand_integrable_ae {u₀ U δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W)
    (henergy : weightedRemainderNormSq S u₀ U W < ⊤)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    ∀ᵐ u ∂volume.restrict (Icc u₀ U), IntervalIntegrable
      (fun a => S.r u a * (weightedIncomingAmplitude S u a * W (u, a))) volume u 0 := by
  let D := weightedTruncatedDomain u₀ U
  have hD := measurableSet_weightedTruncatedDomain u₀ U
  have hWI := h.weighted_remainder_integrableOn_of_energy hi hU hW henergy
  have hH : Integrable (D.indicator W) volume := (integrable_indicator_iff hD).mpr hWI
  rw [Measure.volume_eq_prod] at hH
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_r
  obtain ⟨A, hA, heA⟩ := h.weighted_exists_measurable_amplitude_strip hi hU
  obtain ⟨C, hC⟩ := (isCompact_weightedTruncatedDomain u₀ U).exists_bound_of_continuousOn
    (h.regularCenter.continuous_r.mono (weightedTruncatedDomain_subset_triangle hi hU))
  filter_upwards [ae_restrict_of_ae hH.prod_right_ae, ae_restrict_mem measurableSet_Icc]
    with u hu huI
  have hu0 : u ≤ 0 := huI.2.trans hU.le
  have hWu : IntegrableOn (fun a => W (u, a)) (Ioc u 0) := by
    apply (hu.mono_measure Measure.restrict_le_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact indicator_of_mem (show (u, a) ∈ D from ⟨huI.1, huI.2, ha.1.le, ha.2⟩) W
  let K := fun a => R (u, a) * A (u, a)
  have hK : Measurable K := (hR.mul hA).comp (measurable_const.prodMk measurable_id)
  have hKbound : ∀ᵐ a ∂volume.restrict (Ioc u 0), ‖K a‖ ≤ max C 0 * ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    have hpD : (u, a) ∈ D := ⟨huI.1, huI.2, ha.1.le, ha.2⟩
    have hpS : (u, a) ∈ weightedOffAxisStrip u₀ U := ⟨huI.1, huI.2, ha.1, ha.2⟩
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hpD
    have hAmp : |weightedIncomingAmplitude S u a| ≤ ε :=
      (le_add_of_nonneg_left (abs_nonneg (S.r u a / S.lam u a * S.dvphi u a))).trans
        (hsmall (u, a) hpt huI.1).2
    change ‖R (u, a) * A (u, a)‖ ≤ _
    rw [← heR hpD, ← heA hpS, norm_mul, Real.norm_eq_abs (weightedIncomingAmplitude S u a)]
    exact mul_le_mul ((hC (u, a) hpD).trans (le_max_left _ _)) hAmp
      (abs_nonneg _) (le_max_right _ _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu0]
  apply (hWu.bdd_mul hK.aestronglyMeasurable hKbound).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
  have hpD : (u, a) ∈ D := ⟨huI.1, huI.2, ha.1.le, ha.2⟩
  have hpS : (u, a) ∈ weightedOffAxisStrip u₀ U := ⟨huI.1, huI.2, ha.1, ha.2⟩
  dsimp only [K]
  rw [← heR hpD, ← heA hpS]
  ring

end AcExtensionPrinciple.StandingFull

end
