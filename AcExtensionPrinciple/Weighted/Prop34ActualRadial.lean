module

public import AcExtensionPrinciple.Weighted.Prop34ActualSource
public import AcExtensionPrinciple.Weighted.Prop34ActualL1

/-!
# The full radial source of the actual incoming remainder

Paper `e1a0fd5`, lines 1278–1287 and 1305–1318. All radial
integrals start at the axis, before any incoming energy cutoff.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The radial integrand of the transported initial part is integrable
on every entire proper cone. Paper `e1a0fd5`, lines 1090–1093 and 1278–1287. -/
theorem prop34_initial_radial_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntervalIntegrable (fun s => S.r u s * (weightedIncomingAmplitude S u s *
      S.renormalizedInitial (transportedRadialDatum ui S) ui u s)) volume u 0 := by
  let D := h.sectionThreeDatumInputs
  obtain ⟨M, hM, hcoeff⟩ := h.section3_uniform_coefficients
  have hin := (D.splitting_cone_integrable h hu hu0).2.1
  have hr := (h.cone_primitive_fields_measurable hu hu0).1
  have ha : AEStronglyMeasurable (weightedIncomingAmplitude S u)
      (volume.restrict (Ioc u 0)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (h.weightedIncomingAmplitude_continuousOn hu hu0).aestronglyMeasurable
      measurableSet_Ioo
  have hi := (D.splitting_fields_measurable h hu hu0).1
  have hI : IntegrableOn (fun s => S.r u s * (weightedIncomingAmplitude S u s *
      S.renormalizedInitial (transportedRadialDatum ui S) ui u s)) (Ioc u 0) := by
    apply (hin.norm.const_mul ((-u) * (2 * M))).mono' (hr.mul (ha.mul hi))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hp : (u, s) ∈ pastTriangle ui := ⟨hu, hu0, hs.1.le, hs.2⟩
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (h.r_pos hp hs.1)]
    have hb := (hcoeff (u, s) hp).2.1
    have hrb : S.r u s ≤ -u := (h.radius_bounds hp).2.trans (by linarith [hs.2])
    simpa only [Real.norm_eq_abs, mul_assoc, weightedIncomingAmplitude] using mul_le_mul_of_nonneg_right
      (mul_le_mul hrb hb (abs_nonneg _) (by linarith))
        (abs_nonneg (S.renormalizedInitial (transportedRadialDatum ui S) ui u s))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu0.le).mpr hI

/-- The actual remainder representative has an integrable full radial
integrand on every proper cone. Paper `e1a0fd5`, lines 1292–1318. -/
theorem prop34_actualRemainder_radial_integrable {u₀ U u : ℝ} {R : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hu : u ∈ Icc u₀ U)
    (heR : EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      R (weightedOffAxisStrip u₀ U)) :
    IntervalIntegrable (fun s => S.r u s * (weightedIncomingAmplitude S u s * R (u, s)))
      volume u 0 := by
  have hui := hi.trans hu.1
  have hu0 := hu.2.trans_lt hU
  have hj := h.sectionThreeDatumInputs.radius_interaction_source_integrable h hui hu0
  have hji : IntervalIntegrable (fun s => S.r u s * (weightedIncomingAmplitude S u s *
      S.renormalizedDerivative (transportedRadialDatum ui S) u s)) volume u 0 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hu0.le).mpr
    apply hj.congr
    exact ae_of_all _ (fun _ => by dsimp [weightedIncomingAmplitude]; ring)
  have hiI := h.prop34_initial_radial_integrable hui hu0
  apply (hji.sub hiI).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hu0.le] at hs
  have he := heR (x := (u, s)) ⟨hu.1, hu.2, hs.1, hs.2⟩
  dsimp only at he
  rw [← he]
  dsimp only [SSFields.renormalizedRemainder]
  ring

/-- The actual source minus T j_in is exactly the full radial operator
of the actual incoming remainder, at every off-axis point.
Paper `e1a0fd5`, lines 1278–1287 and 1305–1318. -/
theorem prop34_actualSource_remainder_radial {u₀ U : ℝ} {R H : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0)
    (heR : EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      R (weightedOffAxisStrip u₀ U))
    (heH : EqOn (fun p => S.renormalizedInteraction p.1 p.2 / S.r p.1 p.2)
      H (weightedOffAxisStrip u₀ U)) :
    EqOn (fun p => H p - weightedRadialOperator S
      (fun q => S.renormalizedInitial (transportedRadialDatum ui S) ui q.1 q.2) p)
      (weightedRadialOperator S R) (weightedOffAxisStrip u₀ U) := by
  intro p hp
  dsimp only
  have hui := hi.trans hp.1
  have hu0 := hp.2.1.trans_lt hU
  have hj := h.sectionThreeDatumInputs.radius_interaction_source_integrable h hui hu0
  have hji : IntervalIntegrable (fun s => S.r p.1 s * (weightedIncomingAmplitude S p.1 s *
      S.renormalizedDerivative (transportedRadialDatum ui S) p.1 s)) volume p.1 p.2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hp.2.2.1.le).mpr
    apply (hj.mono_set (Ioc_subset_Ioc_right hp.2.2.2)).congr
    exact ae_of_all _ (fun _ => by dsimp [weightedIncomingAmplitude]; ring)
  have hii := (h.prop34_initial_radial_integrable hui hu0).mono_set
    (show uIcc p.1 p.2 ⊆ uIcc p.1 0 by
      rw [uIcc_of_le hp.2.2.1.le, uIcc_of_le hu0.le]
      exact Icc_subset_Icc_right hp.2.2.2)
  have heT : weightedRadialOperator S
      (fun q => S.renormalizedDerivative (transportedRadialDatum ui S) q.1 q.2) p = H p := by
    rw [← heH hp]
    have he := h.lemma31.axis_primitive p.1 p.2 hui hu0 hp.2.2.1 hp.2.2.2
    simpa only [weightedRadialOperator, one_div, weightedIncomingAmplitude,
      mul_assoc] using he.symm
  rw [← heT, weightedRadialOperator_sub_of_integrable S _ _ p hji hii]
  unfold weightedRadialOperator
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hp.2.2.1.le] at hs
  have he := heR (x := (p.1, s)) ⟨hp.1, hp.2.1, hs.1, hs.2.trans hp.2.2.2⟩
  dsimp only at he ⊢
  rw [← he]
  rfl

/-- The radial subtraction identity needs only integrability on almost
every full cone. For identification, the first input is the actual
L¹ remainder and the second is the constructed L² remainder.
Paper `e1a0fd5`, lines 1305–1318. -/
theorem prop34_radial_sub_ae_of_integrable_rays {u₀ U : ℝ} {R W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hR : Measurable R) (hW : Measurable W)
    (hIR : ∀ᵐ u ∂volume.restrict (Icc u₀ U), IntervalIntegrable
      (fun s => S.r u s * (weightedIncomingAmplitude S u s * R (u, s))) volume u 0)
    (hIW : ∀ᵐ u ∂volume.restrict (Icc u₀ U), IntervalIntegrable
      (fun s => S.r u s * (weightedIncomingAmplitude S u s * W (u, s))) volume u 0) :
    (fun p => weightedRadialOperator S R p - weightedRadialOperator S W p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (fun p => R p - W p) := by
  obtain ⟨TR, hTR, heTR⟩ := h.weightedRadialOperator_measurable_strip hi hU hR
  obtain ⟨TW, hTW, heTW⟩ := h.weightedRadialOperator_measurable_strip hi hU hW
  obtain ⟨TD, hTD, heTD⟩ := h.weightedRadialOperator_measurable_strip hi hU (hR.sub hW)
  apply ae_weighted_triangle_of_strip
  rw [weightedOffAxisStrip_eq_iUnion, ae_restrict_iUnion_iff]
  intro q
  let b := min U (q.1.1 : ℝ)
  let c := (q.1.2 : ℝ)
  have hray : ∀ᵐ u ∂volume.restrict (Icc u₀ b),
      ∀ v ∈ Icc c 0, TR (u, v) - TW (u, v) = TD (u, v) := by
    have hs : Icc u₀ b ⊆ Icc u₀ U := Icc_subset_Icc_right (min_le_left _ _)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hIR,
      ae_restrict_of_ae_restrict_of_subset hs hIW, ae_restrict_mem measurableSet_Icc]
      with u huR huW hu
    intro v hv
    have huv := hu.2.trans_lt (q.2.2.1.trans_le hv.1)
    have hu0 := hu.2.trans (min_le_left _ _) |>.trans hU.le
    have hp : (u, v) ∈ weightedOffAxisStrip u₀ U :=
      ⟨hu.1, hu.2.trans (min_le_left _ _), huv, hv.2⟩
    have hseg : uIcc u v ⊆ uIcc u 0 := by
      rw [uIcc_of_le huv.le, uIcc_of_le hu0]
      exact Icc_subset_Icc_right hv.2
    rw [← heTR hp, ← heTW hp, ← heTD hp]
    exact weightedRadialOperator_sub_of_integrable S R W (u, v)
      (huR.mono_set hseg) (huW.mono_set hseg)
  have he := ae_eq_rectangle_of_outgoing (hTR.sub hTW) hTD hray
  filter_upwards [he, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp hpI
  have hpS : p ∈ weightedOffAxisStrip u₀ U :=
    ⟨hpI.1.1, hpI.1.2.trans (min_le_left _ _),
      hpI.1.2.trans_lt (q.2.2.1.trans_le hpI.2.1), hpI.2.2⟩
  change TR p - TW p = TD p at hp
  rw [heTR hpS, heTW hpS]
  exact hp.trans (heTD hpS).symm

end AcExtensionPrinciple.StandingFull

end
