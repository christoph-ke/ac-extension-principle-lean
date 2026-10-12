module

public import AcExtensionPrinciple.Renormalized.ClassHardyPullback
public import AcExtensionPrinciple.Renormalized.ClassMeasurability
public import AcExtensionPrinciple.Renormalized.ClassUniformBounds
public import AcExtensionPrinciple.Renormalized.ClassL1
public import AcExtensionPrinciple.ACDatum.Propagation

/-!
# Unconditional cone inputs for Proposition 3.5

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1333–1350.
Only outgoing AC is needed here. In particular, no choice of an incoming
transport representative on exceptional initial labels is required.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual radial derivative and scalar amplitude are measurable on
each cone. Paper `e1a0fd5`, lines 555–558, 1069–1078 and 1333–1350. -/
theorem small_cone_fields_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.radialDatumDerivative u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.dvphi u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.renormalizedDerivative S.radialDatumDerivative u)
      (volume.restrict (Ioc u 0)) := by
  obtain ⟨hr, hl, _, _, hphi, _⟩ := h.cone_primitive_fields_measurable hu hu0
  have hq : AEStronglyMeasurable (S.radialDatumDerivative u)
      (volume.restrict (Ioc u 0)) :=
    (measurable_deriv (S.outgoingDatum u)).aestronglyMeasurable.div₀ hl
  have hPac : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0 :=
    h.normalized_datum_ac_out hu hu0
  have hP : AEStronglyMeasurable (S.outgoingDatum u) (volume.restrict (Ioc u 0)) :=
    (hPac.continuousOn.mono
    (by rw [uIcc_of_le hu0.le]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_Ioc
  have hdvpsi : AEStronglyMeasurable (S.dvpsi u) (volume.restrict (Ioc u 0)) := by
    apply (hl.mul hP).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    dsimp [SSFields.outgoingDatum]
    exact mul_div_cancel₀ _ (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩).ne'
  have hdv : AEStronglyMeasurable (S.dvphi u) (volume.restrict (Ioc u 0)) :=
    (hdvpsi.sub (hl.mul hphi)).div₀ hr
  have hA := (hr.div₀ hl).mul hdv
  have hm := (h.cone_geometric_fields_measurable hu hu0).1
  exact ⟨hq, hdv, ((aestronglyMeasurable_const.sub hm).mul hl).mul
    (hq.sub ((hA.pow 3).div₀ hr))⟩

/-- Hardy supplies both genuine integrability and the real integral bound
used for cubic absorption. Paper `e1a0fd5`, `eq:scalar-radial-hardy`,
lines 1010–1015 and 1338–1345. -/
theorem small_cone_hardy_inputs {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntervalIntegrable (fun v => S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) volume u 0 ∧
    (∫ v in u..0, S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) ≤ (S.outgoingVariation u).toReal := by
  let g := fun v => S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|
  obtain ⟨hr, hl, _⟩ := h.cone_primitive_fields_measurable hu hu0
  have hdv := (h.small_cone_fields_measurable hu hu0).2.1
  have hg : AEStronglyMeasurable g (volume.restrict (Ioc u 0)) :=
    (hl.div₀ hr).mul (((hr.div₀ hl).mul hdv).norm)
  have hpos : ∀ᵐ v ∂volume.restrict (Ioc u 0), 0 ≤ g v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    exact mul_nonneg (div_nonneg (h.lam_pos hp).le (h.r_pos hp hv.1).le) (abs_nonneg _)
  have hh : (∫⁻ v in Ioc u 0, ENNReal.ofReal (g v)) ≤ S.outgoingVariation u := by
    simpa only [g, div_mul_eq_mul_div] using
      h.scalar_cone_hardy_of_ac_datum hu hu0 (h.normalized_datum_ac_out hu hu0)
  have hi : IntegrableOn g (Ioc u 0) := by
    refine ⟨hg, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    have he : (fun v => ‖g v‖ₑ) =ᵐ[volume.restrict (Ioc u 0)]
        (fun v => ENNReal.ofReal (g v)) := by
      filter_upwards [hpos] with v hv
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hv]
    rw [lintegral_congr_ae he]
    exact hh.trans_lt (lt_top_iff_ne_top.mpr (h.outgoingVariation_ne_top hu hu0))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hu0.le).mpr hi, ?_⟩
  have hb := ENNReal.toReal_mono (h.outgoingVariation_ne_top hu hu0) hh
  rw [← ofReal_integral_eq_lintegral_ofReal hi hpos,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hpos),
    ← intervalIntegral.integral_of_le hu0.le] at hb
  exact hb

/-- The actual renormalized derivative is integrable on every proper cone.
Paper `e1a0fd5`, `eq:renormalized-local-l1`, lines 1072–1078 and 1340–1350. -/
theorem small_cone_renormalized_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (S.renormalizedDerivative S.radialDatumDerivative u) (Ioc u 0) := by
  have hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0 :=
    h.normalized_datum_ac_out hu hu0
  have hl := (h.cone_primitive_fields_measurable hu hu0).2.1
  have hq := (h.small_cone_fields_measurable hu hu0).1
  have hqV : (∫⁻ v in Ioc u 0,
      ENNReal.ofReal (S.lam u v * |S.radialDatumDerivative u v|)) ≤
        S.outgoingVariation u := by
    have he : (fun v => ENNReal.ofReal (S.lam u v * |S.radialDatumDerivative u v|))
        =ᵐ[volume.restrict (Ioc u 0)]
          (fun v => ENNReal.ofReal |deriv (S.outgoingDatum u) v|) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      dsimp [SSFields.radialDatumDerivative]
      rw [abs_div, abs_of_pos (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩),
        mul_div_cancel₀ _ (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩).ne']
    rw [lintegral_congr_ae he]
    have hd : IntegrableOn (fun v => |deriv (S.outgoingDatum u) v|) (Ioc u 0) := by
      simpa only [uIoc_of_le hu0.le, IntegrableOn] using hP.intervalIntegrable_deriv.abs.def'
    rw [← ofReal_integral_eq_lintegral_ofReal hd (ae_of_all _ (fun _ => abs_nonneg _)),
      ← intervalIntegral.integral_of_le hu0.le]
    have hBV : BoundedVariationOn (S.outgoingDatum u) (Icc u 0) := by
      simpa only [uIcc_of_le hu0.le] using hP.boundedVariationOn
    exact (ENNReal.ofReal_le_ofReal (integral_abs_deriv_le_variation hu0.le hBV)).trans_eq
      (ENNReal.ofReal_toReal (h.outgoingVariation_ne_top hu hu0))
  obtain ⟨M, _, hM⟩ := h.section3_uniform_scalar_bound
  apply h.renormalized_integrable_of_l1_bound hu hu0
    (h.small_cone_fields_measurable hu hu0).2.2
  exact h.renormalized_local_l1_of_hardy hu hu0
    (fun v hv => (hM (u, v) ⟨hu, hu0, hv.1.le, hv.2⟩).1)
    (hl.mul hq.norm |>.aemeasurable.ennreal_ofReal) hqV
    (h.scalar_cone_hardy_of_ac_datum hu hu0 hP)

/-- The actual remainder is L¹ on every proper cone, using its explicit
initial splitting. Paper `e1a0fd5`, lines 1092–1124 and 1340–1350. -/
theorem small_cone_remainder_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (S.renormalizedRemainder S.radialDatumDerivative ui u) (Ioc u 0) := by
  have hsub : Ioc u 0 ⊆ Ioc ui 0 := Ioc_subset_Ioc_left hu
  have hki := AEStronglyMeasurable.mono_set hsub
    (h.cone_geometric_fields_measurable le_rfl h.initial_negative).2
  have hji := AEStronglyMeasurable.mono_set hsub
    (h.small_cone_fields_measurable le_rfl h.initial_negative).2.2
  have hk := (h.cone_geometric_fields_measurable hu hu0).2
  have hinit := h.renormalizedInitial_integrable_of_domination hu hu0 h.initialGap_pos
    (fun p hp => h.kappa_bounds hp)
    (h.small_cone_renormalized_integrable le_rfl h.initial_negative)
    ((hki.div₀ hk).mul hji)
  exact StandingFull.renormalizedRemainder_integrable_of_cone_l1
    (h.small_cone_renormalized_integrable hu hu0) hinit

end AcExtensionPrinciple.StandingFull

end
