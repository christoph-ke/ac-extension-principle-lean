module

public import AcExtensionPrinciple.Renormalized.ClassMeasurability
public import AcExtensionPrinciple.Renormalized.ClassUniformBounds
public import AcExtensionPrinciple.Renormalized.ClassHardyPullback
public import AcExtensionPrinciple.Renormalized.ClassL1

/-!
# Discharging the Section 3 cone L¹ premises

Paper `e1a0fd5`, `equations.tex` lines 1072–1124.
Only the three stated Lemma 2.2 conclusions remain as inputs.
Those inputs are supplied by `StandingFull.sectionThreeDatumInputs` in
`Integration/DatumRepresentative.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SectionThreeDatumInputs

variable {ui : ℝ} {S : SSFields} {q : ℝ → ℝ → ℝ}
    (D : SectionThreeDatumInputs ui S q) (h : StandingFull ui S)
include D h

/-- The radial derivative's L¹ norm is bounded by the cone variation,
without a separate majorant premise. Paper `e1a0fd5`,
`eq:renormalized-local-l1`, lines 1072–1075. -/
theorem q_cone_l1_le_variation {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal (S.lam u v * |q u v|)) ≤ S.outgoingVariation u := by
  have hP := D.outgoing_ac u hu hu0
  have he : (fun v => ENNReal.ofReal (S.lam u v * |q u v|))
      =ᵐ[volume.restrict (Ioc u 0)] (fun v => ENNReal.ofReal |deriv (S.outgoingDatum u) v|) := by
    filter_upwards [D.radial_eq u hu hu0, ae_restrict_mem measurableSet_Ioc] with v hq hv
    rw [hq]
    dsimp [SSFields.radialDatumDerivative]
    rw [abs_div, abs_of_pos (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩),
      mul_div_cancel₀ _ (ne_of_gt (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩))]
  rw [lintegral_congr_ae he]
  have hi : Integrable (fun v => |deriv (S.outgoingDatum u) v|) (volume.restrict (Ioc u 0)) := by
    simpa only [uIoc_of_le hu0.le, IntegrableOn] using hP.intervalIntegrable_deriv.abs.def'
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => abs_nonneg _)),
    ← intervalIntegral.integral_of_le hu0.le]
  have hBV : BoundedVariationOn (S.outgoingDatum u) (Icc u 0) := by
    simpa only [uIcc_of_le hu0.le] using hP.boundedVariationOn
  calc
    _ ≤ ENNReal.ofReal (S.outgoingVariation u).toReal :=
      ENNReal.ofReal_le_ofReal (integral_abs_deriv_le_variation hu0.le hBV)
    _ = _ := ENNReal.ofReal_toReal (h.outgoingVariation_ne_top hu hu0)

/-- Uniform renormalized cone L¹ bound and integrability, with only
Lemma 2.2 inputs. Paper `e1a0fd5`, `eq:renormalized-local-l1`, lines 1072–1078. -/
theorem renormalized_cone_l1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ui ≤ u → u < 0 →
      (∫⁻ v in Ioc u 0, ENNReal.ofReal |S.renormalizedDerivative q u v|) ≤
        ENNReal.ofReal C * S.outgoingVariation u ∧
      IntegrableOn (S.renormalizedDerivative q u) (Ioc u 0) := by
  obtain ⟨M, hM0, hM⟩ := h.section3_uniform_scalar_bound
  refine ⟨1 + M ^ 2, by positivity, fun u hu hu0 => ?_⟩
  have hl := (h.cone_primitive_fields_measurable hu hu0).2.1
  have hq := D.q_measurable h hu hu0
  have hb := h.renormalized_local_l1_of_hardy hu hu0
    (fun v hv => (hM (u, v) ⟨hu, hu0, hv.1.le, hv.2⟩).1)
    (hl.mul hq.norm |>.aemeasurable.ennreal_ofReal)
    (D.q_cone_l1_le_variation h hu hu0)
    (h.scalar_cone_hardy_of_ac_datum hu hu0 (D.outgoing_ac u hu hu0))
  exact ⟨hb, h.renormalized_integrable_of_l1_bound hu hu0
    (D.renormalized_fields_measurable h hu hu0).1 hb⟩

/-- Initial integrability of j, transported initial integrability, and
remainder cone integrability. Paper `e1a0fd5`,
`lem:renormalized-splitting-bounds`, lines 1092–1124. -/
theorem splitting_cone_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (S.renormalizedDerivative q ui) (Ioc ui 0) ∧
    IntegrableOn (S.renormalizedInitial q ui u) (Ioc u 0) ∧
    IntegrableOn (S.renormalizedRemainder q ui u) (Ioc u 0) := by
  obtain ⟨_, _, hj⟩ := D.renormalized_cone_l1 h
  have hji := (hj ui le_rfl h.initial_negative).2
  have hinit := h.renormalizedInitial_integrable_of_domination hu hu0 h.initialGap_pos
    (fun p hp => h.kappa_bounds hp) hji (D.splitting_fields_measurable h hu hu0).1
  exact ⟨hji, hinit, StandingFull.renormalizedRemainder_integrable_of_cone_l1
    (hj u hu hu0).2 hinit⟩

/-- The weighted source `r B j` is integrable on every proper cone.
Paper `e1a0fd5`, `eq:renormalized-radial-primitive`, line 1078. -/
theorem radius_interaction_source_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (fun v => S.r u v * (S.r u v / S.nu u v * S.duphi u v) *
      S.renormalizedDerivative q u v) (Ioc u 0) := by
  obtain ⟨M, hM0, hM⟩ := h.section3_uniform_coefficients
  obtain ⟨_, _, hj⟩ := D.renormalized_cone_l1 h
  have hr := (h.cone_primitive_fields_measurable hu hu0).1
  have hn := (h.cone_primitive_fields_measurable hu hu0).2.2.1
  have hdu := (D.scalar_derivatives_measurable h hu hu0).2
  have hjm := (D.renormalized_fields_measurable h hu hu0).1
  apply ((hj u hu hu0).2.norm.const_mul ((-u) * (2 * M))).mono'
    ((hr.mul ((hr.div₀ hn).mul hdu)).mul hjm)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
  have hr0 := (h.r_pos hp hv.1).le
  have hu_nonneg : 0 ≤ -u := (neg_pos.mpr hu0).le
  have hrle : S.r u v ≤ -u := (h.radius_bounds hp).2.trans (by linarith [hv.2])
  simp only [Real.norm_eq_abs]
  change |S.r u v * (S.r u v / S.nu u v * S.duphi u v) * S.renormalizedDerivative q u v| ≤
    ((-u) * (2 * M)) * |S.renormalizedDerivative q u v|
  rw [abs_mul, abs_mul, abs_of_nonneg hr0]
  calc
    _ ≤ (-u) * (2 * M) * |S.renormalizedDerivative q u v| := by
      gcongr
      exact (hM (u, v) hp).2.1
    _ = _ := by ring

end SectionThreeDatumInputs

end AcExtensionPrinciple

end
