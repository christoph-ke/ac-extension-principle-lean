module

public import AcExtensionPrinciple.Integration.SectionThree
public import AcExtensionPrinciple.Weighted.Prop35Inputs

/-!
# Admissibility of the actual frozen initial remainder

Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124 and
1275–1276. Transfer the proved Lemma 3.2 energy from its incoming transport
representative to the actual radial derivative, then choose a measurable
initial representative for the frozen L² construction.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming representative and actual radial derivative give the same
remainder on each cone almost everywhere. Paper `e1a0fd5`,
`eq:renormalized-splitting`, lines 1088–1092 and 1275–1276. -/
theorem renormalizedRemainder_actual_eq_ae {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    S.renormalizedRemainder (transportedRadialDatum ui S) ui u
      =ᵐ[volume.restrict (Ioc u 0)] S.renormalizedRemainder S.radialDatumDerivative ui u := by
  have hi := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_left hu)
    (h.transportedRadialDatum_radial_eq le_rfl h.initial_negative)
  filter_upwards [h.transportedRadialDatum_radial_eq hu hu0, hi] with v hv hvi
  simp only [SSFields.renormalizedRemainder, SSFields.renormalizedInitial,
    SSFields.renormalizedDerivative, Renormalized.renormalizedDerivativeOf, hv, hvi]

/-- The actual remainder's initial energy is integrable on every proper
cone, with no square-integrability assumption on the initial datum.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124. -/
theorem renormalizedRemainder_actual_energy_integrable {u : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (S.renormalizedRemainderEnergy S.radialDatumDerivative ui u) (Ioc u 0) := by
  obtain ⟨C, _, hC⟩ := h.lemma32.energy_uniform
  apply (hC u hu hu0).1.congr
  filter_upwards [h.renormalizedRemainder_actual_eq_ae hu hu0] with v hv
  simp only [SSFields.renormalizedRemainderEnergy, hv]

/-- The literal I₀ lower integral is finite for the actual remainder.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124 and 1275. -/
theorem renormalizedRemainder_actual_initial_energy_lt_top {u₀ : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) :
    (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
        ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤ := by
  have hE := h.renormalizedRemainder_actual_energy_integrable hi hu₀
  change (∫⁻ v in Ioc u₀ 0,
    ENNReal.ofReal (S.renormalizedRemainderEnergy S.radialDatumDerivative ui u₀ v)) < ⊤
  calc
    _ ≤ ∫⁻ v in Ioc u₀ 0, ‖S.renormalizedRemainderEnergy S.radialDatumDerivative ui u₀ v‖ₑ := by
      apply lintegral_mono
      intro v
      dsimp only
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ < ⊤ := hasFiniteIntegral_iff_enorm.mp hE.hasFiniteIntegral

/-- A measurable initial representative with finite weighted energy exists
for the actual remainder. This is the admissible initial datum for the
frozen finite-M_U construction. Paper `e1a0fd5`, lines 1275–1276. -/
theorem exists_measurable_frozen_initial {u₀ : ℝ} (hi : ui ≤ u₀) (hu₀ : u₀ < 0) :
    ∃ J₀ : ℝ → ℝ, Measurable J₀ ∧
      S.renormalizedRemainder S.radialDatumDerivative ui u₀
        =ᵐ[volume.restrict (Ioc u₀ 0)] J₀ ∧
      (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤ := by
  let R := S.renormalizedRemainder S.radialDatumDerivative ui u₀
  have hm : AEStronglyMeasurable R (volume.restrict (Ioc u₀ 0)) :=
    (h.small_cone_remainder_integrable hi hu₀).aestronglyMeasurable
  refine ⟨hm.mk R, hm.measurable_mk, hm.ae_eq_mk, ?_⟩
  have he : (fun v => ENNReal.ofReal (S.r u₀ v * (hm.mk R v) ^ 2 /
      ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) =ᵐ[volume.restrict (Ioc u₀ 0)]
        (fun v => ENNReal.ofReal (S.r u₀ v * R v ^ 2 /
          ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) := by
    filter_upwards [hm.ae_eq_mk] with v hv
    rw [hv]
  rw [lintegral_congr_ae he]
  exact h.renormalizedRemainder_actual_initial_energy_lt_top hi hu₀

end AcExtensionPrinciple.StandingFull

end
