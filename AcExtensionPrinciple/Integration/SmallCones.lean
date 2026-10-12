module

public import AcExtensionPrinciple.Integration.SectionThree
public import AcExtensionPrinciple.Weighted.Prop35

/-!
# Discharging the cone integrability and Hardy inputs of Proposition 3.5

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, equations.tex lines 1324–1356.
The integral representative agrees almost everywhere with the raw derivative
on each cone. Only late smallness and the coercive energy conclusion remain.
Late smallness is supplied by `StandingFull.weighted_late_smallness` in
`Integration/DecayComplete.lean`; coercive energy by `StandingFull.proposition34`
in `Weighted/Prop34.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The raw renormalized derivative agrees with the transported representative on each cone.
Paper `e1a0fd5`, `eq:renormalized-derivative`, lines 1020–1021, 1072–1078. -/
theorem renormalized_raw_ae_eq {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    S.renormalizedDerivative S.radialDatumDerivative u =ᵐ[volume.restrict (Ioc u 0)]
      S.renormalizedDerivative (transportedRadialDatum ui S) u := by
  filter_upwards [h.sectionThreeDatumInputs.radial_eq u hu hu0] with v hv
  simp only [SSFields.renormalizedDerivative, hv]

/-- Initial and remainder integrability in the raw derivative representative.
Paper `e1a0fd5`, `lem:renormalized-splitting-bounds`, lines 1082–1125. -/
theorem renormalized_raw_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntegrableOn (S.renormalizedDerivative S.radialDatumDerivative ui) (Ioc ui 0) ∧
    IntegrableOn (S.renormalizedRemainder S.radialDatumDerivative ui u) (Ioc u 0) := by
  have hji := h.lemma32.initial_integrable.congr
    (h.renormalized_raw_ae_eq le_rfl h.initial_negative).symm
  have he0 := h.renormalized_raw_ae_eq le_rfl h.initial_negative
  change ∀ᵐ v ∂volume.restrict (Ioc ui 0),
    S.renormalizedDerivative S.radialDatumDerivative ui v =
      S.renormalizedDerivative (transportedRadialDatum ui S) ui v at he0
  rw [ae_restrict_iff' measurableSet_Ioc] at he0
  have heinit : S.renormalizedInitial S.radialDatumDerivative ui u
      =ᵐ[volume.restrict (Ioc u 0)] S.renormalizedInitial (transportedRadialDatum ui S) ui u := by
    filter_upwards [ae_restrict_of_ae he0, ae_restrict_mem measurableSet_Ioc] with v hv hmem
    simp only [SSFields.renormalizedInitial, hv ⟨hu.trans_lt hmem.1, hmem.2⟩]
  have heR : S.renormalizedRemainder S.radialDatumDerivative ui u
      =ᵐ[volume.restrict (Ioc u 0)] S.renormalizedRemainder (transportedRadialDatum ui S) ui u := by
    filter_upwards [h.renormalized_raw_ae_eq hu hu0, heinit] with v hv hi
    simp only [SSFields.renormalizedRemainder, hv, hi]
  exact ⟨hji, (h.sectionThreeDatumInputs.splitting_cone_integrable h hu hu0).2.2.congr heR.symm⟩

/-- The nonnegative Hardy integrand is integrable and its real integral is bounded by variation.
Paper `e1a0fd5`, `eq:scalar-radial-hardy`, lines 1010–1015, 1338–1345. -/
theorem scalar_cone_hardy_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntervalIntegrable (fun v => S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) volume u 0 ∧
    (∫ v in u..0, S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) ≤ (S.outgoingVariation u).toReal := by
  let g := fun v => S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|
  obtain ⟨hr, hl, _⟩ := h.cone_primitive_fields_measurable hu hu0
  have hdv := (h.sectionThreeDatumInputs.scalar_derivatives_measurable h hu hu0).1
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioc u 0)) :=
    (hl.div₀ hr).mul (((hr.div₀ hl).mul hdv).norm)
  have hgn : ∀ᵐ v ∂volume.restrict (Ioc u 0), 0 ≤ g v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (div_pos (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩)
      (h.r_pos (u := u) (v := v) ⟨hu, hu0, hv.1.le, hv.2⟩ hv.1)).le (abs_nonneg _)
  have hb : (∫⁻ v in Ioc u 0, ENNReal.ofReal (g v)) ≤ S.outgoingVariation u := by
    simpa only [g, div_mul_eq_mul_div] using h.lemma31.scalar_cone_hardy u hu hu0
  have hgi : IntegrableOn g (Ioc u 0) := by
    refine ⟨hgm, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simp only [Real.enorm_eq_ofReal_abs]
    have he : (fun v => ENNReal.ofReal |g v|) =ᵐ[volume.restrict (Ioc u 0)]
        (fun v => ENNReal.ofReal (g v)) := hgn.mono (fun _ hv => by
          simp only [abs_of_nonneg hv])
    rw [lintegral_congr_ae he]
    exact hb.trans_lt (lt_top_iff_ne_top.mpr (h.outgoingVariation_ne_top hu hu0))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hu0.le).mpr hgi, ?_⟩
  rw [intervalIntegral.integral_of_le hu0.le, ← ENNReal.toReal_ofReal
    (integral_nonneg_of_ae hgn), ofReal_integral_eq_lintegral_ofReal hgi hgn]
  exact ENNReal.toReal_mono (h.outgoingVariation_ne_top hu hu0) hb

/-- Proposition 3.5's exact sequence conclusion with integrability and Hardy premises discharged.
Late smallness comes from Propositions 2.7 and 2.8, and finite coercive energy is the Proposition
3.4 input. Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem integration_small_outgoing_cones_of_coercive_energy {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hε : ε ^ 2 < 1)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (henergy : (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
      ENNReal.ofReal (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  apply h.small_outgoing_cones_of_coercive_energy_and_hardy hi hu₀ hε hsmall
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h.initial_negative.le).mpr
      (h.renormalized_raw_integrable hi hu₀).1)
    (fun u hu => (h.renormalized_raw_integrable (hi.trans hu.1.le) hu.2).2)
    (fun u hu => (h.scalar_cone_hardy_integrable (hi.trans hu.1.le) hu.2).1)
    (fun u hu => (h.scalar_cone_hardy_integrable (hi.trans hu.1.le) hu.2).2) henergy

end AcExtensionPrinciple.StandingFull

end
