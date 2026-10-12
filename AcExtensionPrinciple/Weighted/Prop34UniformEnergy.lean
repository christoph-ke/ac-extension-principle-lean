module

public import AcExtensionPrinciple.Weighted.Prop34ActualIdentification

/-!
# Uniform coercive energy of the actual remainder on proper truncations

Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236
and 1316–1318. The constructed bound is transferred by proved Kato
identification. Every constant is independent of U.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The explicit uniform energy bound, with the paper's literal I₀ and
original initial L¹ datum. Paper `e1a0fd5`,
`eq:constructed-remainder-bound`, lines 1283–1287 and 1316–1318. -/
@[expose] noncomputable def weightedCoerciveBound
    (ui : ℝ) (S : SSFields) (u₀ δ ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal 4 *
    (ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) *
      (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * (S.renormalizedRemainder S.radialDatumDerivative ui u₀ v) ^ 2 /
          ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
    ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
      (ENNReal.ofReal ((StandingFull.weightedGapConstant ui S)⁻¹ ^ 4 *
        ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
        (∫⁻ a in Ioc ui 0, ENNReal.ofReal
          |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) ^ 2))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The explicit uniform coercive bound is finite by unconditional
Lemma 3.2. Paper `e1a0fd5`, lines 1233–1236 and 1283–1287. -/
theorem weightedCoerciveBound_lt_top {u₀ δ ε : ℝ} (hi : ui ≤ u₀) (hu₀ : u₀ < 0) :
    weightedCoerciveBound ui S u₀ δ ε < ⊤ := by
  have hI := h.renormalizedRemainder_actual_initial_energy_lt_top hi hu₀
  have hL : (∫⁻ a in Ioc ui 0, ENNReal.ofReal
      |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) < ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      hasFiniteIntegral_iff_enorm.mp h.lemma32.initial_integrable.hasFiniteIntegral
  unfold weightedCoerciveBound
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply ENNReal.add_lt_top.mpr
  refine ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI, ?_⟩
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  simpa only [pow_two] using ENNReal.mul_lt_top hL hL

/-- The uniform constructed energy estimate holds for the actual incoming
remainder on every proper triangle, after Kato identification.
Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1316–1318. -/
theorem prop34_truncated_actual_energy_bound {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hbudget : ε ^ 2 ≤ (1 - 3 * δ) * weightedGapConstant ui S * (3 - δ) / 24)
    (hcontract : (3 * ε / (1 - 3 * δ)) *
      ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) < 1) :
    ∀ U : ℝ, U < 0 → weightedRemainderNormSq S u₀ U
      (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2) ≤
        weightedCoerciveBound ui S u₀ δ ε := by
  obtain ⟨J₀, hJ₀, hinitial, heJ₀, hpoints⟩ :=
    h.exists_actual_weighted_fixedPoint_with_energy hi hu₀ hδ hε hsmall hbudget
  have heInitial := (h.renormalizedRemainder_actual_eq_ae hi hu₀).trans heJ₀
  intro U hU
  obtain ⟨F₀, x, heF₀, hx, henergy⟩ := hpoints U hU
  obtain ⟨W, F, hW, hF, heW, hn, hWs, hFs, heF⟩ :=
    h.prop34_fixedPoint_representatives hi hU hδ hε hsmall J₀ hJ₀ hinitial F₀ x heF₀ hx
  obtain ⟨R, hR, heR⟩ := h.prop34_actualRemainder_measurable_strip hi hU
  obtain ⟨H, hH, heH⟩ := h.prop34_interactionSource_measurable_strip hi hU
  have heRW := h.prop34_actual_eq_constructed hi hU hδ hε hsmall hcontract J₀ hR hW hH hF
    heR heW heH hWs hFs heF heInitial
  have he : (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W := by
    filter_upwards [heRW, weightedOffAxisStrip_ae u₀ U] with p hp hpS
    exact (heR hpS).trans hp
  calc
    _ = weightedRemainderNormSq S u₀ U W := by
      apply lintegral_congr_ae
      filter_upwards [he] with p hp
      rw [hp]
    _ = ‖x‖ₑ ^ 2 := hn
    _ ≤ _ := henergy

/-- The proper-triangle estimate in the actual radial derivative interface
used by the main theorem. Paper `e1a0fd5`, lines 1233–1236 and 1316–1318. -/
theorem prop34_truncated_actual_iterated_energy_bound {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hbudget : ε ^ 2 ≤ (1 - 3 * δ) * weightedGapConstant ui S * (3 - δ) / 24)
    (hcontract : (3 * ε / (1 - 3 * δ)) *
      ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) < 1) :
    ∀ U : ℝ, U < 0 →
      (∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) ≤
            weightedCoerciveBound ui S u₀ δ ε := by
  intro U hU
  obtain ⟨R, hR, heR⟩ := h.prop34_actualRemainder_measurable_strip hi hU
  have heprod : weightedRemainderNormSq S u₀ U R =
      weightedRemainderNormSq S u₀ U
        (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2) := by
    apply lintegral_congr_ae
    filter_upwards [weightedOffAxisStrip_ae u₀ U] with p hp
    have he := heR hp
    dsimp only at he
    rw [← he]
  have heiter := h.weighted_remainder_power_eq_iterated hi hU hR 2
  change weightedRemainderNormSq S u₀ U R = _ at heiter
  have heactual : (∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal
      (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) =
        weightedRemainderNormSq S u₀ U R := by
    rw [heiter]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply lintegral_congr_ae
    filter_upwards [h.renormalizedRemainder_actual_eq_ae (hi.trans hu.1) (hu.2.trans_lt hU),
      ae_restrict_mem measurableSet_Ioc] with v hv hvI
    have he := heR (x := (u, v)) ⟨hu.1, hu.2, hvI.1, hvI.2⟩
    dsimp only at he
    rw [← he, hv]
  rw [heactual, heprod]
  exact h.prop34_truncated_actual_energy_bound hi hu₀ hδ hε hsmall hbudget hcontract U hU

end StandingFull

end AcExtensionPrinciple

end
