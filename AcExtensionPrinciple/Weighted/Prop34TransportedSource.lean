module

public import AcExtensionPrinciple.Weighted.Prop34FixedPoint
public import AcExtensionPrinciple.Integration.WeightedDatum

/-!
# The transported initial source in the actual weighted source space

Paper `e1a0fd5`, `eq:transported-radial-estimate` and
`eq:constructed-remainder-bound`, lines 1171–1202 and 1278–1287.
The initial L¹ datum supplies the finite source energy, independently of U.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A measurable initial datum has a jointly measurable transported
representative on each proper triangle. Paper `e1a0fd5`,
`eq:renormalized-initial-transport`, lines 1090–1093 and 1278–1282. -/
theorem weightedTransportedDatum_exists_measurable {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {f : ℝ → ℝ} (hf : Measurable f) :
    ∃ J : ℝ × ℝ → ℝ, Measurable J ∧
      EqOn (weightedTransportedDatum ui S f) J (weightedTruncatedDomain u₀ U) := by
  obtain ⟨K, hK, heK⟩ := h.weighted_exists_measurable_kappa hi hU
  obtain ⟨Ki, hKi, heKi⟩ := h.weighted_exists_measurable_kappa le_rfl h.initial_negative
  refine ⟨fun p => (Ki (ui, p.2) / K p) * f p.2,
    ((hKi.comp (measurable_const.prodMk measurable_snd)).div hK).mul
      (hf.comp measurable_snd), ?_⟩
  intro p hp
  have hpi : (ui, p.2) ∈ weightedTruncatedDomain ui ui :=
    ⟨le_rfl, le_rfl, hi.trans (hp.1.trans hp.2.2.1), hp.2.2.2⟩
  simp only [weightedTransportedDatum, ← heKi hpi, ← heK hp]

/-- T j_in has a jointly measurable source representative. Its actual
weighted L² energy is bounded by Lemma 3.3 with the original L¹ datum.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1171–1202. -/
theorem exists_weightedTransportedSourceL2 {u₀ U δ : ℝ} {f : ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hf : Measurable f)
    (hfi : IntegrableOn f (Ioc ui 0))
    (hsmall : ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 →
      S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) :
    ∃ F₀ : WeightedSourceL2 S u₀ U,
      (F₀ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (weightedTransportedDatum ui S f) ∧
      ‖F₀‖ₑ ^ 2 ≤ ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 4 *
        ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
          (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ^ 2 := by
  obtain ⟨J, hJ, heJ⟩ := h.weightedTransportedDatum_exists_measurable hi hU hf
  obtain ⟨F, hF, heF⟩ := h.weightedRadialOperator_exists_measurable_ae hi hU hJ
  have heT : weightedRadialOperator S J
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (weightedTransportedDatum ui S f) := by
    filter_upwards [ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)] with p hp
    unfold weightedRadialOperator
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.2.2.1] at hs
    dsimp only
    rw [← heJ (x := (p.1, s)) ⟨hp.1, hp.2.1, hs.1, hs.2.trans hp.2.2.2⟩]
  have he : F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      weightedRadialOperator S (weightedTransportedDatum ui S f) := heF.symm.trans heT
  have hb := h.lemma33_transported_sq_of_late_mass_bound hi hU hδ hf.aemeasurable hsmall
  have hs : weightedSourceNormSq S u₀ U F =
      weightedSourceNormSq S u₀ U
        (weightedRadialOperator S (weightedTransportedDatum ui S f)) := by
    apply lintegral_congr_ae
    filter_upwards [he] with p hp
    rw [hp]
  have hL : (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) < ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      hasFiniteIntegral_iff_enorm.mp hfi.hasFiniteIntegral
  have hmem : MemLp F 2 (weightedSourceMeasure S u₀ U) :=
    (h.memLp_weighted_source_iff hi hU hF).mpr (by
      rw [hs]
      exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (by simpa only [pow_two] using ENNReal.mul_lt_top hL hL)))
  have heLp : (hmem.toLp F : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F :=
    (h.ae_weightedSourceMeasure_iff hi hU).mp hmem.coeFn_toLp
  refine ⟨hmem.toLp F, heLp.trans he, ?_⟩
  rw [Lp.enorm_toLp, h.eLpNorm_weighted_source_eq hi hU hF, weightedSourceNorm_sq, hs]
  exact hb

/-- The actual Section 3 transported initial source is an element of
the weighted source quotient, with no measurability or integrability
premise beyond the standing solution and late mass bound.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1171–1202. -/
theorem exists_actual_weightedTransportedSourceL2 {u₀ U δ : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3)
    (hsmall : ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 →
      S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) :
    ∃ F₀ : WeightedSourceL2 S u₀ U,
      (F₀ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S
          (fun p => S.renormalizedInitial (transportedRadialDatum ui S) ui p.1 p.2) ∧
      ‖F₀‖ₑ ^ 2 ≤ ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 4 *
        ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
          (∫⁻ a in Ioc ui 0, ENNReal.ofReal
            |S.renormalizedDerivative (transportedRadialDatum ui S) ui a|) ^ 2 := by
  let f := S.renormalizedDerivative (transportedRadialDatum ui S) ui
  have hfi : IntegrableOn f (Ioc ui 0) := h.lemma32.initial_integrable
  let hf := hfi.aestronglyMeasurable
  have hmk : IntegrableOn (hf.mk f) (Ioc ui 0) := hfi.congr hf.ae_eq_mk
  obtain ⟨F₀, heF₀, hb⟩ := h.exists_weightedTransportedSourceL2 hi hU hδ
    hf.measurable_mk hmk hsmall
  have heL : (∫⁻ a in Ioc ui 0, ENNReal.ofReal |hf.mk f a|) =
      ∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a| := by
    apply lintegral_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha
    rw [ha]
  refine ⟨F₀, ?_, by simpa only [heL] using hb⟩
  apply heF₀.trans
  filter_upwards [ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)] with p hp
  rw [← weightedTransportedDatum_eq_renormalizedInitial]
  unfold weightedRadialOperator
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : uIoc p.1 p.2 ⊆ Ioc ui 0 := by
    rw [uIoc_of_le hp.2.2.1]
    exact fun s hs => ⟨(hi.trans hp.1).trans_lt hs.1, hs.2.trans hp.2.2.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hf.ae_eq_mk] with s hs
  dsimp only [f] at hs
  simp only [weightedTransportedDatum, f, hs]

end AcExtensionPrinciple.StandingFull

end
