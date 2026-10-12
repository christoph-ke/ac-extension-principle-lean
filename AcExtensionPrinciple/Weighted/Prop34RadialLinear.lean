module

public import AcExtensionPrinciple.Weighted.Prop34RadialIntegrability

/-!
# Subtraction in the actual radial operator

Paper `e1a0fd5`, lines 1278–1287. The two full-cone integrals are
integrable for finite remainder energies. Subtraction therefore passes
through the actual radial formula on almost every proper-domain point.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- Subtraction passes through the radial integral whenever both input
integrands are integrable. Paper `e1a0fd5`, lines 1278–1287. -/
theorem weightedRadialOperator_sub_of_integrable (S : SSFields)
    (W₁ W₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hI₁ : IntervalIntegrable
      (fun a => S.r p.1 a * (weightedIncomingAmplitude S p.1 a * W₁ (p.1, a)))
        volume p.1 p.2)
    (hI₂ : IntervalIntegrable
      (fun a => S.r p.1 a * (weightedIncomingAmplitude S p.1 a * W₂ (p.1, a)))
        volume p.1 p.2) :
    weightedRadialOperator S W₁ p - weightedRadialOperator S W₂ p =
      weightedRadialOperator S (fun q => W₁ q - W₂ q) p := by
  unfold weightedRadialOperator
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hI₁ hI₂]
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual full-domain radial operator is additive on finite-energy
measurable representatives, up to volume-null sets. All integrability
premises are discharged from N_U and late smallness. Paper `e1a0fd5`,
lines 1278–1287. -/
theorem weightedRadialOperator_sub_ae {u₀ U δ ε : ℝ} {W₁ W₂ : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (henergy₁ : weightedRemainderNormSq S u₀ U W₁ < ⊤)
    (henergy₂ : weightedRemainderNormSq S u₀ U W₂ < ⊤)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    (fun p => weightedRadialOperator S W₁ p - weightedRadialOperator S W₂ p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (fun p => W₁ p - W₂ p) := by
  obtain ⟨T₁, hT₁, heT₁⟩ := h.weightedRadialOperator_measurable_strip hi hU hW₁
  obtain ⟨T₂, hT₂, heT₂⟩ := h.weightedRadialOperator_measurable_strip hi hU hW₂
  obtain ⟨T₀, hT₀, heT₀⟩ := h.weightedRadialOperator_measurable_strip
    (W := fun p => W₁ p - W₂ p) hi hU (hW₁.sub hW₂)
  have hI₁ := h.weighted_radial_integrand_integrable_ae hi hU hW₁ henergy₁ hsmall
  have hI₂ := h.weighted_radial_integrand_integrable_ae hi hU hW₂ henergy₂ hsmall
  apply ae_weighted_triangle_of_strip
  rw [weightedOffAxisStrip_eq_iUnion, ae_restrict_iUnion_iff]
  intro q
  let b := min U (q.1.1 : ℝ)
  let c := (q.1.2 : ℝ)
  have hbc : b < c := q.2.2.1
  have hray : ∀ᵐ u ∂volume.restrict (Icc u₀ b),
      ∀ v ∈ Icc c 0, T₁ (u, v) - T₂ (u, v) = T₀ (u, v) := by
    have hsubU : Icc u₀ b ⊆ Icc u₀ U := Icc_subset_Icc_right (min_le_left _ _)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubU hI₁,
      ae_restrict_of_ae_restrict_of_subset hsubU hI₂,
      ae_restrict_mem measurableSet_Icc] with u hu₁ hu₂ huI
    intro v hv
    have huv : u < v := huI.2.trans_lt (hbc.trans_le hv.1)
    have hu0 : u ≤ 0 := (huI.2.trans (min_le_left _ _)).trans hU.le
    have hsub : uIcc u v ⊆ uIcc u 0 := by
      rw [uIcc_of_le huv.le, uIcc_of_le hu0]
      exact Icc_subset_Icc_right hv.2
    have hp : (u, v) ∈ weightedOffAxisStrip u₀ U :=
      ⟨huI.1, huI.2.trans (min_le_left _ _), huv, hv.2⟩
    rw [← heT₁ hp, ← heT₂ hp, ← heT₀ hp]
    exact weightedRadialOperator_sub_of_integrable S W₁ W₂ (u, v)
      (hu₁.mono_set hsub) (hu₂.mono_set hsub)
  have heT := ae_eq_rectangle_of_outgoing (hT₁.sub hT₂) hT₀ hray
  filter_upwards [heT, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
    with p hp hpI
  have hpS : p ∈ weightedOffAxisStrip u₀ U :=
    ⟨hpI.1.1, hpI.1.2.trans (min_le_left _ _), hpI.1.2.trans_lt (hbc.trans_le hpI.2.1), hpI.2.2⟩
  change T₁ p - T₂ p = T₀ p at hp
  rw [heT₁ hpS, heT₂ hpS, heT₀ hpS]
  exact hp

end StandingFull

end AcExtensionPrinciple

end
