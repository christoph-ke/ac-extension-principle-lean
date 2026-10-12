module

public import AcExtensionPrinciple.Weighted.Prop34OperatorAE

/-!
# The radial operator respects proper-domain representatives

Paper `e1a0fd5`, `eq:weighted-radial-operator`, lines 1157–1159,
and the fixed-point construction, lines 1278–1287. Incoming and outgoing
integrals keep their full domains when representatives are changed.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Agreement along almost every entire outgoing rectangle ray gives
agreement almost everywhere on the rectangle for measurable functions.
Paper `e1a0fd5`, lines 1278–1287. -/
theorem ae_eq_rectangle_of_outgoing {a b c : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hray : ∀ᵐ u ∂volume.restrict (Icc a b),
      ∀ v ∈ Icc c 0, f (u, v) = g (u, v)) :
    f =ᵐ[volume.restrict (Icc a b ×ˢ Icc c 0)] g := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf hg)).mpr
  filter_upwards [hray] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  exact hu v hv

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Changing a measurable input on a volume-null set in D_U preserves the
full radial operator almost everywhere on D_U. No finite-energy premise
is needed. Paper `e1a0fd5`, `eq:weighted-radial-operator`, lines 1157–1159
and the quotient construction at lines 1278–1287. -/
theorem weightedRadialOperator_congr_ae {u₀ U : ℝ} {W₁ W₂ : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (heW : W₁ =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W₂) :
    weightedRadialOperator S W₁ =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      weightedRadialOperator S W₂ := by
  obtain ⟨T₁, hT₁, heT₁⟩ := h.weightedRadialOperator_measurable_strip hi hU hW₁
  obtain ⟨T₂, hT₂, heT₂⟩ := h.weightedRadialOperator_measurable_strip hi hU hW₂
  have hvol : ∀ᵐ p : ℝ × ℝ ∂volume,
      p ∈ weightedTruncatedDomain u₀ U → W₁ p = W₂ p :=
    (ae_restrict_iff' (measurableSet_weightedTruncatedDomain u₀ U)).mp heW
  rw [Measure.volume_eq_prod] at hvol
  have hcone := Measure.ae_ae_of_ae_prod hvol
  apply ae_weighted_triangle_of_strip
  rw [weightedOffAxisStrip_eq_iUnion, ae_restrict_iUnion_iff]
  intro q
  let b := min U (q.1.1 : ℝ)
  let c := (q.1.2 : ℝ)
  have hbc : b < c := q.2.2.1
  have hray : ∀ᵐ u ∂volume.restrict (Icc u₀ b),
      ∀ v ∈ Icc c 0, T₁ (u, v) = T₂ (u, v) := by
    filter_upwards [ae_restrict_of_ae hcone, ae_restrict_mem measurableSet_Icc] with u hu huI
    intro v hv
    have huv : u < v := huI.2.trans_lt (hbc.trans_le hv.1)
    have hp : (u, v) ∈ weightedOffAxisStrip u₀ U :=
      ⟨huI.1, huI.2.trans (min_le_left _ _), huv, hv.2⟩
    rw [← heT₁ hp, ← heT₂ hp]
    unfold weightedRadialOperator
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hu] with s hs hsI
    rw [uIoc_of_le huv.le] at hsI
    rw [hs ⟨huI.1, huI.2.trans (min_le_left _ _), hsI.1.le, hsI.2.trans hv.2⟩]
  have heT := ae_eq_rectangle_of_outgoing hT₁ hT₂ hray
  filter_upwards [heT, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
    with p hp hpI
  have hpS : p ∈ weightedOffAxisStrip u₀ U :=
    ⟨hpI.1.1, hpI.1.2.trans (min_le_left _ _), hpI.1.2.trans_lt (hbc.trans_le hpI.2.1), hpI.2.2⟩
  rw [heT₁ hpS, heT₂ hpS]
  exact hp

end StandingFull

end AcExtensionPrinciple

end
