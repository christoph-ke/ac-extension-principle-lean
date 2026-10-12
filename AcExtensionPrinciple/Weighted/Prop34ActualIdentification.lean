module

public import AcExtensionPrinciple.Weighted.Prop34DifferenceRays

/-!
# Identification of the actual and constructed remainders

Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1289–1318.
The integrated inequality uses the entire radial operator and the actual
finite-L¹ bound before removing any incoming cutoff.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Finite full-domain weighted L¹ is stable under subtraction of measurable
representatives. Paper `e1a0fd5`, `eq:remainder-difference-l1`, lines 1292–1302. -/
theorem prop34_weighted_l1_sub_le {u₀ U : ℝ} {R W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hR : Measurable R) (hW : Measurable W) :
    weightedRemainderL1 S u₀ U (fun p => R p - W p) ≤
      weightedRemainderL1 S u₀ U R + weightedRemainderL1 S u₀ U W := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  have he (X : ℝ × ℝ → ℝ) : weightedRemainderL1 S u₀ U X =
      ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal (ω p * |X p|) := by
    apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
    intro p hp
    change ENNReal.ofReal (weightedRemainderDensity S p * |X p|) = _
    rw [heω hp]
  rw [he R, he W, he (fun p => R p - W p)]
  have hm : Measurable (fun p => ENNReal.ofReal (ω p * |R p|)) := by
    simpa only [Pi.mul_apply, Real.norm_eq_abs] using (hω.mul hR.norm).ennreal_ofReal
  rw [← lintegral_add_left hm _]
  apply setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
  intro p hp
  have hω0 : 0 ≤ ω p := by
    rw [← heω hp]
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hp
    exact div_nonneg (neg_pos.mpr (h.nu_neg hpt)).le
      (mul_nonneg (sq_nonneg _) (h.lam_pos hpt).le)
  rw [← ENNReal.ofReal_add (mul_nonneg hω0 (abs_nonneg _))
    (mul_nonneg hω0 (abs_nonneg _)), ← mul_add]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hω0
  simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (R p) 0 (W p)

/-- The actual incoming remainder agrees almost everywhere with a
constructed fixed-point representative. Every ray premise and the
full-domain L¹ premise is discharged here. The only smallness inputs
are the paper's late bounds and numerical absorption threshold.
Paper `e1a0fd5`, lines 1289–1318. -/
theorem prop34_actual_eq_constructed {u₀ U δ ε : ℝ} {R W H F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hcontract : (3 * ε / (1 - 3 * δ)) *
      ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) < 1)
    (J₀ : ℝ → ℝ) (hR : Measurable R) (hW : Measurable W)
    (hH : Measurable H) (hF : Measurable F)
    (heR : EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      R (weightedOffAxisStrip u₀ U))
    (heW : EqOn (weightedFrozenSolution S u₀ J₀ F) W (weightedOffAxisStrip u₀ U))
    (heH : EqOn (fun p => S.renormalizedInteraction p.1 p.2 / S.r p.1 p.2)
      H (weightedOffAxisStrip u₀ U))
    (hWs : weightedRemainderNormSq S u₀ U W < ⊤)
    (hFs : weightedSourceNormSq S u₀ U F < ⊤)
    (heF : F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
      (fun p => weightedRadialOperator S
        (fun q => S.renormalizedInitial (transportedRadialDatum ui S) ui q.1 q.2) p +
          weightedRadialOperator S W p))
    (heInitial : S.renormalizedRemainder (transportedRadialDatum ui S) ui u₀
      =ᵐ[volume.restrict (Ioc u₀ 0)] J₀) :
    R =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W := by
  have hRs := h.prop34_actualRemainder_weighted_l1_lt_top hi hU hR heR
  have hWL := h.weighted_remainder_l1_lt_top_of_energy hi hU hW hWs
  have hL := (h.prop34_weighted_l1_sub_le hi hU hR hW).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hRs, hWL⟩)
  have hIR : ∀ᵐ u ∂volume.restrict (Icc u₀ U), IntervalIntegrable
      (fun s => S.r u s * (weightedIncomingAmplitude S u s * R (u, s))) volume u 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact h.prop34_actualRemainder_radial_integrable hi hU hu heR
  have hsub := h.prop34_radial_sub_ae_of_integrable_rays hi hU hR hW hIR
    (h.weighted_radial_integrand_integrable_ae hi hU hW hWs hsmall)
  have heSource : (fun p => H p - F p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (fun p => R p - W p) := by
    filter_upwards [heF, hsub, weightedOffAxisStrip_ae u₀ U] with p hpF hpSub hp
    have he := h.prop34_actualSource_remainder_radial hi hU heR heH hp
    dsimp only at he
    calc
      H p - F p = weightedRadialOperator S R p - weightedRadialOperator S W p := by
        rw [hpF]
        calc
          _ = (H p - weightedRadialOperator S
              (fun q => S.renormalizedInitial (transportedRadialDatum ui S) ui q.1 q.2) p) -
                weightedRadialOperator S W p := by ring
          _ = _ := congrArg (fun a => a - weightedRadialOperator S W p) he
      _ = _ := hpSub
  have hKato := h.weighted_global_kato_bound
    (W := fun p => R p - W p) (F := fun p => H p - F p) hi hU hδ hε hsmall (hH.sub hF)
    (h.prop34_difference_kato_rays hi hU J₀ heR heW heH hH hF hFs heInitial)
  have hz := h.weighted_identification_of_global_kato
    (W := fun p => R p - W p) (F := fun p => H p - F p) hi hU hδ hε hsmall (hR.sub hW)
    hL heSource hKato hcontract
  exact hz.mono (fun p hp => sub_eq_zero.mp hp)

end AcExtensionPrinciple.StandingFull

end
