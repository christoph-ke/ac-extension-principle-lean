module

public import AcExtensionPrinciple.Weighted.Prop34ActualMeasurable

/-!
# Finite full-domain L¹ of the actual remainder

Paper `e1a0fd5`, `eq:remainder-difference-l1`, lines 1292–1302.
Uniform local BV, Lemma 3.1 and initial domination give the bound.
No coercive energy of the actual remainder is assumed.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual incoming remainder has a uniform unweighted cone L¹ bound
on every compact interval of proper outgoing times. Paper `e1a0fd5`,
`eq:renormalized-local-l1`, `eq:renormalized-initial-domination`,
lines 1074–1076, 1090–1093 and 1292–1302. -/
theorem prop34_actualRemainder_cone_l1_bounded {u₀ U : ℝ}
    (hi : ui ≤ u₀) (h₀U : u₀ ≤ U) (hU : U < 0) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u ∈ Icc u₀ U,
      (∫⁻ v in Ioc u 0, ENNReal.ofReal
        |S.renormalizedRemainder (transportedRadialDatum ui S) ui u v|) ≤ B := by
  obtain ⟨C, hC, hcone⟩ := h.lemma31.cone_l1_uniform
  obtain ⟨V, hV⟩ := h.outgoingVariation_locally_bounded h₀U hi hU
  let f := S.renormalizedDerivative (transportedRadialDatum ui S) ui
  let K := (1 / initialGap ui S) / Real.exp (-Bstar ui S)
  have hgap := h.initialGap_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfi : IntegrableOn f (Ioc ui 0) := h.lemma32.initial_integrable
  let L := ∫⁻ v in Ioc ui 0, ENNReal.ofReal |f v|
  have hL : L < ⊤ := by
    simpa only [L, Real.enorm_eq_ofReal_abs] using
      hasFiniteIntegral_iff_enorm.mp hfi.hasFiniteIntegral
  refine ⟨ENNReal.ofReal C * ENNReal.ofReal V + ENNReal.ofReal K * L,
    ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL⟩, ?_⟩
  intro u hu
  have hui := hi.trans hu.1
  have hu0 := hu.2.trans_lt hU
  have hjm := (h.sectionThreeDatumInputs.renormalized_fields_measurable h hui hu0).1
  calc
    _ ≤ ∫⁻ v in Ioc u 0, ENNReal.ofReal
        |S.renormalizedDerivative (transportedRadialDatum ui S) u v| +
          ENNReal.ofReal K * ENNReal.ofReal |f v| := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro v hv
      rw [← ENNReal.ofReal_mul hK,
        ← ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      have hs : |S.renormalizedRemainder (transportedRadialDatum ui S) ui u v| ≤
          |S.renormalizedDerivative (transportedRadialDatum ui S) u v| +
            |S.renormalizedInitial (transportedRadialDatum ui S) ui u v| := by
        simpa only [SSFields.renormalizedRemainder, sub_zero, zero_sub, abs_neg] using
          abs_sub_le (S.renormalizedDerivative (transportedRadialDatum ui S) u v) 0
            (S.renormalizedInitial (transportedRadialDatum ui S) ui u v)
      exact hs.trans (add_le_add le_rfl
        (h.lemma32.initial_domination (u, v) ⟨hui, hu0, hv.1.le, hv.2⟩))
    _ = _ := lintegral_add_left' hjm.aemeasurable.norm.ennreal_ofReal _
    _ ≤ _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply add_le_add
      · exact (hcone u hui hu0).1.trans
          (mul_le_mul_of_nonneg_left (hV u hu) zero_le)
      · exact mul_le_mul_of_nonneg_left
          (lintegral_mono_set (Ioc_subset_Ioc_left hui)) zero_le

/-- A measurable representative agreeing with the actual remainder
off the axis has finite full-domain weighted L¹. Its bound comes from
uniform local BV and initial domination. Paper `e1a0fd5`,
`eq:remainder-difference-l1`, lines 1292–1302. -/
theorem prop34_actualRemainder_weighted_l1_lt_top {u₀ U : ℝ} {R : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hR : Measurable R)
    (heR : EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      R (weightedOffAxisStrip u₀ U)) :
    weightedRemainderL1 S u₀ U R < ⊤ := by
  by_cases h₀U : u₀ ≤ U
  swap
  · have he : weightedTruncatedDomain u₀ U = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun p hp => h₀U (hp.1.trans hp.2.1))
    simp only [weightedRemainderL1, he, Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.zero_lt_top]
  obtain ⟨B, hB, hcone⟩ := h.prop34_actualRemainder_cone_l1_bounded hi h₀U hU
  let D := weightedTruncatedDomain u₀ U
  obtain ⟨c, hc, he⟩ := h.regularCenter.localBV.expansion_bounds D
    (isCompact_weightedTruncatedDomain u₀ U) (weightedTruncatedDomain_subset_triangle hi hU)
  let g := weightedGapConstant ui S
  have hg : 0 < g := h.weightedGapConstant_pos
  let C := (1 / c) / (g ^ 2 * c)
  have hweight (p : ℝ × ℝ) (hp : p ∈ D) : weightedRemainderDensity S p ≤ C := by
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hp
    have hden : g ^ 2 * c ≤ (1 - S.mu p.1 p.2) ^ 2 * S.lam p.1 p.2 :=
      mul_le_mul (pow_le_pow_left₀ hg.le (h.mass_gap_lower hpt) 2) (he p hp).1 hc.le
        (sq_nonneg _)
    exact div_le_div₀ (by positivity) (he p hp).2 (by positivity) hden
  have heIter := h.weighted_remainder_power_eq_iterated hi hU hR 1
  simp only [pow_one] at heIter
  rw [show weightedRemainderL1 S u₀ U R = _ from heIter]
  calc
    _ ≤ ∫⁻ u in Icc u₀ U, ENNReal.ofReal C * B := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      calc
        _ ≤ ∫⁻ v in Ioc u 0, ENNReal.ofReal C * ENNReal.ofReal
            |S.renormalizedRemainder (transportedRadialDatum ui S) ui u v| := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro v hv
          rw [← ENNReal.ofReal_mul (by dsimp [C]; positivity),
            ← heR (x := (u, v)) ⟨hu.1, hu.2, hv.1, hv.2⟩]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (hweight (u, v) ⟨hu.1, hu.2, hv.1.le, hv.2⟩) (abs_nonneg _))
        _ = ENNReal.ofReal C * ∫⁻ v in Ioc u 0, ENNReal.ofReal
            |S.renormalizedRemainder (transportedRadialDatum ui S) ui u v| :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcone u hu) zero_le
    _ < ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB)
        isCompact_Icc.measure_lt_top

end AcExtensionPrinciple.StandingFull

end
