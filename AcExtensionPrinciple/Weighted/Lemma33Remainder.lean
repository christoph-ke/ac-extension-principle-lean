module

public import AcExtensionPrinciple.Weighted.ClassConeEstimates
public import AcExtensionPrinciple.Weighted.ClassWeights

/-!
# Lemma 3.3: the remainder and L¹ estimates on the class

Paper `e1a0fd5`, `eq:remainder-radial-estimate`,
`eq:radial-l1-estimate`, `equations.tex` lines 1174–1183, 1204–1223.
Late smallness is precisely the Propositions 2.7/2.8 conclusion.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Exactly the two late-smallness bounds used in the weighted section.
Paper `e1a0fd5`, `eq:late-renormalized-smallness`, lines 1132–1135. -/
@[expose] def WeightedLateSmallness (ui : ℝ) (S : SSFields) (u₀ δ ε : ℝ) : Prop :=
  ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 →
    S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ ∧
      |(S.r p.1 p.2 / S.lam p.1 p.2) * S.dvphi p.1 p.2| +
        |weightedIncomingAmplitude S p.1 p.2| ≤ ε

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- W3, squared L² estimate for the actual radial operator, uniform in all
proper truncations. Paper `e1a0fd5`, `eq:remainder-radial-estimate`,
lines 1174–1177 and 1204–1215. -/
theorem lemma33_remainder_sq_of_late_smallness {u₀ U δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε) (hW : Measurable W)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    weightedSourceNormSq S u₀ U (weightedRadialOperator S W) ≤
      ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹ * (2 / (3 - δ)) ^ 2 * ε ^ 2) *
        weightedRemainderNormSq S u₀ U W := by
  let C := ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹)
  let H := ENNReal.ofReal ((2 / (3 - δ)) ^ 2 * ε ^ 2)
  have hcone (u : ℝ) (hu : u ∈ Icc u₀ U) :
      (∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)| ^ 2)) ≤
      H * ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) * |W (u, v)| ^ 2) := by
    have hui := hi.trans hu.1
    have hu0 := hu.2.trans_lt hU
    have hp (v : ℝ) (hv : v ∈ Ioc u 0) : (u, v) ∈ pastTriangle ui :=
      ⟨hui, hu0, hv.1.le, hv.2⟩
    have hr := h.weighted_cone_radial_l2_of_smallness hui hu0 hW hδ hε
      (fun v hv => (hsmall (u, v) (hp v hv) hu.1).1)
      (fun v hv => (le_add_of_nonneg_left (abs_nonneg _)).trans
        (hsmall (u, v) (hp v hv) hu.1).2)
    refine hr.trans (mul_le_mul le_rfl ?_ zero_le zero_le)
    exact setLIntegral_mono' measurableSet_Ioc
      (fun v hv => h.weighted_remainder_base_le (hp v hv) (W (u, v)) 2)
  calc
    _ ≤ C * ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal
        ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |weightedRadialOperator S W p| ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
        (fun p hp => h.weighted_source_sq_le_base
          (weightedTruncatedDomain_subset_triangle hi hU hp) _)
    _ ≤ C * ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)| ^ 2) := by
      exact mul_le_mul le_rfl (weighted_triangle_lintegral_le u₀ U _) zero_le zero_le
    _ ≤ C * ∫⁻ u in Icc u₀ U, H * ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) * |W (u, v)| ^ 2) := by
      exact mul_le_mul le_rfl (setLIntegral_mono' measurableSet_Icc hcone) zero_le zero_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← h.weighted_remainder_power_eq_iterated hi hU hW 2]
      dsimp only [C, H, weightedRemainderNormSq]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      simp only [div_eq_mul_inv]
      ring

/-- W3 in norm form, including the finite-energy case of the paper.
Paper `e1a0fd5`, `eq:remainder-radial-estimate`, lines 1174–1177, 1215. -/
theorem lemma33_remainder_of_late_smallness {u₀ U δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε) (hW : Measurable W)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    weightedSourceNorm S u₀ U (weightedRadialOperator S W) ≤
      ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) *
        weightedRemainderNorm S u₀ U W := by
  have hc : 0 ≤ 2 / (weightedGapConstant ui S * (3 - δ)) * ε := by
    have hg := h.weightedGapConstant_pos
    positivity
  have hs : weightedSourceNorm S u₀ U (weightedRadialOperator S W) ^ 2 ≤
      (ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) *
        weightedRemainderNorm S u₀ U W) ^ 2 := by
    rw [mul_pow, weightedSourceNorm_sq, weightedRemainderNorm_sq, ← ENNReal.ofReal_pow hc]
    convert h.lemma33_remainder_sq_of_late_smallness hi hU hδ hε hW hsmall using 1
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]
    ring
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (2 : ℝ))).mp
    (by simpa only [ENNReal.rpow_two] using hs)

/-- W3, the weighted L¹ estimate for the actual operator, with a constant
depending only on δ and the fixed geometry. Paper `e1a0fd5`,
`eq:radial-l1-estimate`, lines 1179–1183 and 1217–1223. -/
theorem lemma33_l1_of_late_smallness {u₀ U δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1) (hε : 0 ≤ ε) (hW : Measurable W)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    weightedSourceL1 S u₀ U (weightedRadialOperator S W) ≤
      ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) * weightedRemainderL1 S u₀ U W := by
  let C := ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹ / Real.exp (-Bstar ui S))
  let H := ENNReal.ofReal (ε / (1 - δ))
  have hcone (u : ℝ) (hu : u ∈ Icc u₀ U) :
      (∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)|)) ≤
      H * ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) * |W (u, v)|) := by
    have hui := hi.trans hu.1
    have hu0 := hu.2.trans_lt hU
    have hp (v : ℝ) (hv : v ∈ Ioc u 0) : (u, v) ∈ pastTriangle ui :=
      ⟨hui, hu0, hv.1.le, hv.2⟩
    have hr := h.weighted_cone_radial_l1_of_smallness hui hu0 hW hδ hε
      (fun v hv => (hsmall (u, v) (hp v hv) hu.1).1)
      (fun v hv => (le_add_of_nonneg_left (abs_nonneg _)).trans
        (hsmall (u, v) (hp v hv) hu.1).2)
    refine hr.trans (mul_le_mul le_rfl ?_ zero_le zero_le)
    exact setLIntegral_mono' measurableSet_Ioc
      (fun v hv => h.weighted_remainder_l1_base_le (hp v hv) (W (u, v)))
  calc
    _ ≤ C * ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal
        ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |weightedRadialOperator S W p|) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
        (fun p hp => h.weighted_source_l1_le_base
          (weightedTruncatedDomain_subset_triangle hi hU hp) _)
    _ ≤ C * ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)|) := by
      exact mul_le_mul le_rfl (weighted_triangle_lintegral_le u₀ U _) zero_le zero_le
    _ ≤ C * ∫⁻ u in Icc u₀ U, H * ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) * |W (u, v)|) := by
      exact mul_le_mul le_rfl (setLIntegral_mono' measurableSet_Icc hcone) zero_le zero_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have he := h.weighted_remainder_power_eq_iterated hi hU hW 1
      simp only [pow_one] at he
      rw [← he]
      dsimp only [C, H, weightedRemainderL1]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end StandingFull

end AcExtensionPrinciple

end
