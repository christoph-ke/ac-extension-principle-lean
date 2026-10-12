module

public import AcExtensionPrinciple.Weighted.Prop34RadialL2
public import AcExtensionPrinciple.Weighted.Abstract

/-!
# The fixed point on the actual weighted remainder space

Paper `e1a0fd5`, lines 1278–1287. The two actual quotient operators
compose to a contraction. The displayed numerical smallness condition
involves only δ, ε and the original geometric gap, independently of U.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal NNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual map W ↦ Z(F₀ + T W) has a unique fixed point in the
complete weighted L² remainder quotient, with the Banach displacement
bound. F₀ will be the source T j_in from Lemma 3.3. The numerical premise
is the paper's sufficiently-small ε requirement, with constants uniform
in U. Paper `e1a0fd5`, lines 1278–1287. -/
theorem exists_weighted_remainder_fixedPoint {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hhalf : ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) ≤
          ENNReal.ofReal (1 / 2))
    (F₀ : WeightedSourceL2 S u₀ U) :
    let hδ3 : δ < 3 := by linarith
    let Φ := fun x : WeightedRemainderL2 S u₀ U =>
      h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
        (F₀ + h.weightedRadialL2Operator hi hU hδ3 hε hsmall x)
    ∃ x : WeightedRemainderL2 S u₀ U, Φ x = x ∧
      dist x 0 ≤ 2 * dist (Φ 0) 0 ∧ ∀ y, Φ y = y → y = x := by
  dsimp only
  let hδ3 : δ < 3 := by linarith
  let T := h.weightedRadialL2Operator hi hU hδ3 hε hsmall
  let Z := h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
  let Φ := fun x : WeightedRemainderL2 S u₀ U => Z (F₀ + T x)
  have hLip : LipschitzWith (1 / 2 : ℝ≥0) Φ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hZ := h.weightedFrozenL2Operator_lipschitz hi hU hδ hsmall J₀ hJ₀ hinitial
      (F₀ + T x) (F₀ + T y)
    have hT := h.weightedRadialL2Operator_lipschitz hi hU hδ3 hε hsmall x y
    have hsub : F₀ + T x - (F₀ + T y) = T x - T y := by abel
    rw [hsub] at hZ
    have hb : ‖Φ x - Φ y‖ₑ ≤ ENNReal.ofReal (1 / 2) * ‖x - y‖ₑ := by
      calc
        _ ≤ ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^
            (1 / 2 : ℝ) * ‖T x - T y‖ₑ := hZ
        _ ≤ ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^
            (1 / 2 : ℝ) *
              (ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) * ‖x - y‖ₑ) :=
          mul_le_mul_of_nonneg_left hT zero_le
        _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hhalf zero_le
    have hbR := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      toReal_enorm, dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hbR
  exact exists_unique_fixedPoint_half Φ 0 (L := 1 / 2) (by norm_num) hLip

/-- The actual weighted-space fixed point has the constructed remainder
energy bound, uniformly in U. F₀ is subsequently supplied by the
transported estimate in Lemma 3.3. Paper `e1a0fd5`,
`eq:constructed-remainder-bound`, lines 1278–1287. -/
theorem exists_weighted_remainder_fixedPoint_with_energy {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hhalf : ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) ≤
          ENNReal.ofReal (1 / 2))
    (F₀ : WeightedSourceL2 S u₀ U) :
    let hδ3 : δ < 3 := by linarith
    let Φ := fun x : WeightedRemainderL2 S u₀ U =>
      h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
        (F₀ + h.weightedRadialL2Operator hi hU hδ3 hε hsmall x)
    ∃ x : WeightedRemainderL2 S u₀ U, Φ x = x ∧
      ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        (ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) * (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
          (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
        ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) * ‖F₀‖ₑ ^ 2) ∧
      ∀ y, Φ y = y → y = x := by
  dsimp only
  let hδ3 : δ < 3 := by linarith
  let Z := h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial
  let Φ := fun x : WeightedRemainderL2 S u₀ U =>
    Z (F₀ + h.weightedRadialL2Operator hi hU hδ3 hε hsmall x)
  obtain ⟨x, hx, hdisp, huniq⟩ := h.exists_weighted_remainder_fixedPoint hi hU hδ hε hsmall
    J₀ hJ₀ hinitial hhalf F₀
  have hΦ0 : Φ 0 = Z F₀ := by
    dsimp only [Φ]
    rw [h.weightedRadialL2Operator_zero hi hU hδ3 hε hsmall, add_zero]
  have hn : ‖x‖ₑ ≤ ENNReal.ofReal 2 * ‖Φ 0‖ₑ := by
    have hb := ENNReal.ofReal_le_ofReal hdisp
    simpa only [dist_zero_right, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ofReal_norm] using hb
  have hsq : ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal 4 * ‖Z F₀‖ₑ ^ 2 := by
    have hb := pow_le_pow_left₀ zero_le hn 2
    simpa only [hΦ0, mul_pow, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      show (2 : ℝ) ^ 2 = 4 by norm_num] using hb
  refine ⟨x, hx, ?_, huniq⟩
  exact hsq.trans (mul_le_mul_of_nonneg_left
    (h.weightedFrozenL2Operator_energy_bound hi hU hδ hsmall J₀ hJ₀ hinitial F₀) zero_le)

end AcExtensionPrinciple.StandingFull

end
