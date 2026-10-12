module

public import AcExtensionPrinciple.Weighted.Prop34OperatorAE
public import AcExtensionPrinciple.Weighted.Prop34SourceSpace

/-!
# Global frozen differences and independence of source representatives

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287.
The Lipschitz bound holds for the literal source difference on the full
proper triangle. Changes of source representative preserve the output.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Vanishing remainder energy means vanishing almost everywhere on the
actual proper domain, for measurable representatives. Paper `e1a0fd5`,
lines 1278–1287 and the identification at lines 1316–1318. -/
theorem weighted_remainder_normSq_zero_iff {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W) :
    weightedRemainderNormSq S u₀ U W = 0 ↔
      W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] 0 := by
  rw [← weightedRemainderNorm_sq, ← h.eLpNorm_weighted_remainder_eq hi hU hW,
    pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), eLpNorm_eq_zero_iff (by norm_num)]
  exact h.ae_weightedRemainderMeasure_iff hi hU

/-- The global squared frozen difference estimate. All source-difference
finiteness is discharged from the two finite source energies. Paper
`e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_global_difference_bound {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤) :
    weightedRemainderNormSq S u₀ U
      (fun p => weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p) ≤
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
        weightedSourceNormSq S u₀ U (fun p => F₁ p - F₂ p) := by
  have he := h.weightedFrozenSolution_sub_ae hi hU hJ₀ hF₁ hF₂ hsource₁ hsource₂
  have hnorm : weightedRemainderNormSq S u₀ U
      (fun p => weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p) =
      weightedRemainderNormSq S u₀ U
        (weightedFrozenSolution S u₀ (fun _ => 0) (fun p => F₁ p - F₂ p)) := by
    apply lintegral_congr_ae
    filter_upwards [he] with p hp
    rw [hp]
  rw [hnorm]
  exact h.weightedFrozenSolution_zero_global_energy_bound hi hU hδ hsmall (hF₁.sub hF₂)
    (h.weighted_source_sub_normSq_lt_top hi hU hF₁ hF₂ hsource₁ hsource₂)

/-- The global frozen Lipschitz estimate in the paper's unsquared norms.
Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_global_lipschitz_bound {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤) :
    weightedRemainderNorm S u₀ U
      (fun p => weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p) ≤
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^ (1 / 2 : ℝ) *
        weightedSourceNorm S u₀ U (fun p => F₁ p - F₂ p) := by
  have hb := ENNReal.rpow_le_rpow
    (h.weightedFrozenSolution_global_difference_bound hi hU hδ hsmall hJ₀ hF₁ hF₂
      hsource₁ hsource₂) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hb

/-- Changes of finite-energy source representative preserve the frozen
solution almost everywhere on the full proper domain. Paper `e1a0fd5`,
lines 1275–1287, well-definedness on the weighted quotient. -/
theorem weightedFrozenSolution_congr_ae {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤)
    (heF : F₁ =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F₂) :
    weightedFrozenSolution S u₀ J₀ F₁
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] weightedFrozenSolution S u₀ J₀ F₂ := by
  have hsource0 : weightedSourceNormSq S u₀ U (fun p => F₁ p - F₂ p) = 0 := by
    calc
      _ = ∫⁻ _p in weightedTruncatedDomain u₀ U, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [heF] with p hp
        simp only [hp, sub_self, abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
          mul_zero, ENNReal.ofReal_zero]
      _ = 0 := lintegral_zero
  have hbound := h.weightedFrozenSolution_global_difference_bound hi hU hδ hsmall
    hJ₀ hF₁ hF₂ hsource₁ hsource₂
  rw [hsource0, mul_zero] at hbound
  obtain ⟨Z₁, hZ₁, heZ₁⟩ := h.weightedFrozenSolution_exists_measurable_ae hi hU hJ₀ hF₁
  obtain ⟨Z₂, hZ₂, heZ₂⟩ := h.weightedFrozenSolution_exists_measurable_ae hi hU hJ₀ hF₂
  have hnorm0 : weightedRemainderNormSq S u₀ U (fun p => Z₁ p - Z₂ p) = 0 := by
    have he : weightedRemainderNormSq S u₀ U (fun p => Z₁ p - Z₂ p) =
        weightedRemainderNormSq S u₀ U (fun p =>
          weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p) := by
      apply lintegral_congr_ae
      filter_upwards [heZ₁, heZ₂] with p hp₁ hp₂
      rw [hp₁, hp₂]
    rw [he]
    exact le_antisymm hbound zero_le
  have hz := (h.weighted_remainder_normSq_zero_iff hi hU (hZ₁.sub hZ₂)).mp hnorm0
  filter_upwards [hz, heZ₁, heZ₂] with p hp hp₁ hp₂
  change Z₁ p - Z₂ p = 0 at hp
  rw [hp₁, hp₂]
  exact sub_eq_zero.mp hp

end AcExtensionPrinciple.StandingFull

end
