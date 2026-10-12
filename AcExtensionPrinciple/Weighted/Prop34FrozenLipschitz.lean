module

public import AcExtensionPrinciple.Weighted.Prop34FrozenL2

/-!
# The global frozen Lipschitz bound on the actual L² quotients

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287.
The quotient operator has the same Lipschitz estimate as its literal
incoming formula, independent of the proper truncation U.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The lower-integral remainder norm respects volume-a.e. equality on
D_U, including for literal formulas before selecting representatives.
Paper `e1a0fd5`, lines 1265–1287. -/
theorem weighted_remainder_norm_congr_ae {S : SSFields} {u₀ U : ℝ}
    {W Z : ℝ × ℝ → ℝ}
    (he : W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] Z) :
    weightedRemainderNorm S u₀ U W = weightedRemainderNorm S u₀ U Z := by
  unfold weightedRemainderNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [he] with p hp
  rw [hp]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A measurable representative's N_U equals the quotient norm.
Paper `e1a0fd5`, line 1150 and lines 1278–1287. -/
theorem weightedRemainderL2_norm_of_representative {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {x : WeightedRemainderL2 S u₀ U}
    {W : ℝ × ℝ → ℝ} (hW : Measurable W)
    (he : (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W) :
    weightedRemainderNorm S u₀ U W = ‖x‖ₑ := by
  rw [← h.eLpNorm_weighted_remainder_eq hi hU hW, Lp.enorm_def]
  have hew : (x : ℝ × ℝ → ℝ) =ᵐ[weightedRemainderMeasure S u₀ U] W :=
    (h.ae_weightedRemainderMeasure_iff hi hU).mpr he
  exact eLpNorm_congr_ae hew.symm

/-- A measurable source representative's M_U equals the quotient norm.
Paper `e1a0fd5`, line 1152 and lines 1265–1287. -/
theorem weightedSourceL2_norm_of_representative {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {f : WeightedSourceL2 S u₀ U}
    {F : ℝ × ℝ → ℝ} (hF : Measurable F)
    (he : (f : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] F) :
    weightedSourceNorm S u₀ U F = ‖f‖ₑ := by
  rw [← h.eLpNorm_weighted_source_eq hi hU hF, Lp.enorm_def]
  have hew : (f : ℝ × ℝ → ℝ) =ᵐ[weightedSourceMeasure S u₀ U] F :=
    (h.ae_weightedSourceMeasure_iff hi hU).mpr he
  exact eLpNorm_congr_ae hew.symm

/-- The actual source-to-remainder quotient operator has the global
frozen Lipschitz constant. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1287. -/
theorem weightedFrozenL2Operator_lipschitz {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (f g : WeightedSourceL2 S u₀ U) :
    ‖h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial f -
      h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial g‖ₑ ≤
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^ (1 / 2 : ℝ) *
        ‖f - g‖ₑ := by
  let x := h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial f
  let y := h.weightedFrozenL2Operator hi hU hδ hsmall J₀ hJ₀ hinitial g
  obtain ⟨F, hF, heF, hFs⟩ := h.weightedSourceL2_exists_measurable_representative hi hU f
  obtain ⟨G, hG, heG, hGs⟩ := h.weightedSourceL2_exists_measurable_representative hi hU g
  obtain ⟨X, hX, heX, _⟩ := h.weightedRemainderL2_exists_measurable_representative hi hU x
  obtain ⟨Y, hY, heY, _⟩ := h.weightedRemainderL2_exists_measurable_representative hi hU y
  have hfrozen := h.weightedFrozenL2Operator_formula_of_representative hi hU hδ hsmall
    J₀ hJ₀ hinitial f hF heF hFs
  have gfrozen := h.weightedFrozenL2Operator_formula_of_representative hi hU hδ hsmall
    J₀ hJ₀ hinitial g hG heG hGs
  have hefg : (f - g : WeightedSourceL2 S u₀ U)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun p => F p - G p) := by
    have hsub : (f - g : WeightedSourceL2 S u₀ U)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
          (fun p => (f : ℝ × ℝ → ℝ) p - (g : ℝ × ℝ → ℝ) p) :=
      (h.ae_weightedSourceMeasure_iff hi hU).mp (Lp.coeFn_sub f g)
    filter_upwards [hsub, heF, heG] with p hp hpF hpG
    rw [hp, hpF, hpG]
  have hexy : (x - y : WeightedRemainderL2 S u₀ U)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun p => X p - Y p) := by
    have hsub : (x - y : WeightedRemainderL2 S u₀ U)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
          (fun p => (x : ℝ × ℝ → ℝ) p - (y : ℝ × ℝ → ℝ) p) :=
      (h.ae_weightedRemainderMeasure_iff hi hU).mp (Lp.coeFn_sub x y)
    filter_upwards [hsub, heX, heY] with p hp hpX hpY
    rw [hp, hpX, hpY]
  have heformula : (fun p => X p - Y p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        (fun p => weightedFrozenSolution S u₀ J₀ F p - weightedFrozenSolution S u₀ J₀ G p) := by
    filter_upwards [heX, heY, hfrozen, gfrozen] with p hpX hpY hpF hpG
    rw [← hpX, ← hpY]
    rw [hpF, hpG]
  have hb := h.weightedFrozenSolution_global_lipschitz_bound hi hU hδ hsmall hJ₀ hF hG hFs hGs
  rw [← weighted_remainder_norm_congr_ae heformula,
    h.weightedRemainderL2_norm_of_representative (W := fun p => X p - Y p)
      hi hU (hX.sub hY) hexy,
    h.weightedSourceL2_norm_of_representative (F := fun p => F p - G p)
      hi hU (hF.sub hG) hefg] at hb
  exact hb

end StandingFull

end AcExtensionPrinciple

end
