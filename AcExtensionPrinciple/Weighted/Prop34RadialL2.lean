module

public import AcExtensionPrinciple.Weighted.Prop34RadialLinear
public import AcExtensionPrinciple.Weighted.Prop34FrozenLipschitz
public import AcExtensionPrinciple.Weighted.Lemma33Remainder

/-!
# The radial operator on the actual weighted L² quotients

Paper `e1a0fd5`, lines 1278–1287. The full-cone integral and Lemma 3.3
define a representative-independent quotient operator with the actual
paper Lipschitz constant. No radial source is truncated at a cutoff.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The lower-integral source norm respects volume-a.e. equality on D_U.
Paper `e1a0fd5`, lines 1265–1287. -/
theorem weighted_source_norm_congr_ae {S : SSFields} {u₀ U : ℝ}
    {F G : ℝ × ℝ → ℝ}
    (he : F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] G) :
    weightedSourceNorm S u₀ U F = weightedSourceNorm S u₀ U G := by
  unfold weightedSourceNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [he] with p hp
  rw [hp]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual radial integral of every finite-energy measurable remainder
defines a source quotient element with the exact Lemma 3.3 bound.
Paper `e1a0fd5`, lines 1174–1177 and 1278–1287. -/
theorem exists_weightedRadialL2_element {u₀ U δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (hW : Measurable W)
    (henergy : weightedRemainderNormSq S u₀ U W < ⊤) :
    ∃ f : WeightedSourceL2 S u₀ U,
      (f : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S W ∧
      ‖f‖ₑ ≤ ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) *
        weightedRemainderNorm S u₀ U W := by
  have hb := h.lemma33_remainder_of_late_smallness hi hU hδ hε hW hsmall
  have hN : weightedRemainderNorm S u₀ U W < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne
  have hM := hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)
  obtain ⟨T, hT, heT⟩ := h.weightedRadialOperator_exists_measurable_ae hi hU hW
  have hnorm := weighted_source_norm_congr_ae (S := S) heT
  have hmem : MemLp T 2 (weightedSourceMeasure S u₀ U) := by
    rw [memLp_iff, h.eLpNorm_weighted_source_eq hi hU hT, ← hnorm]
    exact hM
  refine ⟨hmem.toLp T, ?_, ?_⟩
  · have hf : (hmem.toLp T : ℝ × ℝ → ℝ)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] T :=
      (h.ae_weightedSourceMeasure_iff hi hU).mp hmem.coeFn_toLp
    exact hf.trans heT.symm
  · rw [Lp.enorm_toLp, h.eLpNorm_weighted_source_eq hi hU hT, ← hnorm]
    exact hb

/-- The radial operator on the actual remainder and source L² quotients,
using full outgoing-cone integrals. Paper `e1a0fd5`, lines 1278–1287. -/
@[expose] noncomputable def weightedRadialL2Operator {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (x : WeightedRemainderL2 S u₀ U) : WeightedSourceL2 S u₀ U := by
  classical
  let hx := Lp.aestronglyMeasurable x
  have henergy := (h.memLp_weighted_remainder_iff hi hU hx.measurable_mk).mp
    ((memLp_congr_ae hx.ae_eq_mk).mp (Lp.memLp x))
  exact Classical.choose (h.exists_weightedRadialL2_element hi hU hδ hε hsmall
    hx.measurable_mk henergy)

/-- The radial quotient operator realizes its literal integral for the
canonical measurable remainder representative. Paper `e1a0fd5`,
lines 1278–1287. -/
theorem weightedRadialL2Operator_formula {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (x : WeightedRemainderL2 S u₀ U) :
    (h.weightedRadialL2Operator hi hU hδ hε hsmall x : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S ((Lp.aestronglyMeasurable x).mk x) := by
  let hx := Lp.aestronglyMeasurable x
  have henergy := (h.memLp_weighted_remainder_iff hi hU hx.measurable_mk).mp
    ((memLp_congr_ae hx.ae_eq_mk).mp (Lp.memLp x))
  exact (Classical.choose_spec (h.exists_weightedRadialL2_element hi hU hδ hε hsmall
    hx.measurable_mk henergy)).1

/-- Every measurable representative gives the same radial quotient
formula. Paper `e1a0fd5`, lines 1278–1287. -/
theorem weightedRadialL2Operator_formula_of_representative {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (x : WeightedRemainderL2 S u₀ U)
    {W : ℝ × ℝ → ℝ} (hW : Measurable W)
    (heW : (x : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] W) :
    (h.weightedRadialL2Operator hi hU hδ hε hsmall x : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] weightedRadialOperator S W := by
  let hx := Lp.aestronglyMeasurable x
  have hevol : (x : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] hx.mk x :=
    (h.ae_weightedRemainderMeasure_iff hi hU).mp hx.ae_eq_mk
  exact (h.weightedRadialL2Operator_formula hi hU hδ hε hsmall x).trans
    (h.weightedRadialOperator_congr_ae hi hU hx.measurable_mk hW (hevol.symm.trans heW))

/-- The actual radial quotient operator sends zero to zero. Paper
`e1a0fd5`, lines 1278–1287, the fixed-point displacement estimate. -/
theorem weightedRadialL2Operator_zero {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) :
    h.weightedRadialL2Operator hi hU hδ hε hsmall 0 = 0 := by
  have he0 : (0 : WeightedRemainderL2 S u₀ U)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun _ => (0 : ℝ)) :=
    (h.ae_weightedRemainderMeasure_iff hi hU).mp
      (Lp.coeFn_zero ℝ 2 (weightedRemainderMeasure S u₀ U))
  have he := h.weightedRadialL2Operator_formula_of_representative hi hU hδ hε hsmall
    0 (W := fun _ => 0) measurable_const he0
  have heZ : (h.weightedRadialL2Operator hi hU hδ hε hsmall 0 : ℝ × ℝ → ℝ)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun _ => (0 : ℝ)) := by
    filter_upwards [he] with p hp
    rw [hp]
    simp [weightedRadialOperator]
  apply Lp.ext
  have heW : (h.weightedRadialL2Operator hi hU hδ hε hsmall 0 : ℝ × ℝ → ℝ)
      =ᵐ[weightedSourceMeasure S u₀ U] (fun _ => (0 : ℝ)) :=
    (h.ae_weightedSourceMeasure_iff hi hU).mpr heZ
  exact heW.trans (Lp.coeFn_zero ℝ 2 (weightedSourceMeasure S u₀ U)).symm

/-- Lemma 3.3's actual radial Lipschitz estimate on the weighted quotient
spaces. The full-cone subtraction has been proved, not assumed. Paper
`e1a0fd5`, lines 1174–1177 and 1278–1287. -/
theorem weightedRadialL2Operator_lipschitz {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (x y : WeightedRemainderL2 S u₀ U) :
    ‖h.weightedRadialL2Operator hi hU hδ hε hsmall x -
      h.weightedRadialL2Operator hi hU hδ hε hsmall y‖ₑ ≤
      ENNReal.ofReal (2 / (weightedGapConstant ui S * (3 - δ)) * ε) * ‖x - y‖ₑ := by
  let f := h.weightedRadialL2Operator hi hU hδ hε hsmall x
  let g := h.weightedRadialL2Operator hi hU hδ hε hsmall y
  obtain ⟨X, hX, heX, hXs⟩ := h.weightedRemainderL2_exists_measurable_representative hi hU x
  obtain ⟨Y, hY, heY, hYs⟩ := h.weightedRemainderL2_exists_measurable_representative hi hU y
  obtain ⟨F, hF, heF, _⟩ := h.weightedSourceL2_exists_measurable_representative hi hU f
  obtain ⟨G, hG, heG, _⟩ := h.weightedSourceL2_exists_measurable_representative hi hU g
  have hradial := h.weightedRadialL2Operator_formula_of_representative hi hU hδ hε hsmall
    x hX heX
  have gradial := h.weightedRadialL2Operator_formula_of_representative hi hU hδ hε hsmall
    y hY heY
  have hexy : (x - y : WeightedRemainderL2 S u₀ U)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun p => X p - Y p) := by
    have hsub : (x - y : WeightedRemainderL2 S u₀ U)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
          (fun p => (x : ℝ × ℝ → ℝ) p - (y : ℝ × ℝ → ℝ) p) :=
      (h.ae_weightedRemainderMeasure_iff hi hU).mp (Lp.coeFn_sub x y)
    filter_upwards [hsub, heX, heY] with p hp hpX hpY
    rw [hp, hpX, hpY]
  have hefg : (f - g : WeightedSourceL2 S u₀ U)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] (fun p => F p - G p) := by
    have hsub : (f - g : WeightedSourceL2 S u₀ U)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
          (fun p => (f : ℝ × ℝ → ℝ) p - (g : ℝ × ℝ → ℝ) p) :=
      (h.ae_weightedSourceMeasure_iff hi hU).mp (Lp.coeFn_sub f g)
    filter_upwards [hsub, heF, heG] with p hp hpF hpG
    rw [hp, hpF, hpG]
  have heformula : (fun p => F p - G p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedRadialOperator S (fun p => X p - Y p) := by
    have he : (fun p => F p - G p)
        =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
          (fun p => weightedRadialOperator S X p - weightedRadialOperator S Y p) := by
      filter_upwards [heF, heG, hradial, gradial] with p hpF hpG hpX hpY
      rw [← hpF, ← hpG, hpX, hpY]
    exact he.trans (h.weightedRadialOperator_sub_ae hi hU hX hY hXs hYs hsmall)
  have hb := h.lemma33_remainder_of_late_smallness (W := fun p => X p - Y p)
    hi hU hδ hε (hX.sub hY) hsmall
  rw [← weighted_source_norm_congr_ae heformula,
    h.weightedSourceL2_norm_of_representative (F := fun p => F p - G p)
      hi hU (hF.sub hG) hefg,
    h.weightedRemainderL2_norm_of_representative (W := fun p => X p - Y p)
      hi hU (hX.sub hY) hexy] at hb
  exact hb

end StandingFull

end AcExtensionPrinciple

end
