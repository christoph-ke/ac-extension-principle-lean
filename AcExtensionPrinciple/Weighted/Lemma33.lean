module

public import AcExtensionPrinciple.Weighted.Lemma33Transported
public import AcExtensionPrinciple.Weighted.Lemma33Remainder

/-!
# Lemma 3.3, uniformly over proper truncations

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1167–1224. The three constants are chosen after the
solution and δ, before u₀, ε, U and the data. The only source input
is the exact late-smallness conclusion of Propositions 2.7/2.8. Lemma 3.2
identifies its transported datum with the explicit κ-ratio transport here.

In docstrings, W1 names the late radial expansion comparison (`eq:late-radial-expansion-comparison`,
line 1142) and W3 the radial estimates of this lemma (`lem:weighted-radial-estimates`).
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- W3: all three radial estimates with constants fixed before every
uniformity variable, exactly as claimed at paper line 1137.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`eq:transported-radial-estimate`, `eq:remainder-radial-estimate`,
`eq:radial-l1-estimate`, lines 1167–1224. Measurable W is the representative
of the weighted norm space; the estimates also allow infinite norms. -/
theorem lemma33_weighted_radial_estimates_of_smallness {δ : ℝ}
    (_hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C₀ C₂ C₁ : ℝ, 0 ≤ C₀ ∧ 0 < C₂ ∧ 0 < C₁ ∧
      ∀ (u₀ ε U : ℝ) (f : ℝ → ℝ) (W : ℝ × ℝ → ℝ),
        ui ≤ u₀ → u₀ < U → U < 0 → 0 ≤ ε →
        WeightedLateSmallness ui S u₀ δ ε →
        AEMeasurable f (volume.restrict (Ioc ui 0)) → Measurable W →
        weightedSourceNorm S u₀ U
            (weightedRadialOperator S (weightedTransportedDatum ui S f)) ≤
          ENNReal.ofReal C₀ * (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ∧
        weightedSourceNorm S u₀ U (weightedRadialOperator S W) ≤
          ENNReal.ofReal (C₂ * ε) * weightedRemainderNorm S u₀ U W ∧
        weightedSourceL1 S u₀ U (weightedRadialOperator S W) ≤
          ENNReal.ofReal (C₁ * ε) * weightedRemainderL1 S u₀ U W := by
  have hg := h.weightedGapConstant_pos
  let C₀ := (weightedGapConstant ui S)⁻¹ ^ 2 *
    Real.sqrt ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))
  let C₂ := 2 / (weightedGapConstant ui S * (3 - δ))
  let C₁ := (weightedGapConstant ui S ^ 2)⁻¹ /
    (Real.exp (-Bstar ui S) * (1 - δ))
  have hd3 : δ < 3 := by linarith
  have hd1 : δ < 1 := by linarith
  refine ⟨C₀, C₂, C₁, by dsimp [C₀]; positivity,
    by dsimp [C₂]; positivity, by dsimp [C₁]; positivity, ?_⟩
  intro u₀ ε U f W hi _huU hU hε hsmall hf hW
  exact ⟨h.lemma33_transported_of_late_mass_bound hi hU hd3 hf
      (fun p hp hu => (hsmall p hp hu).1),
    h.lemma33_remainder_of_late_smallness hi hU hd3 hε hW hsmall,
    h.lemma33_l1_of_late_smallness hi hU hd1 hε hW hsmall⟩

end StandingFull

end AcExtensionPrinciple

end
