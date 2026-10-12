module

public import AcExtensionPrinciple.Decay.Prop28Assembly
public import AcExtensionPrinciple.Weighted.Lemma33

/-!
# Discharging geometric and late-smallness interfaces in the decay chain

Paper `e1a0fd5`, lines 742–749, 835–989, 1130–1137, and 1167–1224. The cylinder constant comes from
the standing assumptions. The late bounds come from the exact Propositions 2.7 and 2.8 statements.
`StandingFull.lemma23`, `lemma24`, and `lemma26` in `Integration/CylinderStatements.lean` and
`lemma25` in `Integration/ObservabilityComplete.lean` discharge the source premises. The resulting
decay conclusions are proved in `Integration/DecayComplete.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields}

/-- A cylinder constant chosen only after the standing solution, before
observation constants. Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 742–749. -/
@[expose] noncomputable def integrationCylinderK (h : StandingFull ui S) : ℝ :=
  Classical.choose h.exists_decay_cylinder_K

/-- The chosen constant discharges the geometric premise in Propositions 2.7 and 2.8. Paper
`e1a0fd5`, `eq:boundary-travel-time`, lines 742–749. -/
theorem integrationCylinderK_bounds (h : StandingFull ui S) :
    CylinderKBounds ui S h.integrationCylinderK :=
  Classical.choose_spec h.exists_decay_cylinder_K

variable (h : StandingFull ui S)
include h

/-- Proposition 2.7 conditional on Lemmas 2.4–2.6, supplied in `Integration/CylinderStatements.lean`
and `Integration/ObservabilityComplete.lean`. Paper `e1a0fd5`, `prop:uniform-mass-decay`, lines
835–925. -/
theorem uniform_mass_decay_of_pending_cylinder_lemmas {H C rho : ℝ}
    (h24 : Lemma24Statement ui S) (h25 : Lemma25Statement ui S H C rho)
    (h26 : Lemma26Statement ui S h.integrationCylinderK H) :
    UniformMassDecayStatement ui S :=
  h.uniform_mass_decay_of_cylinder_lemmas h.integrationCylinderK_bounds h24 h25 h26

/-- Proposition 2.8 conditional on Lemmas 2.3–2.6, supplied in `Integration/CylinderStatements.lean`
and `Integration/ObservabilityComplete.lean`. Paper `e1a0fd5`, `prop:common-scalar-limit`, lines
931–989. -/
theorem common_scalar_limit_of_pending_decay_lemmas {H C rho : ℝ}
    (h23 : Lemma23Statement ui S) (h24 : Lemma24Statement ui S)
    (h25 : Lemma25Statement ui S H C rho)
    (h26 : Lemma26Statement ui S h.integrationCylinderK H) :
    CommonScalarLimitStatement ui S ∧ NormalizedScalarAmplitudesVanishStatement ui S :=
  h.common_scalar_limit_of_decay_lemmas h23 h.integrationCylinderK_bounds h24 h25 h26

/-- Proposition 2.7 and the amplitude conclusion of Proposition 2.8 give exactly the late bounds
required by the weighted section. Paper `e1a0fd5`, `eq:late-renormalized-smallness`, lines
1130–1137. -/
theorem weighted_late_smallness_of_decay
    (hmass : UniformMassDecayStatement ui S)
    (hamp : NormalizedScalarAmplitudesVanishStatement ui S)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧ WeightedLateSmallness ui S u₀ δ ε := by
  let g := initialGap ui S * Real.exp (-Bstar ui S)
  have hg : 0 < g := mul_pos h.initialGap_pos (Real.exp_pos _)
  obtain ⟨a, hai, ha0, ha⟩ := hmass (δ * g) (mul_pos hδ hg)
  obtain ⟨b, hbi, hb0, hb⟩ := hamp ε hε
  refine ⟨max a b, hai.trans (le_max_left _ _), max_lt ha0 hb0, ?_⟩
  intro p hp hu
  have hm := ha p.1 p.2 ((le_max_left _ _).trans hu) hp.2.1 hp.2.2.1 hp.2.2.2
  have hgap := h.mass_gap_lower hp
  have hgap0 : 0 < 1 - S.mu p.1 p.2 := hg.trans_le hgap
  refine ⟨(div_le_iff₀ hgap0).mpr ?_, ?_⟩
  · calc
      S.mu p.1 p.2 ≤ |S.mu p.1 p.2| := le_abs_self _
      _ ≤ δ * g := hm.le
      _ ≤ δ * (1 - S.mu p.1 p.2) := mul_le_mul_of_nonneg_left hgap hδ.le
  · exact (hb p.1 p.2 ((le_max_right _ _).trans hu) hp.2.1 hp.2.2.1 hp.2.2.2).le

/-- All three Lemma 3.3 estimates on a sufficiently late cone, with the constant chosen before ε and
the start time. Its only source inputs are the exact Propositions 2.7 and 2.8 conclusions. Paper
`e1a0fd5`, `lem:weighted-radial-estimates`, lines 1130–1137 and 1167–1224. -/
theorem lemma33_weighted_radial_estimates_of_decay
    (hmass : UniformMassDecayStatement ui S)
    (hamp : NormalizedScalarAmplitudesVanishStatement ui S)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 3) :
    ∃ C₀ C₂ C₁ : ℝ, 0 ≤ C₀ ∧ 0 < C₂ ∧ 0 < C₁ ∧
      ∀ ε : ℝ, 0 < ε → ∃ u₀ : ℝ, ui ≤ u₀ ∧ u₀ < 0 ∧
        ∀ (U : ℝ) (f : ℝ → ℝ) (W : ℝ × ℝ → ℝ),
          u₀ < U → U < 0 →
          AEMeasurable f (volume.restrict (Ioc ui 0)) → Measurable W →
          weightedSourceNorm S u₀ U
              (weightedRadialOperator S (weightedTransportedDatum ui S f)) ≤
            ENNReal.ofReal C₀ * (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ∧
          weightedSourceNorm S u₀ U (weightedRadialOperator S W) ≤
            ENNReal.ofReal (C₂ * ε) * weightedRemainderNorm S u₀ U W ∧
          weightedSourceL1 S u₀ U (weightedRadialOperator S W) ≤
            ENNReal.ofReal (C₁ * ε) * weightedRemainderL1 S u₀ U W := by
  obtain ⟨C₀, C₂, C₁, hC₀, hC₂, hC₁, hest⟩ :=
    h.lemma33_weighted_radial_estimates_of_smallness hδ0 hδ
  refine ⟨C₀, C₂, C₁, hC₀, hC₂, hC₁, ?_⟩
  intro ε hε
  obtain ⟨u₀, hi, hu₀, hsmall⟩ := h.weighted_late_smallness_of_decay hmass hamp hδ0 hε
  exact ⟨u₀, hi, hu₀, fun U f W huU hU hf hW =>
    hest u₀ ε U f W hi huU hU hε.le hsmall hf hW⟩

end AcExtensionPrinciple.StandingFull

end
