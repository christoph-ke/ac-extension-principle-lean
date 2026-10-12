module

public import AcExtensionPrinciple.Weighted.Prop34WeightedSpace

/-!
# Almost-everywhere operators on the actual weighted domain

Paper `e1a0fd5`, lines 1265–1287. The axis is volume-null. Rectangle
representatives therefore give representatives on the full triangle,
and the frozen source-difference identity holds on that domain.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The proper off-axis strip is measurable. Paper `e1a0fd5`,
lines 1265–1287, the operator representative domain. -/
theorem measurableSet_weightedOffAxisStrip (u₀ U : ℝ) :
    MeasurableSet (weightedOffAxisStrip u₀ U) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))

/-- The axis edge has zero volume, so the off-axis strip has full measure
in the proper triangle. Paper `e1a0fd5`, lines 1265–1287. -/
theorem weightedOffAxisStrip_ae (u₀ U : ℝ) :
    ∀ᵐ p ∂volume.restrict (weightedTruncatedDomain u₀ U),
      p ∈ weightedOffAxisStrip u₀ U := by
  have hne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ p.2 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact ae_of_all _ (fun u => (volume.ae_ne u).mono (fun _ hv => hv.symm))
  filter_upwards [ae_restrict_of_ae hne,
    ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)] with p hp hpD
  exact ⟨hpD.1, hpD.2.1, lt_of_le_of_ne hpD.2.2.1 hp, hpD.2.2.2⟩

/-- Transfer an almost-everywhere statement on the strip to the whole
proper triangle. Paper `e1a0fd5`, lines 1265–1287. -/
theorem ae_weighted_triangle_of_strip {u₀ U : ℝ} {P : ℝ × ℝ → Prop}
    (hP : ∀ᵐ p ∂volume.restrict (weightedOffAxisStrip u₀ U), P p) :
    ∀ᵐ p ∂volume.restrict (weightedTruncatedDomain u₀ U), P p := by
  rw [ae_restrict_iff' (measurableSet_weightedOffAxisStrip u₀ U)] at hP
  filter_upwards [ae_restrict_of_ae hP, weightedOffAxisStrip_ae u₀ U] with p hp hpD
  exact hp hpD

/-- Measurable functions that agree along almost every entire incoming
rectangle ray agree almost everywhere on the rectangle. Paper `e1a0fd5`,
lines 1265–1287, passage from ray formulas to the quotient space. -/
theorem ae_eq_rectangle_of_incoming {a b c : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hray : ∀ᵐ v ∂volume.restrict (Icc c 0),
      ∀ s ∈ Icc a b, f (s, v) = g (s, v)) :
    f =ᵐ[volume.restrict (Icc a b ×ˢ Icc c 0)] g := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf hg)).mpr
  apply (Measure.ae_ae_comm (p := fun s v => f (s, v) = g (s, v))
    (measurableSet_eq_fun hf hg)).mpr
  filter_upwards [hray] with v hv
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hv s hs

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A joint measurable frozen representative agrees with the literal
formula on the full proper triangle, up to volume-null sets. Paper
`e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287. -/
theorem weightedFrozenSolution_exists_measurable_ae {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF : Measurable F) :
    ∃ Z : ℝ × ℝ → ℝ, Measurable Z ∧
      weightedFrozenSolution S u₀ J₀ F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] Z := by
  obtain ⟨Z, hZ, heZ⟩ := h.weightedFrozenSolution_measurable_strip hi hU hJ₀ hF
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [weightedOffAxisStrip_ae u₀ U] with p hp
  exact heZ hp

/-- The joint measurable radial representative is valid in the full
proper-domain quotient. Paper `e1a0fd5`, lines 1278–1287. -/
theorem weightedRadialOperator_exists_measurable_ae {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {W : ℝ × ℝ → ℝ} (hW : Measurable W) :
    ∃ T : ℝ × ℝ → ℝ, Measurable T ∧
      weightedRadialOperator S W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] T := by
  obtain ⟨T, hT, heT⟩ := h.weightedRadialOperator_measurable_strip hi hU hW
  refine ⟨T, hT, ?_⟩
  filter_upwards [weightedOffAxisStrip_ae u₀ U] with p hp
  exact heT hp

/-- Subtraction of two finite-source frozen formulas gives the zero-initial
formula of their source difference on a.e. point of each rectangle.
Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_sub_ae_rectangle {u₀ U b c : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (hc0 : c ≤ 0) {J₀ : ℝ → ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤) :
    (fun p => weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p)
      =ᵐ[volume.restrict (Icc u₀ b ×ˢ Icc c 0)]
        weightedFrozenSolution S u₀ (fun _ => 0) (fun p => F₁ p - F₂ p) := by
  obtain ⟨Z₁, hZ₁, heZ₁⟩ := h.weightedFrozenSolution_measurable_rectangle hi hU hab hbU
    hbc hc0 hJ₀ hF₁
  obtain ⟨Z₂, hZ₂, heZ₂⟩ := h.weightedFrozenSolution_measurable_rectangle hi hU hab hbU
    hbc hc0 hJ₀ hF₂
  obtain ⟨Z₀, hZ₀, heZ₀⟩ := h.weightedFrozenSolution_measurable_rectangle hi hU hab hbU
    hbc hc0 (J₀ := fun _ => 0) measurable_const (hF₁.sub hF₂)
  have hray : ∀ᵐ v ∂volume.restrict (Icc c 0),
      ∀ s ∈ Icc u₀ b, Z₁ (s, v) - Z₂ (s, v) = Z₀ (s, v) := by
    filter_upwards [h.weighted_source_integrable_ae_rectangle hi hU hab hbU hbc hF₁ hsource₁,
      h.weighted_source_integrable_ae_rectangle hi hU hab hbU hbc hF₂ hsource₂,
      ae_restrict_mem measurableSet_Icc] with v hI₁ hI₂ hv
    intro s hs
    have hsub : uIcc u₀ s ⊆ uIcc u₀ b := by
      rw [uIcc_of_le hs.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right hs.2
    rw [← heZ₁ (x := (s, v)) ⟨hs, hv⟩, ← heZ₂ (x := (s, v)) ⟨hs, hv⟩,
      ← heZ₀ (x := (s, v)) ⟨hs, hv⟩]
    exact h.weightedFrozenSolution_sub hi hs.1 ((hs.2.trans hbU).trans_lt hU)
      (hs.2.trans_lt (hbc.trans_le hv.1)) hv.2 J₀ F₁ F₂
      (hI₁.mono_set hsub) (hI₂.mono_set hsub)
  have hZ := ae_eq_rectangle_of_incoming (hZ₁.sub hZ₂) hZ₀ hray
  filter_upwards [hZ, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp hpD
  change Z₁ p - Z₂ p = Z₀ p at hp
  rw [← heZ₁ hpD, ← heZ₂ hpD, ← heZ₀ hpD] at hp
  exact hp

/-- The global source-difference identity on the actual proper-domain
quotient. Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1287. -/
theorem weightedFrozenSolution_sub_ae {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {J₀ : ℝ → ℝ} {F₁ F₂ : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hsource₁ : weightedSourceNormSq S u₀ U F₁ < ⊤)
    (hsource₂ : weightedSourceNormSq S u₀ U F₂ < ⊤) :
    (fun p => weightedFrozenSolution S u₀ J₀ F₁ p - weightedFrozenSolution S u₀ J₀ F₂ p)
      =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)]
        weightedFrozenSolution S u₀ (fun _ => 0) (fun p => F₁ p - F₂ p) := by
  apply ae_weighted_triangle_of_strip
  rw [weightedOffAxisStrip_eq_iUnion, ae_restrict_iUnion_iff]
  intro q
  exact h.weightedFrozenSolution_sub_ae_rectangle hi hU q.2.1 (min_le_left _ _)
    q.2.2.1 q.2.2.2 hJ₀ hF₁ hF₂ hsource₁ hsource₂

end StandingFull

end AcExtensionPrinciple

end
