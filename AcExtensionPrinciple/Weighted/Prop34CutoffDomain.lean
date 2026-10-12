module

public import AcExtensionPrinciple.Weighted.Prop34Local
public import AcExtensionPrinciple.Weighted.ClassMeasurableStrip
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Finite energy on the full radius-cutoff domain

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1268–1276. Every positive-radius cutoff is
compact and admits a finite cover by off-axis rectangles. Thus the literal frozen formula has finite
cutoff energy before any use of the coercive energy identity.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The proper triangle with the radius cutoff used in the energy proof.
Paper `e1a0fd5`, lines 1268–1276 and 1311–1316. -/
@[expose] def weightedCutoffDomain (S : SSFields) (u₀ U η : ℝ) : Set (ℝ × ℝ) :=
  weightedTruncatedDomain u₀ U ∩ (fun p => S.r p.1 p.2) ⁻¹' Ici η

/-- A compact subset of the off-axis strip is covered by finitely many
proper incoming rectangles. Paper `e1a0fd5`, lines 1268–1276. -/
theorem weighted_compact_strip_finite_cover {u₀ U : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ weightedOffAxisStrip u₀ U) :
    ∃ t : Finset (WeightedStripRectangleIndex u₀ U),
      K ⊆ ⋃ q ∈ t, weightedStripRectangle u₀ U q := by
  let O := fun q : WeightedStripRectangleIndex u₀ U =>
    Iio (q.1.1 : ℝ) ×ˢ Ioi (q.1.2 : ℝ)
  have hcover : K ⊆ ⋃ q, O q := by
    intro p hp
    have hs := hsub hp
    obtain ⟨b, hub, hba⟩ := exists_rat_btwn hs.2.2.1
    obtain ⟨c, hbc, hca⟩ := exists_rat_btwn hba
    have hum : p.1 ≤ min U (b : ℝ) := le_min hs.2.1 hub.le
    let q : WeightedStripRectangleIndex u₀ U :=
      ⟨(b, c), hs.1.trans hum, (min_le_right U (b : ℝ)).trans_lt hbc,
        hca.le.trans hs.2.2.2⟩
    exact mem_iUnion.mpr ⟨q, hub, hca⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O (fun _ => isOpen_Iio.prod isOpen_Ioi) hcover
  refine ⟨t, ?_⟩
  intro p hp
  obtain ⟨q, hq⟩ := mem_iUnion.mp (ht hp)
  obtain ⟨hqt, hpO⟩ := mem_iUnion.mp hq
  have hs := hsub hp
  exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqt,
    ⟨hs.1, le_min hs.2.1 hpO.1.le⟩, hpO.2.le, hs.2.2.2⟩⟩

/-- Finite lower integral on every strip rectangle implies finite lower
integral on every compact off-axis subset. No measurability of the output
is required. Paper `e1a0fd5`, lines 1268–1276. -/
theorem weighted_compact_lintegral_lt_top_of_rectangles {u₀ U : ℝ}
    {K : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ≥0∞}
    (hK : IsCompact K) (hsub : K ⊆ weightedOffAxisStrip u₀ U)
    (hfinite : ∀ q : WeightedStripRectangleIndex u₀ U,
      (∫⁻ p in weightedStripRectangle u₀ U q, f p) < ⊤) :
    (∫⁻ p in K, f p) < ⊤ := by
  classical
  obtain ⟨t, ht⟩ := weighted_compact_strip_finite_cover hK hsub
  have hcover : K ⊆ ⋃ q : {q // q ∈ t}, weightedStripRectangle u₀ U q.1 := by
    intro p hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp (ht hp)
    obtain ⟨hqt, hpq⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨q, hqt⟩, hpq⟩
  calc
    _ ≤ ∫⁻ p in ⋃ q : {q // q ∈ t}, weightedStripRectangle u₀ U q.1, f p :=
      lintegral_mono_set hcover
    _ ≤ ∑' q : {q // q ∈ t}, ∫⁻ p in weightedStripRectangle u₀ U q.1, f p :=
      lintegral_iUnion_le _ _
    _ < ⊤ := by
      rw [tsum_fintype]
      exact ENNReal.sum_lt_top.mpr (fun q _ => hfinite q.1)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A radius cutoff of a proper triangle is compact. Paper `e1a0fd5`,
lines 1268–1276. Radius continuity is part of the standing class. -/
theorem isCompact_weightedCutoffDomain {u₀ U η : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) : IsCompact (weightedCutoffDomain S u₀ U η) := by
  have hr := (h.regularCenter.continuous_r.mono
    (weightedTruncatedDomain_subset_triangle hi hU)).upperSemicontinuousOn
  exact hr.isCompact_inter_preimage_Ici (isCompact_weightedTruncatedDomain u₀ U) η

/-- A positive-radius cutoff lies strictly off the axis. Paper `e1a0fd5`,
lines 1268–1276 and 1311–1316. -/
theorem weightedCutoffDomain_subset_strip {u₀ U η : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hη : 0 < η) :
    weightedCutoffDomain S u₀ U η ⊆ weightedOffAxisStrip u₀ U := by
  intro p hp
  have hr := (h.radius_bounds (weightedTruncatedDomain_subset_triangle hi hU hp.1)).2
  have hηr : η ≤ S.r p.1 p.2 := hp.2
  exact ⟨hp.1.1, hp.1.2.1, by linarith, hp.1.2.2.2⟩

/-- The full radius-cutoff norm of the literal finite-M_U frozen solution is finite. This supplies
preliminary finiteness for radius-cutoff energy integration, without assuming the final N_U norm is
finite. Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1268–1276. -/
theorem weightedFrozenSolution_cutoff_energy_lt_top {u₀ U η : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hη : 0 < η)
    {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF : Measurable F)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    (∫⁻ p in weightedCutoffDomain S u₀ U η,
      ENNReal.ofReal (weightedRemainderDensity S p *
        |weightedFrozenSolution S u₀ J₀ F p| ^ 2)) < ⊤ := by
  apply weighted_compact_lintegral_lt_top_of_rectangles
    (h.isCompact_weightedCutoffDomain hi hU) (h.weightedCutoffDomain_subset_strip hi hU hη)
  intro q
  rw [weightedStripRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans_lt
  exact h.weightedFrozenSolution_rectangle_energy_lt_top hi hU q.2.1 (min_le_left _ _)
    q.2.2.1 q.2.2.2 hJ₀ hF hinitial hsource

end StandingFull

end AcExtensionPrinciple

end
