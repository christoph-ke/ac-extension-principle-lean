module

public import AcExtensionPrinciple.Weighted.ClassMeasurable
public import AcExtensionPrinciple.Weighted.ClassAmplitude

/-!
# Measurable incoming amplitudes on a truncated off-axis strip

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1189–1202. Rational off-axis rectangles form a
countable cover; their local measurable extensions patch without a
global regularity assumption on derivative fields.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The off-axis strip in the kernel's variables (u,a).
Paper `e1a0fd5`, lines 1189–1201. -/
@[expose] def weightedOffAxisStrip (u₀ U : ℝ) : Set (ℝ × ℝ) :=
  {p | u₀ ≤ p.1 ∧ p.1 ≤ U ∧ p.1 < p.2 ∧ p.2 ≤ 0}

/-- Rational rectangles with a positive gap between the two coordinates.
Paper `e1a0fd5`, lines 1189–1202, local BV measurability. -/
@[expose] def WeightedStripRectangleIndex (u₀ U : ℝ) :=
  {q : ℚ × ℚ // u₀ ≤ min U (q.1 : ℝ) ∧ min U (q.1 : ℝ) < (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ 0}

/-- The rectangle index is countable. Paper `e1a0fd5`, lines 1189–1202. -/
instance (u₀ U : ℝ) : Countable (WeightedStripRectangleIndex u₀ U) := by
  unfold WeightedStripRectangleIndex
  infer_instance

/-- The corresponding closed rectangle. Paper `e1a0fd5`,
lines 1189–1202, local BV measurability. -/
@[expose] def weightedStripRectangle (u₀ U : ℝ) (q : WeightedStripRectangleIndex u₀ U) :
    Set (ℝ × ℝ) := Icc u₀ (min U (q.1.1 : ℝ)) ×ˢ Icc (q.1.2 : ℝ) 0

/-- These rational rectangles cover exactly the off-axis strip.
Paper `e1a0fd5`, lines 1189–1202, local BV measurability. -/
theorem weightedOffAxisStrip_eq_iUnion (u₀ U : ℝ) :
    weightedOffAxisStrip u₀ U = ⋃ q, weightedStripRectangle u₀ U q := by
  ext p
  constructor
  · intro hp
    obtain ⟨b, hub, hba⟩ := exists_rat_btwn hp.2.2.1
    obtain ⟨c, hbc, hca⟩ := exists_rat_btwn hba
    have hum : p.1 ≤ min U (b : ℝ) := le_min hp.2.1 hub.le
    let q : WeightedStripRectangleIndex u₀ U :=
      ⟨(b, c), hp.1.trans hum, (min_le_right U (b : ℝ)).trans_lt hbc, hca.le.trans hp.2.2.2⟩
    exact mem_iUnion.mpr ⟨q, ⟨hp.1, hum⟩, ⟨hca.le, hp.2.2.2⟩⟩
  · intro hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp hp
    exact ⟨hq.1.1, hq.1.2.trans (min_le_left _ _),
      hq.1.2.trans_lt (q.2.2.1.trans_le hq.2.1), hq.2.2⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming ψ derivative has a measurable extension from the strip.
Paper `e1a0fd5`, lines 1189–1202. -/
theorem weighted_exists_measurable_dupsi_strip {u₀ U : ℝ} (hi : ui ≤ u₀) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧
      EqOn (fun p => S.dupsi p.1 p.2) F (weightedOffAxisStrip u₀ U) := by
  rw [weightedOffAxisStrip_eq_iUnion]
  apply measurable_piecewise_of_countable_extensions
    (fun _ => measurableSet_Icc.prod measurableSet_Icc)
  intro q
  exact h.weighted_exists_measurable_dupsi_rectangle hi q.2.1 q.2.2.1 q.2.2.2

/-- The actual normalized incoming amplitude has a measurable extension
from the strip. Paper `e1a0fd5`, `eq:weighted-radial-operator`,
lines 1158 and 1189–1202. -/
theorem weighted_exists_measurable_amplitude_strip {u₀ U : ℝ} (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ A : ℝ × ℝ → ℝ, Measurable A ∧
      EqOn (fun p => weightedIncomingAmplitude S p.1 p.2) A (weightedOffAxisStrip u₀ U) := by
  obtain ⟨F, hF, heF⟩ := h.weighted_exists_measurable_dupsi_strip hi
  obtain ⟨N, hN, heN⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_nu
  obtain ⟨P, hP, heP⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_phi
  refine ⟨fun p => F p / N p - P p, (hF.div hN).sub hP, ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U := ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2⟩
  dsimp only
  rw [← heF hp, ← heN hpD, ← heP hpD]
  have hpt := weightedTruncatedDomain_subset_triangle hi hU hpD
  have hr := (h.r_pos hpt hp.2.2.1).ne'
  have hn := (h.nu_neg hpt).ne
  unfold weightedIncomingAmplitude SSFields.duphi SSFields.zeta
  field_simp [hr, hn]

end StandingFull

end AcExtensionPrinciple

end
