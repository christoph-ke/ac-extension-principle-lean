module

public import AcExtensionPrinciple.Solution.InitialMassRatio

/-!
# The positive minimum on the initial cone

Paper `e1a0fd5`,
`eq:initial-gap-and-expansion-bound` (lines 283–287 and 309–310).
The infimum has a single subtype index, so every index belongs to the
compact initial segment.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- The initial mass gap, indexed by points of the initial interval.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`. -/
@[expose] noncomputable def initialGap (ui : ℝ) (S : SSFields) : ℝ :=
  ⨅ v : Icc ui 0, 1 - S.mu ui v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The initial gap values are bounded below by zero.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`, lines 309–310. -/
theorem initial_gap_bddBelow : BddBelow (range (fun v : Icc ui 0 => 1 - S.mu ui v)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (sub_pos.mpr (h.mu_bounds (p := (ui, v))
    ⟨le_rfl, h.initial_negative, v.property.1, v.property.2⟩).2).le

/-- The initial minimum lies below each initial gap value.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`. -/
theorem initialGap_le {v : ℝ} (hv : v ∈ Icc ui 0) :
    initialGap ui S ≤ 1 - S.mu ui v :=
  ciInf_le h.initial_gap_bddBelow ⟨v, hv⟩

/-- The initial gap is attained on the compact initial segment.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`, lines 309–310. -/
theorem initialGap_attained : ∃ v ∈ Icc ui 0, initialGap ui S = 1 - S.mu ui v := by
  have : Nonempty (Icc ui 0) := ⟨⟨ui, le_rfl, h.initial_negative.le⟩⟩
  obtain ⟨v, hv, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr h.initial_negative.le)
    (continuousOn_const.sub h.continuous_mu_initial)
  refine ⟨v, hv, le_antisymm (h.initialGap_le hv) ?_⟩
  exact le_ciInf (fun w => hmin w.property)

/-- G0: the attained initial gap is strictly positive.
Paper `e1a0fd5`, `eq:initial-gap-and-expansion-bound`, lines 283–287, 309–310. -/
theorem initialGap_pos : 0 < initialGap ui S := by
  obtain ⟨v, hv, he⟩ := h.initialGap_attained
  rw [he]
  exact sub_pos.mpr (h.mu_bounds (p := (ui, v))
    ⟨le_rfl, h.initial_negative, hv.1, hv.2⟩).2

/-- The regular-axis gap bounds the initial minimum above by one.
Paper `e1a0fd5`, line 275, `eq:initial-gap-and-expansion-bound`. -/
theorem initialGap_le_one : initialGap ui S ≤ 1 := by
  have hb := h.initialGap_le (v := ui) ⟨le_rfl, h.initial_negative.le⟩
  simpa [h.mu_axis ⟨le_rfl, h.initial_negative, rfl⟩] using hb

end StandingFull

end AcExtensionPrinciple

end
