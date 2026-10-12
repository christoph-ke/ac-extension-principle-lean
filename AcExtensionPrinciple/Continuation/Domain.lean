module

public import AcExtensionPrinciple.Continuation.Restriction
public import AcExtensionPrinciple.Solution.Geometry

/-!
# Proper past sets and compact original triangles

This module proves domain facts for original class membership at line 1411 of paper `e1a0fd5`. The
compact sets include the regular axis and v = 0, and exclude (0,0).
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- The vertex is adjacent to every nonempty proper causal past.
Paper `e1a0fd5`, `equations.tex` line 1411. -/
theorem zero_mem_pastSet_adjacentAxis {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ∈ adjacentAxis (pastSet a b) := by
  have ht : Tendsto (fun ε : ℝ => ((0 : ℝ), ε)) (𝓝[>] 0) (𝓝 (0, 0)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
  exact ⟨⟨le_rfl, ha⟩, hε.1, hε.2.le⟩

/-- The union of proper causal pasts is the late off-axis triangle,
including the terminal incoming ray. Paper `e1a0fd5`, line 1411. -/
theorem mem_late_triangle_iff {b : ℝ} {p : ℝ × ℝ} :
    (0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) ↔
      ∃ a, 0 ≤ a ∧ a < b ∧ p ∈ pastSet a b := by
  constructor
  · rintro ⟨hu, huv, hv⟩
    exact ⟨p.1, hu, huv.trans_le hv, ⟨⟨hu, le_rfl⟩, huv, hv⟩⟩
  · rintro ⟨a, _, _, hp⟩
    exact ⟨hp.1.1, hp.2.1, hp.2.2⟩

/-- A proper original compact triangle reaches v = 0 while keeping u < 0. Paper `e1a0fd5`, lines
1390–1411, original class membership in the continuation chart, ruling Q6. -/
@[expose] def properOriginalTriangle (ū c : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc ū c ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0}

/-- The proper original triangle is compact, including its axis and terminal
ray boundaries. Paper `e1a0fd5`, lines 1390–1411, Q6. -/
theorem isCompact_properOriginalTriangle (ū c : ℝ) :
    IsCompact (properOriginalTriangle ū c) := by
  have he : properOriginalTriangle ū c =
      (Icc ū c ×ˢ Icc ū 0) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    ext p
    simp only [properOriginalTriangle, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨hu, huv, hv⟩
      exact ⟨⟨hu, hu.1.trans huv, hv⟩, huv⟩
    · rintro ⟨⟨hu, hv⟩, huv⟩
      exact ⟨hu, huv, hv.2⟩
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst continuous_snd)

/-- Q6 applies to this compact set even on v = 0. Paper `e1a0fd5`, lines 1390–1411, original class
membership in the continuation chart. -/
theorem properOriginalTriangle_subset {ui ū c : ℝ} (hū : ui ≤ ū) (hc : c < 0) :
    properOriginalTriangle ū c ⊆ pastTriangle ui :=
  fun _ hp => ⟨hū.trans hp.1.1, hp.1.2.trans_lt hc, hp.2.1, hp.2.2⟩

end AcExtensionPrinciple

end
