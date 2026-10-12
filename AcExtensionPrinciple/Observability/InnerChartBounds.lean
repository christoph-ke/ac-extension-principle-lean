module

public import AcExtensionPrinciple.Observability.InnerChartGeometry
public import AcExtensionPrinciple.Observability.ChartRegularity
public import AcExtensionPrinciple.Gauge.Variation

/-!
# Uniform scalar bounds needed for inner-coordinate BV transport

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1877–1907.
No continuity of the BV scalar derivative representatives is assumed.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped Topology

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The full closed normalized cylinder is compact. Paper `e1a0fd5`,
lines 1460–1473; compact local BV bounds at lines 220–275. -/
theorem inner_source_compact : IsCompact (chartCylinder h.g T) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.continuous_g.continuousOn : ContinuousOn h.g (Icc 0 T))
  have hclosed : IsClosed (chartCylinder h.g T) :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le (h.continuous_g.comp continuous_fst) continuous_snd).inter
          (isClosed_le continuous_snd continuous_fst)))
  apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod
    (isCompact_Icc : IsCompact (Icc (-M) T))).of_isClosed_subset hclosed
  intro q hq
  have hh : |h.g q.1| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM q.1 ⟨hq.1, hq.2.1⟩
  exact ⟨⟨hq.1, hq.2.1⟩,
    ⟨(neg_le_neg hh).trans ((neg_abs_le _).trans hq.2.2.1),
      hq.2.2.2.trans hq.2.1⟩⟩

/-- Both boundary scalar derivatives are bounded pointwise, including
their chosen BV representatives. Paper `e1a0fd5`, line 1522 and
`eq:observability-energy-integral`, lines 1477–1480. -/
theorem inner_boundary_scalar_bound :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 T, |S.dupsi x x| ≤ M ∧ |S.dvpsi x x| ≤ M := by
  apply IsCompact.induction_on (s := Icc 0 T) isCompact_Icc
    (p := fun U => ∃ M, 0 ≤ M ∧ ∀ x ∈ U, |S.dupsi x x| ≤ M ∧ |S.dvpsi x x| ≤ M)
  · exact ⟨0, le_rfl, by simp⟩
  · intro U V hUV hV
    obtain ⟨M, hM, hb⟩ := hV
    exact ⟨M, hM, fun x hx => hb x (hUV hx)⟩
  · intro U V hU hV
    obtain ⟨M, hM, hb⟩ := hU
    obtain ⟨N, hN, hc⟩ := hV
    refine ⟨M + N, add_nonneg hM hN, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact ⟨(hb x hx).1.trans (le_add_of_nonneg_right hN),
        (hb x hx).2.trans (le_add_of_nonneg_right hN)⟩
    · exact ⟨(hc x hx).1.trans (le_add_of_nonneg_left hM),
        (hc x hx).2.trans (le_add_of_nonneg_left hM)⟩
  · intro x hx
    obtain ⟨l, r, hl, hlr, hr, hg, hnear⟩ := h.exists_boundary_triangle hx
    obtain ⟨M, hM, hb⟩ := (h.scalar_triangle_regularity hl hlr hr hg).1
    exact ⟨Icc l r, hnear, M, hM, fun y hy => hb y y ⟨hy.1, le_rfl, hy.2⟩⟩

/-- The uniform characteristic BV fields and the boundary bound control
both scalar derivatives on all rays that have entered the outer cylinder.
This includes the regular axis. Paper `e1a0fd5`, line 1522,
lines 1692–1698 and 1877–1907. -/
theorem inner_source_scalar_bound : ∃ M, 0 ≤ M ∧
    ∀ s t, (s, t) ∈ chartCylinder h.g T → 0 ≤ t →
      |S.dupsi s t| ≤ M ∧ |S.dvpsi s t| ≤ M := by
  obtain ⟨B, hB, hb⟩ := h.inner_boundary_scalar_bound
  obtain ⟨A, hA⟩ := h.psi_s_variation _ h.inner_source_compact Subset.rfl
  obtain ⟨D, hD⟩ := h.psi_t_variation _ h.inner_source_compact Subset.rfl
  refine ⟨max A 0 + max D 0 + B, by positivity, ?_⟩
  intro s t hp ht
  have hsI : s ∈ Icc 0 T := ⟨hp.1, hp.2.1⟩
  have htI : t ∈ Icc 0 T := ⟨ht, hp.2.2.2.trans hp.2.1⟩
  have hts := hp.2.2.2
  have hva := hA t t s hts (h.in_subset ht hp.2.1 le_rfl hp.2.2.1)
  have hvd := hD s t s hts (h.out_subset hsI hp.2.2.1 le_rfl)
  have hba : BoundedVariationOn (fun x => S.dupsi x t) (Icc t s) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hva
  have hbd : BoundedVariationOn (S.dvpsi s) (Icc t s) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvd
  have hat := boundedVariation_abs_bound hba (right_mem_Icc.mpr hts)
    (left_mem_Icc.mpr hts)
  have hdt := boundedVariation_abs_bound hbd (left_mem_Icc.mpr hts)
    (right_mem_Icc.mpr hts)
  have hta : (eVariationOn (fun x => S.dupsi x t) (Icc t s)).toReal ≤ max A 0 := by
    simpa only [ENNReal.toReal_ofReal'] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hva
  have htd : (eVariationOn (S.dvpsi s) (Icc t s)).toReal ≤ max D 0 := by
    simpa only [ENNReal.toReal_ofReal'] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvd
  constructor
  · linarith [(hb t htI).1, le_max_right D 0]
  · linarith [(hb s hsI).2, le_max_right A 0]

end NormalizedChartData

end AcExtensionPrinciple

end
