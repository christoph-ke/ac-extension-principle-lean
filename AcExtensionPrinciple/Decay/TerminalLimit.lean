module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# A terminal limit from vanishing tail variation

Paper `e1a0fd5`, `equations.tex` lines 952–962,
`eq:terminal-scalar-variation`. Extended variation avoids assuming finiteness
of variation on early tails.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Vanishing variation of left tails gives a finite left limit by completeness;
paper `e1a0fd5`, `equations.tex` lines 952–962 (`eq:terminal-scalar-variation`). -/
theorem terminal_limit_of_tail_variation {P : ℝ → ℝ}
    (hV : Tendsto (fun a : ℝ ↦ eVariationOn P (Ico a 0)) (𝓝[<] 0) (𝓝 0)) :
    ∃ L : ℝ, Tendsto P (𝓝[<] 0) (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro eps heps
  have hsmall := hV.eventually
    (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal eps by positivity))
  have hneg : ∀ᶠ a : ℝ in 𝓝[<] 0, a < 0 := self_mem_nhdsWithin
  obtain ⟨a, ha, hVa⟩ := (hneg.and hsmall).exists
  refine ⟨P '' Ioo a 0, ?_, ?_⟩
  · change P ⁻¹' (P '' Ioo a 0) ∈ 𝓝[<] 0
    apply mem_of_superset (Ioo_mem_nhdsLT ha)
    intro x hx
    exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hdist := (eVariationOn.edist_le P
      (show x ∈ Ico a 0 from ⟨hx.1.le, hx.2⟩)
      (show y ∈ Ico a 0 from ⟨hy.1.le, hy.2⟩)).trans_lt hVa
    rw [edist_dist] at hdist
    exact (ENNReal.ofReal_lt_ofReal_iff heps).mp hdist

end AcExtensionPrinciple

end
