module

public import AcExtensionPrinciple.Redundancy.RestoreContinuity
public import AcExtensionPrinciple.Solution.Geometry
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.ProjIcc

/-!
# Radius continuity follows from the remaining class
Paper commit `e1a0fd5`, `equations.tex` lines 220–275,
`eq:regular-axis`, `eq:radius-from-axis`. An outgoing primitive of the
remaining continuous expansion has a jointly continuous integral from the axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous expansion has a continuous extension from any proper triangular cutoff. Paper
`e1a0fd5`, lines 220–275, `eq:past-triangle`. The extension is used only for integration and
satisfies no field equation. -/
theorem q1_triangle_extension {ui U : ℝ} {f : ℝ → ℝ → ℝ}
    (hui : ui ≤ U) (hU : U < 0)
    (hf : ContinuousOn (fun p => f p.1 p.2) (pastTriangle ui)) :
    ∃ g : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => g p.1 p.2) ∧
      ∀ p ∈ pastTriangle ui, p.1 ≤ U → g p.1 p.2 = f p.1 p.2 := by
  let c : ℝ → ℝ := fun u => projIcc ui U hui u
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  let g := fun u v => f (c u) (max (c u) (min 0 v))
  refine ⟨g, ?_, ?_⟩
  · exact hf.comp_continuous
      ((hc.comp continuous_fst).prodMk
        ((hc.comp continuous_fst).max (continuous_const.min continuous_snd)))
      (fun p => ⟨(projIcc ui U hui p.1).2.1,
        ((projIcc ui U hui p.1).2.2).trans_lt hU,
        le_max_left _ _, max_le ((projIcc ui U hui p.1).2.2.trans hU.le)
          (min_le_left _ _)⟩)
  · intro p hp hpU
    simp only [g, c, projIcc_of_mem hui ⟨hp.1, hpU⟩,
      min_eq_right hp.2.2.2, max_eq_right hp.2.2.1]

/-- The radius continuity field of the full working class is redundant. The proof uses only the
outgoing radius identity, its zero axis value, and retained λ continuity. Paper `e1a0fd5`, lines
220–275, `eq:regular-axis`, `eq:radius-from-axis`. -/
theorem continuous_r_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_r ui S) :
    ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui) := by
  intro p hp
  let U := p.1 / 2
  have hpU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hU : U < 0 := by dsimp [U]; linarith [hp.2.1]
  obtain ⟨g, hg, he⟩ := q1_triangle_extension (hp.1.trans hpU.le) hU h.continuous_lam
  have hgc : Continuous (fun z : (ℝ × ℝ) × ℝ => g z.1.1 z.2) :=
    hg.comp (continuous_fst.fst.prodMk continuous_snd)
  have hc : Continuous (fun q : ℝ × ℝ => ∫ s in q.1..q.2, g q.1 s) := by
    have hv := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun (q : ℝ × ℝ) s => g q.1 s) (a₀ := (0 : ℝ)) hgc continuous_snd
    have hu := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun (q : ℝ × ℝ) s => g q.1 s) (a₀ := (0 : ℝ)) hgc continuous_fst
    convert hv.sub hu using 1
    ext q
    have hs : Continuous (g q.1) :=
      hg.comp (continuous_const.prodMk continuous_id)
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hs.intervalIntegrable 0 q.1)
      (hs.intervalIntegrable q.1 q.2)
    dsimp only [Pi.sub_apply] at *
    linarith
  have hrep (q : ℝ × ℝ) (hq : q ∈ pastTriangle ui) (hqU : q.1 ≤ U) :
      S.r q.1 q.2 = ∫ s in q.1..q.2, g q.1 s := by
    have hi := (h.regularCenter.localBV.radius_out q.1 q.1 q.2 hq.2.2.1
      (outSeg_subset_triangle hq.1 hq.2.1 le_rfl hq.2.2.2)).2
    rw [(h.regularCenter.localBV.axis_values q.1
      ⟨hq.1, hq.2.1, le_rfl, hq.2.1.le⟩).1, sub_zero] at hi
    rw [hi]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hq.2.2.1] at hs
    exact (he (q.1, s) ⟨hq.1, hq.2.1, hs.1, hs.2.trans hq.2.2.2⟩ hqU).symm
  apply (hc.continuousWithinAt).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono
        nhdsWithin_le_nhds] with q hq hqU
    exact hrep q hq hqU.le
  · exact hrep p hp hpU.le

end AcExtensionPrinciple

end
