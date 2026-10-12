module

public import AcExtensionPrinciple.Minimal.Geometry
public import AcExtensionPrinciple.Redundancy.RadiusContinuity

/-!
# Radius continuity before restoring any deleted field
Paper `e1a0fd5`, `equations.tex` lines 66–84, 122–124 and 220–275.
Integrate the retained continuous ν from the initial gauge.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The incoming radius primitive and the initial gauge give joint radius continuity.
The only continuity premise is the retained ν field. Paper `e1a0fd5`,
`eq:radius`, lines 66–84, 122–124 and 222. -/
theorem StandingAssumptions.continuous_r {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) :
    ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui) := by
  intro p hp
  let U := p.1 / 2
  have hpU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hU : U < 0 := by dsimp [U]; linarith [hp.2.1]
  obtain ⟨g, hg, he⟩ := q1_triangle_extension (hp.1.trans hpU.le) hU
    h.regularCenter.continuous_nu
  have hgc : Continuous (fun z : (ℝ × ℝ) × ℝ => g z.2 z.1.2) :=
    hg.comp (continuous_snd.prodMk continuous_fst.snd)
  have hc : Continuous (fun q : ℝ × ℝ =>
      (∫ s in ui..q.1, g s q.2) + (q.2 - ui)) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun (q : ℝ × ℝ) s => g s q.2)
      (a₀ := ui) hgc continuous_fst).add (continuous_snd.sub continuous_const)
  have hrep (q : ℝ × ℝ) (hq : q ∈ pastTriangle ui) (hqU : q.1 ≤ U) :
      S.r q.1 q.2 = (∫ s in ui..q.1, g s q.2) + (q.2 - ui) := by
    have hi := h.regularCenter.localBV.radius_in q.2 ui q.1 hq.1
      (inSeg_subset_triangle le_rfl hq.2.1 hq.2.2.1 hq.2.2.2)
    have hge : (∫ s in ui..q.1, g s q.2) = ∫ s in ui..q.1, S.nu s q.2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hq.1] at hs
      exact he (s, q.2)
        ⟨hs.1, hs.2.trans_lt hq.2.1, hs.2.trans hq.2.2.1, hq.2.2.2⟩
        (hs.2.trans hqU)
    rw [hge]
    have hgauge := (h.initial_gauge q.2 ⟨hq.1.trans hq.2.2.1, hq.2.2.2⟩).1
    linarith [hi.2]
  apply hc.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono
        nhdsWithin_le_nhds] with q hq hqU
    exact hrep q hq hqU.le
  · exact hrep p hp hpU.le

end AcExtensionPrinciple

end
