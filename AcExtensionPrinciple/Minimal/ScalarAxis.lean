module

public import AcExtensionPrinciple.Minimal.OneSidedPhiContinuity

/-!
# Scalar joint axis traces follow from one-sided traces and primitives

Paper commit `e1a0fd5`, `equations.tex` lines 220–261,
`eq:regular-axis-scalar-traces`. Characteristic traces, vanishing variation, and
the primitive equations give the joint scalar trace. No φ continuity is an input.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- One-sided normalized traces and vanishing variation imply the joint scalar
trace before any scalar or expansion regularity is restored. Paper `e1a0fd5`,
lines 220–261, `eq:axis-vanishing-variation`, `eq:regular-axis-scalar-traces`. -/
theorem minimal_phi_axis_trace {ui a : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) :=
  h.oneSided_phi_axis_trace ha

/-- Outgoing scalar continuity follows from the quotient off-axis and the normalized
axis trace, before restoring scalar AC. Paper `e1a0fd5`, lines 220–261,
`eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.phi_out_continuous {ui u : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (S.phi u) (Icc u 0) := by
  intro v hv
  rcases hv.1.eq_or_lt with he | he
  · subst v
    apply continuousWithinAt_sdiff_self.mp
    have ha : (u, u) ∈ axis ui := ⟨hu, hu0, rfl⟩
    have hc : ContinuousWithinAt (fun w : ℝ => (u, w)) (Icc u 0 \ {u}) u :=
      (continuous_const.prodMk continuous_id).continuousWithinAt
    have hm : MapsTo (fun w : ℝ => (u, w)) (Icc u 0 \ {u})
        (pastTriangle ui \ axis ui) := by
      intro w hw
      rw [← cylinderScalarRegion_eq_axisComplement]
      exact ⟨hu, lt_of_le_of_ne hw.1.1
        (fun he => hw.2 (mem_singleton_iff.mpr (show u = w from he).symm)), hw.1.2⟩
    exact (minimal_phi_axis_trace h ha).comp (hc.tendsto_nhdsWithin hm)
  · have hc := (h.continuous_phi_offAxis (u, v) ⟨hu, he, hv.2⟩).comp_of_eq
      ((continuous_const.prodMk continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun w : ℝ => (u, w)) (Icc u 0 ∩ Ioi u) v)
      (fun w hw => ⟨hu, hw.2, hw.1.2⟩) rfl
    exact hc.mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Ioi_mem_nhds he)))

/-- The scalar continuity field of the full working class is redundant. Off-axis continuity
uses uniform ψ derivative BV bounds; at the axis, its derived scalar trace and
outgoing characteristic continuity control also nearby stored axis values.
Paper `e1a0fd5`, lines 220–261, `eq:regular-axis-scalar-traces`, `eq:wave-psi`. -/
theorem StandingAssumptions.continuous_phi {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) :
    ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have ht := minimal_phi_axis_trace h ha
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, htrace⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht (ε / 2) (by positivity)
    refine ⟨δ / 2, by positivity, ?_⟩
    intro q hq hqd
    have hpEq : p = (p.1, p.1) := Prod.ext rfl he.symm
    have hqp : dist q (p.1, p.1) < δ / 2 := by
      rw [← hpEq]
      exact hqd
    rcases hq.2.2.1.eq_or_lt with hqe | hql
    · have hc := h.phi_out_continuous hq.1 hq.2.1 q.2
        (show q.2 ∈ Icc q.1 0 from ⟨hq.2.2.1, hq.2.2.2⟩)
      obtain ⟨η, hη, hηφ⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by positivity)
      let t := min (-q.1 / 2) (min (δ / 4) (η / 2))
      have htpos : 0 < t := lt_min (by linarith [hq.2.1])
        (lt_min (by positivity) (by positivity))
      have hqt0 : q.1 + t ≤ 0 := by
        have hb : t ≤ -q.1 / 2 := min_le_left _ _
        linarith [hq.2.1]
      have htδ : t ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
      have htη : t ≤ η / 2 := (min_le_right _ _).trans (min_le_right _ _)
      have hdist : dist (q.1 + t) q.2 = t := by
        rw [← hqe, Real.dist_eq, show q.1 + t - q.1 = t by ring, abs_of_pos htpos]
      have hclose := hηφ (x := q.1 + t) ⟨by linarith, hqt0⟩
        (by rw [hdist]; linarith)
      have hnear : dist (q.1, q.1 + t) (p.1, p.1) < δ := by
        have hh : dist (q.1, q.1 + t) q = t := by
          rw [Prod.dist_eq, dist_self, hdist, max_eq_right htpos.le]
        have hb := dist_triangle (q.1, q.1 + t) q (p.1, p.1)
        rw [hh] at hb
        linarith
      have htr := htrace (x := (q.1, q.1 + t))
        (by rw [← cylinderScalarRegion_eq_axisComplement]
            exact ⟨hq.1, by linarith, hqt0⟩) hnear
      have hb := dist_triangle (S.phi q.1 q.2) (S.phi q.1 (q.1 + t)) (S.phi p.1 p.1)
      rw [dist_comm (S.phi q.1 q.2) (S.phi q.1 (q.1 + t))] at hb
      simpa only [← he] using (show dist (S.phi q.1 q.2) (S.phi p.1 p.1) < ε by linarith)
    · have htq := htrace (x := q)
        (by rw [← cylinderScalarRegion_eq_axisComplement]; exact ⟨hq.1, hql, hq.2.2.2⟩)
        (by linarith)
      simpa only [← he] using (htq.trans (by linarith : ε / 2 < ε))
  · have hc := h.continuous_phi_offAxis p ⟨hp.1, he, hp.2.2.2⟩
    apply hc.mono_of_mem_nhdsWithin
    have ho : {q : ℝ × ℝ | q.1 < q.2} ∈ 𝓝 p :=
      isOpen_lt continuous_fst continuous_snd |>.mem_nhds he
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < q.2 from ho)] with q hq hlt
    exact ⟨hq.1, hlt, hq.2.2.2⟩

end AcExtensionPrinciple

end
