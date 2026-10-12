module

public import AcExtensionPrinciple.Redundancy.ScalarInterior

/-!
# Scalar joint axis traces follow from normalized traces and primitives

Paper commit `e1a0fd5`, `equations.tex` lines 220–275,
`eq:regular-axis-scalar-traces`. The scalar is a λ-weighted average of its
normalized outgoing ψ derivative. No φ continuity is used here.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Normalized outgoing scalar traces imply the same joint off-axis trace for
φ, by its weighted-average primitive. Paper `e1a0fd5`, lines 247–261,
`eq:regular-axis-scalar-traces`, `eq:radius-from-axis`, `eq:wave-psi`. -/
theorem q1_phi_axis_trace {ui a : ℝ} {S : SSFields} (h : Q1StandingCore ui S)
    (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, htrace⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (h.regularCenter.axis_dvpsi_trace a ha) (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpd
  have hpa : p.1 < p.2 := (cylinderScalarRegion_eq_axisComplement ui ▸ hp).2.1
  have hr := h.r_pos hp.1 hpa
  have hs := outSeg_subset_triangle hp.1.1 hp.1.2.1 le_rfl hp.1.2.2.2
  have hir := h.regularCenter.localBV.radius_out p.1 p.1 p.2 hpa.le hs
  have hiψ := h.regularCenter.localBV.psi_out p.1 p.1 p.2 hpa.le hs
  have hav := h.regularCenter.localBV.axis_values p.1
    ⟨hp.1.1, hp.1.2.1, le_rfl, hp.1.2.1.le⟩
  have her : (∫ s in p.1..p.2, S.lam p.1 s) = S.r p.1 p.2 := by
    have he := hir.2
    rw [hav.1, sub_zero] at he
    exact he.symm
  have heψ : (∫ s in p.1..p.2, S.dvpsi p.1 s) = S.r p.1 p.2 * S.phi p.1 p.2 := by
    have he := hiψ.2
    dsimp only at he
    rw [hav.1, zero_mul, sub_zero] at he
    exact he.symm
  have hnear (s : ℝ) (hs' : s ∈ Ioo p.1 p.2) :
      dist (S.dvpsi p.1 s / S.lam p.1 s) (S.phi a a) < ε / 2 := by
    apply htrace (x := (p.1, s))
    · rw [← cylinderScalarRegion_eq_axisComplement]
      exact ⟨hp.1.1, hs'.1, hs'.2.le.trans hp.1.2.2.2⟩
    · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hpd ⊢
      exact ⟨hpd.1, ⟨by dsimp only at hpd ⊢; linarith [hpd.1.1, hs'.1],
        by dsimp only at hpd ⊢; linarith [hpd.2.2, hs'.2]⟩⟩
  have hlo : (S.phi a a - ε / 2) * S.r p.1 p.2 ≤ S.r p.1 p.2 * S.phi p.1 p.2 := by
    rw [← heψ, ← her, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hpa.le
      (hir.1.const_mul _) hiψ.1
    intro s hs'
    have hl := h.lam_pos (p := (p.1, s))
      ⟨hp.1.1, hp.1.2.1, hs'.1.le, hs'.2.le.trans hp.1.2.2.2⟩
    have he := (hnear s hs')
    rw [Real.dist_eq, abs_lt] at he
    have hb := (le_div_iff₀ hl).mp (show S.phi a a - ε / 2 ≤
      S.dvpsi p.1 s / S.lam p.1 s by linarith [he.1])
    exact hb
  have hhi : S.r p.1 p.2 * S.phi p.1 p.2 ≤ (S.phi a a + ε / 2) * S.r p.1 p.2 := by
    rw [← heψ, ← her, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hpa.le hiψ.1 (hir.1.const_mul _)
    intro s hs'
    have hl := h.lam_pos (p := (p.1, s))
      ⟨hp.1.1, hp.1.2.1, hs'.1.le, hs'.2.le.trans hp.1.2.2.2⟩
    have he := (hnear s hs')
    rw [Real.dist_eq, abs_lt] at he
    exact (div_le_iff₀ hl).mp (show S.dvpsi p.1 s / S.lam p.1 s ≤
      S.phi a a + ε / 2 by linarith [he.2])
  have hloφ : S.phi a a - ε / 2 ≤ S.phi p.1 p.2 :=
    (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm (S.r p.1 p.2)] using hlo)
  have hhiφ : S.phi p.1 p.2 ≤ S.phi a a + ε / 2 :=
    (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm (S.r p.1 p.2)] using hhi)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Outgoing scalar restrictions are continuous, without the joint continuity
field, directly from Luk–Oh characteristic AC. Paper `e1a0fd5`, line 222,
Luk–Oh Definition 2.1(4). -/
theorem Q1StandingCore.phi_out_continuous {ui u : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (S.phi u) (Icc u 0) := by
  have hs := outSeg_subset_triangle hu hu0 le_rfl le_rfl
  obtain ⟨C, hC, _⟩ := h.regularCenter.localBV.scalar_ac_variation (outSeg u u 0)
    (isCompact_singleton.prod isCompact_Icc) hs
  simpa only [uIcc_of_le hu0.le] using (hC u u 0 hu0.le Subset.rfl).1.continuousOn

/-- The scalar continuity field of the full working class is redundant. Off-axis continuity
uses uniform ψ derivative BV bounds; at the axis, its weighted-average trace and
outgoing characteristic continuity control also nearby stored axis values.
Paper `e1a0fd5`, lines 220–275, `eq:regular-axis-scalar-traces`, `eq:wave-psi`. -/
theorem continuous_phi_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_phi ui S) :
    ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have ht := q1_phi_axis_trace h.toQ1StandingCore ha
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
    · have hc := h.toQ1StandingCore.phi_out_continuous hq.1 hq.2.1 q.2
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
  · have hc := continuous_phi_offAxis_of_rest h p ⟨hp.1, he, hp.2.2.2⟩
    apply hc.mono_of_mem_nhdsWithin
    have ho : {q : ℝ × ℝ | q.1 < q.2} ∈ 𝓝 p :=
      isOpen_lt continuous_fst continuous_snd |>.mem_nhds he
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < q.2 from ho)] with q hq hlt
    exact ⟨hq.1, hlt, hq.2.2.2⟩

end AcExtensionPrinciple

end
