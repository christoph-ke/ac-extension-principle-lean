module

public import AcExtensionPrinciple.Cylinder.ScalarRegion

/-!
# Continuity of the incoming scalar derivative

This module derives incoming continuity from the solution class.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`
and `eq:wave-psi`, used for Lemma 2.4 at lines 709–737.
A near-axis base point and a continuous transport primitive give arbitrarily
accurate continuous approximations locally away from the axis.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming ψ derivative is jointly continuous off-axis, with no extra scalar premise.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, `eq:wave-psi`, lines 709–737. -/
theorem cylinder_dupsi_continuous :
    ContinuousOn (fun p => S.dupsi p.1 p.2) (cylinderScalarRegion ui) := by
  intro p hp
  have haxis : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1.trans_le hp.2.2, rfl⟩
  have ht := h.cylinder_dupsi_axis_tendsto haxis
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨delta, hdelta, hsmall⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht
    (eps / 3) (by positivity)
  let e := min ((p.2 - p.1) / 4) (delta / 4)
  have he : 0 < e := lt_min (by linarith [hp.2.1]) (by positivity)
  have hev : e ≤ (p.2 - p.1) / 4 := min_le_left _ _
  have hed : e ≤ delta / 4 := min_le_right _ _
  let a := p.1 + e
  let U := p.1 + e / 2
  have huU : p.1 < U := by dsimp [U]; linarith
  have hUa : U < a := by dsimp [U, a]; linarith
  have hav : a < p.2 := by dsimp [a]; linarith
  have ha0 : a < 0 := hav.trans_le hp.2.2
  have hUi : ui ≤ U := hp.1.trans huU.le
  let L := S.nu p.1 p.1 * S.phi p.1 p.1
  have hforce := h.cylinder_forcing_continuous.mono
    (cylinder_rectangle_subset_region (ui := ui) hUa (le_refl 0))
  obtain ⟨H, hH, hH_eq⟩ := cylinder_rectangle_extension
    (F := fun u v => S.radiusCoeff u v * S.phi u v) hUi ha0.le hforce
  let G : ℝ × ℝ → ℝ := fun q => L + ∫ s in a..q.2, H q.1 s
  have hG : Continuous G := by
    apply continuous_const.add
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hH.comp (continuous_fst.fst.prodMk continuous_snd)
    · exact continuous_snd
  have hrep (q : ℝ × ℝ) (hq : q ∈ Icc ui U ×ˢ Icc a 0) :
      S.dupsi q.1 q.2 - G q = S.dupsi q.1 a - L := by
    have hqu : q.1 < a := hq.1.2.trans_lt hUa
    have hi := h.regularCenter.localBV.dupsi_out q.1 a q.2 hq.2.1
      (outSeg_subset_offAxis hq.1.1 (hqu.trans ha0) hqu hq.2.2)
    have hint : (∫ s in a..q.2, H q.1 s) =
        ∫ s in a..q.2, S.radiusCoeff q.1 s * S.phi q.1 s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hq.2.1] at hs
      exact hH_eq q.1 hq.1 s ⟨hs.1, hs.2.trans hq.2.2⟩
    dsimp only [G]
    rw [hint]
    linarith [hi.2]
  have hpK : p ∈ Icc ui U ×ˢ Icc a 0 := ⟨⟨hp.1, huU.le⟩, ⟨hav.le, hp.2.2⟩⟩
  have hbase (u : ℝ) (hu : |u - p.1| < delta / 2) (hui : ui ≤ u) (hua : u < a) :
      dist (S.dupsi u a) L < eps / 3 := by
    apply hsmall (show (u, a) ∈ cylinderScalarRegion ui from ⟨hui, hua, ha0.le⟩)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    refine ⟨by linarith, ?_⟩
    have haeq : a - p.1 = e := by dsimp [a]; ring
    rw [haeq, abs_of_pos he]
    linarith
  have hbasep := hbase p.1 (by simpa using (by positivity : (0 : ℝ) < delta / 2))
    hp.1 (huU.trans hUa)
  have herrp : dist (G p) (S.dupsi p.1 p.2) < eps / 3 := by
    rw [dist_comm, Real.dist_eq, hrep p hpK]
    exact hbasep
  have hqU : ∀ᶠ q in 𝓝[cylinderScalarRegion ui] p, q.1 < U :=
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds huU)).filter_mono nhdsWithin_le_nhds
  have hqa : ∀ᶠ q in 𝓝[cylinderScalarRegion ui] p, a < q.2 :=
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hav)).filter_mono nhdsWithin_le_nhds
  have hqu : ∀ᶠ q in 𝓝[cylinderScalarRegion ui] p, |q.1 - p.1| < delta / 2 := by
    have hq : ∀ᶠ q in 𝓝[cylinderScalarRegion ui] p, dist q.1 p.1 < delta / 2 :=
      ((continuous_fst.tendsto p).eventually
      (Metric.ball_mem_nhds p.1 (by positivity : 0 < delta / 2))).filter_mono nhdsWithin_le_nhds
    simpa only [Metric.mem_ball, Real.dist_eq] using hq
  have hqG : ∀ᶠ q in 𝓝[cylinderScalarRegion ui] p, dist (G q) (G p) < eps / 3 :=
    ((hG.tendsto p).eventually (Metric.ball_mem_nhds (G p) (by positivity))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hqU, hqa, hqu, hqG] with q hq hqU hqa hqu hqG
  have hqK : q ∈ Icc ui U ×ˢ Icc a 0 := ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2⟩⟩
  have herrq : dist (S.dupsi q.1 q.2) (G q) < eps / 3 := by
    rw [Real.dist_eq, hrep q hqK]
    exact hbase q.1 hqu hq.1 (hqU.trans hUa)
  calc
    dist (S.dupsi q.1 q.2) (S.dupsi p.1 p.2) ≤
        dist (S.dupsi q.1 q.2) (G q) + dist (G q) (G p) +
          dist (G p) (S.dupsi p.1 p.2) := by
      linarith [dist_triangle (S.dupsi q.1 q.2) (G q) (S.dupsi p.1 p.2),
        dist_triangle (G q) (G p) (S.dupsi p.1 p.2)]
    _ < eps := by linarith

/-- The incoming scalar derivative is jointly continuous off-axis.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, lines 709–737. -/
theorem cylinder_duphi_continuous :
    ContinuousOn (fun p => S.duphi p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  exact (h.cylinder_dupsi_continuous.sub
    ((h.regularCenter.continuous_nu.mono hs).mul (h.regularCenter.continuous_phi.mono hs))).div
    (h.regularCenter.continuous_r.mono hs)
    (fun p hp => (h.r_pos (hs hp) hp.2.1).ne')

end AcExtensionPrinciple.StandingFull

end
