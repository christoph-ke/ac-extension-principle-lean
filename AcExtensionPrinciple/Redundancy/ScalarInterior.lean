module

public import AcExtensionPrinciple.Redundancy.MassContinuity

/-!
# Scalar continuity off-axis from characteristic primitives and BV bounds

Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275.
Incoming transport bounds the outgoing derivative on one side of a rectangle;
uniform outgoing variation bounds it throughout the rectangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- One uniformly Lipschitz characteristic family and continuity on the other
family give joint rectangle continuity. Premises are discharged below by ψ
primitives and uniform derivative BV bounds. Paper `e1a0fd5`, lines 66–84 and 222. -/
theorem q1_joint_continuous_of_uniform_outgoing {f : ℝ → ℝ → ℝ} {a b c d B : ℝ}
    (hB : 0 ≤ B)
    (hu : ∀ v ∈ Icc c d, ContinuousOn (fun u => f u v) (Icc a b))
    (hv : ∀ u ∈ Icc a b, ∀ x ∈ Icc c d, ∀ y ∈ Icc c d,
      dist (f u x) (f u y) ≤ B * dist x y) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc c d) := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.mp
    (hu p.2 hp.2 p.1 hp.1) (ε / 2) (by positivity)
  refine ⟨min δ (ε / (2 * (B + 1))), lt_min hδ (by positivity), ?_⟩
  intro q hq hqd
  have hqu : dist q.1 p.1 < δ := by
    exact (show dist q.1 p.1 ≤ dist q p from by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt (hqd.trans_le (min_le_left _ _))
  have hqv : dist q.2 p.2 < ε / (2 * (B + 1)) := by
    exact (show dist q.2 p.2 ≤ dist q p from by
      rw [Prod.dist_eq]; exact le_max_right _ _).trans_lt (hqd.trans_le (min_le_right _ _))
  have hsmall : B * dist q.2 p.2 < ε / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp hqv
    nlinarith [dist_nonneg (x := q.2) (y := p.2)]
  calc
    dist (f q.1 q.2) (f p.1 p.2) ≤
        dist (f q.1 q.2) (f q.1 p.2) + dist (f q.1 p.2) (f p.1 p.2) := dist_triangle _ _ _
    _ ≤ B * dist q.2 p.2 + dist (f q.1 p.2) (f p.1 p.2) := by
      exact add_le_add (hv q.1 hq.1 q.2 hq.2 p.2 hp.2) le_rfl
    _ < ε := by linarith [hδf hq.1 hqu]

/-- The outgoing ψ derivative is uniformly bounded on every proper rectangle.
The side value is continuous by incoming transport, and outgoing variation bounds
all other values. Paper `e1a0fd5`, lines 66–84 and 222, Luk–Oh Definition 2.1(6). -/
theorem q1_dvpsi_bound_rectangle {ui U a b : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hui : ui ≤ U) (hab : a ≤ b)
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Icc ui U ×ˢ Icc a b, ‖S.dvpsi p.1 p.2‖ ≤ B := by
  have hs : inSeg a ui U ⊆ offAxis (pastTriangle ui) :=
    inSeg_subset_offAxis le_rfl hU hUa (hab.trans hb)
  have hac := intervalPrimitive_ac hui (fun x hx =>
    h.regularCenter.localBV.dvpsi_in a ui x hx.1
      (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
  have hc : ContinuousOn (fun u => S.dvpsi u a) (Icc ui U) := by
    simpa only [uIcc_of_le hui] using hac.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hrect : Icc ui U ×ˢ Icc a b ⊆ pastTriangle ui := fun p hp =>
    ⟨hp.1.1, hp.1.2.trans_lt hU, hp.1.2.trans (hUa.le.trans hp.2.1), hp.2.2.trans hb⟩
  obtain ⟨C, hC, _⟩ := h.regularCenter.localBV.psi_variation (Icc ui U ×ˢ Icc a b)
    (isCompact_Icc.prod isCompact_Icc) hrect
  refine ⟨|M| + |C|, by positivity, ?_⟩
  intro p hp
  have hvar := hC p.1 a b hab (fun q hq => by
    have he : q.1 = p.1 := hq.1
    exact ⟨by simpa only [he] using hp.1, hq.2⟩)
  have hd : dist (S.dvpsi p.1 p.2) (S.dvpsi p.1 a) ≤ |C| := by
    apply (ENNReal.ofReal_le_ofReal_iff (abs_nonneg C)).mp
    rw [← edist_dist]
    exact (eVariationOn.edist_le (S.dvpsi p.1) hp.2 ⟨le_rfl, hab⟩).trans
      (hvar.trans (ENNReal.ofReal_le_ofReal (le_abs_self C)))
  calc
    ‖S.dvpsi p.1 p.2‖ ≤ dist (S.dvpsi p.1 p.2) (S.dvpsi p.1 a) + ‖S.dvpsi p.1 a‖ :=
      by simpa only [dist_eq_norm, add_comm] using
        norm_le_insert' (S.dvpsi p.1 p.2) (S.dvpsi p.1 a)
    _ ≤ |C| + |M| := add_le_add hd ((hM p.1 hp.1).trans (le_abs_self M))
    _ = |M| + |C| := add_comm _ _

/-- ψ is jointly continuous on every proper rectangle, using only the core.
Paper `e1a0fd5`, lines 66–84 and 220–275, `eq:wave-psi`. -/
theorem q1_psi_continuous_rectangle {ui U a b : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hui : ui ≤ U) (hab : a ≤ b)
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2 * S.phi p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := by
  obtain ⟨B, hB, hbound⟩ := q1_dvpsi_bound_rectangle h hui hab hU hUa hb
  apply q1_joint_continuous_of_uniform_outgoing
    (f := fun u v => S.r u v * S.phi u v) hB
  · intro v hv
    have hs : inSeg v ui U ⊆ pastTriangle ui :=
      inSeg_subset_triangle le_rfl hU (hUa.le.trans hv.1) (hv.2.trans hb)
    have hc := intervalPrimitive_ac hui (fun x hx =>
      h.regularCenter.localBV.psi_in v ui x hx.1
        (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
    simpa only [uIcc_of_le hui] using hc.continuousOn
  · intro u hu x hx y hy
    have hordered (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
        dist (S.r u y * S.phi u y) (S.r u x * S.phi u x) ≤ B * dist y x := by
      have hi := (h.regularCenter.localBV.psi_out u x y hxy
        (outSeg_subset_triangle hu.1 (hu.2.trans_lt hU)
          (hu.2.trans (hUa.le.trans hx.1)) (hy.2.trans hb))).2
      rw [Real.dist_eq, hi]
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := S.dvpsi u) (a := x) (b := y) (C := B) (fun t ht => by
          rw [uIoc_of_le hxy] at ht
          exact hbound (u, t) ⟨hu, ⟨hx.1.trans ht.1.le, ht.2.trans hy.2⟩⟩)
      simpa only [Real.norm_eq_abs, Real.dist_eq] using hn
    rcases le_total x y with hxy | hyx
    · simpa only [dist_comm] using hordered x y hx hy hxy
    · exact hordered y x hy hx hyx

/-- Deleting φ continuity leaves joint continuity off-axis. The retained radius
continuity and positivity permit division of the continuous ψ field.
Paper `e1a0fd5`, lines 220–275, `eq:scalar-and-mass-ratio`, `eq:wave-psi`. -/
theorem continuous_phi_offAxis_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_phi ui S) :
    ContinuousOn (fun p => S.phi p.1 p.2) (cylinderScalarRegion ui) := by
  intro p hp
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have hpU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hap : a < p.2 := by dsimp [a, U]; linarith [hp.2.1]
  have hU : U < 0 := by dsimp [U]; linarith [hp.2.1, hp.2.2]
  have hrect : Icc ui U ×ˢ Icc a 0 ⊆ cylinderScalarRegion ui :=
    cylinder_rectangle_subset_region hUa le_rfl
  have hc := (q1_psi_continuous_rectangle h.toQ1StandingCore (hp.1.trans hpU.le)
    (hap.le.trans hp.2.2) hU hUa le_rfl).div
      (h.continuous_r.mono (hrect.trans (cylinderScalarRegion_subset ui)))
      (fun q hq => (h.toQ1StandingCore.r_pos
        (cylinderScalarRegion_subset ui (hrect hq)) (hrect hq).2.1).ne')
  have hφ : ContinuousOn (fun q : ℝ × ℝ => S.phi q.1 q.2) (Icc ui U ×ˢ Icc a 0) := by
    apply hc.congr
    intro q hq
    exact (mul_div_cancel_left₀ _ (h.toQ1StandingCore.r_pos
      (cylinderScalarRegion_subset ui (hrect hq)) (hrect hq).2.1).ne').symm
  apply (hφ p ⟨⟨hp.1, hpU.le⟩, ⟨hap.le, hp.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hap)).filter_mono nhdsWithin_le_nhds]
    with q hq hqU hqa
  exact ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2⟩⟩

end AcExtensionPrinciple

end
