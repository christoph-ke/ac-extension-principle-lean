module

public import AcExtensionPrinciple.Minimal.RadiusContinuity
public import AcExtensionPrinciple.Redundancy.MonotoneContinuity

/-!
# Mass continuity follows from the remaining standing class
Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275,
`eq:mass`, `eq:regular-axis`. Characteristic primitives give separate
continuity; the mass signs give joint off-axis continuity. The retained radius
continuity and 0 ≤ 2m/r < 1 give continuity at the axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The untrapped mass-ratio bounds include the axis by zero division. Paper `e1a0fd5`, lines 120
and 275, `eq:regular-axis`. -/
theorem StandingAssumptions.mu_bounds {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1 := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · have hr := (h.regularCenter.localBV.axis_values p.1
      ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1
    simp [← he, SSFields.mu, massRatio, hr]
  · exact (h.signs p hp he).2.2

/-- The outgoing mass integrand is nonnegative everywhere, including the axis. Paper `e1a0fd5`,
`eq:mass`, lines 66–84 and 222. -/
theorem StandingAssumptions.massV_nonneg {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 ≤ S.massV p.1 p.2 := by
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (h.mu_bounds hp).2.le) (sq_nonneg _))
    (mul_nonneg (by norm_num) (h.lam_pos hp).le)

/-- The incoming mass integrand is nonpositive everywhere, including the axis. Paper `e1a0fd5`,
`eq:mass`, lines 66–84 and 222. -/
theorem StandingAssumptions.massU_nonpos {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.massU p.1 p.2 ≤ 0 := by
  exact div_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (sub_nonneg.mpr (h.mu_bounds hp).2.le) (sq_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (h.nu_neg hp).le)

/-- Incoming characteristic mass restrictions are antitone. Paper `e1a0fd5`, `eq:mass`,
lines 66–84
and 222. -/
theorem StandingAssumptions.mass_in_antitone {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {v a b : ℝ} (hs : inSeg v a b ⊆ pastTriangle ui) :
    AntitoneOn (fun u => S.m u v) (Icc a b) := by
  intro x hx y hy hxy
  have hsub : inSeg v x y ⊆ pastTriangle ui := by
    intro p hp
    exact hs ⟨⟨hx.1.trans hp.1.1, hp.1.2.trans hy.2⟩, hp.2⟩
  have hi := h.regularCenter.localBV.mass_in v x y hxy hsub
  have hn : (∫ s in x..y, S.massU s v) ≤ 0 := by
    have hz : (∫ s in x..y, (0 : ℝ)) = 0 := by simp
    rw [← hz]
    exact intervalIntegral.integral_mono_on hxy hi.1 intervalIntegrable_const
      (fun s hs' => h.massU_nonpos (p := (s, v)) (hsub ⟨hs', by simp⟩))
  linarith [hi.2]

/-- Every proper off-axis rectangle has a jointly continuous mass field, without the additional
mass continuity hypothesis. Paper `e1a0fd5`, `eq:mass`, lines 66–84 and 220–275. -/
theorem minimal_mass_continuous_rectangle {ui U a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hui : ui ≤ U) (hab : a ≤ b)
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.m p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  apply q1_rectangle_continuous_of_antitone hui hab
  · intro v hv
    have hs : inSeg v ui U ⊆ pastTriangle ui :=
      inSeg_subset_triangle le_rfl hU (hUa.le.trans hv.1) (hv.2.trans hb)
    have hc := intervalPrimitive_ac hui (fun x hx =>
      h.regularCenter.localBV.mass_in v ui x hx.1
        (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
    simpa only [uIcc_of_le hui] using hc.continuousOn
  · intro u hu
    have hs := outSeg_subset_triangle hu.1 (hu.2.trans_lt hU)
      (hu.2.trans hUa.le) hb
    have hc := intervalPrimitive_ac hab (fun x hx =>
      h.regularCenter.localBV.mass_out u a x hx.1
        (fun p hp => hs ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hx.2⟩⟩))
    simpa only [uIcc_of_le hab] using hc.continuousOn
  · intro v hv
    exact h.mass_in_antitone
      (inSeg_subset_triangle le_rfl hU (hUa.le.trans hv.1) (hv.2.trans hb))

/-- The untrapped signs bound the mass by half the radius, also at the axis. Paper `e1a0fd5`, line
120, `eq:regular-axis`, `eq:scalar-and-mass-ratio`. -/
theorem StandingAssumptions.mass_radius_bounds {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    0 ≤ S.m p.1 p.2 ∧ S.m p.1 p.2 ≤ S.r p.1 p.2 / 2 := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · have hv := h.regularCenter.localBV.axis_values p.1
      ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩
    simp [← he, hv.1, hv.2]
  · have hr := h.r_pos (u := p.1) (v := p.2) hp he
    have hmu := h.mu_bounds hp
    change 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1 at hmu
    have h₀ := (le_div_iff₀ hr).mp hmu.1
    have h₁ := (div_lt_iff₀ hr).mp hmu.2
    constructor <;> linarith

/-- The mass continuity field of the full working class is redundant. Off-axis continuity uses
incoming antitonicity and the two primitives; the axis uses radius continuity and the mass-ratio
signs. Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:mass`, `eq:regular-axis`. -/
theorem StandingAssumptions.continuous_m {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) :
    ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have hv := h.regularCenter.localBV.axis_values p.1
      ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩
    have hr := (h.continuous_r p hp).tendsto.div_const 2
    have hmp : S.m p.1 p.2 = 0 := by simpa only [← he] using hv.2
    have hrp : S.r p.1 p.2 = 0 := by simpa only [← he] using hv.1
    rw [hrp, zero_div] at hr
    rw [ContinuousWithinAt, hmp]
    apply squeeze_zero' ?_ ?_ hr
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (h.mass_radius_bounds hq).1
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (h.mass_radius_bounds hq).2
  · let U := (p.1 + p.2) / 2
    let a := (U + p.2) / 2
    have hpU : p.1 < U := by dsimp [U]; linarith
    have hUa : U < a := by dsimp [a, U]; linarith
    have hap : a < p.2 := by dsimp [a, U]; linarith
    have hU : U < 0 := by dsimp [U]; linarith [hp.2.1, hp.2.2.2]
    have hc := minimal_mass_continuous_rectangle h (hp.1.trans hpU.le)
      (hap.le.trans hp.2.2.2) hU hUa le_rfl
    apply (hc p ⟨⟨hp.1, hpU.le⟩, ⟨hap.le, hp.2.2.2⟩⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono nhdsWithin_le_nhds,
      ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hap)).filter_mono nhdsWithin_le_nhds]
      with q hq hqU hqa
    exact ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2.2⟩⟩

end AcExtensionPrinciple

end
