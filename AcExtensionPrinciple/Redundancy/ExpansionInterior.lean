module

public import AcExtensionPrinciple.Redundancy.MassContinuity

/-!
# Optional off-axis expansion-continuity results
Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275, `eq:radius`.
The λ result gives joint continuity on proper off-axis rectangles without its own
joint continuity field. The ν result also takes incoming continuity as a premise.
These optional results are independent of `mainTheorem`; axis continuity is outside
these rectangle statements. Global λ continuity is proved in `Redundancy/LambdaContinuity.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The mixed radius integrand is nonpositive off-axis, from the core signs. Paper `e1a0fd5`,
`eq:radius`, lines 66–84 and 222. -/
theorem Q1StandingCore.radiusCoeff_nonpos {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui)
    (hpa : p.1 < p.2) : S.radiusCoeff p.1 p.2 ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (h.mu_bounds hp).1 (h.lam_pos hp).le) (h.nu_neg hp).le)
    (mul_nonneg (sub_nonneg.mpr (h.mu_bounds hp).2.le) (h.r_pos hp hpa).le)

/-- Incoming expansion transport is antitone in its characteristic variable. Paper `e1a0fd5`,
`eq:radius`, lines 66–84 and 222. -/
theorem Q1StandingCore.lam_in_antitone {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) {v a b : ℝ}
    (hs : inSeg v a b ⊆ offAxis (pastTriangle ui)) :
    AntitoneOn (fun u => S.lam u v) (Icc a b) := by
  intro x hx y hy hxy
  have hsub : inSeg v x y ⊆ offAxis (pastTriangle ui) := by
    intro p hp
    exact hs ⟨⟨hx.1.trans hp.1.1, hp.1.2.trans hy.2⟩, hp.2⟩
  have hi := h.regularCenter.localBV.lam_in v x y hxy hsub
  have hn : (∫ s in x..y, S.radiusCoeff s v) ≤ 0 := by
    have hz : (∫ s in x..y, (0 : ℝ)) = 0 := by simp
    rw [← hz]
    apply intervalIntegral.integral_mono_on hxy hi.1 intervalIntegrable_const
    intro s hs'
    have hp := hsub (show (s, v) ∈ inSeg v x y from ⟨hs', by simp⟩)
    exact h.radiusCoeff_nonpos hp.1 (lt_of_le_of_ne hp.1.2.2.1 hp.2)
  linarith [hi.2]

/-- Outgoing expansion transport is antitone in its characteristic variable. Paper `e1a0fd5`,
`eq:radius`, lines 66–84 and 222. -/
theorem Q1StandingCore.nu_out_antitone {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) {u a b : ℝ}
    (hs : outSeg u a b ⊆ offAxis (pastTriangle ui)) :
    AntitoneOn (S.nu u) (Icc a b) := by
  intro x hx y hy hxy
  have hsub : outSeg u x y ⊆ offAxis (pastTriangle ui) := by
    intro p hp
    exact hs ⟨hp.1, ⟨hx.1.trans hp.2.1, hp.2.2.trans hy.2⟩⟩
  have hi := h.regularCenter.localBV.nu_out u x y hxy hsub
  have hn : (∫ s in x..y, S.radiusCoeff u s) ≤ 0 := by
    have hz : (∫ s in x..y, (0 : ℝ)) = 0 := by simp
    rw [← hz]
    apply intervalIntegral.integral_mono_on hxy hi.1 intervalIntegrable_const
    intro s hs'
    have hp := hsub (show (u, s) ∈ outSeg u x y from ⟨by simp, hs'⟩)
    exact h.radiusCoeff_nonpos hp.1 (lt_of_le_of_ne hp.1.2.2.1 hp.2)
  linarith [hi.2]

/-- Deleting λ continuity still leaves joint continuity on every proper rectangle, by incoming
primitives, outgoing AC, and incoming antitonicity. Paper `e1a0fd5`, `eq:radius`, lines
220–275. This optional result concerns off-axis rectangles; global λ continuity
is proved by `continuous_lam_of_rest` in `Redundancy/LambdaContinuity.lean`. -/
theorem continuous_lam_rectangle_of_rest {ui U a b : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) (hui : ui ≤ U) (hab : a ≤ b)
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  apply q1_rectangle_continuous_of_antitone hui hab
  · intro v hv
    have hs : inSeg v ui U ⊆ offAxis (pastTriangle ui) :=
      inSeg_subset_offAxis le_rfl hU (hUa.trans_le hv.1) (hv.2.trans hb)
    have hc := intervalPrimitive_ac hui (fun x hx =>
      h.regularCenter.localBV.lam_in v ui x hx.1
        (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
    simpa only [uIcc_of_le hui] using hc.continuousOn
  · intro u hu
    have hc := h.ac_lam_out u a b hab
      (outSeg_subset_triangle hu.1 (hu.2.trans_lt hU) (hu.2.trans hUa.le) hb)
    simpa only [uIcc_of_le hab] using hc.continuousOn
  · intro v hv
    exact h.toQ1StandingCore.lam_in_antitone
      (inSeg_subset_offAxis le_rfl hU (hUa.trans_le hv.1) (hv.2.trans hb))

/-- Deleting ν continuity still leaves joint continuity on every proper rectangle, by outgoing
primitives, incoming continuity of ν (explicit premise `hin`; formerly supplied by the dropped
incoming-AC field), and outgoing antitonicity. Paper `e1a0fd5`, `eq:radius`, lines 220–275.
This optional result concerns off-axis rectangles and is independent of `mainTheorem`. -/
theorem continuous_nu_rectangle_of_rest {ui U a b : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S)
    (hin : ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui →
      ContinuousOn (fun u => S.nu u v) (Icc a b))
    (hui : ui ≤ U) (hab : a ≤ b)
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => S.nu p.2 p.1)
      (Icc a b ×ˢ Icc ui U) := by
    apply q1_rectangle_continuous_of_antitone (f := fun v u => S.nu u v) hab hui
    · intro u hu
      have hs := outSeg_subset_offAxis hu.1 (hu.2.trans_lt hU)
        (hu.2.trans_lt hUa) hb
      have hc := intervalPrimitive_ac hab (fun x hx =>
        h.regularCenter.localBV.nu_out u a x hx.1
          (fun p hp => hs ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hx.2⟩⟩))
      simpa only [uIcc_of_le hab] using hc.continuousOn
    · intro v hv
      exact hin v ui U hui
        (inSeg_subset_triangle le_rfl hU (hUa.le.trans hv.1) (hv.2.trans hb))
    · intro u hu
      exact h.toQ1StandingCore.nu_out_antitone
        (outSeg_subset_offAxis hu.1 (hu.2.trans_lt hU) (hu.2.trans_lt hUa) hb)
  exact hc.comp (continuous_snd.prodMk continuous_fst).continuousOn
    (fun p hp => ⟨hp.2, hp.1⟩)

end AcExtensionPrinciple

end
