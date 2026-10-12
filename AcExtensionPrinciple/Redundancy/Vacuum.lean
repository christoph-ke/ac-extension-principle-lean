module

public import AcExtensionPrinciple.Redundancy.ExpansionAC

/-!
# Optional vacuum checks for expansion regularity
Paper commit `e1a0fd5`, `equations.tex` lines 66–84, 122–124 and 220–275,
`eq:radius`, `eq:regular-axis`. Zero mass and the fixed initial radius gauge
force both expansions to be constant. These conditional checks exclude vacuum
gauge counterexamples and are independent of `mainTheorem`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The mixed radius coefficient vanishes in the zero-mass subclass. The extra premise is
the vacuum restriction used for this counterexample check, not a new source hypothesis.
Paper `e1a0fd5`, `eq:radius`, lines 70–73. -/
theorem Q1StandingCore.radiusCoeff_eq_zero_of_zero_mass {ui : ℝ} {S : SSFields}
    (_h : Q1StandingCore ui S) (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.radiusCoeff p.1 p.2 = 0 := by
  simp [SSFields.radiusCoeff, SSFields.mu, massRatio, hm p hp]

/-- Incoming transport and the fixed initial gauge force off-axis λ = 1 in vacuum.
The zero-mass premise restricts this counterexample check to vacuum.
Paper `e1a0fd5`, `eq:radius`, lines 122–124 and 222. -/
theorem Q1StandingCore.lam_eq_one_offAxis_of_zero_mass {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (hpa : p.1 < p.2) :
    S.lam p.1 p.2 = 1 := by
  have hs := inSeg_subset_offAxis (ui := ui) le_rfl hp.2.1 hpa hp.2.2.2
  have he := (h.regularCenter.localBV.lam_in p.2 ui p.1 hp.1 hs).2
  have hz : (∫ s in ui..p.1, S.radiusCoeff s p.2) = 0 := by
    calc
      _ = ∫ _s in ui..p.1, (0 : ℝ) := intervalIntegral.integral_congr (fun s hs' => by
        rw [uIcc_of_le hp.1] at hs'
        exact h.radiusCoeff_eq_zero_of_zero_mass hm
          (hs (show (s, p.2) ∈ inSeg p.2 ui p.1 from ⟨hs', by simp⟩)).1)
      _ = 0 := by simp
  have hg := (h.initial_gauge p.2 ⟨hp.1.trans hp.2.2.1, hp.2.2.2⟩).2
  dsimp only at he
  rw [hz, hg] at he
  linarith

/-- Outgoing continuity also fixes the stored λ axis value in vacuum. The AC premise is one
of the retained fields in both deletion classes; the extra mass premise is vacuum.
Paper `e1a0fd5`, `eq:regular-axis`, lines 122–124 and 220–275. -/
theorem Q1StandingCore.lam_eq_one_of_zero_mass {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0)
    (hac : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
      AbsolutelyContinuousOnInterval (S.lam u) a b)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.lam p.1 p.2 = 1 := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl (show (0 : ℝ) ≤ 0 from le_rfl)
  have hc : ContinuousOn (S.lam p.1) (Icc p.1 0) := by
    simpa only [uIcc_of_le hp.2.1.le] using (hac p.1 p.1 0 hp.2.1.le hs).continuousOn
  have hb := interval_bounds_of_open hp.2.1 hc (L := 1) (U := 1) (fun v hv => by
    have he := h.lam_eq_one_offAxis_of_zero_mass hm
      (p := (p.1, v)) ⟨hp.1, hp.2.1, hv.1.le, hv.2.le⟩ hv.1
    exact ⟨he.ge, he.le⟩)
  exact le_antisymm (hb p.2 hp.2.2).2 (hb p.2 hp.2.2).1

/-- Vacuum has global λ continuity even after deleting that field. This rules out a vacuum
counterexample to deletion of this continuity field. The general λ continuity
result is proved in `Redundancy/LambdaContinuity.lean`.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 122–124 and 220–275. -/
theorem continuous_lam_of_rest_of_zero_mass {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S)
    (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0) :
    ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui) := by
  apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 : ℝ))
    (pastTriangle ui)).congr
  intro p hp
  exact h.toQ1StandingCore.lam_eq_one_of_zero_mass hm h.ac_lam_out hp

/-- Vacuum outgoing transport and the axis relation force ν = −1. ν continuity is retained
when its incoming AC field is deleted; the zero-mass premise is only the vacuum restriction.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 122–124 and 220–275. -/
theorem nu_eq_neg_one_of_rest_of_zero_mass {ui : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S)
    (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.nu p.1 p.2 = -1 := by
  have hl : ∀ q ∈ pastTriangle ui, S.lam q.1 q.2 = 1 := fun q hq =>
    h.toQ1StandingCore.lam_eq_one_of_zero_mass hm h.ac_lam_out hq
  have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
  have hnaxis : S.nu p.1 p.1 = -1 := by
    rw [h.regularCenter.axis_expansions p.1 ha, hl _ (axis_subset_pastTriangle ui ha)]
  rcases hp.2.2.1.eq_or_lt with he | he
  · change p.1 = p.2 at he
    simpa only [← he] using hnaxis
  have hconst {x y : ℝ} (hx : p.1 < x) (hxy : x ≤ y) (hy : y ≤ 0) :
      S.nu p.1 y = S.nu p.1 x := by
    have hs := outSeg_subset_offAxis hp.1 hp.2.1 hx hy
    have hi := (h.regularCenter.localBV.nu_out p.1 x y hxy hs).2
    have hz : (∫ s in x..y, S.radiusCoeff p.1 s) = 0 := by
      calc
        _ = ∫ _s in x..y, (0 : ℝ) := intervalIntegral.integral_congr (fun s hs' => by
          rw [uIcc_of_le hxy] at hs'
          exact h.toQ1StandingCore.radiusCoeff_eq_zero_of_zero_mass hm
            (hs (show (p.1, s) ∈ outSeg p.1 x y from ⟨by simp, hs'⟩)).1)
        _ = 0 := by simp
    rw [hz] at hi
    linarith
  have hc : ContinuousOn (S.nu p.1) (Icc p.1 0) :=
    h.continuous_nu.comp (f := fun v : ℝ => (p.1, v))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hp.1, hp.2.1, hv⟩)
  have hb := interval_bounds_of_open hp.2.1 hc
    (L := S.nu p.1 p.2) (U := S.nu p.1 p.2) (fun v hv => by
      have heq : S.nu p.1 v = S.nu p.1 p.2 := by
        rcases le_total v p.2 with hvp | hpv
        · exact (hconst hv.1 hvp hp.2.2.2).symm
        · exact hconst he hpv hv.2.le
      exact ⟨heq.ge, heq.le⟩)
  linarith [(hb p.1 ⟨le_rfl, hp.2.1.le⟩).1, (hb p.1 ⟨le_rfl, hp.2.1.le⟩).2]

/-- Vacuum satisfies incoming ν AC after deleting that field. A full-rest counterexample to
the general deletion must therefore have nonzero mass somewhere.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 122–124 and 220–275. -/
theorem ac_nu_in_of_rest_of_zero_mass {ui : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S)
    (hm : ∀ p ∈ pastTriangle ui, S.m p.1 p.2 = 0) :
    ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui →
      AbsolutelyContinuousOnInterval (fun u => S.nu u v) a b := by
  intro v a b hab hs
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-1 : ℝ)) a b :=
    (LipschitzWith.const (-1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply hc.congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact (nu_eq_neg_one_of_rest_of_zero_mass h hm
    (hs (show (u, v) ∈ inSeg v a b from ⟨hu, by simp⟩))).symm

end AcExtensionPrinciple

end
