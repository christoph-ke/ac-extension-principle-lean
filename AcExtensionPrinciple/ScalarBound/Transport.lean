module

public import AcExtensionPrinciple.ScalarBound.Initial
public import AcExtensionPrinciple.GeometricBounds.TerminalBlueshift
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Incoming scalar representation and continuity

Paper commit `e1a0fd5`, `equations.tex`
lines 395–426, `eq:scalar-bound-linear-transport`. The solution
class already supplies joint continuity of φ; the ψ derivative acquires
joint continuity from its incoming integral equation and the initial datum.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Integrating a continuous rectangle integrand to a variable upper endpoint
preserves joint continuity. Paper `e1a0fd5`, lines 420–426. -/
theorem continuousOn_rectangle_primitive {g : ℝ → ℝ → ℝ} {l U a b : ℝ}
    (hlU : l ≤ U) (hab : a ≤ b)
    (hg : ContinuousOn (fun p => g p.1 p.2) (Icc l U ×ˢ Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in l..p.1, g s p.2)
      (Icc l U ×ˢ Icc a b) := by
  let cu (s : ℝ) := max l (min U s)
  let cv (s : ℝ) := max a (min b s)
  have hcu : Continuous cu := continuous_const.max (continuous_const.min continuous_id)
  have hcv : Continuous cv := continuous_const.max (continuous_const.min continuous_id)
  have hcu_mem (s : ℝ) : cu s ∈ Icc l U :=
    ⟨le_max_left _ _, max_le hlU (min_le_left _ _)⟩
  have hcv_mem (s : ℝ) : cv s ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => g (cu p.2) (cv p.1.2)) :=
    hg.comp_continuous ((hcu.comp continuous_snd).prodMk
      (hcv.comp (continuous_snd.comp continuous_fst)))
      (fun p => ⟨hcu_mem p.2, hcv_mem p.1.2⟩)
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (f := fun (p : ℝ × ℝ) s => g (cu s) (cv p.2))
    (a₀ := l) hc (s := fun p : ℝ × ℝ => p.1) continuous_fst
  apply hi.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hp.1.1] at hs
  have hsu : cu s = s := by
    dsimp [cu]
    rw [min_eq_right (hs.2.trans hp.1.2), max_eq_right hs.1]
  have hsv : cv p.2 = p.2 := by
    dsimp [cv]
    rw [min_eq_right hp.2.2, max_eq_right hp.2.1]
  simp only [hsu, hsv]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The radius coefficient is λγϰ. Paper `e1a0fd5`, `eq:radius`,
`eq:scalar-bound-linear-transport`, lines 420–424. -/
theorem radiusCoeff_eq_lam_gamma (u v : ℝ) :
    S.radiusCoeff u v = S.lam u v * S.gamma u v * S.varkappa u v := by
  unfold SSFields.radiusCoeff SSFields.gamma gammaOf SSFields.varkappa varkappaOf
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The incoming integral equation gives the integrating-factor formula,
including the terminal ray. Paper `e1a0fd5`, lines 420–426. -/
theorem normalized_datum_representation {u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    S.dvpsi u v / S.lam u v =
      (S.dvpsi ui v + ∫ s in ui..u,
        S.lam s v * S.gamma s v * S.varkappa s v * S.phi s v) / S.lam u v := by
  have hi := (h.regularCenter.localBV.dvpsi_in v ui u hp.1
    (inSeg_subset_offAxis le_rfl hp.2.1 huv hp.2.2.2)).2
  have he : S.dvpsi u v = S.dvpsi ui v +
      ∫ s in ui..u, S.lam s v * S.gamma s v * S.varkappa s v * S.phi s v := by
    simp_rw [h.radiusCoeff_eq_lam_gamma] at hi
    linarith
  rw [he]

/-- φ is jointly continuous off the axis under the full working class.
Paper `e1a0fd5`, lines 395–412. This records the already assumed regularity;
the paper's energy proof can strengthen a future weaker class. -/
theorem scalar_continuous_offAxis :
    ContinuousOn (fun p => S.phi p.1 p.2) (offAxis (pastTriangle ui)) :=
  h.regularCenter.continuous_phi.mono (fun _ hp => hp.1)

/-- Proper rectangles used in the running-maximum proof are off the axis.
Paper `e1a0fd5`, lines 395 and 435–439. -/
theorem scalar_rectangle_subset {U a b : ℝ} (hUa : U < a) (hb : b ≤ 0) :
    Icc ui U ×ˢ Icc a b ⊆ offAxis (pastTriangle ui) := by
  intro p hp
  have huv : p.1 < p.2 := hp.1.2.trans_lt (hUa.trans_le hp.2.1)
  exact ⟨⟨hp.1.1, huv.trans_le (hp.2.2.trans hb), huv.le, hp.2.2.trans hb⟩,
    ne_of_lt huv⟩

/-- The normalized ψ derivative is jointly continuous on every proper
rectangle, through its integrating-factor representation.
Paper `e1a0fd5`, lines 420–426, `eq:scalar-bound-linear-transport`. -/
theorem normalized_datum_continuous_rectangle {U a b : ℝ}
    (hU : ui ≤ U) (hUa : U < a) (hab : a ≤ b) (hb : b ≤ 0) :
    ContinuousOn (fun p => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := by
  let K := Icc ui U ×ˢ Icc a b
  have hK : K ⊆ pastTriangle ui := fun p hp => (h.scalar_rectangle_subset hUa hb hp).1
  have hKo : K ⊆ {p ∈ pastTriangle ui | p.1 < p.2} := by
    intro p hp
    exact ⟨hK hp, hp.1.2.trans_lt (hUa.trans_le hp.2.1)⟩
  have hl := h.regularCenter.continuous_lam.mono hK
  have hf := h.regularCenter.continuous_phi.mono hK
  have hG : ContinuousOn (fun p => S.radiusCoeff p.1 p.2 * S.phi p.1 p.2) K := by
    have hg := (hl.mul (h.continuous_blueshift.mono hKo).neg).mul hf
    apply hg.congr
    intro p hp
    dsimp only [Pi.mul_apply, Pi.neg_apply]
    rw [h.radiusCoeff_eq_lam_gamma]
    ring
  have hI := continuousOn_rectangle_primitive
    (g := fun u v => S.radiusCoeff u v * S.phi u v) hU hab hG
  have hd : ContinuousOn (fun p : ℝ × ℝ => S.dvpsi ui p.2) K := by
    have hc : ContinuousOn (S.dvpsi ui) (Icc ui 0) := by
      simpa only [uIcc_of_le h.initial_negative.le] using h.initial_ac_data.continuousOn
    exact hc.comp continuous_snd.continuousOn
      (fun p hp => ⟨hU.trans (hUa.le.trans hp.2.1), hp.2.2.trans hb⟩)
  have hquot := (hd.add hI).div hl (fun p hp => ne_of_gt (h.lam_pos (hK hp)))
  apply hquot.congr
  intro p hp
  have he := (h.regularCenter.localBV.dvpsi_in p.2 ui p.1 hp.1.1
    (inSeg_subset_offAxis le_rfl (hK hp).2.1
      (hp.1.2.trans_lt (hUa.trans_le hp.2.1)) (hp.2.2.trans hb))).2
  dsimp only [Pi.div_apply, Pi.add_apply] at he ⊢
  congr 1
  linarith

/-- Joint continuity of θ on the compact rectangles used for the bootstrap.
Paper `e1a0fd5`, lines 426 and 514–515. -/
theorem theta_continuous_rectangle {U a b : ℝ}
    (hU : ui ≤ U) (hUa : U < a) (hab : a ≤ b) (hb : b ≤ 0) :
    ContinuousOn (fun p => S.theta p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hK : Icc ui U ×ˢ Icc a b ⊆ pastTriangle ui :=
    fun p hp => (h.scalar_rectangle_subset hUa hb hp).1
  have hl := h.regularCenter.continuous_lam.mono hK
  have hc := ((h.normalized_datum_continuous_rectangle hU hUa hab hb).mul hl).sub
    (hl.mul (h.regularCenter.continuous_phi.mono hK))
  apply hc.congr
  intro p hp
  dsimp [SSFields.theta]
  rw [div_mul_cancel₀ _ (ne_of_gt (h.lam_pos (hK hp)))]

end StandingFull

end AcExtensionPrinciple

end
