module

public import AcExtensionPrinciple.GeometricBounds.Blueshift

/-!
# Initial scalar average and bounds

Paper commit `e1a0fd5`, `equations.tex`
lines 387–393, `eq:scalar-bound-initial-average`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The initial scalar is the average of the initial ψ derivative.
Paper `e1a0fd5`, `eq:scalar-bound-initial-average`, lines 387–392. -/
theorem scalar_initial_average {v : ℝ} (hv : v ∈ Ioc ui 0) :
    S.phi ui v = (∫ s in ui..v, S.dvpsi ui s) / (v - ui) := by
  have hp : (ui, ui) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
  have hi := (h.regularCenter.localBV.psi_out ui ui v hv.1.le
    (outSeg_subset_triangle le_rfl h.initial_negative le_rfl hv.2)).2
  dsimp only at hi
  rw [(h.regularCenter.localBV.axis_values ui hp).1, zero_mul, sub_zero,
    (h.initial_gauge v ⟨hv.1.le, hv.2⟩).1] at hi
  exact (eq_div_iff (sub_pos.mpr hv.1).ne').mpr (by simpa [mul_comm] using hi)

/-- Bounded initial differences suffice: the scalar average is bounded by A.
Paper `e1a0fd5`, `eq:scalar-bound-initial-average`, lines 387–393. -/
theorem scalar_initial_le {A v : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A) (hv : v ∈ Icc ui 0) :
    |S.phi ui v| ≤ A := by
  have hb : ∀ v ∈ Ioo ui 0, -A ≤ S.phi ui v ∧ S.phi ui v ≤ A := by
    intro v hv
    have havg := h.scalar_initial_average ⟨hv.1, hv.2.le⟩
    have hi : |∫ s in ui..v, S.dvpsi ui s| ≤ A * (v - ui) := by
      have ht := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := ui) (b := v) (f := S.dvpsi ui) (C := A) (by
          intro s hs
          rw [uIoc_of_le hv.1.le] at hs
          simpa only [Real.norm_eq_abs] using hA s ⟨hs.1.le, hs.2.trans hv.2.le⟩)
      simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hv.1)] using ht
    have ha : |S.phi ui v| ≤ A := by
      rw [havg, abs_div, abs_of_pos (sub_pos.mpr hv.1)]
      exact (div_le_iff₀ (sub_pos.mpr hv.1)).mpr hi
    exact abs_le.mp ha
  have hc := continuous_out h.regularCenter.continuous_phi
    (outSeg_subset_triangle le_rfl h.initial_negative le_rfl le_rfl)
  exact abs_le.mpr (interval_bounds_of_open h.initial_negative hc hb v hv)

/-- The initial outgoing scalar amplitude is bounded by twice the datum bound.
Paper `e1a0fd5`, lines 387–393, `eq:scalar-bound-running-maximum`. -/
theorem theta_initial_le {A v : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A) (hv : v ∈ Icc ui 0) :
    |S.theta ui v| ≤ 2 * A := by
  unfold SSFields.theta
  rw [(h.initial_gauge v hv).2, one_mul]
  exact (abs_sub _ _).trans (by linarith [hA v hv, h.scalar_initial_le hA hv])

/-- AC of the prescribed initial datum gives a single uniform initial bound.
Paper `e1a0fd5`, lines 387–393, `eq:initial-ac-data`. -/
theorem exists_initial_scalar_bound : ∃ A : ℝ, 0 ≤ A ∧
    ∀ v ∈ Icc ui 0, |S.dvpsi ui v| ≤ A ∧ |S.phi ui v| ≤ A ∧
      |S.theta ui v| ≤ 2 * A := by
  have hc : ContinuousOn (S.dvpsi ui) (Icc ui 0) := by
    simpa only [uIcc_of_le h.initial_negative.le] using h.initial_ac_data.continuousOn
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr h.initial_negative.le) hc.abs
  refine ⟨|S.dvpsi ui v|, abs_nonneg _, ?_⟩
  have hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ |S.dvpsi ui v| := hmax
  intro s hs
  exact ⟨hA s hs, h.scalar_initial_le hA hs, h.theta_initial_le hA hs⟩

end StandingFull

end AcExtensionPrinciple

end
