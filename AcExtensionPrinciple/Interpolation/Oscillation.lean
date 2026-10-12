module

public import AcExtensionPrinciple.Interpolation.RadiusChart

/-!
# Oscillation of the scalar amplitude

Paper `e1a0fd5`, `eq:radial-amplitude-oscillation`, lines 627–633.
The rough initial contribution is bounded by the initial AC tail; the
remaining radial variation is bounded by a logarithmic radius ratio.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Algebraic derivative majorant from the radial datum decomposition.
Paper `e1a0fd5`, lines 622–633. -/
theorem amplitude_derivative_majorant {l r f R A D M : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hR : |R| ≤ D / r) (hA : |A| ≤ M) :
    |l * (f / l ^ 2 + R - A / r)| ≤
      |f| / l + (D + M) * (l / r) := by
  rw [abs_mul, abs_of_pos hl]
  calc
    _ ≤ l * (|f / l ^ 2 + R| + |A / r|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hl.le
    _ ≤ l * ((|f / l ^ 2| + |R|) + |A / r|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ l * ((|f| / l ^ 2 + D / r) + M / r) := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hl), abs_div, abs_of_pos hr]
      gcongr
    _ = _ := by field_simp; ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Integrability of the transported absolute initial derivative on a cone.
Paper `e1a0fd5`, `eq:initial-tail-transport`, lines 583–588. -/
theorem initial_tail_weight_integrable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    IntervalIntegrable (fun v => |deriv (S.dvpsi ui) v| / S.lam u v) volume u 0 := by
  have hi := h.initial_second_derivative_integrable.abs.mono_set
    (show uIcc u 0 ⊆ uIcc ui 0 by
      rw [uIcc_of_le hu0.le, uIcc_of_le h.initial_negative.le]
      exact Icc_subset_Icc hu le_rfl)
  have hl := continuous_out h.regularCenter.continuous_lam
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  have hinv : ContinuousOn (fun v => (S.lam u v)⁻¹) (uIcc u 0) := by
    rw [uIcc_of_le hu0.le]
    exact hl.inv₀ (fun v hv => (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv⟩).ne')
  simpa only [div_eq_mul_inv] using hi.mul_continuousOn hinv

/-- Oscillation on any proper cone annulus, with explicit constants from
Lemma 2.1 and the remainder bound. Both premises are discharged by the class
theorems in `Interpolation.Uniform`. Paper `e1a0fd5`,
`eq:radial-amplitude-oscillation`, lines 627–633. -/
theorem outgoingAmplitude_oscillation_of_bounds {M D u a b : ℝ}
    (_hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hscalar : ∀ p ∈ pastTriangle ui, |outgoingAmplitude S p.1 p.2| ≤ M)
    (hrem : ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
      |radialDatumRemainderIntegral ui S u v| ≤ D / S.r u v)
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) :
    |outgoingAmplitude S u a - outgoingAmplitude S u b| ≤
      Real.exp (Bstar ui S) * initialACTail ui S u +
        (D + M) * Real.log (S.r u b / S.r u a) := by
  let F := fun v => S.lam u v *
    (radialDatumDerivative S u v - outgoingAmplitude S u v / S.r u v)
  let J := fun v => |deriv (S.dvpsi ui) v| / S.lam u v
  let G := fun v => S.lam u v / S.r u v
  have hp : ∀ v ∈ Icc a b, (u, v) ∈ pastTriangle ui := fun v hv =>
    ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb⟩
  have hprim := h.outgoingAmplitude_primitive hu hu0 hua hab hb
  have hfull := h.initial_tail_weight_integrable hu hu0
  have hsub : uIcc a b ⊆ uIcc u 0 := by
    rw [uIcc_of_le hab, uIcc_of_le hu0.le]
    exact Icc_subset_Icc hua.le hb
  have hJi : IntervalIntegrable J volume a b := hfull.mono_set hsub
  have hs := outSeg_subset_triangle hu hu0 hua.le hb
  have hGc : ContinuousOn G (Icc a b) :=
    (continuous_out h.regularCenter.continuous_lam hs).div
      (continuous_out h.regularCenter.continuous_r hs)
      (fun v hv => (h.r_pos (hp v hv) (hua.trans_le hv.1)).ne')
  have hGi := hGc.intervalIntegrable_of_Icc (μ := volume) hab
  have hle : (∫ v in a..b, |F v|) ≤ ∫ v in a..b, J v + (D + M) * G v := by
    apply intervalIntegral.integral_mono_ae_restrict hab hprim.1.abs
      (hJi.add (hGi.const_mul (D + M)))
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h.radialDatumDerivative_ae_decomposition] with v hvd hv
    have huv := hua.trans hv.1
    have hv0 := hv.2.trans_le hb
    rw [hvd ⟨hu.trans_lt huv, hv0⟩ u hu hu0 huv]
    exact amplitude_derivative_majorant (h.lam_pos (hp v (Ioo_subset_Icc_self hv)))
      (h.r_pos (hp v (Ioo_subset_Icc_self hv)) huv)
      (hrem u v hu hu0 huv hv0.le) (hscalar (u, v) (hp v (Ioo_subset_Icc_self hv)))
  have htail : (∫ v in a..b, J v) ≤ Real.exp (Bstar ui S) * initialACTail ui S u := by
    apply (intervalIntegral.integral_mono_interval hua.le hab hb ?_ hfull).trans
      (h.initial_tail_transport hu hu0)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
    exact div_nonneg (abs_nonneg _) (h.lam_pos (p := (u, v))
      ⟨hu, hu0, hv.1.le, hv.2⟩).le
  have hnorm : |outgoingAmplitude S u a - outgoingAmplitude S u b| ≤ ∫ v in a..b, |F v| := by
    rw [abs_sub_comm, hprim.2]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  rw [intervalIntegral.integral_add hJi (hGi.const_mul (D + M)),
    intervalIntegral.integral_const_mul,
    h.outgoing_log_radius_integral hu hu0 hua hab hb] at hle
  exact hnorm.trans (hle.trans (by linarith only [htail]))

end StandingFull

end AcExtensionPrinciple

end
