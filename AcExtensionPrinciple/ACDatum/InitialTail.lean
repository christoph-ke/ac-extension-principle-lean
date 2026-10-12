module

public import AcExtensionPrinciple.GeometricBounds.Blueshift

/-!
# Transport of the initial absolutely continuous tail

Paper commit `e1a0fd5`, `eq:initial-ac-tail`
and `eq:initial-tail-transport` (`equations.tex` lines 537–543, 583–588).
These conclusions use only the initial AC datum and the proved λ bounds.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Initial derivative tail ω. Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 539–541. -/
@[expose] noncomputable def initialACTail (ui : ℝ) (S : SSFields) (u : ℝ) : ℝ :=
  ∫ v in u..0, |deriv (S.dvpsi ui) v|

/-- The radial derivative of the normalized datum, with the usual a.e. meaning
of `deriv`. Paper `e1a0fd5`, `eq:radial-datum-derivative`, lines 557–558. -/
@[expose] noncomputable def radialDatumDerivative (S : SSFields) (u v : ℝ) : ℝ :=
  deriv (fun w => S.dvpsi u w / S.lam u w) v / S.lam u v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)

include h

/-- The initial second derivative is integrable on the prescribed data segment.
Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 537–543. -/
theorem initial_second_derivative_integrable :
    IntervalIntegrable (deriv (S.dvpsi ui)) volume ui 0 :=
  h.initial_ac_data.intervalIntegrable_deriv

/-- The initial gauge identifies q with the second derivative of the initial
datum almost everywhere in the data interval. Paper `e1a0fd5`,
`eq:rough-derivative-decomposition`, lines 572–574 and 603. -/
theorem radialDatumDerivative_initial_ae :
    ∀ᵐ v, v ∈ Ioo ui 0 →
      radialDatumDerivative S ui v = deriv (S.dvpsi ui) v := by
  filter_upwards [h.initial_ac_data.ae_differentiableAt] with v hd
  intro hv
  have hvcc : v ∈ Icc ui 0 := ⟨hv.1.le, hv.2.le⟩
  have hdiff := hd (by simpa only [uIcc_of_le h.initial_negative.le] using hvcc)
  have hderiv : HasDerivAt (fun w => S.dvpsi ui w / S.lam ui w)
      (deriv (S.dvpsi ui) v) v := by
    apply hdiff.hasDerivAt.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with w hw
    rw [(h.initial_gauge w hw).2, div_one]
  simp only [radialDatumDerivative, hderiv.deriv, (h.initial_gauge v hvcc).2, div_one]

omit h in
/-- Every initial AC tail is nonnegative. Paper `e1a0fd5`,
`eq:initial-ac-tail`, lines 539–543. -/
theorem initialACTail_nonneg {u : ℝ} (hu : u ≤ 0) : 0 ≤ initialACTail ui S u := by
  exact intervalIntegral.integral_nonneg hu (fun _ _ => abs_nonneg _)

/-- The initial AC tail tends to zero as the incoming label approaches zero
from below. Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 539–543. -/
theorem initialACTail_tendsto_zero :
    Tendsto (initialACTail ui S) (𝓝[<] 0) (𝓝 0) := by
  have hi : IntervalIntegrable (fun v => |deriv (S.dvpsi ui) v|) volume ui 0 := by
    simpa [Real.norm_eq_abs] using h.initial_second_derivative_integrable.norm
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show ui ∈ uIcc ui 0 by simp)
  have hf : ContinuousOn (initialACTail ui S) (Icc ui 0) := by
    have he : ∀ u ∈ Icc ui 0, initialACTail ui S u =
        (∫ v in ui..0, |deriv (S.dvpsi ui) v|) -
          ∫ v in ui..u, |deriv (S.dvpsi ui) v| := by
      intro u hu
      have hiu : IntervalIntegrable (fun v => |deriv (S.dvpsi ui) v|) volume ui u := by
        apply hi.mono_set
        simpa only [uIcc_of_le h.initial_negative.le, uIcc_of_le hu.1] using
          (show Icc ui u ⊆ Icc ui 0 from Icc_subset_Icc le_rfl hu.2)
      have hiu0 : IntervalIntegrable (fun v => |deriv (S.dvpsi ui) v|) volume u 0 := by
        apply hi.mono_set
        simpa only [uIcc_of_le h.initial_negative.le, uIcc_of_le hu.2] using
          (show Icc u 0 ⊆ Icc ui 0 from Icc_subset_Icc hu.1 le_rfl)
      have ha := intervalIntegral.integral_add_adjacent_intervals hiu hiu0
      change _ = _ at ha
      dsimp [initialACTail]
      linarith
    have hc' : ContinuousOn (fun u => ∫ v in ui..u, |deriv (S.dvpsi ui) v|)
        (Icc ui 0) := by
      simpa only [uIcc_of_le h.initial_negative.le] using hc
    have hconst : ContinuousOn (fun _ : ℝ => ∫ v in ui..0, |deriv (S.dvpsi ui) v|)
        (Icc ui 0) := continuousOn_const
    exact (hconst.sub hc').congr he
  have ht0 := hf 0 ⟨h.initial_negative.le, le_rfl⟩
  have he : Icc ui 0 ∈ 𝓝[<] (0 : ℝ) := by
    apply mem_of_superset (Ioo_mem_nhdsLT h.initial_negative)
    exact Ioo_subset_Icc_self
  have hm : 𝓝[<] (0 : ℝ) ≤ 𝓝[Icc ui 0] 0 := nhdsWithin_le_of_mem he
  simpa [initialACTail] using ht0.mono_left hm

/-- Cancellation of the radial measure λ dv in the initial rough term.
Paper `e1a0fd5`, `eq:initial-tail-transport`, lines 585–586. -/
theorem initial_tail_radial_measure {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    (∫ v in u..0, |deriv (S.dvpsi ui) v / S.lam u v ^ 2| * S.lam u v) =
      ∫ v in u..0, |deriv (S.dvpsi ui) v| / S.lam u v := by
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu0.le] at hv
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv⟩
  have hl := h.lam_pos hp
  dsimp only
  rw [abs_div, abs_of_pos (sq_pos_of_pos hl)]
  field_simp [hl.ne']

/-- The transported rough initial derivative has an explicit uniform tail bound.
Paper `e1a0fd5`, `eq:initial-tail-transport`, lines 583–588. -/
theorem initial_tail_transport {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    (∫ v in u..0, |deriv (S.dvpsi ui) v| / S.lam u v) ≤
      Real.exp (Bstar ui S) * initialACTail ui S u := by
  have hi := h.initial_second_derivative_integrable.norm.mono_set
    (show uIcc u 0 ⊆ uIcc ui 0 by
      simpa [uIcc_of_le hu0.le, uIcc_of_le h.initial_negative.le] using
        Icc_subset_Icc hu le_rfl)
  have hlc := continuous_out h.regularCenter.continuous_lam
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  have hinv : ContinuousOn (fun v => (S.lam u v)⁻¹) (uIcc u 0) := by
    rw [uIcc_of_le hu0.le]
    exact hlc.inv₀ (fun v hv => (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv⟩).ne')
  have hip : IntervalIntegrable (fun v => |deriv (S.dvpsi ui) v| / S.lam u v)
      volume u 0 := by
    simpa [Real.norm_eq_abs, div_eq_mul_inv] using hi.mul_continuousOn hinv
  calc
    _ ≤ ∫ v in u..0, |deriv (S.dvpsi ui) v| * Real.exp (Bstar ui S) := by
      apply intervalIntegral.integral_mono_on hu0.le hip
        (by simpa [Real.norm_eq_abs] using hi.mul_const (Real.exp (Bstar ui S)))
      intro v hv
      have hb := (h.lam_bounds (p := (u, v)) ⟨hu, hu0, hv⟩).1
      have hl := h.lam_pos (p := (u, v)) ⟨hu, hu0, hv⟩
      have he : (Real.exp (-Bstar ui S))⁻¹ = Real.exp (Bstar ui S) := by
        rw [Real.exp_neg, inv_inv]
      have hinvb : (S.lam u v)⁻¹ ≤ Real.exp (Bstar ui S) := by
        rw [← he]
        exact inv_anti₀ (Real.exp_pos _) hb
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinvb (abs_nonneg _)
    _ = Real.exp (Bstar ui S) * initialACTail ui S u := by
      rw [intervalIntegral.integral_mul_const, mul_comm]
      rfl

end StandingFull

end AcExtensionPrinciple

end
