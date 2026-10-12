module

public import AcExtensionPrinciple.ACDatum.UniformRemainder
public import AcExtensionPrinciple.ScalarBound.Uniform
public import AcExtensionPrinciple.Decay.Interpolation

/-!
# Cone calculus for AC interpolation

Paper `e1a0fd5`, `lem:ac-interpolation`, `equations.tex` lines 618–659.
The normalized scalar amplitude is AC and its derivative separates the
transported initial density from a uniformly bounded radial remainder.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Normalized outgoing scalar amplitude. Paper `e1a0fd5`,
`eq:ac-interpolation`, lines 611–613. -/
@[expose] noncomputable def outgoingAmplitude (S : SSFields) (u v : ℝ) : ℝ :=
  S.theta u v / S.lam u v

/-- The amplitude is the normalized datum minus the scalar. Paper `e1a0fd5`,
`eq:normalized-scalar-derivatives`, used at lines 622–626. -/
theorem outgoingAmplitude_eq (S : SSFields) {u v : ℝ} (hl : S.lam u v ≠ 0) :
    outgoingAmplitude S u v = S.dvpsi u v / S.lam u v - S.phi u v := by
  dsimp [outgoingAmplitude, SSFields.theta]
  field_simp

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- AC of the amplitude on every off-axis cone segment. Paper `e1a0fd5`,
`eq:scalar-amplitude-radial-derivative`, lines 622–626. -/
theorem outgoingAmplitude_ac {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) :
    AbsolutelyContinuousOnInterval (outgoingAmplitude S u) a b := by
  have hP := (h.normalized_datum_ac_out hu hu0).mono
    (show uIcc a b ⊆ uIcc u 0 by
      rw [uIcc_of_le hab, uIcc_of_le hu0.le]
      exact Icc_subset_Icc hua.le hb)
  have hf := intervalPrimitive_ac hab (fun x hx =>
    h.scalar_primitive_out hx.1 hu hu0 hua (hx.2.trans hb))
  apply (hP.fun_sub hf).congr
  intro v hv
  rw [uIcc_of_le hab] at hv
  exact (outgoingAmplitude_eq S (h.lam_pos
    (p := (u, v)) ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb⟩).ne').symm

/-- Coordinate form of the radial amplitude derivative, including its
integral equation. Paper `e1a0fd5`,
`eq:scalar-amplitude-radial-derivative`, lines 622–626. -/
theorem outgoingAmplitude_primitive {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) :
    IntervalPrimitive (outgoingAmplitude S u)
      (fun v => S.lam u v * (radialDatumDerivative S u v -
        outgoingAmplitude S u v / S.r u v)) a b := by
  have hP := (h.normalized_datum_ac_out hu hu0).mono
    (show uIcc a b ⊆ uIcc u 0 by
      rw [uIcc_of_le hab, uIcc_of_le hu0.le]
      exact Icc_subset_Icc hua.le hb)
  have hf := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.scalar_primitive_out hx.1 hu hu0 hua (hx.2.trans hb))
  apply ac_integral_eq_sub hab (h.outgoingAmplitude_ac hu hu0 hua hab hb)
  filter_upwards [hP.ae_differentiableAt, hf] with v hPv hfv
  intro hv
  have hp : (u, v) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans hv.1).le, hv.2.le.trans hb⟩
  have hl := h.lam_pos hp
  have he : outgoingAmplitude S u =ᶠ[𝓝 v]
      (fun x => S.dvpsi u x / S.lam u x - S.phi u x) := by
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with x hx
    exact outgoingAmplitude_eq S (h.lam_pos (p := (u, x))
      ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb⟩).ne'
  have hd := ((hPv (by simpa only [uIcc_of_le hab] using
    Ioo_subset_Icc_self hv)).hasDerivAt.sub (hfv hv)).congr_of_eventuallyEq he
  apply hd.congr_deriv
  dsimp [radialDatumDerivative, outgoingAmplitude, SSFields.dvphi]
  field_simp [hl.ne']

/-- The radial logarithmic measure is λ/r dv. Paper `e1a0fd5`,
`eq:radial-amplitude-oscillation`, lines 627–633. -/
theorem outgoing_log_radius_integral {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) :
    (∫ v in a..b, S.lam u v / S.r u v) = Real.log (S.r u b / S.r u a) := by
  have hs := outSeg_subset_triangle hu hu0 hua.le hb
  have hr := continuous_out h.regularCenter.continuous_r hs
  have hl := continuous_out h.regularCenter.continuous_lam hs
  have hr0 : ∀ v ∈ Icc a b, 0 < S.r u v := fun v hv =>
    h.r_pos ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb⟩ (hua.trans_le hv.1)
  have hi := (hl.div hr (fun v hv => (hr0 v hv).ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hd : ∀ v ∈ Ioo a b, HasDerivAt (fun x => Real.log (S.r u x))
      (S.lam u v / S.r u v) v := by
    intro v hv
    exact (h.acdatum_radius_hasDerivAt_out hu hu0 (hua.trans hv.1) (hv.2.trans_le hb)).log
      (hr0 v (Ioo_subset_Icc_self hv)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hr.log (fun v hv => (hr0 v hv).ne')) hd hi]
  exact (Real.log_div (hr0 b ⟨hab, le_rfl⟩).ne' (hr0 a ⟨le_rfl, hab⟩).ne').symm

/-- A common constant bounds the nonlinear derivative remainder at every
proper point, including the terminal ray. Paper `e1a0fd5`,
`eq:derivative-remainder-bound`, lines 578–581, used at line 627. -/
theorem exists_radial_remainder_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
      |radialDatumRemainderIntegral ui S u v| ≤ D / S.r u v := by
  obtain ⟨M, hM⟩ := h.uniform_scalar_bound
  obtain ⟨D, hD, hbound⟩ := h.radialDatumRemainderIntegral_bound_of_scalar hM
  exact ⟨D, hD, fun u v hu hu0 huv hv =>
    (hbound u v hu hu0 huv hv).1.trans (hbound u v hu hu0 huv hv).2⟩

end StandingFull

end AcExtensionPrinciple

end
