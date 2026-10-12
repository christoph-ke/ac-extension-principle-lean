module

public import AcExtensionPrinciple.ScalarBound.NormalizedDatum

/-!
# Extending scalar bounds by regular-axis traces

Paper commit `e1a0fd5`, `equations.tex`
lines 247–261 and 524–534. The two definitions below implement the paper's
trace convention. The regular-axis value identities now identify these
representatives with the raw normalized derivative fields on the triangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- θ/λ off the axis, extended by its zero regular-axis trace.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, lines 524–534. -/
@[expose] noncomputable def scalarThetaTrace (S : SSFields) (u v : ℝ) : ℝ :=
  if u = v then 0 else S.theta u v / S.lam u v

/-- dvψ/λ off the axis, extended by the scalar regular-axis trace.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, lines 247–261 and 534. -/
@[expose] noncomputable def scalarDatumTrace (S : SSFields) (u v : ℝ) : ℝ :=
  if u = v then S.phi u v else S.dvpsi u v / S.lam u v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The raw outgoing scalar amplitude vanishes on the regular axis.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`,
`eq:normalized-scalar-derivatives`, lines 247–261 and 534. -/
theorem theta_axis_eq_zero {a : ℝ} (ha : (a, a) ∈ axis ui) : S.theta a a = 0 := by
  have hv := h.regularCenter.axis_dvpsi_value a ha
  have hn := (h.lam_pos (axis_subset_pastTriangle ui ha)).ne'
  have he : S.dvpsi a a = S.lam a a * S.phi a a := by
    calc
      _ = (S.dvpsi a a / S.lam a a) * S.lam a a := (div_mul_cancel₀ _ hn).symm
      _ = _ := by rw [hv]; ring
  simp only [SSFields.theta, he, sub_self]

/-- The normalized amplitude trace representative agrees with the raw
field throughout the triangle. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, lines 247–261 and 534. -/
theorem scalarThetaTrace_eq_raw {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    scalarThetaTrace S p.1 p.2 = S.theta p.1 p.2 / S.lam p.1 p.2 := by
  by_cases he : p.1 = p.2
  · simp only [scalarThetaTrace, ite_eq_left he]
    rw [← he, h.theta_axis_eq_zero ⟨hp.1, hp.2.1, rfl⟩, zero_div]
  · simp only [scalarThetaTrace, ite_eq_right he]

/-- The normalized datum trace representative agrees with the raw field
throughout the triangle. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, lines 247–261 and 534. -/
theorem scalarDatumTrace_eq_raw {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    scalarDatumTrace S p.1 p.2 = S.dvpsi p.1 p.2 / S.lam p.1 p.2 := by
  by_cases he : p.1 = p.2
  · simp only [scalarDatumTrace, ite_eq_left he]
    rw [← he, h.regularCenter.axis_dvpsi_value p.1 ⟨hp.1, hp.2.1, rfl⟩]
  · simp only [scalarDatumTrace, ite_eq_right he]

/-- The off-axis normalized amplitude has the zero regular-axis trace,
justifying the extension used in `scalarThetaTrace`. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, `eq:normalized-scalar-derivatives`, line 534. -/
theorem scalar_theta_axis_trace {a : ℝ} (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.theta p.1 p.2 / S.lam p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 0) := by
  have hphi := (h.regularCenter.continuous_phi (a, a)
    (axis_subset_pastTriangle ui ha)).mono (sdiff_subset : pastTriangle ui \ axis ui ⊆ pastTriangle ui)
  have ht := (h.regularCenter.axis_dvpsi_trace a ha).sub hphi
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with p hp
  unfold SSFields.theta
  field_simp [(h.lam_pos hp.1).ne']

/-- A uniform normalized-datum bound passes to its regular-axis trace.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 534. -/
theorem axis_scalar_le_of_normalized_datum_bound {C a : ℝ}
    (ha : (a, a) ∈ axis ui)
    (hC : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.dvpsi p.1 p.2 / S.lam p.1 p.2| ≤ C) :
    |S.phi a a| ≤ C := by
  have hna : (𝓝[Ioo a 0] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (by rw [closure_Ioo ha.2.1.ne]; exact left_mem_Icc.mpr ha.2.1.le)
  haveI := hna
  have ht : Tendsto (fun v : ℝ => (a, v)) (𝓝[Ioo a 0] a)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_const.continuousAt.prodMk_nhds continuous_id.continuousAt |>.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with v hv
    exact ⟨⟨ha.1, ha.2.1, hv.1.le, hv.2.le⟩, by
      intro hav
      have he : v = a := hav.2.2
      linarith [hv.1]⟩
  have hnb : (𝓝[pastTriangle ui \ axis ui] (a, a)).NeBot := ht.neBot
  haveI := hnb
  apply le_of_tendsto (h.regularCenter.axis_dvpsi_trace a ha).abs
  filter_upwards [eventually_mem_nhdsWithin] with p hp
  have huv : p.1 < p.2 := by
    apply lt_of_le_of_ne hp.1.2.2.1
    intro he
    apply hp.2
    exact ⟨hp.1.1, hp.1.2.1, he.symm⟩
  exact hC p hp.1 huv

/-- Off-axis sum of the three scalar bounds, after the amplitude estimate.
The amplitude premise is discharged by the strip/mass argument.
Paper `e1a0fd5`, `eq:uniform-scalar-bound`, lines 524–534. -/
theorem scalar_sum_le_of_theta_bound {A T u v : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A)
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    |S.theta u v / S.lam u v| + |S.dvpsi u v / S.lam u v| + |S.phi u v| ≤
      2 * (A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S))) := by
  linarith [h.normalized_theta_le_of_theta_bound hT hp huv,
    h.normalized_datum_le_of_theta_bound hA hT hp huv,
    h.scalar_le_of_theta_bound hA hT hp huv]

/-- The bound including the paper's regular-axis trace convention, after
the amplitude estimate. Paper `e1a0fd5`, `eq:uniform-scalar-bound`, line 534. -/
theorem scalar_trace_sum_le_of_theta_bound {A T : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A)
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T) :
    ∀ p ∈ pastTriangle ui,
      |scalarThetaTrace S p.1 p.2| + |scalarDatumTrace S p.1 p.2| + |S.phi p.1 p.2| ≤
        2 * (A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S))) := by
  intro p hp
  by_cases he : p.1 = p.2
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have hb := h.axis_scalar_le_of_normalized_datum_bound ha
      (fun p hp huv => h.normalized_datum_le_of_theta_bound hA hT hp huv)
    have hN : 0 ≤ T / Real.exp (-Bstar ui S) :=
      div_nonneg ((abs_nonneg _).trans (hT (ui, 0)
        ⟨le_rfl, h.initial_negative, h.initial_negative.le, le_rfl⟩ h.initial_negative))
        (Real.exp_pos _).le
    simp only [scalarThetaTrace, scalarDatumTrace, ite_eq_left he, abs_zero, zero_add]
    rw [← he]
    linarith
  · simp only [scalarThetaTrace, scalarDatumTrace, ite_eq_right he]
    exact h.scalar_sum_le_of_theta_bound hA hT hp (lt_of_le_of_ne hp.2.2.1 he)

/-- The uniform sum bound for raw fields on the whole triangle, obtained
from the trace bound and the regular-axis value identities. The amplitude
premise is discharged by the strip/mass argument. Paper `e1a0fd5`,
`eq:uniform-scalar-bound`, `eq:regular-axis-scalar-traces`, lines 524–535. -/
theorem scalar_sum_on_triangle_le_of_theta_bound {A T : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A)
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T) :
    ∀ p ∈ pastTriangle ui,
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤
          2 * (A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S))) := by
  intro p hp
  have hb := h.scalar_trace_sum_le_of_theta_bound hA hT p hp
  rwa [h.scalarThetaTrace_eq_raw hp, h.scalarDatumTrace_eq_raw hp] at hb

end StandingFull

end AcExtensionPrinciple

end
