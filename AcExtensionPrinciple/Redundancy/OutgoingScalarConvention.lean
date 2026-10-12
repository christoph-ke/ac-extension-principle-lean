module

public import AcExtensionPrinciple.Redundancy.RestoreConventions
public import AcExtensionPrinciple.Redundancy.Geometry
public import AcExtensionPrinciple.Redundancy.ExpansionConvention

/-!
# The outgoing scalar right-continuity convention is redundant
Paper commit `e1a0fd5`, `equations.tex` lines 114–132 and 220–275,
`eq:wave-psi`, `eq:regular-axis-scalar-traces`. The incoming transport
starts at an AC initial datum. Both the axis limit and axis value are used.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A normalized joint axis trace and its value give outgoing right-continuity of the unnormalized
field. All premises come from the retained core and expansion continuity. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, lines 247–261. -/
theorem q1_scalar_axis_right_cont {ui a : ℝ} {S : SSFields}
    {f g : ℝ → ℝ → ℝ} (ha : (a, a) ∈ axis ui)
    (hg : ContinuousOn (fun p => g p.1 p.2) (pastTriangle ui))
    (hne : ∀ p ∈ pastTriangle ui, g p.1 p.2 ≠ 0)
    (htrace : Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / g p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)))
    (hvalue : f a a / g a a = S.phi a a) :
    ContinuousWithinAt (f a) {w | a ≤ w ∧ (a, w) ∈ pastTriangle ui} a := by
  let A := {w : ℝ | a ≤ w ∧ (a, w) ∈ pastTriangle ui}
  have hm : MapsTo (fun w : ℝ => (a, w)) (A \ {a}) (pastTriangle ui \ axis ui) := by
    intro w hw
    refine ⟨hw.1.2, ?_⟩
    intro hwa
    exact hw.2 hwa.2.2
  have hc : ContinuousWithinAt (fun w : ℝ => (a, w)) (A \ {a}) a :=
    (continuous_const.prodMk continuous_id).continuousWithinAt
  have ht : Tendsto (fun w : ℝ => (a, w)) (𝓝[A \ {a}] a)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) :=
    hc.tendsto_nhdsWithin hm
  have hgt : Tendsto (fun w => g a w) (𝓝[A \ {a}] a) (𝓝 (g a a)) :=
    ((hg (a, a) (axis_subset_pastTriangle ui ha)).comp_of_eq hc
      (fun _ hw => hw.1.2) rfl).tendsto
  have hprod := (htrace.comp ht).mul hgt
  have hv := (div_eq_iff (hne (a, a) (axis_subset_pastTriangle ui ha))).mp hvalue
  have hf : ContinuousWithinAt (f a) (A \ {a}) a := by
    rw [ContinuousWithinAt, hv]
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact div_mul_cancel₀ _ (hne (a, w) hw.1.2)
  exact continuousWithinAt_sdiff_self.mp hf

/-- Incoming transport and the initial AC datum give joint outgoing-scalar continuity off-axis,
without its BV representative convention. Paper `e1a0fd5`, `eq:wave-psi`, lines 66–84 and
114–132. -/
theorem q1_dvpsi_continuous_offAxis {ui : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S)
    (hf : ContinuousOn (fun p => S.radiusCoeff p.1 p.2 * S.phi p.1 p.2)
      (cylinderScalarRegion ui)) :
    ContinuousOn (fun p => S.dvpsi p.1 p.2) (cylinderScalarRegion ui) := by
  have hc := cylinder_primitive_continuous_region
    (F := fun u v => S.radiusCoeff u v * S.phi u v) hf
  have hi : ContinuousOn (fun p : ℝ × ℝ => S.dvpsi ui p.2)
      (cylinderScalarRegion ui) :=
    h.initial_ac_data.continuousOn.comp continuous_snd.continuousOn
      (fun p hp => by
        rw [uIcc_of_le h.initial_negative.le]
        exact ⟨(hp.1.trans_lt hp.2.1).le, hp.2.2⟩)
  apply (hc.add hi).congr
  intro p hp
  have he := (h.regularCenter.localBV.dvpsi_in p.2 ui p.1 hp.1
    (inSeg_subset_offAxis le_rfl (hp.2.1.trans_le hp.2.2) hp.2.1 hp.2.2)).2
  dsimp only [Pi.add_apply] at *
  linarith

/-- The outgoing scalar right-continuity field follows from all remaining standing hypotheses.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:wave-psi`, `eq:regular-axis-scalar-traces`. -/
theorem dvpsi_right_cont_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_dvpsi_right_cont ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (S.dvpsi p.1)
      {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2 := by
  have hf := q1_forcing_continuous h.toQ1StandingCore h.continuous_r h.continuous_m
    h.continuous_lam h.continuous_nu h.continuous_phi
  have hc := q1_dvpsi_continuous_offAxis h.toQ1StandingCore hf
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    simpa only [← he] using q1_scalar_axis_right_cont ha h.continuous_lam
      (fun q hq => (h.toQ1StandingCore.lam_pos hq).ne')
      (h.regularCenter.axis_dvpsi_trace p.1 ha)
      (h.regularCenter.axis_dvpsi_value p.1 ha)
  · apply (hc p ⟨hp.1, he, hp.2.2.2⟩).comp_of_eq
      ((continuous_const.prodMk continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun w : ℝ => (p.1, w)) _ p.2) ?_ rfl
    intro w hw
    exact ⟨hw.2.1, he.trans_le hw.1, hw.2.2.2.2⟩

end AcExtensionPrinciple

end
