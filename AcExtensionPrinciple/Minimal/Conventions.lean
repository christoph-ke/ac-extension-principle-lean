module

public import AcExtensionPrinciple.Minimal.LambdaContinuity
public import AcExtensionPrinciple.Redundancy.IncomingScalarConvention

/-!
# Restore representative conventions from derived continuity
Paper `e1a0fd5`, `equations.tex` lines 220–275.
The incoming ψ transport uses the normalized axis trace and stored value.
No right-continuity field of the full working class is used.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The outgoing scalar right-continuity field follows from all remaining standing hypotheses.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:wave-psi`, `eq:regular-axis-scalar-traces`. -/
theorem MinimalExpansionDraft.dvpsi_right_cont {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
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


/-- The incoming scalar right-continuity field follows from the remaining standing hypotheses.
Incoming right sections at the axis are singletons. Paper `e1a0fd5`, lines 220–275,
`eq:regular-axis-scalar-traces`, `eq:wave-psi`. -/
theorem MinimalExpansionDraft.dupsi_right_cont {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (fun u => S.dupsi u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui} p.1 := by
  have hf := q1_forcing_continuous h.toQ1StandingCore h.continuous_r h.continuous_m
    h.continuous_lam h.continuous_nu h.continuous_phi
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · apply continuousWithinAt_singleton.mono
    intro u hu
    simp only [mem_singleton_iff]
    have hvu := hu.2.2.2.1
    linarith [hu.1]
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    exact q1_outgoing_transport_right_cont hp.1 he hp.2.2.2 hf
      h.regularCenter.localBV.dupsi_out
      (q1_scalar_axis_trace ha h.continuous_nu
        (fun q hq => (h.toQ1StandingCore.nu_neg hq).ne)
        (h.regularCenter.axis_dupsi_trace p.1 ha)
        (h.regularCenter.axis_dupsi_value p.1 ha))

/-- Derived joint λ continuity supplies the outgoing representative convention.
Paper `e1a0fd5`, line 222, Luk–Oh BV convention. -/
theorem MinimalExpansionDraft.lam_right_cont {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (S.lam p.1)
      {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2 :=
  fun _ hp => q1_right_cont_out_of_continuous h.continuous_lam hp

/-- Retained joint ν continuity supplies the incoming representative convention.
Paper `e1a0fd5`, line 222, Luk–Oh BV convention. -/
theorem MinimalExpansionDraft.nu_right_cont {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (fun u => S.nu u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui} p.1 :=
  fun _ hp => q1_right_cont_in_of_continuous h.continuous_nu hp

end AcExtensionPrinciple

end
