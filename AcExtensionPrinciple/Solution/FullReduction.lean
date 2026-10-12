module

public import AcExtensionPrinciple.Solution.StandingFull
public import AcExtensionPrinciple.Minimal.OneSidedPaths

/-!
# Forget internal derived fields
Paper `e1a0fd5`, `equations.tex` lines 114–132 and 220–275.
These maps forget the restored additions; the arbitrary-domain local map
also preserves flat-space and gluing interfaces.
-/

public section

namespace AcExtensionPrinciple

/-- Forget scalar AC and the four representative conventions on any domain.
Paper `e1a0fd5`, lines 66–84 and 220–275. -/
theorem LocalBVSolutionFull.toMinimal {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : LocalBVSolutionFull D S) : LocalBVSolution D S := {
  radius_out := h.radius_out
  radius_in := h.radius_in
  psi_out := h.psi_out
  psi_in := h.psi_in
  mass_out := h.mass_out
  mass_in := h.mass_in
  lam_in := h.lam_in
  nu_out := h.nu_out
  dvpsi_in := h.dvpsi_in
  dupsi_out := h.dupsi_out
  expansion_bounds := h.expansion_bounds
  expansion_variation := h.expansion_variation
  expansion_axis_limit := h.expansion_axis_limit
  scalar_variation := by
    intro K hK hKD
    obtain ⟨C, hout, hin⟩ := h.scalar_ac_variation K hK hKD
    exact ⟨C, fun u a b hab hs => (hout u a b hab hs).2,
      fun v a b hab hs => (hin v a b hab hs).2⟩
  scalar_axis_variation := h.scalar_axis_variation
  psi_variation := h.psi_variation
  psi_axis_limit := h.psi_axis_limit
  axis_values := h.axis_values
}

/-- Forget the restored regular-center fields and restrict joint scalar traces
to the four one-sided characteristic traces, retaining ν continuity.
Paper `e1a0fd5`, lines 220–261, `eq:regular-axis-scalar-traces`. -/
theorem RegularCenterFull.toMinimal {ui : ℝ} {S : SSFields}
    (h : RegularCenterFull ui S) : RegularCenterLocalACBV ui S := {
  localBV := h.localBV.toMinimal
  continuous_nu := h.continuous_nu
  axis_expansions := h.axis_expansions
  axis_dvpsi_out := fun a ha => oneSided_outgoing_of_joint
    (f := fun u v => S.dvpsi u v / S.lam u v) ha (h.axis_dvpsi_trace a ha)
  axis_dupsi_out := fun a ha => oneSided_outgoing_of_joint
    (f := fun u v => S.dupsi u v / S.nu u v) ha (h.axis_dupsi_trace a ha)
  axis_dvpsi_in := fun a ha => oneSided_incoming_of_joint
    (f := fun u v => S.dvpsi u v / S.lam u v) ha (h.axis_dvpsi_trace a ha)
  axis_dupsi_in := fun a ha => oneSided_incoming_of_joint
    (f := fun u v => S.dupsi u v / S.nu u v) ha (h.axis_dupsi_trace a ha)
  axis_dvpsi_value := h.axis_dvpsi_value
  axis_dupsi_value := h.axis_dupsi_value
}

/-- Forget the internal full bundle while preserving every standing hypothesis
with the four one-sided scalar traces. Paper `e1a0fd5`, `thm:main`,
lines 114–132 and 220–261. -/
theorem StandingFull.toMinimal {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingAssumptions ui S := {
  initial_negative := h.initial_negative
  regularCenter := h.regularCenter.toMinimal
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

end AcExtensionPrinciple

end
